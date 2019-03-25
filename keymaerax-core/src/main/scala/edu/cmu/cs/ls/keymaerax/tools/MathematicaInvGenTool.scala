package edu.cmu.cs.ls.keymaerax.tools

import java.io.{File, FileOutputStream}
import java.nio.channels.Channels

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.{FormulaTools, InvGenTool}
import edu.cmu.cs.ls.keymaerax.btactics.helpers.DifferentialHelper
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tools.MathematicaConversion.KExpr
import org.apache.logging.log4j.scala.Logging

import scala.collection.immutable.Seq
import scala.util.Try

/**
 * A continuous invariant implementation using Mathematica over the JLink interface.
 * @author Andrew Sogokon, based on QETool by Nathan Fulton and Stefan Mitsch
 */
class MathematicaInvGenTool(override val link: MathematicaLink)
  extends BaseKeYmaeraMathematicaBridge[KExpr](link, new UncheckedBaseK2MConverter(), PegasusM2KConverter)
    with InvGenTool with Logging {

  init()

  private val pegasusPath = System.getProperty("user.home") + File.separator + Configuration(Configuration.Keys.PEGASUS_PATH)

  def invgen(ode: ODESystem, assumptions: Seq[Formula], postCond: Formula): Seq[Either[Seq[Formula],Seq[Formula]]] = {
    require(postCond.isFOL, "Unable to generate invariant, expected FOL post conditions but got " + postCond.prettyString)

    val vars = DifferentialHelper.getPrimedVariables(ode)
    val stringVars = "{" + vars.map(k2m(_)).mkString(", ") + "}"
    val vectorField = "{" + DifferentialHelper.atomicOdes(ode).map(o => k2m(o.e)).mkString(", ") + "}"
    val problem = "{ " +
      k2m(assumptions.reduceOption(And).getOrElse(True)) + ", { " +
      vectorField + ", " +
      stringVars + ", " +
      k2m(ode.constraint) + " }, " +
      k2m(postCond) + " }"

    logger.debug("Raw Mathematica input into Pegasus: " + problem)

    timeout = Try(Integer.parseInt(Configuration(Configuration.Keys.PEGASUS_INVGEN_TIMEOUT))).getOrElse(-1)

    val command = s"""
       |SetDirectory["$pegasusPath"];
       |Needs["Strategies`","$pegasusPath/Strategies.m"];
       |Strategies`Pegasus[$problem]""".stripMargin.trim()

    try {
      val (output, result) = runUnchecked(command)
      logger.debug("Generated invariant: " + result.prettyString + " from raw output " + output)
      PegasusM2KConverter.decodeFormulaList(result).map({ case (fmls, flag) =>
        assert(flag == True || flag == False, "Expected invariant/candidate flag, but got " + flag.prettyString)
        if (flag == True) Left(fmls) else Right(fmls)
      })
    } catch {
      case ex: ConversionException =>
        logger.warn("Pegasus conversion exception", ex)
        Nil
    }
  }

  def lzzCheck(ode: ODESystem, inv: Formula): Boolean = {
    val vars = DifferentialHelper.getPrimedVariables(ode)
    val stringVars = "{" + vars.map(k2m(_)).mkString(", ") + "}"
    val vectorField = "{" + DifferentialHelper.atomicOdes(ode).map(o => k2m(o.e)).mkString(", ") + "}"
    val problem =
      k2m(inv) + ", " +
      vectorField + ", " +
      stringVars + ", " +
      k2m(ode.constraint)

    logger.debug("Raw Mathematica input into Pegasus: " + problem)

    timeout = Try(Integer.parseInt(Configuration(Configuration.Keys.PEGASUS_INVCHECK_TIMEOUT))).getOrElse(-1)

    val command = s"""
                  |SetDirectory["$pegasusPath"];
                  |Needs["LZZ`","$pegasusPath/LZZ.m"];
                  |LZZ`InvS[$problem]""".stripMargin.trim()

    val (output, result) = runUnchecked(command)
    logger.debug("LZZ check: "+ result.prettyString + " from raw output " + output)
    result match {
      case True => true
      case False => false
      case _ => throw ToolException("Expected true/false from Pegasus call but got expression: " +
        result.prettyString)
    }
  }

  override def refuteODE(ode: ODESystem, assumptions: Seq[Formula], postCond: Formula): Option[Map[NamedSymbol, KExpr]] = {
    require(postCond.isFOL, "Unable to refute ODE, expected FOL post conditions but got " + postCond.prettyString)
    require(assumptions.forall(_.isFOL), "Unable to refute ODE, expected FOL assumptions but got " + assumptions)

    // LHS of ODEs
    val odevars = DifferentialHelper.getPrimedVariables(ode)

    val rhs = DifferentialHelper.atomicOdes(ode).map(_.e)
    // All things that need to be considered as parameters (or variables)
    val fmlvars = (assumptions :+ postCond :+ ode.constraint).flatMap(StaticSemantics.symbols)
    val trmvars = rhs.flatMap(StaticSemantics.symbols)

    val vars = (trmvars ++ fmlvars).distinct.filter({ case Function(_, _, _, _, interpreted) => !interpreted case _ => true}).sorted
      .map({
        case f@Function(_,_,Unit,_,_) =>
          FuncOf(f,Nothing) //for k2m conversion to work reliably on constants
        case e => e
      } )

    val stringodeVars = "{" + odevars.map(k2m(_)).mkString(", ") + "}"
    val stringVars = "{" + vars.map(k2m(_)).mkString(", ") + "}"
    val vectorField = "{" + rhs.map(k2m(_)).mkString(", ") + "}"
    val problem =
      k2m(assumptions.reduceOption(And).getOrElse(True)) + "," +
      k2m(postCond) + "," +
      vectorField + ", " +
      stringodeVars + ", " +
      k2m(ode.constraint) + ", " +
      stringVars

    timeout = Try(Integer.parseInt(Configuration(Configuration.Keys.PEGASUS_INVCHECK_TIMEOUT))).getOrElse(-1)

    val command = s"""
                     |SetDirectory["$pegasusPath"];
                     |Needs["Refute`","$pegasusPath/Refute.m"];
                     |Refute`RefuteS[$problem]""".stripMargin.trim()

    try {
      val (output, result) = runUnchecked(command, CEXM2KConverter)
      logger.debug("Counterexample: " + result + " from raw output " + output)
      result match {
        case Left(cex: Formula) => cex match {
          case False =>
            logger.debug("No counterexample, Mathematica returned: " + cex.prettyString)
            None
          case _ =>
            logger.debug("Counterexample " + cex.prettyString)
            Some(FormulaTools.conjuncts(cex).map({
              case Equal(name: Variable, value) => name -> value
              case Equal(name: DifferentialSymbol, value) => name -> value
              case Equal(FuncOf(fn, _), value) => fn -> value
              case Equiv(PredOf(fn, _), value) => fn -> value
            }).toMap)
        }
        case _ =>
          logger.debug("No counterexample, Mathematica returned: " + result)
          None
      }
    } catch {
      case ex: ConversionException =>
        logger.warn("Conversion exception", ex)
        None
    }
  }

  private def init(): Unit = {
    // copy Pegasus Mathematica notebooks
    val pegasusTempDir = Configuration.path(Configuration.Keys.PEGASUS_PATH)
    if (!new File(pegasusTempDir).exists) new File(pegasusTempDir).mkdirs

    val pegasusResourcePath = "/pegasus-mathematica/"
    val pegasusResourceNames =
      "AbstractionPolynomials.m" ::
      "BarrierCertificateMethod.m" ::
      "Classifier.m" ::
      "DarbouxPolyGen.m" ::
      "DiscreteAbstraction.m" ::
      "FirstIntegralGen.m" ::
      "FirstIntegralMethod.m" ::
      "Linear.m" ::
      "LZZ.m" ::
      "MultiLinear.m" ::
      "NilpotentMethod.m" ::
      "OneDimensional.m" ::
      "PlanarLinear.m" ::
      "Primitives.m" ::
      "QualitativeMethods.m" ::
      "Refute.m" ::
      "Strategies.m" :: Nil

    pegasusResourceNames.foreach(n => {
      val pegasusDest = new FileOutputStream(pegasusTempDir + File.separator + n)
      val pegasusSrc = Channels.newChannel(getClass.getResourceAsStream(pegasusResourcePath + n))
      pegasusDest.getChannel.transferFrom(pegasusSrc, 0, Long.MaxValue)
    })
    val pegasusAbsPaths = pegasusResourceNames.map(n => pegasusTempDir + File.separator + n)
    assert(pegasusAbsPaths.forall(new File(_).exists()), "Missing Pegasus files")
  }

}
