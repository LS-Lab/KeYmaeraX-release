package edu.cmu.cs.ls.keymaerax.tools.ext

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.btactics.InvGenTool
import edu.cmu.cs.ls.keymaerax.btactics.helpers.DifferentialHelper
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.infrastruct.FormulaTools
import edu.cmu.cs.ls.keymaerax.tools.qe.MathematicaOpSpec._
import edu.cmu.cs.ls.keymaerax.tools.ext.ExtMathematicaOpSpec._
import edu.cmu.cs.ls.keymaerax.tools.ConversionException
import edu.cmu.cs.ls.keymaerax.tools.install.PegasusInstaller


import org.apache.logging.log4j.scala.Logging

import scala.collection.immutable.Seq
import scala.util.Try

/**
 * A continuous invariant implementation using Mathematica over the JLink interface.
 * @author Andrew Sogokon, based on QETool by Nathan Fulton and Stefan Mitsch
 */
class MathematicaInvGenTool(override val link: MathematicaLink)
  extends BaseKeYmaeraMathematicaBridge[Expression](link, new UncheckedBaseK2MConverter(), PegasusM2KConverter)
    with InvGenTool with Logging {

  private val PEGASUS_NAMESPACE = "Pegasus`"
  private val LZZ_NAMESPACE = "LZZ`"
  private val REFUTE_NAMESPACE = "Refute`"

  private val pegasusPath = PegasusInstaller.pegasusRelativeResourcePath
  private val pathSegments = scala.reflect.io.File(pegasusPath).segments.map(string)
  private val joinedPath = fileNameJoin(list(homeDirectory.op :: pathSegments:_*))
  private val setPathsCmd = compoundExpression(setDirectory(joinedPath), appendTo(path.op, joinedPath))

  /** @inheritdoc */
  override def invgen(ode: ODESystem, assumptions: Seq[Formula], postCond: Formula): Seq[Either[Seq[(Formula, String)], Seq[(Formula, String)]]] = {
    require(postCond.isFOL, "Unable to generate invariant, expected FOL post conditions but got " + postCond.prettyString)
    timeout = Try(Integer.parseInt(Configuration(Configuration.Keys.PEGASUS_INVGEN_TIMEOUT))).getOrElse(-1)

    val vars = list(DifferentialHelper.getPrimedVariables(ode).map(k2m):_*)
    val vectorField = list(DifferentialHelper.atomicOdes(ode).map(o => k2m(o.e)):_*)
    val problem = list(
      k2m(assumptions.reduceOption(And).getOrElse(True)),
      list(vectorField, vars, k2m(ode.constraint)),
      k2m(postCond)
    )
    logger.debug("Raw Mathematica input into Pegasus: " + problem)

    val sanityTimeout = rule(symbol("SanityTimeout"), int(Integer.parseInt(Configuration.getOption(Configuration.Keys.PEGASUS_SANITY_TIMEOUT).getOrElse("0"))))
    val pegasusMain = Configuration.getOption(Configuration.Keys.PEGASUS_MAIN_FILE).getOrElse("Pegasus.m")
    val command = compoundExpression(
      setPathsCmd,
      needs(string(PEGASUS_NAMESPACE), string(pegasusMain)),
      applyFunc(symbol(PEGASUS_NAMESPACE + "InvGen"))(problem, sanityTimeout)
    )

    try {
      val (output, result) = run(command)
      logger.debug("Generated invariant: " + result.prettyString + " from raw output " + output)
      (PegasusM2KConverter.decodeFormulaList(result)::Nil).map({ case (invariants, flag) =>
        assert(flag == True || flag == False, "Expected invariant/candidate flag, but got " + flag.prettyString)
        if (flag == True) Left(invariants) else Right(invariants)
      })
    } catch {
      case ex: ConversionException =>
        logger.warn("Pegasus conversion exception", ex)
        Nil
    }
  }

  /** @inheritdoc */
  override def lzzCheck(ode: ODESystem, inv: Formula): Boolean = {
    timeout = Try(Integer.parseInt(Configuration(Configuration.Keys.PEGASUS_INVCHECK_TIMEOUT))).getOrElse(-1)

    val vars = list(DifferentialHelper.getPrimedVariables(ode).map(k2m):_*)
    val vectorField = list(DifferentialHelper.atomicOdes(ode).map(o => k2m(o.e)):_*)
    val command = compoundExpression(
      setPathsCmd,
      needs(string(LZZ_NAMESPACE), fileNameJoin(list(string("Primitives"), string("LZZ.m")))),
      applyFunc(symbol(LZZ_NAMESPACE + "InvS"))(k2m(inv), vectorField, vars, k2m(ode.constraint))
    )

    val (output, result) = run(command)
    logger.debug("LZZ check: "+ result.prettyString + " from raw output " + output)
    result match {
      case True => true
      case False => false
      case _ => throw ConversionException("Expected true/false from Pegasus call but got expression: " +
        result.prettyString)
    }
  }

  /** @inheritdoc */
  override def refuteODE(ode: ODESystem, assumptions: Seq[Formula], postCond: Formula): Option[Map[NamedSymbol, Expression]] = {
    require(postCond.isFOL, "Unable to refute ODE, expected FOL post conditions but got " + postCond.prettyString)
    require(assumptions.forall(_.isFOL), "Unable to refute ODE, expected FOL assumptions but got " + assumptions)

    timeout = Try(Integer.parseInt(Configuration(Configuration.Keys.PEGASUS_INVCHECK_TIMEOUT))).getOrElse(-1)

    val rhs = DifferentialHelper.atomicOdes(ode).map(_.e)
    // All things that need to be considered as parameters (or variables)
    val fmlvars = (assumptions :+ postCond :+ ode.constraint).flatMap(StaticSemantics.symbols)
    val trmvars = rhs.flatMap(StaticSemantics.symbols)

    val vars = (trmvars ++ fmlvars).distinct.filter({ case Function(_, _, _, _, interpreted) => !interpreted case _ => true}).sorted
      .map({
        case f@Function(_,_,Unit,_,_) => FuncOf(f, Nothing) //for k2m conversion to work reliably on constants
        case e => e
      })

    val odeVars = list(DifferentialHelper.getPrimedVariables(ode).map(k2m):_*)
    val varsList = list(vars.map(k2m):_*)
    val vectorField = list(rhs.map(k2m):_*)

    val command = compoundExpression(
      setPathsCmd,
      needs(string(REFUTE_NAMESPACE), string("Refute.m")),
      applyFunc(symbol(REFUTE_NAMESPACE + "RefuteS"))(
        k2m(assumptions.reduceOption(And).getOrElse(True)),
        k2m(postCond),
        vectorField,
        odeVars,
        k2m(ode.constraint),
        varsList
      )
    )

    try {
      val (output, result) = run(command, CEXM2KConverter)
      logger.debug("Counterexample: " + result + " from raw output " + output)
      result match {
        case Left(cex: Formula) => cex match {
          case False =>
            logger.debug("No counterexample, Mathematica returned: " + cex.prettyString)
            None
          case _ =>
            logger.debug("Counterexample " + cex.prettyString)
            Some(FormulaTools.conjuncts(cex).map({
              case Equal(name: DifferentialSymbol, value) => name -> value
              case Equal(name: Variable, value) => name -> value
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

  /** @inheritdoc */
  override def genODECond(ode: ODESystem, assumptions: Seq[Formula], postCond: Formula): (List[Formula],List[Formula]) = {
    require(postCond.isFOL, "Unable to generate ODE conditions, expected FOL post conditions but got " + postCond.prettyString)
    require(assumptions.forall(_.isFOL), "Unable to generate ODE conditions, expected FOL assumptions but got " + assumptions)

    timeout = Try(Integer.parseInt(Configuration(Configuration.Keys.PEGASUS_INVCHECK_TIMEOUT))).getOrElse(-1)

    val odeVars = list(DifferentialHelper.getPrimedVariables(ode).map(k2m):_*)
    val vectorField = list(DifferentialHelper.atomicOdes(ode).map(_.e).map(k2m):_*)
    val command = compoundExpression(
      setPathsCmd,
      needs(string(REFUTE_NAMESPACE), string("Refute.m")),
      applyFunc(symbol(REFUTE_NAMESPACE + "SeqFml"))(
        k2m(assumptions.reduceOption(And).getOrElse(True)),
        k2m(postCond),
        vectorField,
        odeVars,
        k2m(ode.constraint)
      )
    )

    try {
      val (output, result) = run(command)
      result match {
        case And(Equal(_, n: Number), And(And(And( And(i1, i2), n1), n2), n3)) =>
          assert(n.value.toInt == 5)
          (List(i1, i2), List(n1, n2, n3))
        case _ =>
          logger.warn("Incorrect pattern returned: " + output)
          (List(), List())
      }
    }
  }
}
