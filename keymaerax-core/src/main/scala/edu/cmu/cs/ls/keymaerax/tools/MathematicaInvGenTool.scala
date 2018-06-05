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
  extends BaseKeYmaeraMathematicaBridge[KExpr](link, new UncheckedK2MConverter(), PegasusM2KConverter)
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
       |Needs["Strategies`","$pegasusPath/Strategies.m"];
       |Needs["Methods`","$pegasusPath/Methods.m"];
       |Needs["Classifier`","$pegasusPath/Classifier.m"];
       |Needs["AbstractionPolynomials`","$pegasusPath/AbstractionPolynomials.m"];
       |Strategies`Pegasus[$problem]""".stripMargin

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

    val command = s"""Needs["Methods`","$pegasusPath/Methods.m"];
                     |Methods`InvS[$problem]""".stripMargin

    val (output, result) = runUnchecked(command)
    logger.debug("LZZ check: "+ result.prettyString + " from raw output " + output)
    result match {
      case True => true
      case False => false
      case _ => throw ToolException("Expected true/false from Pegasus call but got expression: " +
        result.prettyString)
    }
  }

  private def init(): Unit = {
    // copy Pegasus Mathematica notebooks
    val pegasusTempDir = Configuration.path(Configuration.Keys.PEGASUS_PATH)
    if (!new File(pegasusTempDir).exists) new File(pegasusTempDir).mkdirs

    val pegasusResourcePath = "/pegasus-mathematica/"
    val pegasusResourceNames =
      "AbstractionPolynomials.m" ::
      "Classifier.m" ::
      "FirstIntegralGen.m" ::
      "Methods.m" ::
      "PlanarLinear.m" ::
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
