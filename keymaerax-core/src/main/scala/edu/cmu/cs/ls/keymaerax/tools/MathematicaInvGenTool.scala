package edu.cmu.cs.ls.keymaerax.tools

import java.io.{File, FileOutputStream}
import java.nio.channels.Channels

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.btactics.InvGenTool
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
  extends BaseKeYmaeraMathematicaBridge[KExpr](link, KeYmaeraToMathematica, MathematicaToKeYmaera)
    with InvGenTool with Logging {

  init()

  def invgen(ode: ODESystem, assumptions: Seq[Formula], postCond: Formula): Seq[Formula] = {
    val k2m = new UncheckedK2MConverter()
    val vars = DifferentialHelper.getPrimedVariables(ode)
    val stringVars = "{" + vars.map(k2m(_)).mkString(", ") + "}"
    val vectorField = "{" + DifferentialHelper.atomicOdes(ode).map(o => k2m(o.e)).mkString(", ") + "}"
    val problem = "{ " +
      k2m.apply(assumptions.reduce(And)) + ", { " +
      vectorField + ", " +
      stringVars + ", " +
      k2m.apply(ode.constraint) + " }, " +
      k2m.apply(postCond) + " }"

    logger.debug("Raw Mathematica input into Pegasus: " + problem)

    val pegasusPath = Configuration(Configuration.Keys.PEGASUS_PATH)

    val timeout = Try(Integer.parseInt(Configuration(Configuration.Keys.PEGASUS_INVGEN_TIMEOUT))).toOption

    def pegasus(cmd: String): String = timeout match {
      case Some(to) if to >= 0 => "TimeConstrained[Strategies`Pegasus[" + cmd + "]," + to + "]"
      case _ => "Strategies`Pegasus[" + cmd + "]"
    }

    val command = s"""
       |Needs["Strategies`","$pegasusPath/Strategies.m"];
       |Needs["Methods`","$pegasusPath/Methods.m"];
       |Needs["Classifier`","$pegasusPath/Classifier.m"];
       |Needs["AbstractionPolynomials`","$pegasusPath/AbstractionPolynomials.m"];
       |${pegasus(problem)}""".stripMargin

    val (output, result) = runUnchecked(command)
    logger.debug("Generated invariant: "+ result.prettyString + " from raw output " + output)
    result match {
      case continuousInvariant: Formula => continuousInvariant :: Nil
      case _ => throw ToolException("Expected a formula from Pegasus call but got a non-formula expression: " +
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
      val pegasusSrc = Channels.newChannel(getClass.getResourceAsStream(pegasusResourcePath + "/" + n))
      pegasusDest.getChannel.transferFrom(pegasusSrc, 0, Long.MaxValue)
    })
    val pegasusAbsPaths = pegasusResourceNames.map(n => pegasusTempDir + File.separator + n)
    assert(pegasusAbsPaths.forall(new File(_).exists()), "Missing Pegasus files")
  }

}
