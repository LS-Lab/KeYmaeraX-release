package edu.cmu.cs.ls.keymaerax.tools

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.btactics.InvGenTool
import edu.cmu.cs.ls.keymaerax.btactics.helpers.DifferentialHelper
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tools.MathematicaConversion.KExpr
import org.apache.logging.log4j.scala.Logging

import scala.collection.immutable.Seq

/**
 * A continuous invariant implementation using Mathematica over the JLink interface.
 * @author Andrew Sogokon, based on QETool by Nathan Fulton and Stefan Mitsch
 */
class MathematicaInvGenTool(override val link: MathematicaLink)
  extends BaseKeYmaeraMathematicaBridge[KExpr](link, KeYmaeraToMathematica, MathematicaToKeYmaera)
    with InvGenTool with Logging {

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

    //@todo configurable timeout
    val command = s"""
       |Needs["Strategies`","$pegasusPath/Strategies.m"];
       |Needs["Methods`","$pegasusPath/Methods.m"];
       |Needs["Classifier`","$pegasusPath/Classifier.m"];
       |Needs["AbstractionPolynomials`","$pegasusPath/AbstractionPolynomials.m"];
       |TimeConstrained[Strategies`Pegasus[$problem], 60]
            """.stripMargin

    val (output, result) = runUnchecked(command)
    logger.debug("Generated invariant: "+ result.prettyString + " from raw output " + output)
    result match {
      case continuousInvariant: Formula => continuousInvariant :: Nil
      case _ => throw ToolException("Expected a formula from Pegasus call but got a non-formula expression: " +
        result.prettyString)
    }
  }

}
