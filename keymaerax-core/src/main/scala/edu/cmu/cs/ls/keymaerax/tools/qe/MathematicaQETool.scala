/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
/**
  * @note Code Review: 2016-06-01 (QETool parts and its dependencies only)
  */
package edu.cmu.cs.ls.keymaerax.tools.qe

import com.wolfram.jlink.Expr
import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.{FormulaTools, PosInExpr}
import edu.cmu.cs.ls.keymaerax.tools.KMComparator.hasHead
import edu.cmu.cs.ls.keymaerax.tools.MathematicaConversion.{KExpr, MExpr}
import edu.cmu.cs.ls.keymaerax.tools._
import org.apache.logging.log4j.scala.Logging

import scala.collection.immutable

/**
  * A QE tool implementation using the provided JLink link to Mathematica/Wolfram Engine.
  * @param link The link to Mathematica/Wolfram Engine
  * @author Nathan Fulton
  * @author Stefan Mitsch
  */
class MathematicaQETool(override val link: MathematicaLink)
  extends BaseKeYmaeraMathematicaBridge[KExpr](link, KeYmaeraToMathematica, MathematicaToKeYmaera) with QETool with Logging {

  /** Converts Mathematica to KeYmaera, except that it undoes (t \in Reals) proof obligations added by the EnsureRealsConverter. */
  private object EnsureRealsM2K extends MathematicaToKeYmaera {
    override private[tools] def convert(e: MExpr) = {
      if (hasHead(e, MathematicaSymbols.AND) && hasHead(e.args.head, MathematicaSymbols.ELEMENT)) super.convert(e.args.last)
      else if (hasHead(e, MathematicaSymbols.IMPL) && hasHead(e.args.head, MathematicaSymbols.ELEMENT)) super.convert(e.args.last)
      else super.convert(e)
    }
  }

  /** Adds assertions of the form {{{t \[Element] Reals}}} for each term in mustBeReal at the term's parent formula. */
  private class EnsureRealsK2M(fullFormula: Formula, mustBeReal: Map[Formula, (Term, PosInExpr)]) extends KeYmaeraToMathematica {
    override def m2k: M2KConverter[KExpr] = EnsureRealsM2K

    override protected def convertFormula(f: Formula): MExpr = mustBeReal.get(f) match {
      case Some((t: Term, p: PosInExpr)) =>
        //term \in Reals
        val inReals = new Expr(MathematicaSymbols.ELEMENT, Array(k2m(t), MathematicaSymbols.REALS))
        if (FormulaTools.polarityAt(fullFormula, p) >= 0) new Expr(MathematicaSymbols.AND, Array(inReals, k2m(f)))
        else new Expr(MathematicaSymbols.IMPL, Array(inReals, k2m(f)))
      case _ => super.convertFormula(f)
    }
  }

  def qeEvidence(originalFormula: Formula): (Formula, Evidence) = {
//    val f = {
//      val mustBeReals = FormulaTools.unnaturalPowers(originalFormula)
//      val mustBeRealsInParentFml = mustBeReals.map({ case (t: Term, p: PosInExpr) =>
//        val parentFormulaPos = FormulaTools.parentFormulaPos(p, originalFormula)
//        originalFormula.sub(parentFormulaPos).get.asInstanceOf[Formula] -> (t -> parentFormulaPos)
//      })
//      new EnsureRealsK2M(originalFormula, mustBeRealsInParentFml.toMap)(originalFormula)
//    }
    val f = k2m(originalFormula)
    val method = Configuration.getOption(Configuration.Keys.MATHEMATICA_QE_METHOD).getOrElse("Reduce") match {
      case "Reduce" => MathematicaSymbols.REDUCE
      case "Resolve" => MathematicaSymbols.RESOLVE
      case m => throw new IllegalStateException("Unknown Mathematica QE method '" + m + "'. Please configure either 'Reduce' or 'Resolve'.")
    }
    val input = new MExpr(method,
      Array(f, new MExpr(MathematicaSymbols.LIST, new Array[MExpr](0)), MathematicaSymbols.REALS))
    try {
      val (output, result) = run(input)
      result match {
        case resultingQeFormula: Formula =>
          logger.debug(s"Mathematica QE result from input ${originalFormula.prettyString}: " + resultingQeFormula.prettyString)
          (resultingQeFormula, ToolEvidence(immutable.List("input" -> input.toString, "output" -> output)))
        case _ => throw ToolException("Expected a formula from Reduce call but got a non-formula expression.")
      }
    } finally { input.dispose() }
  }

}
