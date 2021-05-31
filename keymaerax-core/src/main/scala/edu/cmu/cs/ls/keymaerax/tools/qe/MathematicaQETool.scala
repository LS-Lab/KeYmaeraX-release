/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
/**
  * @note Code Review: 2016-06-01 (QETool parts and its dependencies only)
  */
package edu.cmu.cs.ls.keymaerax.tools.qe

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.bellerophon.OnAll
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors.SequentAugmentor
import edu.cmu.cs.ls.keymaerax.tools._
import edu.cmu.cs.ls.keymaerax.tools.qe.MathematicaOpSpec._

import scala.collection.immutable.Seq

/**
  * A QE tool implementation using the provided link to Mathematica/Wolfram Engine.
  * @param link The link to Mathematica/Wolfram Engine.
  * @author Nathan Fulton
  * @author Stefan Mitsch
  */
class MathematicaQETool(val link: MathematicaCommandRunner) extends QETool {
  /** QE options, see [[https://reference.wolfram.com/language/tutorial/RealPolynomialSystems.html]] (InequalitySolvingOptions). */
  private val qeOptions = Configuration.getMap(Configuration.Keys.MATHEMATICA_QE_OPTIONS).map({ case (k, v) =>
    rule(string(k), v match {
      case "true" | "false" => bool(v.toBoolean)
      case _ => string(v)
    })
  }).toList

  /** QE method, one of `Resolve` or `Reduce`. */
  private val qeMethod = Configuration.getString(Configuration.Keys.MATHEMATICA_QE_METHOD).getOrElse("Reduce")

  /** Whether or not to split the QE call into parallel attempts. */
  private val parallelQE = Configuration.getBoolean(Configuration.Keys.MATHEMATICA_PARALLEL_QE).getOrElse(false)

  /** Goals for parallel QE execution. */
  private trait Goal
  /** A single formula. */
  private case class Atom(goal: Formula) extends Goal
  /** One of the goals must be proved. */
  private case class OneOf(goals: Seq[Goal]) extends Goal
  /** All of the goals must be proved. */
  private case class AllOf(goals: Seq[Goal]) extends Goal

  /** @inheritdoc */
  override def quantifierElimination(formula: Formula): Formula = {
    if (parallelQE) firstResultQE(splitFormula(formula))
    else singleQE(formula)
  }

  /** Returns the result of QE on `formula`. */
  private def singleQE(formula: Formula): Formula = {
    val input =
      if (qeOptions.nonEmpty) compoundExpr(
        MathematicaOpSpec(symbol("SetSystemOptions"))(
          rule(
            string("InequalitySolvingOptions"),
            list(qeOptions:_*)) :: Nil
        ),
        qe(formula)
      )
      else qe(formula)
    try {
      val (_, result) = link.run(input, MathematicaToKeYmaera)
      result match {
        case resultFormula: Formula => resultFormula
        case _ => throw ConversionException("Expected a formula result but got a non-formula expression: " + result.prettyString)
      }
    } finally { input.dispose() }
  }

  /** Returns the result of the first QE call to succeed among the formulas in `fmls`. */
  private def firstResultQE(goal: Goal): Formula = {
    // {res, id, eids} = WaitNext[...]; AbortKernels[]; res
    val input = goal match {
      case Atom(goal) => qe(goal)
      case OneOf(goals) => module(
        list(),
        compoundExpr(
          set(list(symbol("res"), symbol("id"), symbol("eids")), waitNext(list(goals.map({
            case Atom(g) => parallelSubmit(qe(g))
            case AllOf(andGoals) => parallelSubmit(and(andGoals.map({
              case Atom(g) => qe(g)
              case _ => throw new IllegalArgumentException("Unsupported parallel QE feature: nested non-atom in AllOf")
            }):_*))
            case OneOf(_) => throw new IllegalArgumentException("Unsupported parallel QE feature: nested OneOf in OneOf")
          }):_*))),
          abortKernels(),
          symbol("res")
        )
      )
      case AllOf(_) => throw new IllegalArgumentException("Unsupported parallel QE feature: top-level AllOf")
    }
    try {
      val (_, result) = link.run(input, MathematicaToKeYmaera)
      result match {
        case p: Formula => p
        case _ => throw ConversionException("Expected a formula result but got a non-formula expression: " + result.prettyString)
      }
    } finally { input.dispose() }
  }

  /** Creates the QE call Mathematica command. */
  private def qe(formula: Formula) = {
    val f = try {
      KeYmaeraToMathematica(formula)
    } catch {
      case ex: ConversionException => throw ex
      case ex: Throwable => throw ConversionException("Error converting to Mathematica: " + formula.prettyString, ex)
    }
    val doQE = qeMethod match {
      case "Reduce" => (f: MathematicaConversion.MExpr) => reduce(f, list(), reals.op)
      case "Resolve" => (f: MathematicaConversion.MExpr) => resolve(f, reals.op)
      case m => throw ToolCommunicationException("Unknown Mathematica QE method '" + m + "'. Please configure either 'Reduce' or 'Resolve'.")
    }
    doQE(f)
  }

  /** Transforms the leaves in goal `g` according to transformation `trafo`. */
  private def applyTo(g: Goal, trafo: Formula => Formula): Goal = g match {
    case Atom(goal) => Atom(trafo(goal))
    case OneOf(goals) => OneOf(goals.map(applyTo(_, trafo)))
    case AllOf(goals) => AllOf(goals.map(applyTo(_, trafo)))
  }

  /** Splits formula `fml` into QE goals that can potentially be executed concurrently. */
  private def splitFormula(fml: Formula): Goal = fml match {
    case Forall(x, p) => applyTo(splitFormula(p), Forall(x, _))
    case _: Imply =>
      //@note soundness-critical conversion
      val propSubgoals = TactixLibrary.proveBy(fml, TactixLibrary.prop).subgoals
      val expandedSubgoals = TactixLibrary.proveBy(fml, TactixLibrary.expandAll & TactixLibrary.prop &
        OnAll(TactixLibrary.applyEqualities)).subgoals
      if (propSubgoals.size > 1) {
        if (expandedSubgoals.size > 1) OneOf(List(Atom(fml), AllOf(propSubgoals.map(p => Atom(p.toFormula))), AllOf(expandedSubgoals.map(p => Atom(p.toFormula)))))
        else OneOf(List(Atom(fml), AllOf(propSubgoals.map(p => Atom(p.toFormula)))))
      } else if (expandedSubgoals.size > 1) {
        OneOf(List(Atom(fml), AllOf(expandedSubgoals.map(p => Atom(p.toFormula)))))
      } else Atom(fml)
    case _ => Atom(fml)
  }
}
