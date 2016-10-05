/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.bellerophon

import java.lang.Number

import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.ExpressionTraversal.{ExpressionTraversalFunction, StopTraversal}
import edu.cmu.cs.ls.keymaerax.btactics.{DerivationInfo, ExpressionTraversal}
import edu.cmu.cs.ls.keymaerax.core._

import scala.annotation.tailrec

/**
  * User-Interface Axiom/Tactic Index: Indexing data structure for all canonically applicable (derived) axioms/rules/tactics in User-Interface.
  * @author aplatzer
  * @see [[edu.cmu.cs.ls.keymaerax.btactics.AxiomIndex]]
  */
object UIIndex {
  //@todo import a debug flag as in Tactics.DEBUG
  private val DEBUG = System.getProperty("DEBUG", "false")=="true"

  /** Give the canonical (derived) axiom name or tactic names that simplifies the expression expr, optionally considering that this expression occurs at the indicated position pos in the given sequent. Disregard tactics that require input */
  def theStepAt(expr: Expression, pos: Option[Position] = None): Option[String] = expr match {
    case _ => allStepsAt(expr, pos).find(DerivationInfo(_).inputs.isEmpty)
  }

  def theStepAt(pos1: Position, pos2: Position, sequent: Sequent): Option[String] = allTwoPosSteps(pos1, pos2, sequent).
    find(DerivationInfo(_).inputs.isEmpty)

  private val unknown = Nil

  /** Return ordered list of all canonical (derived) axiom names or tactic names that simplifies the expression expr, optionally considering that this expression occurs at the indicated position pos in the given sequent. */
  def allStepsAt(expr: Expression, pos: Option[Position] = None, sequent: Option[Sequent] = None): List[String] = autoPad(pos, sequent, {
    val isTop = pos.nonEmpty && pos.get.isTopLevel
    //@note the truth-value of isAnte is nonsense if !isTop ....
    val isAnte = pos.nonEmpty && pos.get.isAnte
    //@todo cutL and cutR are always applicable on top level
    val alwaysApplicable = Nil
    if (DEBUG) println("allStepsAt(" + expr + ") at " + pos + " which " + (if (isTop) "is top" else "is not top") + " and " + (if (isAnte) "is ante" else "is succ"))
    expr match {

//      case Not(f) => f match {
//        case _: Forall => "!all" :: alwaysApplicable
//        case _: Exists => "!exists" :: alwaysApplicable
//        case _: Not => "!! double negation" :: alwaysApplicable
//        case _: And => "!& deMorgan" :: alwaysApplicable
//        case _: Or => "!| deMorgan" :: alwaysApplicable
//        case _: Imply => "!-> deMorgan" :: alwaysApplicable
//        case _: Equiv => "!<-> deMorgan" :: alwaysApplicable
//        case _ => alwaysApplicable
//      }

      case _ =>
        // Check for axioms vs. rules separately because sometimes we might want to apply these axioms when we don't
        // have positions available (which we need to check rule applicability
        val axioms =
          expr match {
            case (And(True, _)) => "true&" :: Nil
            case (And(_, True)) => "&true" :: Nil
            case (Imply(True, _)) => "true->" :: Nil
            case (Imply(_, True)) => "->true" :: Nil
              //@todo add true|, false&, and similar as new DerivedAxioms
            case _ => Nil
          }
        if (!isTop) axioms
        else {
          (expr, isAnte) match {
            case (True, false) => "closeTrue" :: alwaysApplicable
            case (False, true) => "closeFalse" :: alwaysApplicable
           case (_: Not, true) => "notL" :: alwaysApplicable
           case (_: Not, false) => "notR" :: alwaysApplicable
            case (_: And, true) => "andL" :: alwaysApplicable
            case (_: And, false) => "andR" :: alwaysApplicable
            case (_: Or, true) => "orL" :: alwaysApplicable
            case (_: Or, false) => "orR1" :: "orR2" :: alwaysApplicable
            case (_: Imply, true) => "implyL" :: alwaysApplicable
            case (_: Imply, false) => "implyR" :: alwaysApplicable
           case (_: Equiv, true) => "equivL" :: alwaysApplicable
           case (_: Equiv, false) => "equivR" :: alwaysApplicable
           case (_: Forall, true) => "allL" :: alwaysApplicable
           case (_: Forall, false) => "allR" :: alwaysApplicable
           case (_: Exists, true) => "existsL" :: alwaysApplicable
           case (_: Exists, false) => "existsR" :: alwaysApplicable
            case _ => alwaysApplicable
          }
        }
    }
  })

  def allTwoPosSteps(pos1: Position, pos2: Position, sequent: Sequent): List[String] = {
    val expr1 = sequent.sub(pos1)
    val expr2 = sequent.sub(pos2)
    (pos1, pos2, expr1, expr2) match {
      case (p1: AntePosition, p2: SuccPosition, Some(e1), Some(e2)) if p1.isTopLevel &&  p2.isTopLevel && e1 == e2 => "closeId" :: Nil
//      case (_, _: AntePosition, Some(_: Term), Some(_: Forall)) => /*@todo "all instantiate pos" ::*/ Nil
//      case (_, _: SuccPosition, Some(_: Term), Some(_: Exists)) => /*@todo "exists instantiate pos" ::*/ Nil
      case _ => Nil
      //@todo more drag-and-drop support
    }
  }

  @tailrec
  private def bodyIsEquiv(x: Forall): Boolean = x.child match {
    case Forall(_, child:Forall) => bodyIsEquiv(child)
    case Equiv(_,_) => true
    case _ => false
  }

  def comfortOf(stepName: String): Option[String] = stepName match {
    case "diffCut" => Some("diffInvariant")
    case "DIRule" => Some("autoDIRule")
    case "diffInd" => Some("autoDiffInd")
    case "diffSolve" => Some("autoDiffSolve")
    case _ => None
  }

  private def autoPad(pos: Option[Position], sequent: Option[Sequent], axioms: List[String]): List[String] = {
    //@note don't augment with hide since UI has a special button for it already.
    //@note don't augment with cutL+cutR since too cluttered.
    //    if (!axioms.isEmpty && pos.isDefined && pos.get.isTopLevel)
    //      axioms ++ (if (pos.get.isAnte) "hideL" :: /*"cutL" ::*/ Nil else "hideR" :: /*"cutR" ::*/ Nil)
    //    else
    if (DEBUG) println("allStepsAt=" + axioms)
    axioms
  }
}
