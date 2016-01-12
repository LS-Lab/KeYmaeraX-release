/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.btacticinterface

import java.lang.Number

import edu.cmu.cs.ls.keymaerax.bellerophon.Position
import edu.cmu.cs.ls.keymaerax.core._

/**
  * User-Interface Axiom/Tactic Index: Indexing data structure for all canonically applicable (derived) axioms/rules/tactics in User-Interface.
  * @author aplatzer
  * @see [[edu.cmu.cs.ls.keymaerax.btactics.AxiomIndex]]
  */
object UIIndex {
  //@todo import a debug flag as in Tactics.DEBUG
  private val DEBUG = System.getProperty("DEBUG", "true")=="true"

  /** Give the canonical (derived) axiom name or tactic names that simplifies the expression expr, optionally considering that this expression occurs at the indicated position pos in the given sequent. */
  def theStepAt(expr: Expression, pos: Option[Position] = None): Option[String] = allStepsAt(expr, pos).headOption

  private val odeList: List[String] = "DI differential invariant" :: "diffCut" :: "DG differential ghost" :: Nil

  private val unknown = Nil

  /** Return ordered list of all canonical (derived) axiom names or tactic names that simplifies the expression expr, optionally considering that this expression occurs at the indicated position pos in the given sequent. */
  def allStepsAt(expr: Expression, pos: Option[Position] = None, sequent: Option[Sequent] = None): List[String] = autoPad(pos, sequent, {
    val isTop = pos.nonEmpty && pos.get.isTopLevel
    //@note the truth-value of isAnte is nonsense if !isTop ....
    val isAnte = pos.nonEmpty && pos.get.isAnte
    val alwaysApplicable = "cut" :: Nil
    if (DEBUG) println("allStepsAt(" + expr + ") at " + pos + " which " + (if (isTop) "is top" else "is not top") + " and " + (if (isAnte) "is ante" else "is succ"))
    expr match {
      case Differential(t) => t match {
        case _: Variable => "DvariableTactic" :: alwaysApplicable
        case _: Number => "c()' derive constant fn" :: alwaysApplicable
        // optimizations
        case t: Term if StaticSemantics.freeVars(t).isEmpty => "c()' derive constant fn" :: alwaysApplicable
        case _: Neg => "-' derive neg" :: alwaysApplicable
        case _: Plus => "+' derive sum" :: alwaysApplicable
        case _: Minus => "-' derive minus" :: alwaysApplicable
        // optimizations
        case Times(num, _) if StaticSemantics.freeVars(num).isEmpty => "' linear" :: alwaysApplicable
        case Times(_, num) if StaticSemantics.freeVars(num).isEmpty => "' linear right" :: alwaysApplicable
        case _: Times => "*' derive product" :: alwaysApplicable
        case _: Divide => "/' derive quotient" :: alwaysApplicable
        case _: Power => "^' derive power" :: alwaysApplicable
        case FuncOf(_, Nothing) => "c()' derive constant fn" :: alwaysApplicable
        case _ => alwaysApplicable
      }

      case DifferentialFormula(f) => f match {
        case _: Equal => "=' derive =" :: alwaysApplicable
        case _: NotEqual => "!=' derive !=" :: alwaysApplicable
        case _: Greater => ">' derive >" :: alwaysApplicable
        case _: GreaterEqual => ">=' derive >=" :: alwaysApplicable
        case _: Less => "<' derive <" :: alwaysApplicable
        case _: LessEqual => "<=' derive <=" :: alwaysApplicable
        case _: And => "&' derive and" :: alwaysApplicable
        case _: Or => "|' derive or" :: alwaysApplicable
        case _: Imply => "->' derive imply" :: alwaysApplicable
        case _: Forall => "forall' derive forall" :: alwaysApplicable
        case _: Exists => "exists' derive exists" :: alwaysApplicable
        case _ => alwaysApplicable
      }

      case Box(a, post) =>
        val rules =
        // @todo Better applicability test for V
          if (isTop && sequent.isDefined && sequent.get.ante.isEmpty && sequent.get.succ.length == 1) {"G" :: "V vacuous" :: alwaysApplicable} else { "V vacuous" :: alwaysApplicable}
        a match {
          case _: Assign => "assignbTactic" :: rules
          case _: AssignAny => "[:*] assign nondet" :: rules
          case _: DiffAssign => "[':=] differential assign" :: rules
          case _: Test => "[?] test" :: rules
          case _: Compose => "[;] compose" :: rules
          case _: Choice => "[++] choice" :: rules
          case _: Dual => "[^d] dual" :: alwaysApplicable
          case _: Loop => "loop" :: "[*] iterate" :: rules
          // @todo: This misses the case where differential formulas are not top-level, but strategically okay
          case ODESystem(ode, constraint) if post.isInstanceOf[DifferentialFormula] => ode match {
            case _: AtomicODE => "DE differential effect" :: /*"DW differential weakening" ::*/ alwaysApplicable
            case _: DifferentialProduct => "DE differential effect (system)" :: /*"DW differential weakening" ::*/ alwaysApplicable
            case _ => alwaysApplicable
          }
          case ODESystem(ode, constraint) =>
            val tactics: List[String] = "diffSolve" :: "diffInd" :: /*@todo "diffInvariant" with inputs instead of DC? ::*/  Nil
            if (constraint == True)
              tactics ++ odeList ++ rules
            else
              (tactics :+ "DW differential weakening") ++ odeList ++ rules
          case _ => alwaysApplicable
        }

      case Diamond(a, _) => a match {
        case _: Assign => "<:=> assign" :: alwaysApplicable
        case _: AssignAny => "<:*> assign nondet" :: alwaysApplicable
        case _: Test => "<?> test" :: alwaysApplicable
        case _: Compose => "<;> compose" :: alwaysApplicable
        case _: Choice => "<++> choice" :: alwaysApplicable
        case _: Dual => "<^d> dual" :: alwaysApplicable
        case _: ODESystem => println("AxiomIndex for <ODE> still missing"); unknown
        case _ => alwaysApplicable
      }

      case Not(f) => f match {
        case Box(_, Not(_)) => "<> diamond" :: alwaysApplicable
        case _: Box => "![]" :: alwaysApplicable
        case Diamond(_, Not(_)) => "[] box" :: alwaysApplicable
        case _: Diamond => "!<>" :: alwaysApplicable
        case _: Forall => "!all" :: alwaysApplicable
        case _: Exists => "!exists" :: alwaysApplicable
        case _: Equal => "! =" :: alwaysApplicable
        case _: NotEqual => "! !=" :: alwaysApplicable
        case _: Less => "! <" :: alwaysApplicable
        case _: LessEqual => "! <=" :: alwaysApplicable
        case _: Greater => "! >" :: alwaysApplicable
        case _: GreaterEqual => "! >=" :: alwaysApplicable
        case _: Not => "!! double negation" :: alwaysApplicable
        case _: And => "!& deMorgan" :: alwaysApplicable
        case _: Or => "!| deMorgan" :: alwaysApplicable
        case _: Imply => "!-> deMorgan" :: alwaysApplicable
        case _: Equiv => "!<-> deMorgan" :: alwaysApplicable
        case _ => alwaysApplicable
      }

      case _ =>
        // Check for axioms vs. rules separately because sometimes we might want to apply these axioms when we don't
        // have positions available (which we need to check rule applicability
        val axioms =
          expr match {
            case (And(True, _)) => "true&" :: Nil
            case (And(_, True)) => "&true" :: Nil
            case (Imply(True, _)) => "true->" :: Nil
            case (Imply(_, True)) => "->true" :: Nil
            case _ => Nil
          }
        if (!isTop) axioms
        else {
          (expr, isAnte) match {
            case (True, false) => "closeTrue" :: alwaysApplicable
            case (False, true) => "closeFalse" :: alwaysApplicable
            case (_: Not, true) => "notL" :: alwaysApplicable
            case (_: Not, false) => "notR" :: alwaysApplicable
            case (_: And, true) => axioms ++ ("andL" :: alwaysApplicable)
            case (_: And, false) => axioms ++ ("andR" :: alwaysApplicable)
            case (_: Or, true) => "orL" :: alwaysApplicable
            case (_: Or, false) => "orR" :: alwaysApplicable
            case (_: Imply, true) => axioms ++ ("implyL" :: alwaysApplicable)
            case (_: Imply, false) => axioms ++ ("implyR" :: alwaysApplicable)
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
