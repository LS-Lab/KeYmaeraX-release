/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.btacticinterface

import java.lang.Number

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tactics.Position

/**
  * User-Interface Axiom/Tactic Index: Indexing data structure for all canonically applicable (derived) axioms/rules/tactics in User-Interface.
  * @author aplatzer
  * @see [[edu.cmu.cs.ls.keymaerax.tactics.AxiomIndex]]
  */
object UIIndex {
  /** Give the canonical (derived) axiom name or tactic names that simplifies the expression expr, optionally considering that this expression occurs at the indicated position pos in the given sequent. */
  def theStepAt(expr: Expression, pos: Option[Position] = None): Option[String] = allStepsAt(expr, pos).headOption

  private val odeList: List[String] = "DI differential invariant" :: "diffCut" :: "DG differential ghost" :: Nil

  private val unknown = Nil

  /** Return ordered list of all canonical (derived) axiom names or tactic names that simplifies the expression expr, optionally considering that this expression occurs at the indicated position pos in the given sequent. */
  def allStepsAt(expr: Expression, pos: Option[Position] = None, sequent: Option[Sequent] = None): List[String] = autoPad(pos, sequent, {
    val isTop = pos.nonEmpty && pos.get.isTopLevel
    val isAnte = pos.nonEmpty && pos.get.isAnte
    expr match {
      case Differential(t) => t match {
        case _: Variable => "DvariableTactic" :: Nil
        case _: Number => "c()' derive constant fn" :: Nil
        // optimizations
        case t: Term if StaticSemantics.freeVars(t).isEmpty => "c()' derive constant fn" :: Nil
        case _: Neg => "-' derive neg" :: Nil
        case _: Plus => "+' derive sum" :: Nil
        case _: Minus => "-' derive minus" :: Nil
        // optimizations
        case Times(num, _) if StaticSemantics.freeVars(num).isEmpty => "' linear" :: Nil
        case Times(_, num) if StaticSemantics.freeVars(num).isEmpty => "' linear right" :: Nil
        case _: Times => "*' derive product" :: Nil
        case _: Divide => "/' derive quotient" :: Nil
        case _: Power => "^' derive power" :: Nil
        case FuncOf(_, Nothing) => "c()' derive constant fn" :: Nil
        case _ => Nil
      }

      case DifferentialFormula(f) => f match {
        case _: Equal => "=' derive =" :: Nil
        case _: NotEqual => "!=' derive !=" :: Nil
        case _: Greater => ">' derive >" :: Nil
        case _: GreaterEqual => ">=' derive >=" :: Nil
        case _: Less => "<' derive <" :: Nil
        case _: LessEqual => "<=' derive <=" :: Nil
        case _: And => "&' derive and" :: Nil
        case _: Or => "|' derive or" :: Nil
        case _: Imply => "->' derive imply" :: Nil
        case _: Forall => "forall' derive forall" :: Nil
        case _: Exists => "exists' derive exists" :: Nil
        case _ => Nil
      }

      case Box(a, post) =>
        val rules =
        // @todo Better applicability test for V
          if (isTop && sequent.isDefined && sequent.get.ante.isEmpty && sequent.get.succ.length == 1) {"G" :: "V vacuous" :: Nil} else { "V vacuous" :: Nil}
        a match {
          case _: Assign => "assignbTactic" :: rules
          case _: AssignAny => "[:*] assign nondet" :: rules
          case _: DiffAssign => "[':=] differential assign" :: rules
          case _: Test => "[?] test" :: rules
          case _: Compose => "[;] compose" :: rules
          case _: Choice => "[++] choice" :: rules
          case _: Dual => "[^d] dual" :: Nil
          case _: Loop => "loop" :: "[*] iterate" :: rules
          // @todo: This misses the case where differential formulas are not top-level, but strategically okay
          case ODESystem(ode, constraint) if post.isInstanceOf[DifferentialFormula] => ode match {
            case _: AtomicODE => "DE differential effect" :: /*"DW differential weakening" ::*/ Nil
            case _: DifferentialProduct => "DE differential effect (system)" :: /*"DW differential weakening" ::*/ Nil
            case _ => Nil
          }
          case ODESystem(ode, constraint) =>
            val tactics: List[String] = "diffSolve" :: "diffInd" :: /*@todo "diffInvariant" with inputs instead of DC? ::*/  Nil
            if (constraint == True)
              tactics ++ odeList ++ rules
            else
              (tactics :+ "DW differential weakening") ++ odeList ++ rules
          case _ => Nil
        }

      case Diamond(a, _) => a match {
        case _: Assign => "<:=> assign" :: Nil
        case _: AssignAny => "<:*> assign nondet" :: Nil
        case _: Test => "<?> test" :: Nil
        case _: Compose => "<;> compose" :: Nil
        case _: Choice => "<++> choice" :: Nil
        case _: Dual => "<^d> dual" :: Nil
        case _: ODESystem => println("AxiomIndex for <ODE> still missing"); unknown
        case _ => Nil
      }

      case Not(f) => f match {
        case Box(_, Not(_)) => "<> diamond" :: Nil
        case _: Box => "![]" :: Nil
        case Diamond(_, Not(_)) => "[] box" :: Nil
        case _: Diamond => "!<>" :: Nil
        case _: Forall => "!all" :: Nil
        case _: Exists => "!exists" :: Nil
        case _: Equal => "! =" :: Nil
        case _: NotEqual => "! !=" :: Nil
        case _: Less => "! <" :: Nil
        case _: LessEqual => "! <=" :: Nil
        case _: Greater => "! >" :: Nil
        case _: GreaterEqual => "! >=" :: Nil
        case _: Not => "!! double negation" :: Nil
        case _: And => "!& deMorgan" :: Nil
        case _: Or => "!| deMorgan" :: Nil
        case _: Imply => "!-> deMorgan" :: Nil
        case _: Equiv => "!<-> deMorgan" :: Nil
        case _ => Nil
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
            case (True, false) => "closeTrue" :: Nil
            case (False, true) => "closeFalse" :: Nil
            case (_: Not, true) => "notL" :: Nil
            case (_: Not, false) => "notR" :: Nil
            case (_: And, true) => axioms :+ "andL"
            case (_: And, false) => axioms :+ "andR"
            case (_: Or, true) => "orL" :: Nil
            case (_: Or, false) => "orR" :: Nil
            case (_: Imply, true) => axioms :+ "implyL"
            case (_: Imply, false) => axioms :+ "implyR"
            case (_: Equiv, true) => "equivL" :: Nil
            case (_: Equiv, false) => "equivR" :: Nil
            case (_: Forall, false) => "allR" :: Nil
            case (_: Exists, true) => "existsL" :: Nil
            case _ => Nil
          }
        }
    }
  })

  private def autoPad(pos: Option[Position], sequent: Option[Sequent], axioms: List[String]): List[String] =
  //@note don't augment with hide since UI has a special button for it already.
  //@note don't augment with cutL+cutR since too cluttered.
  //    if (!axioms.isEmpty && pos.isDefined && pos.get.isTopLevel)
  //      axioms ++ (if (pos.get.isAnte) "hideL" :: /*"cutL" ::*/ Nil else "hideR" :: /*"cutR" ::*/ Nil)
  //    else
    axioms

}
