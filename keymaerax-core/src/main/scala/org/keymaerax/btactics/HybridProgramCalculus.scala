/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics

import org.keymaerax.bellerophon._
import org.keymaerax.btactics.TacticFactory._
import org.keymaerax.btactics.macros.{DisplayLevel, Tactic}
import org.keymaerax.core._
import org.keymaerax.infrastruct.Position

/**
 * Hybrid Program Calculus for differential dynamic logic.
 * @author
 *   Andre Platzer
 * @author
 *   Stefan Mitsch
 * @see
 *   [[HilbertCalculus]]
 */
object HybridProgramCalculus extends HybridProgramCalculus

/**
 * Hybrid Program Calculus for differential dynamic logic. Basic axioms for hybrid programs are in [[HilbertCalculus]].
 *
 * Provides the elementary derived proof rules for hybrid programs from Figure 7.4 and Figure 12.9 in: Andre Platzer.
 * [[https://doi.org/10.1007/978-3-319-63588-0 Logical Foundations of Cyber-Physical Systems]]. Springer, 2018.
 * @author
 *   Andre Platzer
 * @author
 *   Stefan Mitsch
 * @see
 *   Andre Platzer. [[https://doi.org/10.1007/978-3-319-63588-0 Logical Foundations of Cyber-Physical Systems]].
 *   Springer, 2018.
 * @see
 *   Andre Platzer.
 *   [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]].
 *   Journal of Automated Reasoning, 59(2), pp. 219-266, 2017.
 * @see
 *   Andre Platzer. [[https://doi.org/10.1109/LICS.2012.13 Logics of dynamical systems]]. ACM/IEEE Symposium on Logic in
 *   Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 13-24. IEEE 2012
 * @see
 *   Andre Platzer. [[https://doi.org/10.1109/LICS.2012.64 The complete proof theory of hybrid systems]]. ACM/IEEE
 *   Symposium on Logic in Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 541-550. IEEE 2012
 * @see
 *   [[org.keymaerax.core.AxiomBase]]
 * @see
 *   [[org.keymaerax.btactics.Ax]]
 * @see
 *   [[HilbertCalculus]]
 * @see
 *   [[TactixLibrary]]
 * @Tactic
 *   complete
 */
trait HybridProgramCalculus {

  /**
   * ***************************************************************** Hybrid Program Proof Rules
   */

  // hybrid program elementary derived proof rules

  /**
   * MR: Generalize postcondition to `C` and, separately, prove that `C` implies postcondition. The operational effect
   * of {a;b;}@generalize(f1) is generalize(f1).
   * {{{
   *   genUseLbl:        genShowLbl:
   *   G |- [a]C, D      C |- B
   *   ------------------------- MR
   *          G |- [a]B, D
   * }}}
   *
   * @example
   *   {{{
   *   genUseLbl:        genShowLbl:
   *   |- [x:=2;]x>1     x>1 |- [y:=x;]y>1
   *   ------------------------------------generalize("x>1".asFormula)(1)
   *   |- [x:=2;][y:=x;]y>1
   *   }}}
   * @example
   *   {{{
   *   genUseLbl:                      genShowLbl:
   *   |- a=2 -> [z:=3;][x:=2;]x>1     x>1 |- [y:=x;]y>1
   *   -------------------------------------------------generalize("x>1".asFormula)(1, 1::1::Nil)
   *   |- a=2 -> [z:=3;][x:=2;][y:=x;]y>1
   *   }}}
   */
  // @todo code name on cheat sheet is generalize
  @Tactic(
    name = "MR",
    displayNameLong = Some("Monotonicity"),
    displayPremises = "Γ |- [a]Q, Δ ;; Q |- P",
    displayConclusion = "Γ |- [a]P, Δ",
    displayContextPremises = "Γ |- C( Γ<sub>const</sub>∧[a]Q ), Δ ;; Γ<sub>const</sub>, Q |- P",
    displayContextConclusion = "Γ |- C( [a]P ), Δ",
    inputs = "Q:formula",
    revealInternalSteps = true,
  )
  def generalize(C: Formula): DependentPositionWithAppliedInputTactic = inputanon { (pos: Position) =>
    DLBySubst.generalize(C)(pos)
  }

  /**
   * loop: prove a property of a loop by induction with the given loop invariant. For hybrid systems wipes conditions
   * that contain bound variables of the loop. For hybrid games may wipe all context.
   * {{{
   *   Post:                       Init:        Step:
   *   J, G\BV(a) |- P, D\BV(a)    G |- J, D    J, G\BV(a) |- [a]J, D\BV(a)
   *   -------------------------------------------------------------------- loop(J)
   *   G |- [{a}*]P, D
   * }}}
   *
   * @example
   *   {{{
   *   Post:         Init:         Step:
   *   x>1 |- x>0    x>2 |- x>1    x>1 |- [x:=x+1;]x>1
   *   ------------------------------------------------I("x>1".asFormula)(1)
   *   x>2 |- [{x:=x+1;}*]x>0
   *   }}}
   * @example
   *   {{{
   *   Post:              Init:              Step:
   *   x>1, y>0 |- x>0    x>2, y>0 |- x>1    x>1, y>0 |- [x:=x+y;]x>1
   *   ---------------------------------------------------------------I("x>1".asFormula)(1)
   *   x>2, y>0 |- [{x:=x+y;}*]x>0
   *   }}}
   * @example
   *   Games
   *   {{{
   *   Init:                  Step:                                   Post:
   *   x>1, y=1 |- x>0&y>0    x>0&y>0 |- [x:=0;--x:=x+y;](x>0&y>0)    x&0&y>0 |- x>0
   *   -----------------------------------------------------------------------------I("x>0&y>0".asFormula)(1)
   *   x>1, y=1 |- [{x:=0; -- x:=x+y;}*]x>0
   *   }}}
   * @param invariant
   *   The loop invariant `I`.
   * @note
   *   Currently uses I induction axiom, which is unsound for hybrid games and will, thus, throw an exception on hybrid
   *   games.
   * @note
   *   Beware that, unlike for hybrid systems, the order of premises for hybrid games is Post, Step, Init.
   */
  @Tactic(
    name = "loop",
    displayNameLong = Some("Loop Invariant"),
    displayLevel = DisplayLevel.All,
    displayPremises = "Γ |- J, Δ ;; J |- P ;; J |- [a]J",
    displayConclusion = "Γ |- [a<sup>*</sup>]P, Δ",
    revealInternalSteps = true,
    // @note contextPremises, contextConclusion without J not allowed
    inputs = "J:formula",
  )
  def loop(invariant: Formula): DependentPositionWithAppliedInputTactic = inputanon { (pos: Position) =>
    DLBySubst.loop(invariant)(pos)
  }

  /**
   * fp: make use of an assumption `⟨a*⟩P` to read off a fixpoint `J` of `⟨a⟩` that is implied by postcondition `P`.
   * Presently wipes all context.
   * {{{
   *   Usefix:            Fixpoint:
   *   G,<a*>P, J |- D    P | <a>J |- J
   *   -------------------------------- fp(J)
   *   G, <a*>P |- D
   * }}}
   *
   * @example
   *   {{{
   *   Usefix:                                    Fixpoint:
   *   <{x:=x+y;}*>x<=0,x<=2|y<=0 |- x<=2|y<=0    x<=0 | <x:=x+y;>(x<=2|y<=0) |- x<=2|y<=0
   *   -----------------------------------------------------------------------------------fp("x<=2|y<=0".asFormula)(1)
   *   <{x:=x+y;}*>x<=0 |- x<=2|y<=0
   *   }}}
   * @example
   *   {{{
   *   Usefix:                             Fixpoint:
   *   <{x:=0;--x:=x+1;}*>P, x<1 |- x<1    x<=0 | <x:=0;--x:=x+1;>x<1 |- x<1
   *   --------------------------------------------------------------------- fp("x<1".asFormula)(-1)
   *   <{x:=0;--x:=x+1;}*>x<=0 |- x<1
   *   }}}
   *
   * @param fixpoint
   *   A formula `J` that is a prefixpoint of `⟨a⟩` that also follows from `P`.
   */
  @Tactic(
    name = "fp",
    displayNameLong = Some("Fixpoint"),
    displayLevel = DisplayLevel.All,
    displayPremises = "Γ, &langle;a<sup>*</sup>&rangle;P, J |- Δ ;; P ∨ &langle;a&rangle;J |- J",
    displayConclusion = "Γ, &langle;a<sup>*</sup>&rangle;P |- Δ",
    revealInternalSteps = true,
    // @note contextPremises, contextConclusion without J not allowed
    inputs = "J:formula",
  )
  def fp(fixpoint: Formula): DependentPositionWithAppliedInputTactic = inputanon { (pos: Position) =>
    DLBySubst.fpRule(fixpoint)(pos)
  }

  /**
   * iG discreteGhost: introduces a discrete ghost called `ghost` defined as term `t`; if `ghost` is None the tactic
   * chooses a name by inspecting `t`.
   * {{{
   *   G, y=e |- p(y), D
   *   ------------------iG (where y is new)
   *        G |- p(x), D
   * }}}
   * @example
   *   {{{
   *   |- [y_0:=y;]x>0
   *   ----------------discreteGhost("y".asTerm)(1)
   *   |- x>0
   *   }}}
   * @example
   *   {{{
   *   |- [z:=2;][y:=5;]x>0
   *   ---------------------discreteGhost("0".asTerm, Some("y".asVariable))(1, 1::Nil)
   *   |- [z:=2;]x>0
   *   }}}
   * @param t
   *   The ghost's initial value.
   * @param ghost
   *   The new ghost variable. If `None`, the tactic chooses a name by inspecting t (must be a variable then). For
   *   robustness you are advised to choose a name.
   * @incontext
   */
  def discreteGhost(t: Term, ghost: Option[Variable] = None): DependentPositionTactic = DLBySubst
    .discreteGhost(t, ghost)

}
