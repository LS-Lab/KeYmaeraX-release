/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.Position
import edu.cmu.cs.ls.keymaerax.macros.Tactic
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._


import scala.collection.immutable._

/**
  * Hybrid Program Calculus for differential dynamic logic.
  * @author Andre Platzer
  * @author Stefan Mitsch
  * @see [[HilbertCalculus]]
  */
object HybridProgramCalculus extends HybridProgramCalculus

/**
  * Hybrid Program Calculus for differential dynamic logic.
  * Basic axioms for hybrid programs are in [[HilbertCalculus]].
  *
  * Provides the elementary derived proof rules for hybrid programs from Figure 7.4 and Figure 12.9 in:
  * Andre Platzer. [[https://doi.org/10.1007/978-3-319-63588-0 Logical Foundations of Cyber-Physical Systems]]. Springer, 2018.
  * @author Andre Platzer
  * @author Stefan Mitsch
  * @see Andre Platzer. [[https://doi.org/10.1007/978-3-319-63588-0 Logical Foundations of Cyber-Physical Systems]]. Springer, 2018.
  * @see Andre Platzer. [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 59(2), pp. 219-266, 2017.
  * @see Andre Platzer. [[https://doi.org/10.1109/LICS.2012.13 Logics of dynamical systems]]. ACM/IEEE Symposium on Logic in Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 13-24. IEEE 2012
  * @see Andre Platzer. [[https://doi.org/10.1109/LICS.2012.64 The complete proof theory of hybrid systems]]. ACM/IEEE Symposium on Logic in Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 541-550. IEEE 2012
  * @see [[edu.cmu.cs.ls.keymaerax.core.AxiomBase]]
  * @see [[edu.cmu.cs.ls.keymaerax.btactics.Ax]]
  * @see [[HilbertCalculus]]
  * @Tactic complete
  */
trait HybridProgramCalculus {

  /*******************************************************************
    * Hybrid Program Proof Rules
    *******************************************************************/

  // hybrid program elementary derived proof rules

  /**
    * MR: Generalize postcondition to `C` and, separately, prove that `C` implies postcondition.
    * The operational effect of {a;b;}@generalize(f1) is generalize(f1).
    * {{{
    *   genUseLbl:        genShowLbl:
    *   G |- [a]C, D      C |- B
    *   ------------------------- MR
    *          G |- [a]B, D
    * }}}
    *
    * @example {{{
    *   genUseLbl:        genShowLbl:
    *   |- [x:=2;]x>1     x>1 |- [y:=x;]y>1
    *   ------------------------------------generalize("x>1".asFormula)(1)
    *   |- [x:=2;][y:=x;]y>1
    * }}}
    * @example {{{
    *   genUseLbl:                      genShowLbl:
    *   |- a=2 -> [z:=3;][x:=2;]x>1     x>1 |- [y:=x;]y>1
    *   -------------------------------------------------generalize("x>1".asFormula)(1, 1::1::Nil)
    *   |- a=2 -> [z:=3;][x:=2;][y:=x;]y>1
    * }}}
    */
  @Tactic(
    names = "Monotonicity",
    codeName = "MR",
    premises =      "Γ |- [a]Q, Δ ;; Q |- P",
    // Monotonicity ------------------------
    conclusion =    "Γ |- [a]P, Δ",
    inputs = "Q:formula",
    revealInternalSteps = true)
  def generalize(C: Formula)  : DependentPositionTactic = anon {(pos:Position) => DLBySubst.generalize(C)(pos) }

  /** loop: prove a property of a loop by induction with the given loop invariant (hybrid systems)
    * Wipes conditions that contain bound variables of the loop.
    * {{{
    *   use:                        init:        step:
    *   I, G\BV(a) |- p, D\BV(a)    G |- I, D    I, G\BV(a) |- [a]p, D\BV(a)
    *   --------------------------------------------------------------------
    *   G |- [{a}*]p, D
    * }}}
    *
    * @example {{{
    *   use:          init:         step:
    *   x>1 |- x>0    x>2 |- x>1    x>1 |- [x:=x+1;]x>1
    *   ------------------------------------------------I("x>1".asFormula)(1)
    *   x>2 |- [{x:=x+1;}*]x>0
    * }}}
    * @example {{{
    *   use:               init:              step:
    *   x>1, y>0 |- x>0    x>2, y>0 |- x>1    x>1, y>0 |- [x:=x+y;]x>1
    *   ---------------------------------------------------------------I("x>1".asFormula)(1)
    *   x>2, y>0 |- [{x:=x+y;}*]x>0
    * }}}
    * @param invariant The loop invariant `I`.
    * @note Currently uses I induction axiom, which is unsound for hybrid games.
    * @note Beware that the order of premises for hybrid games is use, step, init.
    */
  @Tactic(premises = "Γ |- J, Δ ;; J |- P ;; J |- [a]J",
    conclusion = "Γ |- [a<sup>*</sup>]P, Δ", revealInternalSteps = true,
    inputs = "J:formula", displayLevel = "full")
  def loop(invariant: Formula)  : DependentPositionTactic = anon {(pos:Position) => DLBySubst.loop(invariant)(pos) }

  /** iG discreteGhost: introduces a discrete ghost called `ghost` defined as term `t`; if `ghost` is None the tactic chooses a name by inspecting `t`.
    * {{{
    *   G, y=e |- p(y), D
    *   ------------------iG (where y is new)
    *        G |- p(x), D
    * }}}
    * @example {{{
    *         |- [y_0:=y;]x>0
    *         ----------------discreteGhost("y".asTerm)(1)
    *         |- x>0
    * }}}
    * @example {{{
    *         |- [z:=2;][y:=5;]x>0
    *         ---------------------discreteGhost("0".asTerm, Some("y".asVariable))(1, 1::Nil)
    *         |- [z:=2;]x>0
    * }}}
    * @param t The ghost's initial value.
    * @param ghost The new ghost variable. If `None`, the tactic chooses a name by inspecting t (must be a variable then).
    *              For robustness you are advised to choose a name.
    * @incontext
    */
  def discreteGhost(t: Term, ghost: Option[Variable] = None): DependentPositionTactic = DLBySubst.discreteGhost(t, ghost)

}
