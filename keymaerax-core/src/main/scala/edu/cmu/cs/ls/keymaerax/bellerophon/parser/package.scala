/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.bellerophon

/**
 * Parser for concrete syntax of Bellerophon tactics language.
 *   - [[edu.cmu.cs.ls.keymaerax.bellerophon.BelleExpr tactic language expressions]]
 *   - [[edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser tactic parser]] for BelleExpr
 *
 * All Bellerophon tactic expressions are of type [[edu.cmu.cs.ls.keymaerax.bellerophon.BelleExpr]], which provides the
 * following tactic combinators
 *
 *   - `s ; t` [[edu.cmu.cs.ls.keymaerax.bellerophon.SeqTactic sequential composition]] executes t` on the output of
 *     `s`, failing if either fail.
 *   - `s | t` [[edu.cmu.cs.ls.keymaerax.bellerophon.EitherTactic alternative composition]] executes `t` if applying `s`
 *     fails, failing if both fail.
 *   - `t*` [[edu.cmu.cs.ls.keymaerax.bellerophon.SaturateTactic saturating repetition]] executes tactic `t` repeatedly
 *     to a fixpoint, casting result to type annotation, diverging if no fixpoint.
 *   - `t*n` [[edu.cmu.cs.ls.keymaerax.bellerophon.RepeatTactic bounded repetition]] executes `t` tactic `n` number of
 *     times, failing if any of those repetitions fail.
 *   - `<(e1,...,en)` [[edu.cmu.cs.ls.keymaerax.bellerophon.BranchTactic branching]] to run tactic `ei` on branch `i`,
 *     failing if any of them fail or if there are not exactly `n` branches.
 *
 * [[edu.cmu.cs.ls.keymaerax.bellerophon.PositionalTactic Positional tactics]] support flexible modes of identifying
 * what position to apply them to via [[edu.cmu.cs.ls.keymaerax.bellerophon.AtPosition]]. Applying a positional tactic
 * `t` at a position supports many different ways of specifying the position:
 *
 *   - `t(1)` applied at the first [[edu.cmu.cs.ls.keymaerax.core.Sequent.succ succedent]] formula.
 *   - `t(-1)` applied at the first [[edu.cmu.cs.ls.keymaerax.core.Sequent.ante antecedent]] formula.
 *   - `t(-4.0.1.1)` applied at [[PosInExpr subexpression positioned at]] `.0.1.1` of the fourth antecedent formula,
 *     that is at the second child of the second child of the first child of the fourth antecedent formula in the
 *     sequent.
 *   - `t('L)` applied at the first applicable position in the [[edu.cmu.cs.ls.keymaerax.core.Sequent.ante antecedent]]
 *     (left side of the sequent).
 *   - `t('R)` applied at the first applicable position in the [[edu.cmu.cs.ls.keymaerax.core.Sequent.succ succedent]]
 *     (right side of the sequent).
 *
 * @author
 *   Nathan Fulton
 * @author
 *   Stefan Mitsch
 * @see
 *   Nathan Fulton, Stefan Mitsch, Brandon Bohrer and Andre Platzer.
 *   [[https://doi.org/10.1007/978-3-319-66107-0_14 Bellerophon: Tactical theorem proving for hybrid systems]]. In
 *   Mauricio Ayala-Rincon and Cesar Munoz, editors, Interactive Theorem Proving, International Conference, ITP 2017,
 *   volume 10499 of LNCS. Springer, 2017.
 * @see
 *   [[edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser]]
 */
package object parser {}
