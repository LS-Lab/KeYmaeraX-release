package edu.cmu.cs.ls.keymaerax

/**
 * Bellerophon tactics language framework. This package includes
 *    - [[edu.cmu.cs.ls.keymaerax.bellerophon.BelleExpr tactic language expressions]]
 *    - a [[edu.cmu.cs.ls.keymaerax.bellerophon.SequentialInterpreter sequential tactic interpreter]]
 *
  * All Bellerophon tactic expressions are of type [[edu.cmu.cs.ls.keymaerax.bellerophon.BelleExpr]],
  * which provides the following tactic combinators
  *
  *   - `s & t` [[edu.cmu.cs.ls.keymaerax.bellerophon.SeqTactic sequential composition]] executes `t` on the output of `s`, failing if either fail.
  *   - `s | t` [[edu.cmu.cs.ls.keymaerax.bellerophon.EitherTactic alternative composition]] executes `t` if applying `s` fails, failing if both fail.
  *   - `t*` [[edu.cmu.cs.ls.keymaerax.bellerophon.SaturateTactic saturating repetition]] executes tactic `t` repeatedly to a fixpoint, casting result to type annotation,
  *     diverging if no fixpoint.
  *   - `t*n` [[edu.cmu.cs.ls.keymaerax.bellerophon.RepeatTactic bounded repetition]] executes `t` tactic `n` number of times, failing if any of those repetitions fail.
  *   - `t+` saturating repetition executes tactic `t` to a fixpoint, requires at least one successful application.
  *   - `<(e1,...,en)` [[edu.cmu.cs.ls.keymaerax.bellerophon.BranchTactic branching]] to run tactic `ei` on branch `i`, failing if any of them fail or if there are not exactly `n` branches.
  *   - `case _ of {fi => ei}` [[edu.cmu.cs.ls.keymaerax.bellerophon.USubstPatternTactic uniform substitution case pattern]] applies the first `ei` such that
  *     `fi` uniformly substitutes to current provable for which `ei` does not fail, fails if the `ei` of all matching `fi` fail.`
  *   - `t partial` [[edu.cmu.cs.ls.keymaerax.bellerophon.PartialTactic partial tactic marker]] marks that tactic `t` is allowed to not close all its goals.
  *
  * [[edu.cmu.cs.ls.keymaerax.bellerophon.PositionTactic Positional tactics]] support flexible modes of identifying what position to apply them to via
  * [[edu.cmu.cs.ls.keymaerax.bellerophon.AtPosition]].
  * Applying a positional tactic `t` at a position supports many different ways of specifying the position:
  *
  *   - `t(1)` applied at the first [[edu.cmu.cs.ls.keymaerax.core.Sequent.succ succedent]] formula.
  *   - `t(-1)` applied at the first [[edu.cmu.cs.ls.keymaerax.core.Sequent.ante antecedent]] formula.
  *   - `t(-4, 0::1::1::Nil)` applied at [[PosInExpr subexpression positioned at]] `.0.1.1` of the fourth antecedent formula,
  *     that is at the second child of the second child of the first child of the fourth antecedent formula in the sequent.
  *   - `t('L)` applied at the first applicable position in the [[edu.cmu.cs.ls.keymaerax.core.Sequent.ante antecedent]] (left side of the sequent).
  *   - `t('R)` applied at the first applicable position in the [[edu.cmu.cs.ls.keymaerax.core.Sequent.succ succedent]] (right side of the sequent).
  *   - `t('_)` applied at the first applicable position in the side of the sequent to which tactic `t` applies.
  *     The side of the sequent is uniquely determined by type of tactic.
  *   - `t('Llast)` applied at the last antecedent position (left side of the sequent).
  *   - `t('Rlast)` applied at the last succedent position (right side of the sequent).
  *
  * In addition, the formulas expected or sought for at the respective positions identified by the locators can be provided,
  * which is useful for tactic contract and tactic documentation purposes.
  * It is also useful for finding a corresponding formula by pattern matching.
  *
  *   - `t(2, fml)` applied at the second [[edu.cmu.cs.ls.keymaerax.core.Sequent.succ succedent]] formula,
  *     ensuring that the formula `fml` is at that position.
  *   - `t(-2, fml)` applied at the second [[edu.cmu.cs.ls.keymaerax.core.Sequent.ante antecedent]] formula,
  *     ensuring that the formula `fml` is at that position.
  *   - `t(5, 0::1::1::Nil, ex)` applied at [[PosInExpr subexpression positioned at]] `.0.1.1` of the fifth succedent formula,
  *     that is at the second child of the second child of the first child of the fifth succcedent formula in the sequent,
  *     ensuring that the expression `ex` is at that position.
  *   - `t('L, fml)` applied at the antecedent position (left side of the sequent)
  *     where the expected formula `fml` can be found (on the top level).
  *   - `t('R, fml)` applied at the succedent position (right side of the sequent)
  *     where the expected formula `fml` can be found (on the top level).
  *   - `t('_, fml)` applied at the suitable position (uniquely determined by type of tactic)
  *     where the expected formula `fml` can be found (on the top level).
  *
  * @author Nathan Fulton
  * @author Stefan Mitsch
  * @author Andre Platzer
  * @see Nathan Fulton and Andre Platzer. Bellerophon: A Typed Language for Automated Deduction in a Uniform Substitution Calculus
  *    To be published.
 */
package object bellerophon {}
