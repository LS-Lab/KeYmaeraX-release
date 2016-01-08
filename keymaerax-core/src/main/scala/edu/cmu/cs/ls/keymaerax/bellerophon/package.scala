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
  * [[PositionTactic Positional tactics]] support flexible modes of identifying [[PositionLocator what position to apply them to]] via
  * [[AtPosition]].
  *
  * @author Nathan Fulton
  * @author Stefan Mitsch
  * @author Andre Platzer
  * @see Nathan Fulton and Andre Platzer. Bellerophon: A Typed Language for Automated Deduction in a Uniform Substitution Calculus
  *    To be published.
 */
package object bellerophon {}
