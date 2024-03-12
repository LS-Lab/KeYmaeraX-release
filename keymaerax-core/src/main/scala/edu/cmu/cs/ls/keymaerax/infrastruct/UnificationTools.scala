/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.infrastruct

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.ProvableHelper.exhaustiveSubst

object UnificationTools {
  private val expansible = (t: Expression) =>
    t match {
      case _: DotTerm => false
      case _: Variable => false
      case _ => true
    }

  /** Collects substitutions (of `defs`) that are needed to make `sub` fit the `i`-th subgoal of `goal`. */
  def collectSubst(goal: Provable, i: Int, sub: Provable, substs: List[SubstitutionPair]): USubst = {
    collectSubst(goal.subgoals(i), sub.conclusion, sub.isProved, substs)
  }

  /** Collects substitutions (of `defs`) that are needed to make `have` fit `goal`. */
  def collectSubst(goal: Sequent, have: Sequent, haveIsProved: Boolean, substs: List[SubstitutionPair]): USubst = {
    if (goal == have) USubst(List.empty)
    else {
      // order substitutions by dependency
      val adj = substs
        .map(sp =>
          StaticSemantics.symbols(sp.what).filter(expansible).head ->
            StaticSemantics.symbols(sp.repl).filter(expansible)
        )
        .groupBy(_._1)
        .map({ case (v, e) => v -> e.flatMap(_._2).toSet })
      val symbolDeps = DependencyAnalysis.dfs(adj)

      collectSubstOrdered(goal, have, haveIsProved, substs, symbolDeps)
    }
  }

  /**
   * Collects substitutions (of `defs`) that are needed to make `sub` fit the `i`-th subgoal of `goal`. Uses
   * `symbolDeps` to determine in which order to expand symbols.
   */
  private def collectSubstOrdered(
      goal: Provable,
      i: Int,
      sub: Provable,
      substs: List[SubstitutionPair],
      symbolDeps: List[NamedSymbol],
  ): USubst = { collectSubstOrdered(goal.subgoals(i), sub.conclusion, sub.isProved, substs, symbolDeps) }

  /**
   * Collects substitutions (of `defs`) that are needed to make `have` fit `goal`. Uses `symbolDeps` to determine in
   * which order to expand symbols.
   */
  private def collectSubstOrdered(
      goal: Sequent,
      have: Sequent,
      haveIsProved: Boolean,
      substs: List[SubstitutionPair],
      symbolDeps: List[NamedSymbol],
  ): USubst = {
    if (goal == have) USubst(List.empty)
    else {
      val (sg, ss, _) = FormulaTools.symbolsDiff(goal.ante ++ goal.succ, have.ante ++ have.succ)
      if (sg.isEmpty && ss.isEmpty)
        USubst(
          List.empty
        ) // @note if `goal` and `have` formulas have the same symbols, but differ in order, or a similar other way
      else {
        val (exp, nonexp) = (sg ++ ss).partition(symbolDeps.contains)
        val constifications =
          if (haveIsProved) {
            nonexp
              .groupBy(n => (n.name, n.index, n.sort))
              .filter(_._2.size > 1)
              .flatMap({ case (_, s) =>
                s.toList match {
                  case (v: Variable) :: (f @ Function(_, _, Unit, Real, None)) :: Nil =>
                    Some(SubstitutionPair(FuncOf(f, Nothing), v))
                  case (f @ Function(_, _, Unit, Real, None)) :: (v: Variable) :: Nil =>
                    Some(SubstitutionPair(FuncOf(f, Nothing), v))
                  case _ => None
                }
              })
              .toList
          } else List.empty
        val expand = if (exp.nonEmpty) Some(exp.minBy(symbolDeps.indexOf)) else None
        val subst = expand
          .map(e =>
            USubst(substs.find({ case SubstitutionPair(what, _) => StaticSemantics.symbols(what).contains(e) }).toList)
          )
          .getOrElse(USubst(List.empty)) ++ USubst(constifications)
        assert(
          subst.subsDefsInput.nonEmpty,
          "Unexpected empty substitution since symbols " + sg.map(_.prettyString).mkString(",") + " from goal\n  " +
            goal.prettyString + "\ndo not occur in sub-derivation\n  " + have.prettyString +
            (if (ss.nonEmpty) " and symbols " + ss.map(_.prettyString).mkString(",") +
               " from sub-derivation to not occur in goal"
             else "") + "\nand there is no substitution to address the difference" +
            (if (substs.nonEmpty) " in\n  " + substs.mkString(", ") else ""),
        )

        val substGoal = exhaustiveSubst(goal, subst)
        val substHave = exhaustiveSubst(have, subst)
        subst ++ collectSubstOrdered(substGoal, substHave, haveIsProved, substs.diff(subst.subsDefsInput), symbolDeps)
      }
    }
  }
}
