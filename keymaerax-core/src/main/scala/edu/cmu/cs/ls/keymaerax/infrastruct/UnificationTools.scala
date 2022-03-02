/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.infrastruct

import edu.cmu.cs.ls.keymaerax.core.{DotTerm, Expression, NamedSymbol, Provable, StaticSemantics, SubstitutionPair, USubst, Variable}
import edu.cmu.cs.ls.keymaerax.infrastruct.ProvableHelper.exhaustiveSubst


object UnificationTools {
  private val expansible = (t: Expression) => t match { case _: DotTerm => false case _: Variable => false case _ => true }
  /** Collects substitutions (of `defs`) that are needed to make `sub` fit the `i`-th subgoal of `goal`. */
  def collectSubst(goal: Provable, i: Int, sub: Provable, substs: List[SubstitutionPair]): USubst = {
    if (goal.subgoals(i) == sub.conclusion) USubst(List.empty)
    else {
      // order substitutions by dependency
      val adj = substs.map(sp =>
        StaticSemantics.symbols(sp.what).filter(expansible).head -> StaticSemantics.symbols(sp.repl).filter(expansible)
      ).groupBy(_._1).map({ case (v, e) => v -> e.flatMap(_._2).toSet })
      val symbolDeps = DependencyAnalysis.dfs(adj)

      collectSubstOrdered(goal, i, sub, substs, symbolDeps)
    }
  }

  /** Collects substitutions (of `defs`) that are needed to make `sub` fit the `i`-th subgoal of `goal`. Uses `symbolDeps` to determine in which order to expand symbols. */
  private def collectSubstOrdered(goal: Provable, i: Int, sub: Provable, substs: List[SubstitutionPair], symbolDeps: List[NamedSymbol]): USubst = {
    if (goal.subgoals(i) == sub.conclusion) USubst(List.empty)
    else {
      val (sg, ss, _) = FormulaTools.symbolsDiff(goal.subgoals(i).ante ++ goal.subgoals(i).succ, sub.conclusion.ante ++ sub.conclusion.succ)
      val expand = (sg ++ ss).filter(expansible).toList.minBy(symbolDeps.indexOf)
      val subst = USubst(substs.find({ case SubstitutionPair(what, _) => StaticSemantics.symbols(what).contains(expand) }).toList)

      val substGoal = exhaustiveSubst(goal, subst)
      val substSub = exhaustiveSubst(sub, subst)
      subst ++ collectSubstOrdered(substGoal, i, substSub, substs.diff(subst.subsDefsInput), symbolDeps)
    }
  }
}
