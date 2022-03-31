/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.infrastruct

import edu.cmu.cs.ls.keymaerax.core.{DotTerm, Expression, FuncOf, Function, NamedSymbol, Nothing, Provable, Real, StaticSemantics, SubstitutionPair, USubst, Unit, Variable}
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
      val (exp, nonexp) = (sg ++ ss).partition(symbolDeps.contains)
      val constifications =
        if (sub.isProved) {
          nonexp.groupBy(n => (n.name, n.index, n.sort)).filter(_._2.size > 1).flatMap({ case (_, s) => s.toList match {
            case (v: Variable) :: (f@Function(_, _, Unit, Real, false)) :: Nil => Some(SubstitutionPair(FuncOf(f, Nothing), v))
            case (f@Function(_, _, Unit, Real, false)) :: (v: Variable) :: Nil => Some(SubstitutionPair(FuncOf(f, Nothing), v))
            case _ => None
          } }).toList
        } else List.empty
      val expand = if (exp.nonEmpty) Some(exp.minBy(symbolDeps.indexOf)) else None
      val subst = expand.map(e => USubst(substs.find({ case SubstitutionPair(what, _) => StaticSemantics.symbols(what).contains(e) }).toList)).getOrElse(USubst(List.empty)) ++ USubst(constifications)
      assert(subst.subsDefsInput.nonEmpty, "Unexpected empty substitution since symbol differences " + sg.map(_.prettyString).mkString(",") + " and " + ss.map(_.prettyString).mkString(","))

      val substGoal = exhaustiveSubst(goal, subst)
      val substSub = exhaustiveSubst(sub, subst)
      subst ++ collectSubstOrdered(substGoal, i, substSub, substs.diff(subst.subsDefsInput), symbolDeps)
    }
  }
}
