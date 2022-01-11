/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.infrastruct

import edu.cmu.cs.ls.keymaerax.core.{NamedSymbol, Provable, StaticSemantics, SubstitutionPair, USubst}
import edu.cmu.cs.ls.keymaerax.infrastruct.ProvableHelper.exhaustiveSubst
import edu.cmu.cs.ls.keymaerax.parser.Declaration

object UnificationTools {
  /** Collects substitutions (of `defs`) that are needed to make `sub` fit the `i`-th subgoal of `goal`. */
  def collectSubst(goal: Provable, i: Int, sub: Provable, substs: List[SubstitutionPair]): USubst = {
    if (goal.subgoals(i) == sub.conclusion) USubst(List.empty)
    else {
      val symbols = FormulaTools.symbolsDiff(goal.subgoals(i).ante ++ goal.subgoals(i).succ, sub.conclusion.ante ++ sub.conclusion.succ)._3
      val subst = USubst(substs.filter({ case SubstitutionPair(what, _) => symbols.intersect(StaticSemantics.symbols(what)).nonEmpty }))
      val substGoal = exhaustiveSubst(goal, subst)
      val substSub = exhaustiveSubst(sub, subst)
      if (symbols.isEmpty) assert(substGoal.subgoals(i) == substSub.conclusion, "No difference in symbols, but subderivation\n  " + substSub.conclusion.prettyString + "  does not fit goal\n  " + substGoal.subgoals(i).prettyString)
      if (substGoal.subgoals(i) == substSub.conclusion) subst
      else if (subst.subsDefsInput.nonEmpty) subst ++ collectSubst(substGoal, i, substSub, substs) // expand nested definitions
      else subst ++ RestrictedBiDiUnificationMatch(substGoal.subgoals(i), substSub.conclusion).usubst
    }
  }
}
