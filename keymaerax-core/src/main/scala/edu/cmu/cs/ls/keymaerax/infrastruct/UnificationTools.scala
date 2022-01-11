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
    //@note prefer to expand definitions from goal towards sub (in analogy to what happens in the proof)
    //@todo performance will degrade with depth of nested definitions
    if (goal.subgoals(i) == sub.conclusion) USubst(List.empty)
    else {
      val (sg, ss, _) = FormulaTools.symbolsDiff(goal.subgoals(i).ante ++ goal.subgoals(i).succ, sub.conclusion.ante ++ sub.conclusion.succ)
      val downSubst = USubst(substs.filter({ case SubstitutionPair(what, _) => sg.intersect(StaticSemantics.symbols(what)).nonEmpty }))
      val downSubstGoal = exhaustiveSubst(goal, downSubst)
      val downSubstSub = exhaustiveSubst(sub, downSubst)
      if (downSubstGoal.subgoals(i) == downSubstSub.conclusion) downSubst
      else if (downSubst.subsDefsInput.nonEmpty) downSubst ++ collectSubst(downSubstGoal, i, downSubstSub, substs) // expand nested definitions
      else if (ss.nonEmpty) {
        //@note if even after expanding all nested definitions from goal towards sub there are still differences,
        // then goal may have a symbol expanded but sub hasn't; can happen when applying a general lemma
        val upSubst = USubst(substs.filter({ case SubstitutionPair(what, _) => ss.intersect(StaticSemantics.symbols(what)).nonEmpty }))
        val upSubstGoal = exhaustiveSubst(downSubstGoal, upSubst)
        val upSubstSub = exhaustiveSubst(downSubstSub, upSubst)
        if (upSubstGoal.subgoals(i) == upSubstSub.conclusion) downSubst ++ upSubst
        else if (upSubst.subsDefsInput.nonEmpty) downSubst ++ upSubst ++ collectSubst(upSubstGoal, i, upSubstSub, substs) // expand nested definitions
        else downSubst ++ upSubst ++ RestrictedBiDiUnificationMatch(upSubstGoal.subgoals(i), upSubstSub.conclusion).usubst
      } else downSubst ++ RestrictedBiDiUnificationMatch(downSubstGoal.subgoals(i), downSubstSub.conclusion).usubst
    }
  }
}
