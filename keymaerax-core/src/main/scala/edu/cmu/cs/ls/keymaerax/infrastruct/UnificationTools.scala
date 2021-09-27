/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.infrastruct

import edu.cmu.cs.ls.keymaerax.core.{Provable, StaticSemantics, USubst}
import edu.cmu.cs.ls.keymaerax.parser.Declaration

object UnificationTools {
  /** Collects substitutions (of `defs`) that are needed to make `sub` fit the `i`-th subgoal of `goal`. */
  def collectSubst(goal: Provable, i: Int, sub: Provable, defs: Declaration): USubst = {
    if (goal.subgoals(i) == sub.conclusion) USubst(List.empty)
    else {
      val unifSubstSymbols = RestrictedBiDiUnificationMatch(goal.subgoals(i), sub.conclusion).usubst.subsDefsInput.
        map(_.what).flatMap(StaticSemantics.symbols).toSet
      val subst = USubst(defs.substs.filter(s => unifSubstSymbols.intersect(StaticSemantics.symbols(s.what)).nonEmpty))
      if (subst.subsDefsInput.nonEmpty) subst ++ collectSubst(goal(subst), i, sub(subst), defs)
      else subst
    }
  }
}
