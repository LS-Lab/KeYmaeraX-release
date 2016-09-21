/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
/**
  * Sequent prover, proof rules, and axioms of KeYmaera X.
  * @note Soundness-critical: Only provide sound proof rule application mechanisms.
  * @author Andre Platzer
  * @author Jan-David Quesel
  * @author nfulton
  * @see Andre Platzer. [[http://dx.doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 2016.
  * @see Andre Platzer. [[http://dx.doi.org/10.1007/978-3-319-21401-6_32 A uniform substitution calculus for differential dynamic logic]].  In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015. [[http://arxiv.org/pdf/1503.01981.pdf arXiv 1503.01981]]
  * @see Andre Platzer. [[http://dx.doi.org/10.1145/2817824 Differential game logic]]. ACM Trans. Comput. Log. 17(1), 2015. [[http://arxiv.org/pdf/1408.1980 arXiv 1408.1980]]
  * @see Andre Platzer. [[http://dx.doi.org/10.1109/LICS.2012.64 The complete proof theory of hybrid systems]]. ACM/IEEE Symposium on Logic in Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 541-550. IEEE 2012
  * @see "Andre Platzer. Differential dynamic logic for hybrid systems. Journal of Automated Reasoning, 41(2), pages 143-189, 2008."
  * @note Code Review: 2016-08-17
  */
package edu.cmu.cs.ls.keymaerax.core

// require favoring immutable Seqs for soundness

import scala.collection.immutable

/*--------------------------------------------------------------------------------*/
/*--------------------------------------------------------------------------------*/

/*********************************************************************************
  * Sequents and positioning
  *********************************************************************************
  */

/**
  * Position of a formula in a sequent, i.e. antecedent or succedent positions.
  *
  * @see [[SeqPos.apply()]]
  * @see [[Sequent.apply()]]
  * @see [[AntePos]]
  * @see [[SuccPos]]
  */
sealed trait SeqPos {
  /** Whether this position is in the antecedent on the left of the sequent arrow */
  val isAnte: Boolean
  /** Whether this position is in the succedent on the right of the sequent arrow */
  val isSucc: Boolean

  /**
    * The '''unsigned''' index into the antecedent or succedent list, respectively, '''0-indexed'''.
    */
  private[keymaerax] val getIndex: Int

  /**
    * The '''signed''' position for the antecedent or succedent list, respectively, '''1-indexed'''.
    *  Negative numbers indicate antecedent positions, -1, -2, -3, ....
    *  Positive numbers indicate succedent positions, 1, 2, 3.
    *  Zero is a degenerate case indicating whole sequent 0.
    * @see [[SeqPos.apply()]]
    */
  final lazy val getPos: Int = if (isSucc) {assert(!isAnte); getIndex+1} else {assert(isAnte); -(getIndex+1)}

  override def toString: String = getPos.toString
}

/**
  * Antecedent Positions of formulas in a sequent, i.e. in the assumptions on the left of the sequent arrow.
  *
  * @param index the position 0-indexed in antecedent.
  */
case class AntePos private[ls] (private[core] val index: Int) extends SeqPos {
  val isAnte: Boolean = true
  val isSucc: Boolean = !isAnte
  /** The position 0-indexed in antecedent. */
  private[keymaerax] val getIndex: Int = index
}

/**
  * Antecedent Positions of formulas in a sequent, i.e. on the right of the sequent arrow.
  *
  * @param index the position 0-indexed in succedent.
  */
case class SuccPos private[ls] (private[core] val index: Int) extends SeqPos {
  val isAnte: Boolean = false
  val isSucc: Boolean = !isAnte
  /** The position 0-indexed in succedent. */
  private[keymaerax] val getIndex: Int = index
}

object SeqPos {
  /**
    * Sequent position of signed index `signedPos` where positive is succedent and negative antecedent.
    *
    * @param signedPos the signed integer position of the formula in the antecedent or succedent, respectively.
    *  Negative numbers indicate antecedent positions, -1, -2, -3, ....
    *  Positive numbers indicate succedent positions, 1, 2, 3.
    *  Zero is a degenerate case indicating whole sequent 0.
    * @see [[SeqPos.getPos]]
    */
  def apply(signedPos: Int): SeqPos =
    if (signedPos>0) {SuccPos(signedPos-1)} else {require(signedPos<0, "nonzero positions");AntePos(-(signedPos+1))}

}


/**
  * Sequent `ante |- succ` with antecedent ante and succedent succ.
  * {{{
  *   ante(0),ante(1),...,ante(n) |- succ(0),succ(1),...,succ(m)
  * }}}
  * This sequent is often pretty-printed with signed line numbers:
  * {{{
  *     -1: ante(0)
  *     -2: ante(1)
  *         ...
  * -(n+1): ante(n)
  *  ==> 1: succ(0)
  *      2: succ(1)
  *         ...
  *  (m+1): succ(m)
  * }}}
  * The semantics of sequent `ante |- succ` is the conjunction of the formulas in `ante` implying
  * the disjunction of the formulas in `succ`.
  *
  * @param ante The ordered list of antecedents of this sequent whose conjunction is assumed.
  * @param succ The orderd list of succedents of this sequent whose disjunction needs to be shown.
  * @author Andre Platzer
  * @see Andre Platzer. [[http://dx.doi.org/10.1007/s10817-008-9103-8 Differential dynamic logic for hybrid systems]]. Journal of Automated Reasoning, 41(2), pages 143-189, 2008.
  */
final case class Sequent(ante: immutable.IndexedSeq[Formula], succ: immutable.IndexedSeq[Formula]) {
  /**
    * Retrieves the formula in sequent at a given position.
    *
    * @param pos the position of the formula
    * @return the formula at the given position either from the antecedent or the succedent
    */
  def apply(pos: SeqPos): Formula = pos match {
    case ap: AntePos => apply(ap)
    case sp: SuccPos => apply(sp)
  }

  /**
    * Retrieves the formula in sequent at a given succedent position.
    * @param pos the succedent position of the formula
    * @return the formula at the given position from the succedent
    * @note slightly faster version with the same result as [[Sequent.apply(SeqPos)]]
    */
  def apply(pos: AntePos): Formula = ante(pos.getIndex)

  /**
    * Retrieves the formula in sequent at a given antecedent position.
    * @param pos the antecedent position of the formula
    * @return the formula at the given position from the antecedent
    * @note slightly faster version with the same result as [[Sequent.apply(SeqPos)]]
    */
  def apply(pos: SuccPos): Formula = succ(pos.getIndex)

  // transformations giving copies of sequents

  /**
    * A copy of this sequent concatenated with given sequent s.
    * Sequent(A,S) glue Sequent(B,T) == Sequent(A++B, S++T)
    *
    * @param s the sequent whose antecedent to append to ours and whose succedent to append to ours.
    * @return a copy of this sequent concatenated with s.
    * Results in a least upper bound with respect to subsets of this and s.
    */
  def glue(s: Sequent): Sequent = {
    Sequent(ante ++ s.ante, succ ++ s.succ)
    } ensuring(r => this.subsequentOf(r) && s.subsequentOf(r)
        && r.ante.forall(f=>this.ante.contains(f) || s.ante.contains(f))
        && r.succ.forall(f=>this.succ.contains(f) || s.succ.contains(f)),
        "result is a supersequent of its pieces and all formulas in result come from either one"
    )

  /**
    * A copy of this sequent with the indicated position replaced by the formula f.
    *
    * @param p the position of the replacement
    * @param f the replacing formula
    * @return a copy of this sequent with the formula at position p replaced by f.
    */
  def updated(p: SeqPos, f: Formula): Sequent = p match {
    case sp: SuccPos => updated(sp, f)
    case ap: AntePos => updated(ap, f)
  }
  def updated(p: AntePos, f: Formula): Sequent = Sequent(ante.updated(p.getIndex, f), succ)
  def updated(p: SuccPos, f: Formula): Sequent = Sequent(ante, succ.updated(p.getIndex, f))

  /**
    * A copy of this sequent with the indicated position replaced by gluing the sequent s.
    *
    * @param p the position of the replacement
    * @param s the sequent glued / concatenated to this sequent after dropping p.
    * @return a copy of this sequent with the formula at position p removed and the sequent s appended.
    * @see [[Sequent.updated(Position,Formula)]]
    * @see [[Sequent.glue(Sequent)]]
    */
  def updated(p: SeqPos, s: Sequent): Sequent = p match {
    case sp: SuccPos => updated(sp, s)
    case ap: AntePos => updated(ap, s)
  }
  def updated(p: AntePos, s: Sequent): Sequent = {
    Sequent(ante.patch(p.getIndex, Nil, 1), succ).glue(s)
  } ensuring(r=> r.glue(Sequent(immutable.IndexedSeq(this(p)), immutable.IndexedSeq())).sameSequentAs(this.glue(s)),
    "result after re-including updated formula is equivalent to " + this + " glue " + s)
  def updated(p: SuccPos, s: Sequent): Sequent = {
    Sequent(ante, succ.patch(p.getIndex, Nil, 1)).glue(s)
  } ensuring(r=> r.glue(Sequent(immutable.IndexedSeq(), immutable.IndexedSeq(this(p)))).sameSequentAs(this.glue(s)),
    "result after re-including updated formula is equivalent to " + this + " glue " + s)

  /**
    * Check whether this sequent is a subsequent of the given sequent r (considered as sets)
    *
    * @note Used for contracts in the core.
    */
  def subsequentOf(r: Sequent): Boolean = ante.toSet.subsetOf(r.ante.toSet) && succ.toSet.subsetOf(r.succ.toSet)

  /**
    * Check whether this sequent is the same as the given sequent r (considered as sets)
    *
    * @note Used for contracts in the core.
    */
  def sameSequentAs(r: Sequent): Boolean = this.subsequentOf(r) && r.subsequentOf(this)

  override def toString: String =
    ante.map(_.prettyString).mkString(", ") + (if (ante.isEmpty) "  ==>  " else "\n  ==>  ") + succ.map(_.prettyString).mkString(", ")

  /** Pretty-print sequent */
  def prettyString: String = (if (ante.isEmpty) "" else "   ") +
    (1 to ante.length).map(i => -i + ":  " + ante(i-1).prettyString + "\t" + ante(i-1).getClass.getSimpleName).mkString("\n   ") +
      (if (ante.isEmpty) "" else "\n") + "==> " +
    (1 to succ.length).map(i => +i + ":  " + succ(i-1).prettyString + "\t" + succ(i-1).getClass.getSimpleName).mkString("\n    ")

}


/*********************************************************************************
  * Provables as certificates of provability.
  *********************************************************************************
  */

/**
  * Provable(conclusion, subgoals) is the proof certificate representing certified provability of
  * `conclusion` from the premises in `subgoals`.
  * If `subgoals` is an empty list, then `conclusion` is provable.
  * Otherwise `conclusion` is provable from the set of all assumptions in `subgoals`.
  * {{{
  *    G1 |- D1 ... Gn |- Dn    (subgoals)
  *   -----------------------
  *            G |- D           (conclusion)
  * }}}
  *
  * Invariant: All Provables ever produced are locally sound,
  * because only the prover kernel can create Provable objects and chooses not to use the globally sound uniform substitution rule.
  *
  * @param conclusion the conclusion `G |- D` that follows if all subgoals are valid.
  * @param subgoals the premises `Gi |- Di` that, if they are all valid, imply the conclusion.
  * @note soundness-critical logical framework.
  * @note Only private constructor calls for soundness
  * @note For soundness: No reflection should bypass constructor call privacy,
  *       nor reflection to bypass immutable val algebraic data types.
  * @see Andre Platzer. [[http://dx.doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 2016.
  * @author Andre Platzer
  * @example Proofs can be constructed in (backward/tableaux) sequent order using Provables:
  * {{{
  *   import scala.collection.immutable._
  *   val verum = new Sequent(IndexedSeq(), IndexedSeq(True))
  *   // conjecture
  *   val provable = Provable.startProof(verum)
  *   // construct a proof
  *   val proof = provable(CloseTrue(SuccPos(0)), 0)
  *   // check if proof successful
  *   if (proof.isProved) println("Successfully proved " + proof.proved)
  * }}}
  * @example Multiple Provable objects for subderivations obtained from different sources can also be merged
  * {{{
  *   // ... continuing other example
  *   val more = new Sequent(IndexedSeq(),
  *     IndexedSeq(Imply(Greater(Variable("x"), Number(5)), True)))
  *   // another conjecture
  *   val moreProvable = Provable.startProof(more)
  *   // construct another (partial) proof
  *   val moreProof = moreProvable(ImplyRight(SuccPos(0)), 0)(HideLeft(AntePos(0)), 0)
  *   // merge proofs by gluing their Provables together
  *   val mergedProof = moreProof(proof, 0)
  *   // check if proof successful
  *   if (mergedProof.isProved) println("Successfully proved " + mergedProof.proved)
  * }}}
  * @example Proofs in backward tableaux sequent order are straight-forward
  * {{{
  *  import scala.collection.immutable._
  *  val fm = Greater(Variable("x"), Number(5))
  *  // |- x>5 -> x>5 & true
  *  val finGoal = new Sequent(IndexedSeq(), IndexedSeq(Imply(fm, And(fm, True))))
  *  // conjecture
  *  val finProvable = Provable.startProof(finGoal)
  *  // construct a proof
  *  val proof = finProvable(
  *    ImplyRight(SuccPos(0)), 0)(
  *      AndRight(SuccPos(0)), 0)(
  *      HideLeft(AntePos(0)), 1)(
  *      CloseTrue(SuccPos(0)), 1)(
  *      Close(AntePos(0), SuccPos(0)), 0)
  *  // proof of finGoal
  *  println(proof.proved)
  * }}}
  * @example Proofs in forward Hilbert order are straightforward with merging of branches
  * {{{
  *  import scala.collection.immutable._
  *  val fm = Greater(Variable("x"), Number(5))
  *  // proof of x>5 |- x>5 & true merges left and right branch by AndRight
  *  val proof = Provable.startProof(Sequent(IndexedSeq(fm), IndexedSeq(And(fm, True))))(
  *    AndRight(SuccPos(0)), 0) (
  *    // left branch: x>5 |- x>5
  *    Provable.startProof(Sequent(IndexedSeq(fm), IndexedSeq(fm)))(
  *      Close(AntePos(0), SuccPos(0)), 0),
  *    0) (
  *    //right branch: |- true
  *    Provable.startProof(Sequent(IndexedSeq(), IndexedSeq(True)))(
  *      CloseTrue(SuccPos(0)), 0)(
  *        // x>5 |- true
  *        Sequent(IndexedSeq(fm), IndexedSeq(True)), HideLeft(AntePos(0))),
  *    0) (
  *    // |- x>5 -> x>5 & true
  *    new Sequent(IndexedSeq(), IndexedSeq(Imply(fm, And(fm, True)))),
  *    ImplyRight(SuccPos(0))
  *  )
  *  // proof of finGoal:  |- x>5 -> x>5 & true
  *  println(proof.proved)
  * }}}
  * @example Proofs in Hilbert-calculus style order can also be based exclusively on subsequent merging
  * {{{
  *  import scala.collection.immutable._
  *  val fm = Greater(Variable("x"), Number(5))
  *  // x>0 |- x>0
  *  val left = Provable.startProof(Sequent(IndexedSeq(fm), IndexedSeq(fm)))(
  *    Close(AntePos(0), SuccPos(0)), 0)
  *  // |- true
  *  val right = Provable.startProof(Sequent(IndexedSeq(), IndexedSeq(True)))(
  *    CloseTrue(SuccPos(0)), 0)
  *  val right2 = Provable.startProof(Sequent(IndexedSeq(fm), IndexedSeq(True)))(
  *    HideLeft(AntePos(0)), 0) (right, 0)
  *  // gluing order for subgoals is irrelevant. Could use: (right2, 1)(left, 0))
  *  val merged = Provable.startProof(Sequent(IndexedSeq(fm), IndexedSeq(And(fm, True))))(
  *    AndRight(SuccPos(0)), 0) (
  *    left, 0)(
  *      right2, 0)
  *  // |- x>5 -> x>5 & true
  *  val finGoal = new Sequent(IndexedSeq(), IndexedSeq(Imply(fm, And(fm, True))))
  *  val proof = Provable.startProof(finGoal)(
  *    ImplyRight(SuccPos(0)), 0) (merged, 0)
  *  // proof of finGoal
  *  println(proof.proved)
  * }}}
  * @example Branching proofs in backward tableaux sequent order are straight-forward,
  *          yet might become more readable when closing branches right-to-left to keep explicit subgoals:
  * {{{
  *  // explicit proof certificate construction of |- !!p() <-> p()
  *  val proof = (Provable.startProof(
  *    "!!p() <-> p()".asFormula)
  *    (EquivRight(SuccPos(0)), 0)
  *    // right branch
  *      (NotRight(SuccPos(0)), 1)
  *      (NotLeft(AntePos(1)), 1)
  *      (Close(AntePos(0),SuccPos(0)), 1)
  *    // left branch
  *      (NotLeft(AntePos(0)), 0)
  *      (NotRight(SuccPos(1)), 0)
  *      (Close(AntePos(0),SuccPos(0)), 0)
  *  )
  * }}}
  */
final case class Provable private (conclusion: Sequent, subgoals: immutable.IndexedSeq[Sequent]) {
  /**
    * Position types for the subgoals of a Provable.
    */
  type Subgoal = Int

  /**
    * Checks whether this Provable proves its conclusion.
    *
    * @return true if conclusion is proved by this Provable,
    *         false if subgoals are missing that need to be proved first.
    * @note soundness-critical
    */
  final def isProved: Boolean = subgoals.isEmpty

  /**
    * What conclusion this Provable proves if isProved.
    *
    * @requires(isProved)
    */
  final def proved: Sequent = {
    if (isProved) conclusion else throw new CoreException("Only Provables that have been proved have a proven conclusion " + this)
  }

  /**
    * Apply Rule: Apply given proof rule to the indicated subgoal of this Provable, returning the resulting Provable
    * {{{
    *    G1 |- D1 ... Gi |- Di ... Gn |- Dn              G1 |- D1 ... Gr1 |- Dr1 ... Gn |- Dn Gr2 |- Dr2 ... Grk | Drk
    *   ------------------------------------     =>     ---------------------------------------------------------------
    *                  G |- D                                         G |- D
    * }}}
    * using the rule instance
    * {{{
    *   Gr1 |- Dr1  Gr2 |- Dr2 ... Grk |- Drk
    *   ------------------------------------ (rule)
    *                Gi |- Di
    * }}}
    *
    * @param rule the proof rule to apply to the indicated subgoal of this Provable derivation.
    * @param subgoal which of our subgoals to apply the given proof rule to.
    * @return A Provable derivation that proves the premise subgoal by using the given proof rule.
    * Will return a Provable with the same conclusion but an updated set of premises.
    * @requires(0 <= subgoal && subgoal < subgoals.length)
    * @note soundness-critical. And soundness needs Rule to be sealed.
    */
  final def apply(rule: Rule, subgoal: Subgoal): Provable = {
    require(0 <= subgoal && subgoal < subgoals.length, "Rules " + rule + " should be applied to an index " + subgoal + " that is within the subgoals " + subgoals)
    rule(subgoals(subgoal)) match {
      // subgoal closed by proof rule
      case Nil => new Provable(conclusion, subgoals.patch(subgoal, Nil, 1))
      // subgoal replaced by new subgoals fml::rest
      case fml :: rest => new Provable(conclusion, subgoals.updated(subgoal, fml) ++ rest)
    }
  } ensuring(r => r.conclusion == conclusion, "Same conclusion after applying proof rules") ensuring (
    r => subgoals.patch(subgoal, Nil, 1).toSet.subsetOf(r.subgoals.toSet),
    "All previous premises still around except the one that the proof rule " + rule + " has been applied to subgoal " + subgoals(subgoal) + " in " + this) ensuring (
    r => rule(subgoals(subgoal)).toSet.subsetOf(r.subgoals.toSet), "All premises generated by rule application are new subgoals")

  /**
    * Substitute subderivation as a proof of subgoal.
    * Merge: Replace premise subgoal by the given subderivation.
    * Use the given provable derivation in place of the indicated subgoal of this Provable, returning the resulting concatenated Provable.
    *
    * In particular, if subderivation.isProved, then the given subgoal will disappear,
    * otherwise it will be replaced by the subgoals of subderivation
    * (with the first subgoal of subderivation in place of subgoal and all other subgoals at the end).
    *
    * This function implements the substitution principle for hypotheses.
    * {{{
    *    G1 |- D1 ... Gi |- Di ... Gn |- Dn              G1 |- D1 ... Gr1 |- Dr1 ... Gn |- Dn Gr2 |- Dr2 ... Grk | Drk
    *   ------------------------------------     =>     ---------------------------------------------------------------
    *                  G |- D                                         G |- D
    * }}}
    * using the given subderivation
    * {{{
    *   Gr1 |- Dr1  Gr2 |- Dr2 ... Grk |- Drk
    *   ------------------------------------ (subderivation)
    *                Gi |- Di
    * }}}
    *
    * @param subderivation the Provable derivation that proves premise subgoal.
    * @param subgoal the index of our subgoal that the given subderivation concludes.
    * @return A Provable derivation that joins our derivation and subderivation to a joint derivation of our conclusion using subderivation to show our subgoal.
    * Will return a Provable with the same conclusion but an updated set of premises.
    * @requires(0 <= subgoal && subgoal < subgoals.length)
    * @requires(subderivation.conclusion == subgoals(subgoal))
    * @note soundness-critical
    */
  final def apply(subderivation: Provable, subgoal: Subgoal): Provable = {
    require(0 <= subgoal && subgoal < subgoals.length, "derivation " + subderivation + " can only be applied to an index " + subgoal + " within the subgoals " + subgoals)
    if (subderivation.conclusion != subgoals(subgoal)) throw new CoreException("substituting Provables requires the given subderivation to conclude the indicated subgoal:\nsubderivation " + subderivation + "\nconclude: " + subderivation.conclusion + "\nexpected: " + subgoals(subgoal) + "\nwhile substituting this subderivation for subgoal " + subgoal + " into\n" + this)
    subderivation.subgoals.toList match {
      // subderivation proves given subgoal
      case Nil =>
        assert(subderivation.isProved && subderivation.proved == subgoals(subgoal), "Subderivation proves the given subgoal " + subgoals(subgoal) + " of\n" + this + "\nby subderivation\n" + subderivation)
        new Provable(conclusion, subgoals.patch(subgoal, Nil, 1))
      // subderivation replaces subgoal by new premises fml::rest
      case fml :: rest => new Provable(conclusion, subgoals.updated(subgoal, fml) ++ rest)
    }
  } ensuring(r => r.conclusion == conclusion,
    "Same conclusion\n" + conclusion + " after joining derivations") ensuring (
    r => subgoals.patch(subgoal, Nil, 1).toSet.subsetOf(r.subgoals.toSet),
    "All previous premises still around except the one replaced by a derivation") ensuring (
    r => subderivation.subgoals.toSet.subsetOf(r.subgoals.toSet), "All premises in joined derivation are new subgoals")

  /**
    * Apply a uniform substitution to a (locally sound!) Provable.
    * Substitutes both subgoals and conclusion with the same uniform substitution `subst`.
    * {{{
    *    G1 |- D1 ... Gn |- Dn              s(G1) |- s(D1) ... s(Gn) |- s(Dn)
    *   -----------------------     =>     -----------------------------------   (USR)
    *            G |- D                                s(G) |- s(D)
    * }}}
    *
    * @param subst The uniform substitution (of no free variables) to be used on the premises and conclusion of this Provable.
    * @return The Provable resulting from applying `subst` to our subgoals and conclusion.
    * @author Andre Platzer
    * @see Andre Platzer. [[http://dx.doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 2016. Theorem 26+27."
    * @note soundness-critical. And soundness-critical that only locally sound Provables can be constructed (otherwise implementation would be more complicated).
    */
  final def apply(subst: USubst): Provable =
    try {
      //@note if isProved, uniform substitution of Provables has the same effect as the globally sound uniform substitution rule (whatever free variables), which is also locally sound if no premises.
      //@note case subst.freeVars.isEmpty is covered by "Andre Platzer. [[http://dx.doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 2016. Theorem 27."
      //@note case isProved is covered by "Andre Platzer. [[http://dx.doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 2016. Theorem 26." and Theorem 27 without subgoals having same effect as Theorem 26. There is no difference between locally sound and globally sound if isProved so no subgoals.
      insist(subst.freeVars.isEmpty || isProved || Provable.LAX_MODE&&this==Provable.rules("CQ equation congruence"), "Unless proved, uniform substitutions instances cannot introduce free variables " + subst.freeVars.prettyString + "\nin " + subst + " on\n" + this)
      new Provable(subst(conclusion), subgoals.map(s => subst(s)))
    } catch { case exc: SubstitutionClashException => throw exc.inContext(subst + " on\n" + this) }

  // forward proofs (convenience)

  /**
    * Apply Rule Forward: Apply given proof rule forward in Hilbert style to prolong this Provable to a Provable for concludes.
    * This Provable with conclusion `G |- D` transforms as follows
    * {{{
    *     G1 |- D1 ... Gn |- Dn                  G1 |- D1 ... Gn |- Dn
    *   -------------------------       =>     -------------------------
    *            G |- D                              newConsequence
    * }}}
    * provided
    * {{{
    *            G |- D
    *   ------------------------- rule
    *         newConsequence
    * }}}
    *
    * @param newConsequence the new conclusion that the rule shows to follow from this.conclusion
    * @param rule the proof rule to apply to concludes to reduce it to this.conclusion.
    * @return A Provable derivation that proves concludes from the same subgoals by using the given proof rule.
    * Will return a Provable with the same subgoals but an updated conclusion.
    * @note not soundness-critical derived function since implemented in terms of other apply functions
    */
  def apply(newConsequence: Sequent, rule: Rule): Provable = {
    //@note the following requirement is redundant and not soundness-critical. It just gives a better error message.
    insist(rule(newConsequence)==List(this.conclusion), "Rule " + rule + " was expected to justify\n" + this.conclusion.prettyString + "\n-----------------------------" + rule + "??\n" + newConsequence.prettyString +
      "\n\nThat is, applying the rule backwards to new consequence\n" + newConsequence + "\nshould result in\n" + this.conclusion + "\nwhich is the conclusion of this " + this + "\nThe rule instead led to " + rule(newConsequence) +
      "\n\nExpected: " + edu.cmu.cs.ls.keymaerax.parser.FullPrettyPrinter(this.conclusion) +
      "\nFound:    " + rule(newConsequence).map(s=>edu.cmu.cs.ls.keymaerax.parser.FullPrettyPrinter(s)).mkString(", "))
    Provable.startProof(newConsequence)(rule, 0)(this, 0)
  } ensuring(r => r.conclusion == newConsequence, "New conclusion\n" + newConsequence + " after continuing derivations") ensuring(
    r => r.subgoals == subgoals, "Same subgoals\n" + subgoals + " after continuing derivations")

  /**
    * Substitute Subderivation Forward: Prolong this Provable with the given prolongation.
    * This Provable with conclusion `G |- D` transforms as follows
    * {{{
    *     G1 |- D1 ... Gn |- Dn                  G1 |- D1 ... Gn |- Dn
    *   -------------------------       =>     -------------------------
    *            G |- D                                 G0 |- D0
    * }}}
    * provided
    * {{{
    *            G |- D
    *   ------------------------- prolongation
    *           G0 |- D0
    * }}}
    *
    * @param prolongation the subderivation used to prolong this Provable.
    *                       Where subderivation has a  subgoal equaling our conclusion.
    * @return A Provable derivation that proves prolongation's conclusion from our subgoals.
    * @note not soundness-critical derived function since implemented in terms of other apply functions
    */
  def apply(prolongation: Provable): Provable = {
    //@note it really already works when prolongation.subgoal(0)==conclusion but it's somewhat surprising so disallowed.
    require(prolongation.subgoals.length==1, "Currently only for prolongations with exactly one subgoal\n" + this + "\nwith\n" + prolongation)
    prolongation(this, 0)
  } ensuring(r => r.conclusion == prolongation.conclusion && r.subgoals == subgoals, "Prolonging proof forward\n" + this + "\nwith\n" + prolongation)

  /**
    * Sub-Provable: Get a sub-Provable corresponding to a Provable with the given subgoal as conclusion.
    * Provables resulting from the returned subgoal can be merged into this Provable to prove said subgoal.
    *
    * @param subgoal the index of our subgoal for which to return a new open Provable.
    * @return an initial unfinished open Provable for the subgoal `i`:
    * {{{
    *    Gi |- Di
    *   ----------
    *    Gi |- Di
    * }}}
    * which is suitable for being merged back into this Provable for subgoal `i` subsequently.
    * @note not soundness-critical only helpful for completeness-critical
    */
  def sub(subgoal: Subgoal): Provable = {
    require(0 <= subgoal && subgoal < subgoals.length, "Subprovable can only be applied to an index " + subgoal + " within the subgoals " + subgoals)
    Provable.startProof(subgoals(subgoal))
  } ensuring (r => r.conclusion == subgoals(subgoal), "sub yields Provable with expected subgoal " + subgoals(subgoal) + " as the conclusion") ensuring (
    r => r.subgoals == immutable.List(r.conclusion), "sub Provable is an unfinished Provable")

  override def toString: String = "Provable(" + conclusion + (if (isProved) " proved" else "\n  from   " + subgoals.mkString("\n  with   ")) + ")"
  def prettyString: String = "Provable(" + conclusion.prettyString + (if (isProved) " proved" else "\n  from   " + subgoals.map(_.prettyString).mkString("\n  with   ")) + ")"
}


/** Starting new Provables to begin a proof, either with unproved conjectures or with proved axioms or axiomatic proof rules. */
object Provable {
  //@todo Code Review: it would be nice if LAX_MODE were false
  private val LAX_MODE = System.getProperty("LAX", "true")=="true"
  /** List of the class names of all external real arithmetic tools whose answers KeYmaera X would believe */
  private[this] val trustedTools: immutable.List[String] =
  "edu.cmu.cs.ls.keymaerax.tools.Mathematica" :: "edu.cmu.cs.ls.keymaerax.tools.Z3" ::
    (if (LAX_MODE) "edu.cmu.cs.ls.keymaerax.tools.Polya" :: Nil else Nil)


  /** immutable list of sound axioms, i.e., valid formulas of differential dynamic logic. (convenience method) */
  val axiom: immutable.Map[String, Formula] = AxiomBase.loadAxioms

  /** immutable list of Provables of sound axioms, i.e., valid formulas of differential dynamic logic.
    * {{{
    *       *
    *   ---------- (axiom)
    *    |- axiom
    * }}}
    *
    * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic. In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015. arXiv 1503.01981, 2015."
    * @note soundness-critical: only valid formulas are sound axioms.
    */
  val axioms: immutable.Map[String, Provable] = axiom.mapValues(axiom =>
    new Provable(Sequent(immutable.IndexedSeq(), immutable.IndexedSeq(axiom)), immutable.IndexedSeq())
  )

  /** immutable list of Provables of locally sound axiomatic proof rules.
    * {{{
    *    Gi |- Di
    *   ---------- (axiomatic rule)
    *     G |- D
    * }}}
    *
    * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic. In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015. arXiv 1503.01981, 2015."
    * @note soundness-critical: only list locally sound rules.
    * @see [[Provable.apply(USubst)]]
    */
  val rules: immutable.Map[String, Provable] = AxiomBase.loadAxiomaticRules.mapValues(rule =>
    new Provable(rule._2, rule._1)
  )

  /**
    * Begin a new proof for the desired conclusion goal
    * {{{
    *    goal
    *   ------
    *    goal
    * }}}
    *
    * @param goal the desired conclusion.
    * @return a Provable whose subgoals need to be all proved in order to prove goal.
    * @note soundness-critical
    */
  def startProof(goal : Sequent): Provable = {
    Provable(goal, immutable.IndexedSeq(goal))
  } ensuring(
    r => !r.isProved && r.subgoals == immutable.IndexedSeq(r.conclusion), "correct initial proof start")

  /**
    * Begin a new proof for the desired conclusion formula from no antecedent.
    * {{{
    *    |- goal
    *   ---------
    *    |- goal
    * }}}
    *
    * @param goal the desired conclusion formula for the succedent.
    * @return a Provable whose subgoals need to be all proved in order to prove goal.
    * @note Not soundness-critical (convenience method)
    */
  def startProof(goal : Formula): Provable =
    startProof(Sequent(immutable.IndexedSeq(), immutable.IndexedSeq(goal)))

  /**
    * Proves a formula f in real arithmetic using an external tool for quantifier elimination.
    *
    * @param t The quantifier-elimination tool.
    * @param f The formula.
    * @return a Lemma with a quantifier-free formula equivalent to f and evidence as provided by the tool.
    */
  def proveArithmetic(t: QETool, f: Formula): Lemma = {
    insist(trustedTools.contains(t.getClass.getCanonicalName), "Trusted tool required: " + t.getClass.getCanonicalName)
    // Quantifier elimination determines (quantifier-free) equivalent of f.
    val (equivalent, evidence) = t.qeEvidence(f)
    //@note soundness-critical
    val fact = Provable.oracle(new Sequent(immutable.IndexedSeq(), immutable.IndexedSeq(Equiv(f, equivalent))),
      immutable.IndexedSeq())
    Lemma(fact, Lemma.requiredEvidence(fact, evidence :: Nil), None)
  }

  /**
    * Create a new provable for oracle facts provided by external tools or lemma loading.
    *
    * @param conclusion the desired conclusion.
    * @param subgoals the remaining subgoals.
    * @return a Provable of given conclusion and given subgoals.
    * @note soundness-critical magic/trustme, only call from RCF/Lemma within core with true facts.
    */
  private[core] def oracle(conclusion: Sequent, subgoals: immutable.IndexedSeq[Sequent]) =
    Provable(conclusion, subgoals)
}


/*********************************************************************************
 * Categorize Kinds of Proof Rules
 **********************************************************************************
 */

/**
  * Subclasses represent all proof rules.
  * A proof rule is ultimately a named mapping from sequents to lists of sequents.
  * The resulting list of sequents represent the subgoal/premise and-branches all of which need to be proved
  * to prove the current sequent (desired conclusion).
  *
  * @note soundness-critical This class is sealed, so no rules can be added outside Proof.scala
  */
sealed trait Rule extends (Sequent => immutable.List[Sequent]) {
  //@note If there were inherited contracts in Scala, we could augment apply with contract "ensuring instanceOf[ClosingRule](_) || (!_.isEmpty)" to ensure only closing rules can ever come back with an empty list of premises

  /** Name of this proof rule */
  val name: String

  //@note Convenience method not used in the soundness-critical core nor anywhere else.
  override def toString: String = name
}

/*********************************************************************************
  * Categories of Proof Rules
  *********************************************************************************
  */

/** A rule applied to a position */
trait PositionRule extends Rule {
  /** The position where this rule will be applied at */
  val pos: SeqPos
  override def toString: String = name + " at " + pos
}

/** A rule applied to a position in the antecedent on the left */
trait LeftRule extends PositionRule {
  /** The position (on the left) where this rule will be applied at */
  val pos: AntePos
}

/** A rule applied to a position in the succedent on the right */
trait RightRule extends PositionRule {
  /** The position (on the right) where this rule will be applied at */
  val pos: SuccPos
}

/*********************************************************************************
  * Proof Rules
  *********************************************************************************
  */

/*********************************************************************************
  * Structural Sequent Proof Rules
  *********************************************************************************
  */

/**
  * Hide right.
  * {{{
  *    G |- D
  * ------------- (Weaken right)
  *    G |- p, D
  * }}}
  */
case class HideRight(pos: SuccPos) extends RightRule {
  val name: String = "HideRight"
  /** weakening right = hide right */
  def apply(s: Sequent): immutable.List[Sequent] = {
    immutable.List(Sequent(s.ante, s.succ.patch(pos.getIndex, Nil, 1)))
  } ensuring (_.forall(r => r.subsequentOf(s)), "structural rule subsequents")
}

/**
  * Hide left.
  * {{{
  *     G |- D
  * ------------- (Weaken left)
  *  p, G |- D
  * }}}
  */
case class HideLeft(pos: AntePos) extends LeftRule {
  val name: String = "HideLeft"
  /** weakening left = hide left */
  def apply(s: Sequent): immutable.List[Sequent] = {
    immutable.List(Sequent(s.ante.patch(pos.getIndex, Nil, 1), s.succ))
  } ensuring (_.forall(r => r.subsequentOf(s)), "structural rule subsequents")
}

/**
  * Exchange right rule reorders succedent.
  * {{{
  * G |- q, p, D
  * ------------- (Exchange right)
  * G |- p, q, D
  * }}}
  */
case class ExchangeRightRule(pos1: SuccPos, pos2: SuccPos) extends Rule {
  val name: String = "ExchangeRight"
  def apply(s: Sequent): immutable.List[Sequent] = {
    immutable.List(Sequent(s.ante, s.succ.updated(pos1.getIndex, s.succ(pos2.getIndex)).updated(pos2.getIndex, s.succ(pos1.getIndex))))
  } ensuring (_.forall(r => r.sameSequentAs(s)), "structural rule subsequents")
}

/**
  * Exchange left rule reorders antecedent.
  * {{{
  * q, p, G |- D
  * ------------- (Exchange left)
  * p, q, G |- D
  * }}}
  */
case class ExchangeLeftRule(pos1: AntePos, pos2: AntePos) extends Rule {
  val name: String = "ExchangeLeft"
  def apply(s: Sequent): immutable.List[Sequent] = {
    immutable.List(Sequent(s.ante.updated(pos1.getIndex, s.ante(pos2.getIndex)).updated(pos2.getIndex, s.ante(pos1.getIndex)), s.succ))
  } ensuring (_.forall(r => r.sameSequentAs(s)), "structural rule subsequents")
}

/*********************************************************************************
  * Sequent Proof Rules for identity/closing and cut
  *********************************************************************************
  */

/**
  * Close / Identity rule
  * {{{
  *        *
  * ------------------ (Id)
  *   p, G |- p, D
  * }}}
  */
case class Close(assume: AntePos, pos: SuccPos) extends Rule {
  val name: String = "Close"
  /** Close identity */
  def apply(s: Sequent): immutable.List[Sequent] = {
    if (s(assume) == s(pos)) {assert (assume.isAnte && pos.isSucc); Nil }
    else throw new InapplicableRuleException("The referenced formulas are not identical. Cannot close goal.\n  " + s(assume) + " not the same as\n  " + s(pos), this, s)
  } ensuring (r => r.isEmpty, "closed if applicable")
}

/**
  * Close by true
  * {{{
  *       *
  * ------------------ (close true)
  *   G |- true, D
  * }}}
  */
case class CloseTrue(pos: SuccPos) extends RightRule {
  val name: String = "CloseTrue"
  /** close true */
  override def apply(s: Sequent): immutable.List[Sequent] = {
    if (s(pos) == True) {assert(pos.isSucc); Nil }
    else throw new InapplicableRuleException("CloseTrue is not applicable to " + s + " at " + pos, this, s)
  } ensuring (r => s(pos) == True && pos.isSucc && r.isEmpty, "closed if applicable")
}

/**
  * Close by false.
  * {{{
  *        *
  * ------------------ (close false)
  *   false, G |- D
  * }}}
  */
case class CloseFalse(pos: AntePos) extends LeftRule {
  val name: String = "CloseFalse"
  /** close false */
  override def apply(s: Sequent): immutable.List[Sequent] = {
    if (s(pos) == False) { assert(pos.isAnte); Nil }
    else throw new InapplicableRuleException("CloseFalse is not applicable to " + s + " at " + pos, this, s)
  } ensuring (r => s(pos) == False && pos.isAnte && r.isEmpty, "closed if applicable")
}


/**
  * Cut in the given formula c.
  * {{{
  * G, c |- D     G |- D, c
  * ----------------------- (cut)
  *         G |- D
  * }}}
  *
  * @note c will be added at the end on the subgoals
  */
case class Cut(c: Formula) extends Rule {
  val name: String = "cut"
  /** cut in the given formula c */
  def apply(s: Sequent): immutable.List[Sequent] = {
    val use = new Sequent(s.ante :+ c, s.succ)
    val show = new Sequent(s.ante, s.succ :+ c)
    immutable.List(use, show)
  } ensuring(r => r.length==2 && s.subsequentOf(r(0)) && s.subsequentOf(r(1)),
    "subsequent of subgoals of cuts"
    ) ensuring (r => r == immutable.List(
    s.glue(Sequent(immutable.IndexedSeq(c), immutable.IndexedSeq())),
    s.glue(Sequent(immutable.IndexedSeq(), immutable.IndexedSeq(c)))),
    "same as glueing construction")
}

/*********************************************************************************
 * Propositional Sequent Proof Rules
 *********************************************************************************
 */

/**
  * !R Not right.
  * {{{
  *   G, p |- D
  * ------------ (!R Not right)
  *   G |- !p, D
  * }}}
  */
case class NotRight(pos: SuccPos) extends RightRule {
  val name: String = "Not Right"
  /** !R Not right */
  def apply(s: Sequent): immutable.List[Sequent] = {
    val Not(p) = s(pos)
    immutable.List(s.updated(pos, Sequent(immutable.IndexedSeq(p), immutable.IndexedSeq())))
  }
}

/**
  * !L Not left.
  * {{{
  *   G |- D, p
  * ------------ (!L Not left)
  *  !p, G |- D
  * }}}
  */
case class NotLeft(pos: AntePos) extends LeftRule {
  val name: String = "Not Left"
  /** !L Not left */
  def apply(s: Sequent): immutable.List[Sequent] = {
    val Not(p) = s(pos)
    immutable.List(s.updated(pos, Sequent(immutable.IndexedSeq(), immutable.IndexedSeq(p))))
  }
}

/**
  * &R And right
  * {{{
  * G |- p, D    G |- q, D
  * ---------------------- (&R And right)
  *   G |- p&q, D
  * }}}
  */
case class AndRight(pos: SuccPos) extends RightRule {
  val name: String = "And Right"
  /** &R And right */
  def apply(s: Sequent): immutable.List[Sequent] = {
    val And(p,q) = s(pos)
    immutable.List(s.updated(pos, p), s.updated(pos, q))
  }
}

/**
  * &L And left.
  * {{{
  *   G, p, q |- D
  * --------------- (&L And left)
  *   p&q, G |- D
  * }}}
  */
case class AndLeft(pos: AntePos) extends LeftRule {
  val name: String = "And Left"
  /** &L And left */
  def apply(s: Sequent): immutable.List[Sequent] = {
    val And(p,q) = s(pos)
    immutable.List(s.updated(pos, Sequent(immutable.IndexedSeq(p,q), immutable.IndexedSeq())))
  }
}

case class OrR1() extends Rule {
  val name: String = "Or Right Left Projection"
  def apply(s:Sequent): immutable.List[Sequent] = {
    val pos = SuccPos(0)
    val Or(p,q) = s(pos)
    immutable.List(s.updated(pos, Sequent(immutable.IndexedSeq(), immutable.IndexedSeq(p))))
  }
}

case class OrR2() extends Rule {
  val name: String = "Or Right Right Projection"
  def apply(s:Sequent): immutable.List[Sequent] = {
    val pos = SuccPos(0)
    val Or(p,q) = s(pos)
    immutable.List(s.updated(pos, Sequent(immutable.IndexedSeq(), immutable.IndexedSeq(q))))
  }
}

/**
  * |L Or left.
  * {{{
  * p, G |- D     q, G |- D
  * ----------------------- (|L Or left)
  *   p|q, G |- D
  * }}}
  */
case class OrLeft(pos: AntePos) extends LeftRule {
  val name: String = "Or Left"
  /** |L Or left */
  def apply(s: Sequent): immutable.List[Sequent] = {
    val Or(p,q) = s(pos)
    immutable.List(s.updated(pos, p), s.updated(pos, q))
  }
}

/**
  * ->R Imply right.
  * {{{
  *   G, p |- D, q
  * --------------- (->R Imply right)
  *   G |- p->q, D
  * }}}
  */
case class ImplyRight(pos: SuccPos) extends RightRule {
  val name: String = "Imply Right"
  /** ->R Imply right */
  def apply(s: Sequent): immutable.List[Sequent] = {
    val Imply(p,q) = s(pos)
    immutable.List(s.updated(pos, Sequent(immutable.IndexedSeq(p), immutable.IndexedSeq(q))))
  }
}


/**
  * ->L Imply left.
  * {{{
  * G, p->q |- p    q, G |- D
  * ---------------------- (-> Imply left)
  *   p->q, G |- D
  * }}}
  */
case class ImplyLeft(pos: AntePos) extends LeftRule {
  val name: String = "Imply Left"
  /** ->L Imply left */
  def apply(s: Sequent): immutable.List[Sequent] = {
    val Imply(p,q) = s(pos)
    val newAnte = s.updated(pos, p).ante
    immutable.List(
      Sequent( s.ante , immutable.IndexedSeq(p)),
      Sequent( newAnte, immutable.IndexedSeq(q))
    )
  }
}

/**
  * <->R Equiv right.
  * {{{
  * G, p |- D, q    G, q |- D, p
  * ----------------------------- (<->R Equiv right)
  *   G |- p<->q, D
  * }}}
  */
case class EquivRight(pos: SuccPos) extends RightRule {
  val name: String = "Equiv Right"
  /** <->R Equiv right */
  def apply(s: Sequent): immutable.List[Sequent] = {
    val Equiv(p,q) = s(pos)
    immutable.List(s.updated(pos, Sequent(immutable.IndexedSeq(p), immutable.IndexedSeq(q))),
                   s.updated(pos, Sequent(immutable.IndexedSeq(q), immutable.IndexedSeq(p))))
  }
}

/**
  * <->L Equiv left.
  * {{{
  * p&q, G |- D    !p&!q, G |- D
  * ----------------------------- (<-> Equiv left)
  *   p<->q, G |- D
  * }}}
  * @note Positions remain stable when decomposed this way around.
  */
case class EquivLeft(pos: AntePos) extends LeftRule {
  val name: String = "Equiv Left"
  /** <->L Equiv left */
  def apply(s: Sequent): immutable.List[Sequent] = {
    val Equiv(p,q) = s(pos)
    //@note This choice is compatible with tactics and has stable positions but is perhaps unreasonably surprising. Could prefer upper choices
    immutable.List(s.updated(pos, And(p,q)),
                   s.updated(pos, And(Not(p),Not(q))))
  }
}


/*********************************************************************************
 * Uniform Renaming Proof Rule
 *********************************************************************************
 */


/**
  * Convenience for uniform renaming.
  */
object UniformRenaming {
  /** Apply uniform renaming what~>repl to provable forward in Hilbert-style (convenience) */
  def UniformRenamingForward(provable: Provable, what: Variable, repl: Variable): Provable =
    provable(URename(what,repl)(provable.conclusion), UniformRenaming(what, repl))
}

/**
  * Uniformly rename all occurrences of what and what' to repl and repl' and vice versa.
  * Uniformly rename all occurrences of variable what (and its associated DifferentialSymbol) to repl.
  *
  * @param what What variable to replace (along with its associated DifferentialSymbol).
  * @param repl The target variable to replace what with.
  * @requires repl is fresh in the sequent.
  * @author Andre Platzer
  * @see [[URename]]
  */
final case class UniformRenaming(what: Variable, repl: Variable) extends Rule {
  //@note implied: insist(what.sort == repl.sort, "Uniform renaming only to variables of the same sort")
  val name: String = "Uniform Renaming"
  //@note soundness-critical: For uniform renaming purposes semantic renaming would be sound but not locally sound. The kernel is easier when keeping everything locally sound.
  private[this] val renaming: URename = URename(what, repl)

  override def toString: String = renaming.toString

  def apply(s: Sequent): immutable.List[Sequent] = List(renaming(s))
}

/**
  * Performs bound renaming renaming all occurrences of variable what
  * (and its associated DifferentialSymbol) to repl.
  *
  * @param what What variable (and its associated DifferentialSymbol) to replace.
  * @param repl The target variable to replace what with.
  * @param pos The position at which to perform a bound renaming.
  * @requires repl is fresh in the sequent.
  * @author Andre Platzer
  * @author Stefan Mitsch
  */
final case class BoundRenaming(what: Variable, repl: Variable, pos: SeqPos) extends PositionRule {
  //@note implied: insist(what.sort == repl.sort, "Bounding renaming only to variables of the same sort")
  val name: String = "Bound Renaming"

  //@note soundness-critical: For bound renaming purposes semantic renaming would be unsound.
  private[this] val renaming = URename(what, repl)

  override def toString: String = name + "(" + what.asString + "~>" + repl.asString + ") at " + pos

  def apply(s: Sequent): immutable.List[Sequent] = immutable.List(s.updated(pos, apply(s(pos))))

  def apply(f: Formula): Formula = { if (admissible(f))
    f match {
      case Forall(vars, g) if vars==immutable.IndexedSeq(what) => Forall(immutable.IndexedSeq(repl), renaming(g))
      case Exists(vars, g) if vars==immutable.IndexedSeq(what) => Exists(immutable.IndexedSeq(repl), renaming(g))
      //@note e is not in scope of x so is, unlike g, not affected by the renaming
      case Box    (Assign(x, e), g) if x==what => Box    (Assign(repl, e), renaming(g))
      case Diamond(Assign(x, e), g) if x==what => Diamond(Assign(repl, e), renaming(g))
      case _ => throw new RenamingClashException("Bound renaming only to bound variables " +
        what + " is not bound by a quantifier or single assignment", this.toString, f.prettyString)
    } else
    throw new RenamingClashException("Bound renaming only to fresh names but name " +
      repl + " is not fresh", this.toString, f.prettyString)
  } ensuring(r => r.getClass == f.getClass, "shape unchanged by bound renaming " + this)

  /**
    * Check whether this renaming is admissible for expression e, i.e.
    * the new name repl does not already occur (or the renaming was the identity).
    *
    * @note identity renaming is merely allowed to enable BoundVariableRenaming to introduce stutter.
    * @note This implementation currently errors if repl.sort!=Real
    * @note what==repl identity case is not used in the prover but is sound.
    * @note URename.TRANSPOSITION is irrelevant here, since repl can't occur when admissible.
    */
  private def admissible(e: Expression): Boolean =
    what == repl ||
      StaticSemantics.freeVars(e).intersect(Set(repl, DifferentialSymbol(repl), DifferentialSymbol(what))).isEmpty
}


/*********************************************************************************
  * Skolemization Proof Rule
  *********************************************************************************
  */

/**
  * Skolemization assumes that the names of the quantified variables to be skolemized are unique within the sequent.
  * This can be ensured by finding a unique name and renaming the bound variable through alpha conversion.
  * {{{
  * G |- p(x), D
  * ----------------------- (Skolemize) provided x not in G,D
  * G |- \forall x p(x), D
  * }}}
  * Skolemize also handles '''existential''' quantifiers on the left.
  * {{{
  *           p(x), G |- D
  * ------------------------ (Skolemize) provided x not in G,D
  * \exists x p(x), G |- D
  * }}}
  *
  * @note Could in principle replace by uniform substitution rule application mechanism for rule "all generalization"
  * along with tactics expanding scope of quantifier with axiom "all quantifier scope" at the cost of propositional repacking and unpacking.
  *      p(x)
  *  ---------------all generalize
  *  \forall x. p(x)
  * Kept because of the incurred cost.
  */
case class Skolemize(pos: SeqPos) extends PositionRule {
  val name: String = "Skolemize"
  override def apply(s: Sequent): immutable.List[Sequent] = {
    // all free symbols anywhere else in the sequent, i.e. except at the quantifier position
    // note: this skolemization will be by identity, not to a new name, so no clashes can be caused from s(pos)
    //@note Taboos are the free symbols which is the same as the free symbols in the remaining sequent, i.e. after replacing pos with innocent True
    //@note Literal mentions of free variables (via freeVars(s).symbols) is unsound, because <a;>true in antecedent might be usubsted to free <?x=1>true subsequently.
    val taboos = StaticSemantics.freeVars(s)
    val (v,phi) = s(pos) match {
      case Forall(qv, qphi) if pos.isSucc => (qv, qphi)
      case Exists(qv, qphi) if pos.isAnte => (qv, qphi)
      case _ => throw new InapplicableRuleException("Skolemization only applicable to universal quantifiers in the succedent or to existential quantifiers in the antecedent", this, s)
    }
    if (taboos.intersect(SetLattice(v)).isEmpty) immutable.List(s.updated(pos, phi))
    else throw new SkolemClashException("Variables to be skolemized should not appear anywhere else in the sequent. BoundRenaming required.",
        taboos.intersect(SetLattice(v)), v.toString, s.toString)
  }

}

/*********************************************************************************
  * Hybrid Games
  *********************************************************************************
  */

/**
  * Dual-free proves [a]true for dual-free a, i.e., if a is a hybrid system not a hybrid game.
  * {{{
  *       *
  * ------------------ (dual-free)
  *   G |- [a]true, D
  * }}}
  *
  * @note When using hybrid games axiomatization
  */
final case class DualFree(pos: SuccPos) extends RightRule {
  val name: String = "dualFree"
  /** Prove [a]true by showing that a is dual-free */
  override def apply(s: Sequent): immutable.List[Sequent] = {
    s(pos) match {
      case Box(a, True) if dualFree(a) => Nil
      case _ => throw new InapplicableRuleException("DualFree is not applicable to " + s + " at " + pos + " because a duality operator occurs", this, s)
    }
  } ensuring (s(pos).isInstanceOf[Box] && s(pos).asInstanceOf[Box].child==True && dualFree(s(pos).asInstanceOf[Box].program) && pos.isSucc && _.isEmpty, "closed if applicable")

  /** Check whether given program is dual-free, so a hybrid system and not a hybrid game */
  private def dualFree(program: Program): Boolean = program match {
    case a: ProgramConst             => false /* @note false Unless USubst rejects Duals as substitutues for ProgramConst */
    case Assign(x, e)                => true
    case AssignAny(x)                => true
    case Test(f)                     => true /* even if f contains duals, since they're different nested games) */
    case ODESystem(a, h)             => true /*|| dualFreeODE(a)*/ /* @note Optimized assuming no differential games */
    case Choice(a, b)                => dualFree(a) && dualFree(b)
    case Compose(a, b)               => dualFree(a) && dualFree(b)
    case Loop(a)                     => dualFree(a)
    case Dual(a)                     => false
  }

  /** Check whether given differential program is dual-free, which is mostly unnecessary */
//  private def dualFreeODE(program: DifferentialProgram): Boolean = program match {
//    case AtomicODE(DifferentialSymbol(x), e) => true
//    case c: DifferentialProgramConst => true
//    case DifferentialProduct(a, b)   => dualFreeODE(a) && dualFreeODE(b)
//  }
}


/*********************************************************************************
  * Derived Sequent Proof Rules, for efficiency
  *********************************************************************************
  */

/**
  * CoHide right.
  * {{{
  *     |- p
  * ------------- (CoHide right)
  *   G |- p, D
  * }}}
  *
  * @derived
  */
case class CoHideRight(pos: SuccPos) extends RightRule {
  val name: String = "CoHideRight"
  /** co-weakening right = co-hide right (all but indicated position) */
  def apply(s: Sequent): immutable.List[Sequent] = {
    immutable.List(Sequent(immutable.IndexedSeq(), immutable.IndexedSeq(s.succ(pos.getIndex))))
  } ensuring (_.forall(r => r.subsequentOf(s)), "structural rule subsequents")
}

/**
  * CoHide left.
  * {{{
  *      p |-
  * ------------- (CoHide left)
  *   p, G |- D
  * }}}
  *
  * @note Rarely useful (except for contradictory `p`)
  * @note Not used, just contained for symmetry reasons
  * @derived
  */
case class CoHideLeft(pos: AntePos) extends LeftRule {
  val name: String = "CoHideLeft"
  /** co-weakening left = co-hide left (all but indicated position) */
  def apply(s: Sequent): immutable.List[Sequent] = {
    immutable.List(Sequent(immutable.IndexedSeq(s.ante(pos.getIndex)), immutable.IndexedSeq()))
  } ensuring (_.forall(r => r.subsequentOf(s)), "structural rule subsequents")
}

/**
  * CoHide2 hides all but the two indicated positions.
  * {{{
  *      p |- q
  * --------------- (CoHide2)
  *   p, G |- q, D
  * }}}
  *
  * @derived
  */
case class CoHide2(pos1: AntePos, pos2: SuccPos) extends Rule {
  val name: String = "CoHide2"
  /** co-weakening = co-hide all but the indicated positions */
  def apply(s: Sequent): immutable.List[Sequent] = {
    immutable.List(Sequent(immutable.IndexedSeq(s.ante(pos1.getIndex)), immutable.IndexedSeq(s.succ(pos2.getIndex))))
  } ensuring (_.forall(r => r.subsequentOf(s)), "structural rule subsequents")
}


/**
  * Cut in the given formula c in place of p on the right.
  * {{{
  * G |- c, D    G |- c->p, D
  * ------------------------- (Cut right)
  *        G |- p, D
  * }}}
  * Forward Hilbert style rules can move further away, implicationally, from the sequent implication.
  * Backwards tableaux style sequent rules can move closer, implicationally, toward the sequent implication.
  *
  * @derived(cut(c->p) & <(ImplyLeft & <(CloseId, HideRight), HideRight))
  */
case class CutRight(c: Formula, pos: SuccPos) extends Rule {
  val name: String = "cut Right"
  def apply(s: Sequent): immutable.List[Sequent] = {
    val p = s(pos)
    immutable.List(s.updated(pos, c), s.updated(pos, Imply(c, p)))
  }
}

/**
  * Cut in the given formula c in place of p on the left.
  * {{{
  * c, G |- D    G |- D, p->c
  * ------------------------- (Cut Left)
  *        p, G |- D
  * }}}
  * Forward Hilbert style rules can move further away, implicationally, from the sequent implication.
  * Backwards tableaux style sequent rules can move closer, implicationally, toward the sequent implication.
  *
  * @note this would perhaps surprising that inconsistent posititioning within this rule, unlike in ImplyLeft?
  * @derived(cut(p->c) & <(ImplyLeft & <(HideLeft, CloseId), HideLeft))
  */
case class CutLeft(c: Formula, pos: AntePos) extends Rule {
  val name: String = "cut Left"
  def apply(s: Sequent): immutable.List[Sequent] = {
    val p = s(pos)
    immutable.List(s.updated(pos, c),
                   s.updated(pos, Sequent(immutable.IndexedSeq(), immutable.IndexedSeq(Imply(p, c)))))
  }
}

/**
  * Commute equivalence right
  * {{{
  * G |- q<->p, D
  * ------------- (<->cR)
  * G |- p<->q, D
  * }}}
  *
  * @derived
  */
case class CommuteEquivRight(pos: SuccPos) extends RightRule {
  val name: String = "CommuteEquivRight"
  def apply(s: Sequent): immutable.List[Sequent] = {
    val Equiv(p,q) = s(pos)
    immutable.List(s.updated(pos, Equiv(q, p)))
  }
}

/**
  * Commute equivalence left
  * {{{
  * q<->p, G |-  D
  * -------------- (<->cL)
  * p<->q, G |-  D
  * }}}
  *
  * @derived
  * @note Not used, just contained for symmetry reasons
  */
case class CommuteEquivLeft(pos: AntePos) extends LeftRule {
  val name: String = "CommuteEquivLeft"
  def apply(s: Sequent): immutable.List[Sequent] = {
    val Equiv(p,q) = s(pos)
    immutable.List(s.updated(pos, Equiv(q, p)))
  }
}

/**
  * Equivify Right: Convert implication to equivalence.
  * {{{
  * G |- a<->b, D
  * -------------
  * G |- a->b,  D
  * }}}
  */
// ->2<-> Equivify Right: Equivalencify Implication Right
//@derived(cut(a<->b) & prop...)
case class EquivifyRight(pos: SuccPos) extends RightRule {
  val name: String = "EquivifyRight"
  def apply(s: Sequent): immutable.List[Sequent] = {
    val Imply(a,b) = s(pos)
    immutable.List(s.updated(pos, Equiv(a, b)))
  }
}

