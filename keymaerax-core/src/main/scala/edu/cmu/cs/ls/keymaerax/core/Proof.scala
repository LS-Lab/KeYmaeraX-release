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
  * @see Andre Platzer and Yong Kiam Tan. [[https://doi.org/10.1145/3380825 Differential equation invariance axiomatization]]. J. ACM. 67(1), 6:1-6:66, 2020.
  * @see Andre Platzer. [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 59(2), pp. 219-266, 2017.
  * @see Andre Platzer. [[https://doi.org/10.1007/978-3-319-21401-6_32 A uniform substitution calculus for differential dynamic logic]].  In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015. [[http://arxiv.org/pdf/1503.01981.pdf arXiv 1503.01981]]
  * @see Andre Platzer. [[https://doi.org/10.1145/2817824 Differential game logic]]. ACM Trans. Comput. Log. 17(1), 2015. [[http://arxiv.org/pdf/1408.1980 arXiv 1408.1980]]
  * @see Andre Platzer. [[https://doi.org/10.1109/LICS.2012.64 The complete proof theory of hybrid systems]]. ACM/IEEE Symposium on Logic in Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 541-550. IEEE 2012
  * @see Andre Platzer. [[https://doi.org/10.1007/s10817-008-9103-8 Differential dynamic logic for hybrid systems]]. Journal of Automated Reasoning, 41(2), pages 143-189, 2008.
  * @note Code Review: 2020-02-17
  */
package edu.cmu.cs.ls.keymaerax.core

import java.security.MessageDigest

import edu.cmu.cs.ls.keymaerax.Configuration

// require favoring immutable Seqs for soundness

import scala.collection.immutable

/*--------------------------------------------------------------------------------*/
/*--------------------------------------------------------------------------------*/

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
  * Provables are stateless and do not themselves remember other provables that they resulted from.
  * The ProofTree data structure outside the kernel provides such proof tree navigation information.
  *
  * @param conclusion the conclusion `G |- D` that follows if all subgoals are valid.
  * @param subgoals the premises `Gi |- Di` that, if they are all valid, imply the conclusion.
  * @note soundness-critical logical framework.
  * @note Only private constructor calls for soundness
  * @note For soundness: No reflection should bypass constructor call privacy,
  *       nor reflection to bypass immutable val algebraic data types.
  * @author Andre Platzer
  * @see Andre Platzer. [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 59(2), pp. 219-266, 2017.
  * @see [[edu.cmu.cs.ls.keymaerax.core.Provable.startProof(goal:edu\.cmu\.cs\.ls\.keymaerax\.core\.Sequent):edu\.cmu\.cs\.ls\.keymaerax\.core\.Provable*]]
  * @see [[edu.cmu.cs.ls.keymaerax.core.Provable.axioms]]
  * @see [[edu.cmu.cs.ls.keymaerax.core.Provable.rules]]
  * @see [[edu.cmu.cs.ls.keymaerax.core.Provable.proveArithmetic]]
  * @see [[edu.cmu.cs.ls.keymaerax.core.Provable.fromStorageString(storedProvable:String):edu\.cmu\.cs\.ls\.keymaerax\.core\.Provable*]]
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
final case class Provable private(conclusion: Sequent, subgoals: immutable.IndexedSeq[Sequent]) {
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
    * @requires(isProved)
    * @throws UnprovedException if !isProved so illegally trying to read a proved sequent from a Provable that is not in fact proved.
    */
  final def proved: Sequent =
    if (isProved) conclusion else throw new UnprovedException("Only Provables that have been proved have a proven conclusion", toString)

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
    * @throws IllegalArgumentException if subgoal is out of range of the subgoals.
    * @throws CoreException subtypes if rule raises those exceptions when applied to the indicated subgoal.
    * @requires(0 <= subgoal && subgoal < subgoals.length)
    * @note soundness-critical. And soundness needs Rule to be sealed.
    */
  final def apply(rule: Rule, subgoal: Subgoal): Provable = {
    require(0 <= subgoal && subgoal < subgoals.length, "Rules " + rule + " should be applied to a subgoal " + subgoal + " that is within the subgoals " + subgoals)
    rule(subgoals(subgoal)) match {
      // subgoal closed by proof rule
      case Nil => new Provable(conclusion, subgoals.patch(subgoal, Nil, 1))
      // subgoal replaced by new subgoals goal::rest
      case goal :: rest => new Provable(conclusion, subgoals.updated(subgoal, goal) ++ rest)
    }
  } ensures(r => r.conclusion == conclusion, "Same conclusion after applying proof rules") ensures (
    r => subgoals.patch(subgoal, Nil, 1).toSet.subsetOf(r.subgoals.toSet),
    "All previous premises still around except the one that the proof rule " + rule + " has been applied to subgoal " + subgoals(subgoal) + " in " + this) ensures (
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
    *   G1 |- D1 ... Gi |- Di ... Gn |- Dn      G1 |- D1 ... Gr1 |- Dr1 ... Gn |- Dn Gr2 |- Dr2 ... Grk | Drk
    *   ----------------------------------  =>  -------------------------------------------------------------
    *                 G |- D                                           G |- D
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
    * @throws IllegalArgumentException if subgoal is out of range of the subgoals.
    * @throws SubderivationSubstitutionException if the subderivation's conclusion is not equal to the indicated subgoal.
    * @requires(0 <= subgoal && subgoal < subgoals.length)
    * @requires(subderivation.conclusion == subgoals(subgoal))
    * @note soundness-critical
    */
  final def apply(subderivation: Provable, subgoal: Subgoal): Provable = {
    require(0 <= subgoal && subgoal < subgoals.length, "derivation " + subderivation + " can only be applied to an index " + subgoal + " within the subgoals " + subgoals)
    if (subderivation.conclusion != subgoals(subgoal)) throw new SubderivationSubstitutionException(subderivation.toString, subderivation.conclusion.toString, subgoals(subgoal).toString, subgoal, toString)
    subderivation.subgoals.toList match {
      // subderivation proves given subgoal
      case Nil =>
        assert(subderivation.isProved && subderivation.proved == subgoals(subgoal), "Subderivation proves the given subgoal " + subgoals(subgoal) + " of\n" + this + "\nby subderivation\n" + subderivation)
        new Provable(conclusion, subgoals.patch(subgoal, Nil, 1))
      // subderivation replaces subgoal by new premises goal::rest
      case goal :: rest => new Provable(conclusion, subgoals.updated(subgoal, goal) ++ rest)
    }
  } ensures(r => r.conclusion == conclusion,
    "Same conclusion\n" + conclusion + " after joining derivations") ensures (
    r => subgoals.patch(subgoal, Nil, 1).toSet.subsetOf(r.subgoals.toSet),
    "All previous premises still around except the one replaced by a derivation") ensures (
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
    * @throws SubstitutionClashException if this substitution is not admissible for this Provable.
    * @author Andre Platzer
    * @see Andre Platzer. [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 59(2), pp. 219-266, 2017. Theorem 26+27."
    * @note soundness-critical. And soundness-critical that only locally sound Provables can be constructed (otherwise implementation would be more complicated).
    */
  final def apply(subst: USubst): Provable =
    try {
      //@note if isProved, uniform substitution of Provables has the same effect as the globally sound uniform substitution rule (whatever free variables), which is also locally sound if no premises.
      //@note case subst.freeVars.isEmpty is covered by Theorem 27 of Andre Platzer. [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 59(2), pp. 219-266, 2017
      //@note case isProved is covered by Andre Platzer. [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 59(2), pp. 219-266, 2017. Theorem 26 and Theorem 27 without subgoals having same effect as Theorem 26. There is no difference between locally sound and globally sound if isProved so no subgoals.
      //@note special blessing for "CQ equation congruence" is covered by Brandon Bohrer [[https://github.com/LS-Lab/Isabelle-dL/blob/master/Proof_Checker.thy]]
      if (usubstChurch) {
        insist(subst.freeVars.isEmpty || isProved || this==Provable.rules("CQ equation congruence"), "Unless proved, uniform substitutions instances cannot introduce free variables " + subst.freeVars.prettyString + "\nin " + subst + " on\n" + this)
        new Provable(subst(conclusion), subgoals.map(s => subst(s)))
      } else {
        if (isProved || this==Provable.rules("CQ equation congruence"))
          new Provable(subst(conclusion), subgoals.map(s => subst(s)))
        else
          new Provable(subst.applyAllTaboo(conclusion), subgoals.map(s => subst.applyAllTaboo(s)))
      }
    } catch { case exc: SubstitutionClashException => throw exc.inContext(subst + " on\n" + this) }

  /**
    * Apply a (possibly semantic) uniform renaming to a (locally sound!) Provable.
    * Uniformly renames by transposition both subgoals and conclusion with the same uniform renaming `ren`.
    * {{{
    *    G1 |- D1 ... Gn |- Dn              r(G1) |- r(D1) ... r(Gn) |- r(Dn)
    *   -----------------------     =>     -----------------------------------   (URen)
    *            G |- D                                r(G) |- r(D)
    * }}}
    *
    * @param ren The uniform renaming to be used on the premises and conclusion of this Provable.
    * @return The Provable resulting from applying `ren` to our subgoals and conclusion.
    * @throws RenamingClashException if this uniform renaming is not admissible (because a semantic symbol occurs despite !semantic).
    * @author Andre Platzer
    * @see Andre Platzer. [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 59(2), pp. 219-266, 2017. Theorem 26+27."
    * @see Andre Platzer. [[https://doi.org/10.1007/978-3-030-29436-6_25 Uniform substitution at one fell swoop]]. In Pascal Fontaine, editor, International Conference on Automated Deduction, CADE'19, Natal, Brazil, Proceedings, volume 11716 of LNCS, pp. 425-441. Springer, 2019.
    * @since 4.7.5
    * @note soundness-critical: Semantic uniform renaming requires locally sound input provables. The kernel is easier when keeping everything locally sound.
    * @see [[URename]]
    * @see [[UniformRenaming]]
    */
  final def apply(ren: URename): Provable =
    try {
      new Provable(ren(conclusion), subgoals.map(s => ren(s)))
    } catch { case exc: RenamingClashException => throw exc.inContext(ren + " on\n" + this) }


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
    * @throws CoreException subtypes if rule raises those exceptions when applied to `newConsequent`.
    * @note not soundness-critical derived function since implemented in terms of other apply functions
    */
  def apply(newConsequence: Sequent, rule: Rule): Provable = {
    //@note the following requirement is redundant and not soundness-critical. It just gives a better error message.
    insist(rule(newConsequence)==List(this.conclusion), "Rule " + rule + " was expected to justify\n" + this.conclusion.prettyString + "\n-----------------------------" + rule + "??\n" + newConsequence.prettyString +
      "\n\nThat is, applying the rule backwards to new consequence\n" + newConsequence + "\nshould result in\n" + this.conclusion + "\nwhich is the conclusion of this " + this + "\nThe rule instead led to " + rule(newConsequence) +
      "\n\nExpected: " + edu.cmu.cs.ls.keymaerax.parser.FullPrettyPrinter(this.conclusion) +
      "\nFound:    " + rule(newConsequence).map(s=>edu.cmu.cs.ls.keymaerax.parser.FullPrettyPrinter(s)).mkString(", "))
    Provable.startProof(newConsequence)(rule, 0)(this, 0)
  } ensures(r => r.conclusion == newConsequence, "New conclusion\n" + newConsequence + " after continuing derivations") ensures(
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
  } ensures(r => r.conclusion == prolongation.conclusion && r.subgoals == subgoals, "Prolonging proof forward\n" + this + "\nwith\n" + prolongation)

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
    * @throws IllegalArgumentException if subgoal is out of range of the subgoals.
    * @note not soundness-critical only helpful for completeness-critical
    */
  def sub(subgoal: Subgoal): Provable = {
    require(0 <= subgoal && subgoal < subgoals.length, "Subprovable can only be applied to an index " + subgoal + " within the subgoals " + subgoals)
    Provable.startProof(subgoals(subgoal))
  } ensures (r => r.conclusion == subgoals(subgoal), "sub yields Provable with expected subgoal " + subgoals(subgoal) + " as the conclusion") ensures (
    r => r.subgoals == immutable.List(r.conclusion), "sub Provable is an unfinished Provable")

  override def toString: String = "Provable(" + conclusion + (if (isProved) " proved" else "\n  from   " + subgoals.mkString("\n  with   ")) + ")"
  def prettyString: String = "Provable{" + (if (isProved) conclusion.prettyString + " proved" else "\n" + conclusion.prettyString + "\n  from\n" + subgoals.map(_.prettyString).mkString("\n  with\n")) + "}"
}


/** Starting new Provables to begin a proof, either with unproved conjectures or with proved axioms or axiomatic proof rules.
  * @see [[Provable.axioms]]
  * @see [[Provable.rules]]
  * @see [[Provable$.startProof(goal:edu\.cmu\.cs\.ls\.keymaerax\.core\.Sequent):edu\.cmu\.cs\.ls\.keymaerax\.core\.Provable*]]
  */
object Provable {
  /** List of the class names of all external real arithmetic tools whose answers KeYmaera X would believe */
  private val trustedTools: immutable.List[String] =
  "edu.cmu.cs.ls.keymaerax.tools.qe.MathematicaQETool" :: "edu.cmu.cs.ls.keymaerax.tools.qe.Z3QETool" ::
    "edu.cmu.cs.ls.keymaerax.tools.qe.BigDecimalQETool$" :: Nil


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
    * @see [[Provable.apply(subst:edu\.cmu\.cs\.ls\.keymaerax\.core\.USubstOne):edu\.cmu\.cs\.ls\.keymaerax\.core\.Provable*]]
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
  final def startProof(goal: Sequent): Provable = {
    Provable(goal, immutable.IndexedSeq(goal))
  } ensures(
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
  def startProof(goal: Formula): Provable =
    startProof(Sequent(immutable.IndexedSeq(), immutable.IndexedSeq(goal)))

  /**
    * Proves a formula f in real arithmetic using an external tool for quantifier elimination.
    * {{{
    *           *
    *    -------------- (tool)
    *     |- f<->QE(f)
    * }}}
    *
    * @param tool The quantifier-elimination tool that computes the equivalent `QE(f)`.
    * @param f The formula.
    * @requires QE(f) is equivalent to f
    * @return a Provable with an equivalence of f to the quantifier-free formula equivalent to f, justified by tool.
    * @see [[QETool.quantifierElimination()]]
    */
  final def proveArithmetic(tool: QETool, f: Formula): Provable = {
    insist(trustedTools.contains(tool.getClass.getCanonicalName), "Trusted tool required: " + tool.getClass.getCanonicalName)
    // Quantifier elimination determines (quantifier-free) equivalent of f.
    val equivalent = tool.quantifierElimination(f)
    //@note soundness-critical
    oracle(Sequent(immutable.IndexedSeq(), immutable.IndexedSeq(Equiv(f, equivalent))),
      immutable.IndexedSeq())
  }

  /**
    * Axiom schema for vectorial differential ghosts, schematic in dimension.
    * Schema returns two Provables, one for each direction of the differential ghost axiom.
    * This reduces duplication of code constructing the ghost vectors.
    * {{{
    *   [{y_'=g(||),c{|y_|}&q(|y_|)}] (||y_||^2) <= f(|y_|)
    *   -> ( [{y_'=g(||),c{|y_|}&q(|y_|)}]p(|y_|) -> [{c{|y_|}&q(|y_|)}]p(|y_|) )
    *
    *   [{c{|y_|}&q(|y_|)}]p(|y_|) -> [{y_'=g(||),c{|y_|}&q(|y_|)}]p(|y_|)
    * }}}
    *
    * @param dim The number of ghost variables
    */
  final def vectorialDG(dim : Int): (Provable,Provable) = {
    insist(dim > 0, "Must introduce at least one vectorial differential ghost variable.")

    // The list of variables y__1, y__2, ..., y__dim
    val ghosts = (1 to dim).map(i => BaseVariable("y_", Some(i)))
    // The list of RHS g1(||), g2(||), ..., gdim(||)
    // @todo: UnitFunctionals may need an index argument
    val ghostRHSs = (1 to dim).map(i => UnitFunctional("g"+i,AnyArg,Real))
    // The list ghost ODEs y__1'=g1(||), y__2'=g2(||), ..., y__dim'=gdim(||)
    val ghostODEList = (ghosts zip ghostRHSs).map{ case (y,rhs) => AtomicODE(DifferentialSymbol(y), rhs) }
    // The list of ghost ODEs as a single ODE
    val ghostODEs = ghostODEList.reduce(DifferentialProduct.apply)

    // The base ODE c{|y_|}
    val baseODE = DifferentialProgramConst("c",Except(ghosts))
    // The base ODE extended with ghost ODEs
    val extODE = DifferentialProduct(ghostODEs,baseODE)
    val domain = UnitPredicational("q",Except(ghosts))
    val post = UnitPredicational("p",Except(ghosts))

    // The squared norm of the vector ||y__1, y__2, ..., y__dim||^2
    val sqnorm = ghosts.map(e => Times(e, e)).reduceLeft(Plus)
    // The bounding term f(|y__1,y__2,...,y__dim|)
    val cofF = UnitFunctional("f_",Except(ghosts),Real)
    // The norm bound required of the ghost ODEs (||y_||^2) <= f(|y_|)
    val normBound = LessEqual(sqnorm,cofF)

    val DGimply =
      Imply(
      // [{y_'=g(||),c{|y_|}&q(|y_|)}] ||y_||^2 <= f(|y_|) ->
      Box(ODESystem(extODE,domain),normBound),
      // [{y_'=g(||),c{|y_|}&q(|y_|)}]p(|y_|) -> [{c{|y_|}&q(|y_|)}]p(|y_|)
      Imply(Box(ODESystem(extODE,domain),post), Box(ODESystem(baseODE,domain),post))
      )

    val DGylpmi =
      // [{c{|y_|}&q(|y_|)}]p(|y_|) -> [{y_'=g(||),c{|y_|}&q(|y_|)}]p(|y_|)
      Imply(Box(ODESystem(baseODE,domain),post), Box(ODESystem(extODE,domain),post))

    //@note soundness-critical
    (
      oracle(Sequent(immutable.IndexedSeq(), immutable.IndexedSeq(DGimply)), immutable.IndexedSeq()),
      oracle(Sequent(immutable.IndexedSeq(), immutable.IndexedSeq(DGylpmi)), immutable.IndexedSeq())
    )
  }

  /**
    * Axiom schema for differential adjoints, schematic in dimension.
    * {{{
    *   <{x_'=f_(x_) & q_(x_)}>x_=y_ <-> <{y_'=-f_(y_) & q_(y_)}>x_=y_
    * }}}
    *
    * @param dim The dimension of ODE x_'=f_(x_)
    */
  final def diffAdjoint(dim : Int): Provable = {
    insist(dim > 0, "Diff. adjoint over ODE with at least 1 variable.")

    //Indices 1,2,...dim
    val indices = 1 to dim
    // The list of LHS variables x__1, x__2, ..., x__dim
    val xLHS = indices.map(i => BaseVariable("x_", Some(i)))
    // The list of LHS variables y__1, y__2, ..., y__dim
    val yLHS = indices.map(i => BaseVariable("y_", Some(i)))
    // The sort of RHS functions and predicates is (real,(real,...)) n times
    val sort = indices.map( _ => Real).reduceRight(Tuple)
    val RHSfunc = indices.map(i => Function("f_", Some(i), sort,Real))
    // The application f_(x_) where x_ is written as a tuple of the right sort  (x_1,(x_2,(...))
    val RHSxarg = xLHS.reduceRight(Pair)
    val xRHS =  RHSfunc.map{ f => FuncOf(f,RHSxarg) }
    // The application f_(y_) where y_ is written as a tuple of the right sort (y_1,(y_2,(...))
    val RHSyarg = yLHS.reduceRight(Pair)
    val yRHS =  RHSfunc.map{ f => FuncOf(f,RHSyarg) }

    // ODEs for x_, y_
    val xODE = (xLHS zip xRHS).map{case (x,rhs) => AtomicODE(DifferentialSymbol(x), rhs)}
      .reduceRight(DifferentialProduct.apply)
    val yODE = (yLHS zip yRHS).map{case (y,rhs) => AtomicODE(DifferentialSymbol(y), Neg(rhs))}
      .reduceRight(DifferentialProduct.apply)
    // Domains for x_, y_
    val xDom = PredOf(Function("q_", None, sort, Bool), RHSxarg)
    val yDom = PredOf(Function("q_", None, sort, Bool), RHSyarg)
    // Postcondition x_ = y_
    val eq = (xLHS zip yLHS).map( xy => Equal(xy._1,xy._2)).reduceRight(And)

    //<x_'=f_(x_)&q_(x_)>x_=y_ <-> <y_'=-f_(y_)&q_(y_)>x_=y_
    val diffAdj = Equiv(Diamond(ODESystem(xODE,xDom),eq),Diamond(ODESystem(yODE,yDom),eq))

    //@note soundness-critical
    oracle(Sequent(immutable.IndexedSeq(), immutable.IndexedSeq(diffAdj)), immutable.IndexedSeq())
  }

  /**
    * Create a new provable for oracle facts provided by external tools or lemma loading.
    *
    * @param conclusion the desired conclusion.
    * @param subgoals the remaining subgoals.
    * @return a Provable of given conclusion and given subgoals.
    * @note soundness-critical magic/trustme, only call from [[proveArithmetic()]]/[[fromStorageString()]] with true facts.
    */
  private final def oracle(conclusion: Sequent, subgoals: immutable.IndexedSeq[Sequent]) =
    Provable(conclusion, subgoals)



  /*********************************************************************************
    * Stored Provable as Strings for lemmas, DB, and persistence purposes.
    * Printed Provables are parsed again if their reprinted checksum is unmodified.
    * Checksum protection is against nonadversarial accidental modification.
    **********************************************************************************
    */

  /** Stored Provable representation as a string of the given Provable that will reparse correctly.
    * @note If store printer is injective function, then only `fact` reparses via fromStorageString unless checksum modified or not injective.
    * @see [[Provable.fromStorageString(storedProvable:String):edu\.cmu\.cs\.ls\.keymaerax\.core\.Provable*]]
    * @ensures fromStorageString(\result) == fact
    */
  final def toStorageString(fact: Provable): String = {
    val s = toExternalString(fact)
    s + "::" + checksum(s)
    //@note soundness-critical check reparsing to original (unless printer+checksum injective or unless printer+parser trusted)
  } ensures(r => fromStorageString(r) == fact, "Stored Provable should reparse to the original\n\n" +
     toExternalString(fact) + "::" + checksum(toExternalString(fact)))

  /**
    * Parses a Stored Provable String representation back again as a Provable.
    * Soundness depends on the fact that the String came from [[toStorageString()]],
    * which is checked in a lightweight fashion using checksums.
    * @param storedProvable The String obtained via [[toStorageString(fact:edu\.cmu\.cs\.ls\.keymaerax\.core\.Provable):String*]].
    * @return The Provable that represents `storedProvable`.
    * @throws ProvableStorageException if storedProvable is illegal.
    * @see [[Provable.toStorageString(fact:edu\.cmu\.cs\.ls\.keymaerax\.core\.Provable):String*]]
    */
  final def fromStorageString(storedProvable: String): Provable = {
    val separator = storedProvable.lastIndexOf("::")
    if (separator < 0)
      throw new ProvableStorageException("syntactically ill-formed format", storedProvable)
    val storedChecksum = storedProvable.substring(separator+2)
    val remainder = storedProvable.substring(0, separator)
    (try {
      edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXStoredProvableParser(remainder)
    } catch {
      case ex: Exception => throw new ProvableStorageException("cannot be parsed: " + ex.toString, storedProvable).initCause(ex)
    }) match {
      case conclusion :: subgoals =>
        //@note soundness-critical, guarded lightly by checksum
        val reconstructed = oracle(conclusion, subgoals.to)
        if (checksum(toExternalString(reconstructed)) != storedChecksum)
          throw new ProvableStorageException("checksum has been tampered with", storedProvable)
        else
          reconstructed
      case Nil =>
        throw new ProvableStorageException("empty list of sequents is no Provable", storedProvable)
    }
  }

  // storage implementation

  /** The permanent pretty printer that is used for Provable storage purposes */
  // = java.lang.Class.forName("edu.cmu.cs.ls.keymaerax.parser.FullPrettyPrinter").newInstance
  private val store: PrettyPrinter.PrettyPrinter = edu.cmu.cs.ls.keymaerax.parser.FullPrettyPrinter

  /** Checksum computation implementation using the checksum algorithm used to stamp stored Provables. */
  private def checksum(s: String): String =
  //@note New instance every time, because digest() is not threadsafe. It calls digest.update() internally, so may compute hash of multiple strings at once
  MessageDigest.getInstance("MD5").digest(s.getBytes("UTF-8")).map("%02x".format(_)).mkString

  /** A fully parenthesized String representation of the given Sequent for externalization.
    * @see [[Sequent.toString]]
    */
  private def toExternalString(s: Sequent): String =
  s.ante.map(store).mkString(" :: ") + (if (s.ante.isEmpty) "  ==>  " else "\n  ==>  ") + s.succ.map(store).mkString(" :: ")

  /** A fully parenthesized String representation of the given Provable for externalization.
    * @see [[Provable.toString()]]
    * @see [[toStorageString(fact:edu\.cmu\.cs\.ls\.keymaerax\.core\.Provable):String*]]
    */
  private def toExternalString(fact: Provable): String =
    toExternalString(fact.conclusion) +
    (if (fact.isProved) "\n\\qed"
    else "\n\\from   " + fact.subgoals.map(toExternalString).mkString("\n\\from   ") + "\n\\qed" )

}


/*********************************************************************************
 * Categorize Kinds of Proof Rules
 **********************************************************************************
 */

/**
  * Subclasses represent all built-in proof rules.
  * A proof rule is ultimately a named mapping from sequents to lists of sequents.
  * The resulting list of sequents represent the subgoals/premises all of which need to be proved
  * to prove the current sequent (desired conclusion).
  *
  * @note soundness-critical This class is sealed, so no rules can be added outside Proof.scala
  * @see [[Provable.rules]]
  */
sealed trait Rule extends (Sequent => immutable.List[Sequent]) {
  //@note If there were inherited contracts in Scala, we could augment apply with contract "ensures instanceOf[ClosingRule](_) || (!_.isEmpty)" to ensure only closing rules can ever come back with an empty list of premises

  /** Name of this proof rule */
  val name: String

  //@note Convenience method not used in the soundness-critical core nor anywhere else.
  override def toString: String = name
}

/*********************************************************************************
  * Categories of Proof Rules
  *********************************************************************************
  */

/** A rule applied to a position in a sequent.
  * @see [[SeqPos]] */
trait PositionRule extends Rule {
  /** The position where this rule will be applied at. */
  val pos: SeqPos
  override def toString: String = name + " at " + pos
}

/** A rule applied to a position in the antecedent on the left of a sequent.
  * LeftRules can only be applied to antecedent positions.
  * @see [[AntePos]] */
trait LeftRule extends PositionRule {
  /** The position (on the left) where this rule will be applied at. */
  val pos: AntePos
}

/** A rule applied to a position in the succedent on the right of a sequent.
  * RightRules can only be applied to succedent positions.
  * @see [[SuccPos]] */
trait RightRule extends PositionRule {
  /** The position (on the right) where this rule will be applied at. */
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
  } ensures (_.forall(r => r.subsequentOf(s)), "structural rule subsequents")
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
  } ensures (_.forall(r => r.subsequentOf(s)), "structural rule subsequents")
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
  } ensures (_.forall(r => r.sameSequentAs(s)), "structural rule subsequents")
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
  } ensures (_.forall(r => r.sameSequentAs(s)), "structural rule subsequents")
}

/*********************************************************************************
  * Sequent Proof Rules for identity/closing and cut
  *********************************************************************************
  */

/**
  * Close / Identity rule proving an assumption available in the antecedent.
  * {{{
  *        *
  * ------------------ (Id)
  *   p, G |- p, D
  * }}}
  */
case class Close(assume: AntePos, pos: SuccPos) extends Rule {
  val name: String = "Close"
  /** Close identity
    * @throws InapplicableRuleException if the two formulas at the two indicated positions in the sequent are not identical.
    */
  def apply(s: Sequent): immutable.List[Sequent] = {
    if (s(assume) == s(pos)) {assert (assume.isAnte && pos.isSucc); Nil }
    else throw InapplicableRuleException("The referenced formulas are not identical. Cannot close goal.\n  " + s(assume) + " not the same as\n  " + s(pos), this, s)
  } ensures (r => r.isEmpty, "closed if applicable")
}

/**
  * Close by true among the succedent desiderata.
  * {{{
  *       *
  * ------------------ (close true)
  *   G |- true, D
  * }}}
  */
case class CloseTrue(pos: SuccPos) extends RightRule {
  val name: String = "CloseTrue"
  /** close true
    * @throws InapplicableRuleException if the formula True is not at the indicated position in the sequent.
    */
  override def apply(s: Sequent): immutable.List[Sequent] = {
    if (s(pos) == True) {assert(pos.isSucc); Nil }
    else throw InapplicableRuleException("CloseTrue is not applicable to " + s + " at " + pos, this, s)
  } ensures (r => s(pos) == True && pos.isSucc && r.isEmpty, "closed if applicable")
}

/**
  * Close by false among the antecedent assumptions.
  * {{{
  *        *
  * ------------------ (close false)
  *   false, G |- D
  * }}}
  */
case class CloseFalse(pos: AntePos) extends LeftRule {
  val name: String = "CloseFalse"
  /** close false
    * @throws InapplicableRuleException if the formula False is not at the indicated position in the sequent. */
  override def apply(s: Sequent): immutable.List[Sequent] = {
    if (s(pos) == False) { assert(pos.isAnte); Nil }
    else throw InapplicableRuleException("CloseFalse is not applicable to " + s + " at " + pos, this, s)
  } ensures (r => s(pos) == False && pos.isAnte && r.isEmpty, "closed if applicable")
}


/**
  * Cut in the given formula `c` to use `c` on the first branch and proving `c` on the second branch.
  * {{{
  * G, c |- D     G |- D, c
  * ----------------------- (cut)
  *         G |- D
  * }}}
  * The ordering of premises is optimistic, i.e., the premise using the cut-in formula `c` comes before the one proving `c`.
  * @note c will be added at the end on the subgoals
  */
case class Cut(c: Formula) extends Rule {
  val name: String = "cut"
  /** cut in the given formula c */
  def apply(s: Sequent): immutable.List[Sequent] = {
    val use = Sequent(s.ante :+ c, s.succ)
    val show = Sequent(s.ante, s.succ :+ c)
    immutable.List(use, show)
  } ensures(r => r.length==2 && s.subsequentOf(r(0)) && s.subsequentOf(r(1)),
    "subsequent of subgoals of cuts"
    ) ensures (r => r == immutable.List(
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

/**
  * |R Or right.
  * {{{
  *   G |- D, p,q
  * --------------- (|R Or right)
  *   G |- p|q, D
  * }}}
  */
case class OrRight(pos: SuccPos) extends RightRule {
  val name: String = "Or Right"
  /** |R Or right */
  def apply(s: Sequent): immutable.List[Sequent] = {
    val Or(p,q) = s(pos)
    immutable.List(s.updated(pos, Sequent(immutable.IndexedSeq(), immutable.IndexedSeq(p,q))))
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
  * G |- D, p    q, G |- D
  * ---------------------- (-> Imply left)
  *   p->q, G |- D
  * }}}
  */
case class ImplyLeft(pos: AntePos) extends LeftRule {
  val name: String = "Imply Left"
  /** ->L Imply left */
  def apply(s: Sequent): immutable.List[Sequent] = {
    val Imply(p,q) = s(pos)
    immutable.List(s.updated(pos, Sequent(immutable.IndexedSeq(), immutable.IndexedSeq(p))),
      s.updated(pos, q))
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
  * Uniform renaming, thus, is a transposition.
  *
  * {{{
  *    r(G) |- r(D)
  *   --------------- UR
  *       G |- D
  * }}}
  *
  * @param what What variable to replace (along with its associated [[DifferentialSymbol]]).
  * @param repl The target variable to replace `what` with (and vice versa).
  * @author Andre Platzer
  * @see [[URename]]
  * @see [[edu.cmu.cs.ls.keymaerax.core.Provable.apply(ren:edu\.cmu\.cs\.ls\.keymaerax\.core\.URename):edu\.cmu\.cs\.ls\.keymaerax\.core\.Provable*]]
  * @see [[BoundRenaming]]
  * @see [[RenamingClashException]]
  * @note soundness-critical: For uniform renaming purposes the semantic renaming proof rule would be sound but not locally sound. The kernel is easier when keeping everything locally sound.
  */
final case class UniformRenaming(what: Variable, repl: Variable) extends Rule {
  //@note implied: insist(what.sort == repl.sort, "Uniform renaming only to variables of the same sort")
  val name: String = "Uniform Renaming"
  private[this] val renaming: URename = URename(what, repl, semantic=false)

  override def toString: String = renaming.toString

  /**
    * Apply uniform renaming everywhere in the sequent.
    * @throws RenamingClashException if uniform renaming what~>repl is not admissible for s (because a semantic symbol occurs).
    */
  def apply(s: Sequent): immutable.List[Sequent] = List(renaming(s))
}

/**
  * Performs bound renaming renaming all occurrences of variable what
  * (and its associated DifferentialSymbol) to repl.
  * Proper bound renaming requires the replacement to be a fresh variable that does not occur previously.
  *
  * {{{
  *    G |- [repl:=e]r(P), D
  *   ------------------------ BR (where what',repl,repl' do not occur in P)
  *    G |- [what:=e]P,    D
  * }}}
  * where `r(P)` is the result of uniformly renaming `what` to the (fresh) `repl` in `P`.
  * The proof rule works accordingly for diamond modalities, nondeterministic assignments, or quantifiers,
  * or in the antecedent.
  * {{{
  *    G |- <repl:=e>r(P), D
  *   ------------------------ BR (where what',repl,repl' do not occur in P)
  *    G |- <what:=e>P,    D
  * }}}
  * {{{
  *    G |- \forall repl r(P), D
  *   --------------------------- BR (where what',repl,repl' do not occur in P)
  *    G |- \forall what P,    D
  * }}}
  * {{{
  *    G |- \exists repl r(P), D
  *   --------------------------- BR (where what',repl,repl' do not occur in P)
  *    G |- \exists what P,    D
  * }}}
  * {{{
  *    G, [repl:=e]r(P) |- D
  *   ------------------------ BR (where what',repl,repl' do not occur in P)
  *    G, [what:=e]P    |- D
  * }}}
  *
  * @param what What variable (and its associated DifferentialSymbol) to replace.
  * @param repl The target variable to replace what with.
  * @param pos The position at which to perform a bound renaming.
  * @requires repl is fresh in the sequent.
  * @author Andre Platzer
  * @author Stefan Mitsch
  * @note soundness-critical: For bound renaming purposes semantic renaming would be unsound.
  * @see [[UniformRenaming]]
  * @see [[RenamingClashException]]
  */
final case class BoundRenaming(what: Variable, repl: Variable, pos: SeqPos) extends PositionRule {
  //@note implied: insist(what.sort == repl.sort, "Bounding renaming only to variables of the same sort")
  val name: String = "Bound Renaming"

  private[this] val renaming = URename(what, repl, semantic=false)

  override def toString: String = name + "(" + what.asString + "~>" + repl.asString + ") at " + pos

  /**
    * Performs bound renaming what~>repl for a fresh repl on a sequent.
    * @throws RenamingClashException if this bound renaming is not admissible for s at the indicated position
    *                                because repl,repl',what' already occurred, or
    *                                because a semantic symbol occurs, or
    *                                because the formula at `pos` has the wrong shape.
    */
  def apply(s: Sequent): immutable.List[Sequent] = immutable.List(s.updated(pos, apply(s(pos))))

  /**
    * Performs bound renaming what~>repl for a fresh repl on a formula.
    * @throws RenamingClashException if this bound renaming is not admissible for f
    *                                because repl,repl',what' already occurred, or
    *                                because a semantic symbol occurs, or
    *                                because the formula has the wrong shape.
    */
  def apply(f: Formula): Formula = { if (admissible(f))
    f match {
      case Forall(vars, g) if vars.contains(what) => Forall(vars.updated(vars.indexOf(what), repl), renaming(g))
      case Exists(vars, g) if vars.contains(what) => Exists(vars.updated(vars.indexOf(what), repl), renaming(g))
      //@note e is not in scope of x so is, unlike g, not affected by the renaming
      case Box    (Assign(x, e), g) if x==what => Box    (Assign(repl, e), renaming(g))
      case Diamond(Assign(x, e), g) if x==what => Diamond(Assign(repl, e), renaming(g))
      case Box    (AssignAny(x), g) if x==what => Box    (AssignAny(repl), renaming(g))
      case Diamond(AssignAny(x), g) if x==what => Diamond(AssignAny(repl), renaming(g))
      case _ => throw RenamingClashException("Bound renaming only to bound variables " +
        what + " is not bound by a quantifier or single assignment", this.toString, f.prettyString)
    } else
    throw RenamingClashException("Bound renaming only to fresh names but name " +
      repl + " is not fresh", this.toString, f.prettyString)
  } ensures(r => r.getClass == f.getClass, "shape unchanged by bound renaming " + this)

  /**
    * Check whether this renaming is admissible for expression e, i.e.
    * the new name repl and primed version of old name what do not already occur (or the renaming was the identity).
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
  * Skolemization also handles '''existential''' quantifiers on the left:
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
  * @see SkolemClashException
  */
case class Skolemize(pos: SeqPos) extends PositionRule {
  val name: String = "Skolemize"

  /** Skolemize a universal quantifier in the succedent or an existential quantifier in the antecedent.
    * @throws InapplicableRuleException if something other than the appropriate quantifier is at the indicated position.
    * @throws SkolemClashException if the quantified variable that is to be Skolemized already occurs free in the sequent.
    *                              Use [[BoundRenaming]] to resolve.
    */
  override def apply(s: Sequent): immutable.List[Sequent] = {
    // all free symbols anywhere else in the sequent, i.e. except at the quantifier position
    // note: this skolemization will be by identity, not to a new name, so no clashes can be caused from s(pos)
    //@note Taboos are the free symbols which is the same as the free symbols in the remaining sequent, i.e. after replacing pos with innocent True
    //@note Literal mentions of free variables (via freeVars(s).symbols) is unsound, because <a;>true in antecedent might be usubsted to free <?x=1>true subsequently.
    val taboos = StaticSemantics.freeVars(s)
    val (v,phi) = s(pos) match {
      case Forall(qv, qphi) if pos.isSucc => (qv, qphi)
      case Exists(qv, qphi) if pos.isAnte => (qv, qphi)
      case _ => throw InapplicableRuleException("Skolemization only applicable to universal quantifiers in the succedent or to existential quantifiers in the antecedent", this, s)
    }
    if (taboos.intersect(SetLattice(v)).isEmpty) immutable.List(s.updated(pos, phi))
    else throw SkolemClashException("Variables to be skolemized cannot appear anywhere else in the sequent. BoundRenaming required.",
        taboos.intersect(SetLattice(v)), v.toString, s.toString)
  }

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
  } ensures (_.forall(r => r.subsequentOf(s)), "structural rule subsequents")
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
  } ensures (_.forall(r => r.subsequentOf(s)), "structural rule subsequents")
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
  } ensures (_.forall(r => r.subsequentOf(s)), "structural rule subsequents")
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

