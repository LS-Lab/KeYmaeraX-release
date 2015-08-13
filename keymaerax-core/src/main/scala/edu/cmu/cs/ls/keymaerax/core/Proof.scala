/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
/**
 * Sequent prover, proof rules, and axioms of KeYmaera X.
 * @note Soundness-critical: Only provide sound proof rule application mechanisms.
 * @author Andre Platzer
 * @author Jan-David Quesel
 * @author nfulton
 * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic. In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015. arXiv 1503.01981, 2015."
 * @see "Andre Platzer. Differential game logic. ACM Trans. Comput. Log. arXiv 1408.1980"
 * @see "Andre Platzer. The complete proof theory of hybrid systems. ACM/IEEE Symposium on Logic in Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 541-550. IEEE 2012"
 * @see "Andre Platzer. Differential dynamic logic for hybrid systems. Journal of Automated Reasoning, 41(2), pages 143-189, 2008."
 * @note Code Review: 2015-05-01
 */
package edu.cmu.cs.ls.keymaerax.core

// require favoring immutable Seqs for soundness

import scala.collection.immutable

import edu.cmu.cs.ls.keymaerax.parser.ToolEvidence  // external

/*--------------------------------------------------------------------------------*/
/*--------------------------------------------------------------------------------*/

/*********************************************************************************
  * Sequents and positioning
  *********************************************************************************
  */

/**
 * Positions of formulas in a sequent, i.e. antecedent or succedent positions.
 */
sealed trait SeqPos {
  /** Whether this position is in the antecedent on the left of the sequent arrow */
  def isAnte: Boolean
  /** Whether this position is in the succedent on the right of the sequent arrow */
  def isSucc: Boolean = !isAnte

  /**
   * The unsigned index into the antecedent or succedent list, respectively, base 0.
   */
  def getIndex: Int

  /**
   * The signed position for the antecedent or succedent list, respectively, base 1.
   *  Negative numbers indicate antecedent positions, -1, -2, -3, ....
   *  Positive numbers indicate succedent positions, 1, 2, 3.
   *  Zero is a degenerate case indicating whole sequent 0.
   */
  final def getPos: Int = if (isAnte) {-(getIndex+1)} else {assert(isSucc); getIndex+1}

  override def toString: String = "(" + (if (isAnte) "Ante" else "Succ") + ", " + getIndex + ")" //= "(" + getPos + ")"
}

/**
 * Antecedent Positions of formulas in a sequent.
 * @param index the position base 0 in antecedent.
 */
case class AntePos(private[core] val index: Int) extends SeqPos {
  def isAnte: Boolean = true
  /** The position base 0 in antecedent. */
  def getIndex: Int = index
}

/**
 * Antecedent Positions of formulas in a sequent.
 * @param index the position base 0 in succedent.
 */
case class SuccPos(private[core] val index: Int) extends SeqPos {
  def isAnte: Boolean = false
  /** The position base 0 in succedent. */
  def getIndex: Int = index
}

object SeqPos {
  /**
   * @param signedPos the signed integer position of the formula in the antecedent or succedent, respectively.
   *  Negative numbers indicate antecedent positions, -1, -2, -3, ....
   *  Positive numbers indicate succedent positions, 1, 2, 3.
   *  Zero is a degenerate case indicating whole sequent 0.
   * @see SeqPos#pos
   */
  def apply(signedPos: Int): SeqPos =
    if (signedPos>0) {SuccPos(signedPos-1)} else {assert(signedPos<0);AntePos(-signedPos-1)}

}

/**
 * Sequent ante |- succ with antecedent ante and succedent succ.
 * {{{
 *   ante(0),ante(1),...,ante(n) |- succ(0),succ(1),...,succ(m)
 * }}}
 * The semantics of sequent ante |- succ is the conjunction of the formulas in ante implying
 * the disjunction of the formulas in succ.
 * @author Andre Platzer
 * @see "Andre Platzer. Differential dynamic logic for hybrid systems. Journal of Automated Reasoning, 41(2), pages 143-189, 2008."
 */
final case class Sequent(pref: immutable.Seq[NamedSymbol],
                         ante: immutable.IndexedSeq[Formula],
                         succ: immutable.IndexedSeq[Formula]) {
  require(pref.isEmpty, "only empty sequent prefix supported so far " + pref)

  /**
   * Retrieves the formula in sequent at a given position.
   * @param p the position of the formula
   * @return the formula at the given position either from the antecedent or the succedent
   */
  def apply(p: SeqPos): Formula = {
    if (p.isAnte) {
      ante(p.getIndex)
    } else {
      assert (p.isSucc)
      succ(p.getIndex)
    }
  }

  //@todo enable quicker apply(AntePos) and apply(SeqPos) after resolving ambiguous implicit conversion from tactics.Position.
//  /**
//   * Retrieves the formula in sequent at a given succedent position.
//   * @param pos the succedent position of the formula
//   * @return the formula at the given position from the succedent
//   * @note slightly faster version with the same result as #apply(SeqPos)
//   */
//  def apply(pos: AntePos): Formula = {
//    ante(pos.getIndex)
//  } ensuring (r => r == apply(pos.asInstanceOf[SeqPos]), "consistent retrieving")
//
//  /**
//   * Retrieves the formula in sequent at a given antecedent position.
//   * @param pos the antecedent position of the formula
//   * @return the formula at the given position from the antecedent
//   * @note slightly faster version with the same result as #apply(SeqPos)
//   */
//  def apply(pos: SuccPos): Formula = {
//    succ(pos.getIndex)
//  } ensuring (r => r == apply(pos.asInstanceOf[SeqPos]), "consistent retrieving")

  // transformations giving copies of sequents
  
  /**
   * A copy of this sequent concatenated with given sequent s.
   * Sequent(pref, A,S) glue Sequent(pref, B,T) == Sequent(pref, A++B, S++T)
   * @param s the sequent whose antecedent to append to ours and whose succedent to append to ours.
   * @return a copy of this sequent concatenated with s.
   * Results in a least upper bound with respect to subsets of this and s.
   */
  def glue(s: Sequent): Sequent = {
    require(s.pref == pref, "identical sequent prefix required when gluing " + this + " with " + s)
    Sequent(pref, ante ++ s.ante, succ ++ s.succ)
    } ensuring(r => this.subsequentOf(r) && s.subsequentOf(r)
        && r.ante.forall(f=>this.ante.contains(f) || s.ante.contains(f))
        && r.succ.forall(f=>this.succ.contains(f) || s.succ.contains(f)),
        "result is a supersequent of its pieces and all formulas in result come from either one"
    )

  /**
   * A copy of this sequent with the indicated position replaced by the formula f.
   * @param p the position of the replacement
   * @param f the replacing formula
   * @return a copy of this sequent with the formula at position p replaced by f.
   */
  def updated(p: SeqPos, f: Formula): Sequent = {
    if (p.isAnte) {
      Sequent(pref, ante.updated(p.getIndex, f), succ)
    } else {
      assert(p.isSucc)
      Sequent(pref, ante, succ.updated(p.getIndex, f))
    }
  }

  /**
   * A copy of this sequent with the indicated position replaced by gluing the sequent s.
   * @param p the position of the replacement
   * @param s the sequent glued / concatenated to this sequent after dropping p.
   * @return a copy of this sequent with the formula at position p removed and the sequent s appended.
   * @see #updated(Position,Formula)
   * @see #glue(Sequent)
   */
  def updated(p: SeqPos, s: Sequent): Sequent = {
    if (p.isAnte) {
      Sequent(pref, ante.patch(p.getIndex, Nil, 1), succ).glue(s)
    } else {
      assert(p.isSucc)
      Sequent(pref, ante, succ.patch(p.getIndex, Nil, 1)).glue(s)
    }
  } ensuring(r=> if (p.isAnte)
    r.glue(Sequent(pref, immutable.IndexedSeq(this(p)), immutable.IndexedSeq())).sameSequentAs(this.glue(s))
  else
    r.glue(Sequent(pref, immutable.IndexedSeq(), immutable.IndexedSeq(this(p)))).sameSequentAs(this.glue(s)),
    "result after re-including updated formula is equivalent to " + this + " glue " + s
    )

  /**
   * Check whether this sequent is a subsequent of the given sequent r (considered as sets)
   */
  def subsequentOf(r: Sequent): Boolean = (pref == r.pref && ante.toSet.subsetOf(r.ante.toSet) && succ.toSet.subsetOf(r.succ.toSet))

  /**
   * Check whether this sequent is a equivalent to the given sequent r (considered as sets)
   */
  def sameSequentAs(r: Sequent): Boolean = (this.subsequentOf(r) && r.subsequentOf(this))

  override def toString: String = {assert(pref.isEmpty);
    ante.map(_.prettyString).mkString(", ") + "\n  ==>  " + succ.map(_.prettyString).mkString(", ")}

}


/*********************************************************************************
  * Provables as certificates of provability.
  *********************************************************************************
  */

/** Starting new Provables to begin a proof */
object Provable {
  private[core] val DEBUG: Boolean = System.getProperty("DEBUG", "false")=="true"

  /**
   * Begin a new proof for the desired conclusion goal
   * @param goal the desired conclusion.
   * @return a Provable whose subgoals need to be all proved in order to prove goal.
   * @note soundness-critical
   */
  def startProof(goal : Sequent): Provable = {
    Provable(goal, immutable.IndexedSeq(goal))
  } ensuring(
    r => !r.isProved && r.subgoals == immutable.IndexedSeq(r.conclusion), "correct initial proof start")

  /**
   * Create a new provable for facts provided by external tools.
   * @param goal the desired conclusion.
   * @return a Provable without subgoals.
   * @note soundness-critical magic, only call from RCF/LemmaDB within core with true facts.
   */
  private[core] def toolFact(goal: Sequent): Provable = {
    Provable(goal, immutable.IndexedSeq())
  }
}

/**
 * Provable(conclusion, subgoals) is the proof certificate representing certified provability of
 * conclusion from the premises in subgoals.
 * If subgoals is an empty list, conclusion is provable.
 * Otherwise conclusion is provable from the set of assumptions in subgoals.
 * @param conclusion the conclusion that follows if all subgoals are valid.
 * @param subgoals the premises that, if they are all valid, imply the conclusion.
 * @note soundness-critical
 * @note Only private constructor calls for soundness
 * @note For soundness: No reflection to bybass constructor call privacy,
 *       nor reflection to bypass immutable val data structures.
 * @author Andre Platzer
 * @todo may want to split into different locality levels of subgoals
 * @example Proofs can be constructed in sequent order using Provables:
 * {{{
 *   import scala.collection.immutable._
 *   val verum = new Sequent(Seq(), IndexedSeq(), IndexedSeq(True))
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
 *   val more = new Sequent(Seq(), IndexedSeq(),
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
 *  val finGoal = new Sequent(Seq(), IndexedSeq(), IndexedSeq(Imply(fm, And(fm, True))))
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
 * @example Proofs in Hilbert-calculus style order use subsequent merging
 * {{{
 *  import scala.collection.immutable._
 *  val fm = Greater(Variable("x"), Number(5))
 *  // x>0 |- x>0
 *  val left = Provable.startProof(Sequent(Seq(), IndexedSeq(fm), IndexedSeq(fm)))(
 *    Close(AntePos(0), SuccPos(0)), 0)
 *  // |- true
 *  val right = Provable.startProof(Sequent(Seq(), IndexedSeq(), IndexedSeq(True)))(
 *    CloseTrue(SuccPos(0)), 0)
 *  val right2 = Provable.startProof(Sequent(Seq(), IndexedSeq(fm), IndexedSeq(True)))(
 *    HideLeft(AntePos(0)), 0) (right, 0)
 *  // gluing order for subgoals is irrelevant. Could use: (right2, 1)(left, 0))
 *  val merged = Provable.startProof(Sequent(Seq(), IndexedSeq(fm), IndexedSeq(And(fm, True))))(
 *    AndRight(SuccPos(0)), 0) (
 *    left, 0)(
 *      right2, 0)
 *  // |- x>5 -> x>5 & true
 *  val finGoal = new Sequent(Seq(), IndexedSeq(), IndexedSeq(Imply(fm, And(fm, True))))
 *  val proof = Provable.startProof(finGoal)(
 *    ImplyRight(SuccPos(0)), 0) (merged, 0)
 *  // proof of finGoal
 *  println(proof.proved)
 * }}}
 * @example Proofs directly in forward Hilbert order and merging of branches
 * {{{
 *  import scala.collection.immutable._
 *   val fm = Greater(Variable("x"), Number(5))
 *  // proof of x>5 |- x>5 & true merges left and right branch by AndRight
 *  val proof = Provable.startProof(Sequent(Seq(), IndexedSeq(fm), IndexedSeq(And(fm, True))))(
 *    AndRight(SuccPos(0)), 0) (
 *    // left branch: x>5 |- x>5
 *    Provable.startProof(Sequent(Seq(), IndexedSeq(fm), IndexedSeq(fm)))(
 *      Close(AntePos(0), SuccPos(0)), 0),
 *    0) (
 *    //right branch: |- true
 *    Provable.startProof(Sequent(Seq(), IndexedSeq(), IndexedSeq(True)))(
 *      CloseTrue(SuccPos(0)), 0)(
 *        // x>5 |- true
 *        Sequent(Seq(), IndexedSeq(fm), IndexedSeq(True)), HideLeft(AntePos(0))),
 *    0) (
 *    // |- x>5 -> x>5 & true
 *    new Sequent(Seq(), IndexedSeq(), IndexedSeq(Imply(fm, And(fm, True)))),
 *    ImplyRight(SuccPos(0))
 *  )
 *  // proof of finGoal  |- x>5 -> x>5 & true
 *  println(proof.proved)
 * }}}
 */
final case class Provable private (conclusion: Sequent, subgoals: immutable.IndexedSeq[Sequent]) {
  if (Provable.DEBUG && subgoals.distinct.size != subgoals.size) print("INFO: repeated subgoals may warrant set construction or compactification in Provable " + this)

  /**
   * Position types for the subgoals of a Provable.
   */
  type Subgoal = Int

  /**
   * Checks whether this Provable proves its conclusion.
   * @return true if conclusion is proved by this Provable,
   *         false if subgoals are missing that need to be proved first.
   * @note soundness-critical
   */
  final def isProved: Boolean = subgoals.isEmpty

  /**
   * What conclusion this Provable proves if isProved.
   * @requires(isProved)
   */
  final def proved: Sequent = {
    require(isProved, "Only Provables that have been proved have a proven conclusion " + this)
    if (isProved) conclusion else throw new CoreException("ASSERT: Provables with remaining subgoals are not proved yet " + this)
  }

  /**
   * Apply Rule: Apply given proof rule to the indicated subgoal of this Provable, returning the resulting Provable
   * @param rule the proof rule to apply to the indicated subgoal of this Provable derivation.
   * @param subgoal which of our subgoals to apply the given proof rule to.
   * @return A Provable derivation that proves the premise subgoal by using the given proof rule.
   * Will return a Provable with the same conclusion but an updated set of premises.
   * @requires(0 <= subgoal && subgoal < subgoals.length)
   * @note soundness-critical
   */
  final def apply(rule: Rule, subgoal: Subgoal): Provable = {
    require(0 <= subgoal && subgoal < subgoals.length, "Rules " + rule + " can only be applied to an index " + subgoal + " within the subgoals " + subgoals)
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
   * Merge: Replace premise by the given subderivation.
   * Use the given provable derivation in place of the indicated subgoal of this Provable, returning the resulting concatenated Provable.
   * In particular, if subderivation.isProved, then the given subgoal will disappear,
   * otherwise it will be replaced by the subgoals of subderivation
   * (with the first subgoal of subderivation in place of subgoal and all other subgoals at the end).
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
    require(subderivation.conclusion == subgoals(subgoal), "merging Provables requires the subderivation to conclude the indicated subgoal:\nsubderivation " + subderivation + "\nconcludes " + subderivation.conclusion + "\nshould be subgoal " + subgoals(subgoal))
    if (subderivation.conclusion != subgoals(subgoal)) throw new CoreException("ASSERT: Provables not concluding the required subgoal cannot be joined")
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
   * Apply Rule Forward: Apply given proof rule forward in Hilbert style to prolong this Provable to a Provable for concludes.
   * @param concludes the new conclusion that the rule shows to follow from this.conclusion
   * @param rule the proof rule to apply to concludes to reduce it to this.conclusion.
   * @return A Provable derivation that proves concludes from the same subgoals by using the given proof rule.
   * Will return a Provable with the same subgoals but an updated conclusion.
   * @note not soundness-critical since implemented in terms of other apply functions
   */
  final def apply(concludes: Sequent, rule: Rule): Provable = {
    Provable.startProof(concludes)(rule, 0)(this, 0)
  } ensuring(r => r.conclusion == concludes, "New conclusion\n" + concludes + " after continuing derivations") ensuring(
    r => r.subgoals == subgoals, "Same subgoals\n" + subgoals + " after continuing derivations")

  /**
   * Sub-Provable: Get a sub-Provable corresponding to a Provable with the given subgoal as conclusion.
   * Provables resulting from the returned subgoal can be merged into this Provable to prove said subgoal.
   * @note not soundness-critical only completeness-critical
   */
  def sub(subgoal: Subgoal): Provable = {
    require(0 <= subgoal && subgoal < subgoals.length, "Subprovable can only be applied to an index " + subgoal + " within the subgoals " + subgoals)
    Provable.startProof(subgoals(subgoal))
  } ensuring (r => r.conclusion == subgoals(subgoal), "sub yields Provable with expected subgoal " + subgoals(subgoal) + " as the conclusion") ensuring (
    r => r.subgoals == immutable.List(r.conclusion), "sub Provable is an unfinished Provable")

  override def toString: String = "Provable(concludes " + conclusion + (if (isProved) " proved" else "\nfrom " + subgoals.mkString(",\nwith ")) + ")"
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
 * @note soundness-critical This class is sealed, so no rules can be added outside Proof.scala
 */
sealed trait Rule extends (Sequent => immutable.List[Sequent]) {
  //@note If there were inherited contracts in Scala, we could augment apply with contract "ensuring instanceOf[ClosingRule](_) || (!_.isEmpty)" to ensure only closing rules can ever come back with an empty list of premises

  private[core] val LAX_MODE = true

  def name: String

  override def toString: String = name
}

/*********************************************************************************
  * Categories of Proof Rules
  *********************************************************************************
  */

/** A rule that tries closing a subgoal */
trait ClosingRule extends Rule {}

/** A rule applied to a position */
trait PositionRule extends Rule {
  def pos: SeqPos
  override def toString: String = name + " at " + pos
}

/** A rule applied to a position in the antecedent on the left */
trait LeftRule extends PositionRule {
  def pos: AntePos
}

/** A rule applied to a position in the succedent on the right */
trait RightRule extends PositionRule {
  def pos: SuccPos
}

/** An assumption rule, which is a position rule that has an additional position of an assumption. */
trait AssumptionRule extends PositionRule {
  def assume: SeqPos
  override def toString: String = name + " at " + pos + " assumption at " + assume
}

/** A rule applied to two positions. */
trait TwoPositionRule extends Rule {
  def pos1: SeqPos
  def pos2: SeqPos
  override def toString: String = name + " at " + pos1 + " and " + pos2
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
 * Hide left.
 * {{{
 *     G |- D
 * ------------- (Hide left)
 *  p, G |- D
 * }}}
 */
case class HideLeft(pos: AntePos) extends LeftRule {
  val name: String = "HideLeft"
  /** weakening left = hide left */
  def apply(s: Sequent): immutable.List[Sequent] = {
    immutable.List(Sequent(s.pref, s.ante.patch(pos.getIndex, Nil, 1), s.succ))
  } ensuring (_.forall(r => r.subsequentOf(s)), "structural rule subsequents")
}

/**
 * Hide right.
 * {{{
 *    G |- D
 * ------------- (Hide right)
 *   G |- p, D
 * }}}
 */
case class HideRight(pos: SuccPos) extends RightRule {
  val name: String = "HideRight"
  /** weakening right = hide right */
  def apply(s: Sequent): immutable.List[Sequent] = {
    immutable.List(Sequent(s.pref, s.ante, s.succ.patch(pos.getIndex, Nil, 1)))
  } ensuring (_.forall(r => r.subsequentOf(s)), "structural rule subsequents")
}

/** Exchange left rule reorders antecedent */
case class ExchangeLeftRule(pos1: AntePos, pos2: AntePos) extends TwoPositionRule {
  val name: String = "ExchangeLeft"
  def apply(s: Sequent): immutable.List[Sequent] = {
    immutable.List(Sequent(s.pref, s.ante.updated(pos1.getIndex, s.ante(pos2.getIndex)).updated(pos2.getIndex, s.ante(pos1.getIndex)), s.succ))
  } ensuring (_.forall(r => r.subsequentOf(s)), "structural rule subsequents")
}

/** Exchange right rule reorders succedent */
case class ExchangeRightRule(pos1: SuccPos, pos2: SuccPos) extends TwoPositionRule {
  val name: String = "ExchangeRight"
  def apply(s: Sequent): immutable.List[Sequent] = {
    immutable.List(Sequent(s.pref, s.ante, s.succ.updated(pos1.getIndex, s.succ(pos2.getIndex)).updated(pos2.getIndex, s.succ(pos1.getIndex))))
  } ensuring (_.forall(r => r.subsequentOf(s)), "structural rule subsequents")
}

// Contraction right rule duplicates a formula in the succedent
/*
object ContractionRight {
  def apply(p: Position): Rule = new ContractionRightRule(p)

  private class ContractionRightRule(p: Position) extends PositionRule("ContractionRight", p) {
    require(!p.isAnte && p.inExpr == HereP, "Rule is only applicable to a position in the succedent " + this)
    def apply(s: Sequent): immutable.List[Sequent] = {
      immutable.List(Sequent(s.pref, s.ante, s.succ :+ s.succ(p.getIndex)))
    } ensuring (_.forall(r => r.subsequentOf(s)), "structural rule subsequents")
  }
}

// Contraction left rule duplicates a formula in the succedent

object ContractionLeft {
  def apply(p: Position): Rule = new ContractionLeftRule(p)

  private class ContractionLeftRule(p: Position) extends PositionRule("ContractionLeft", p) {
    require(p.isAnte && p.inExpr == HereP, "Rule is only applicable to a position in the antecedent " + this)
    def apply(s: Sequent): immutable.List[Sequent] = {
      immutable.List(Sequent(s.pref, s.ante :+ s.ante(p.getIndex), s.succ))
    } ensuring (_.forall(r => r.subsequentOf(s)), "structural rule subsequents")
  }
}
*/

/*********************************************************************************
 * Sequent Proof Rules for identity/closing and cut
 *********************************************************************************
 */

/**
 * Ax Axiom close / Identity rule
 * {{{
 *        *
 * ------------------ (Close)
 *   p, G |- p, D
 * }}}
 */
case class Close(assume: AntePos, pos: SuccPos) extends AssumptionRule with ClosingRule {
  val name: String = "Axiom"
  /** Close identity */
  def apply(s: Sequent): immutable.List[Sequent] = {
    if (s(assume) == s(pos)) {assert (assume.isAnte && pos.isSucc); Nil }
    else throw new InapplicableRuleException("The referenced formulas are not identical. Cannot close goal.\n  " + s(assume) + " not the same as\n  " + s(pos), this, s)
  } ensuring (_.isEmpty, "closed if applicable")
}

/**
 * close by true
 * {{{
 *       *
 * ------------------ (close true)
 *   G |- true, D
 * }}}
*/
case class CloseTrue(pos: SuccPos) extends RightRule with ClosingRule {
  val name: String = "CloseTrue"
  /** close true */
  override def apply(s: Sequent): immutable.List[Sequent] = {
    if (s(pos) == True) {assert(pos.isSucc); Nil }
    else throw new InapplicableRuleException("CloseTrue is not applicable to " + s + " at " + pos, this, s)
  } ensuring (s(pos) == True && pos.isSucc && _.isEmpty, "closed if applicable")
}

/**
 * close by false.
 * {{{
 *        *
 * ------------------ (close false)
 *   false, G |- D
 * }}}
 */
case class CloseFalse(pos: AntePos) extends LeftRule with ClosingRule {
  val name: String = "CloseFalse"
  /** close false */
  override def apply(s: Sequent): immutable.List[Sequent] = {
    if (s(pos) == False) { assert(pos.isAnte); Nil }
    else throw new InapplicableRuleException("CloseFalse is not applicable to " + s + " at " + pos, this, s)
  } ensuring (s(pos) == False && pos.isAnte && _.isEmpty, "closed if applicable")
}


/**
 * cut in the given formula c.
 * {{{
 * G, c |- D     G |- D, c
 * ----------------------- (cut)
 *   G |- D
 * }}}
 */
case class Cut(c: Formula) extends Rule {
  val name: String = "cut"
  /** cut in the given formula c */
  def apply(s: Sequent): immutable.List[Sequent] = {
    val use = new Sequent(s.pref, s.ante :+ c, s.succ)
    val show = new Sequent(s.pref, s.ante, s.succ :+ c)
    immutable.List(use, show)
  } ensuring(r => r.length==2 && s.subsequentOf(r(0)) && s.subsequentOf(r(1)),
    "subsequent of subgoals of cuts"
    ) ensuring (r => r == immutable.List(
    s.glue(Sequent(s.pref, immutable.IndexedSeq(c), immutable.IndexedSeq())),
    s.glue(Sequent(s.pref, immutable.IndexedSeq(), immutable.IndexedSeq(c)))),
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
    immutable.List(s.updated(pos, Sequent(s.pref, immutable.IndexedSeq(p), immutable.IndexedSeq())))
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
    immutable.List(s.updated(pos, Sequent(s.pref, immutable.IndexedSeq(), immutable.IndexedSeq(p))))
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
    immutable.List(s.updated(pos, Sequent(s.pref, immutable.IndexedSeq(), immutable.IndexedSeq(p,q))))
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
    immutable.List(s.updated(pos, Sequent(s.pref, immutable.IndexedSeq(p,q), immutable.IndexedSeq())))
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
    immutable.List(s.updated(pos, Sequent(s.pref, immutable.IndexedSeq(p), immutable.IndexedSeq(q))))
  }
}


/**
 * ->L Imply left.
 * {{{
 * G |- D, p    G, q |- D
 * ---------------------- (-> Imply left)
 *   p->q, G |- D
 * }}}
 * @note Perhaps surprising that both positions change but at least consistent for this rule.
 */
case class ImplyLeft(pos: AntePos) extends LeftRule {
  val name: String = "Imply Left"
  /** ->L Imply left */
  def apply(s: Sequent): immutable.List[Sequent] = {
    val Imply(p,q) = s(pos)
    immutable.List(s.updated(pos, Sequent(s.pref, immutable.IndexedSeq(), immutable.IndexedSeq(p))),
                   s.updated(pos, Sequent(s.pref, immutable.IndexedSeq(q), immutable.IndexedSeq())))
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
    //immutable.List(s.updated(p, And(Imply(a,b), Imply(b,a))))  // and then AndRight ~ ImplyRight
    immutable.List(s.updated(pos, Sequent(s.pref, immutable.IndexedSeq(p), immutable.IndexedSeq(q))),
                   s.updated(pos, Sequent(s.pref, immutable.IndexedSeq(q), immutable.IndexedSeq(p))))
  }
}

/**
 * <->L Equiv left.
 * {{{
 * p&q, G |- D    !p&!q, G |- D
 * ----------------------------- (<-> Equiv left)
 *   p<->q, G |- D
 * }}}
 */
case class EquivLeft(pos: AntePos) extends LeftRule {
  val name: String = "Equiv Left"
  /** <->L Equiv left */
  def apply(s: Sequent): immutable.List[Sequent] = {
    val Equiv(a,b) = s(pos)
    //immutable.List(s.updated(p, Or(And(a,b), And(Not(a),Not(b)))))  // and then OrLeft ~ AndLeft
    // immutable.List(s.updated(p, Sequent(s.pref, IndexedSeq(a,b),IndexedSeq())),
    //      s.updated(p, Sequent(s.pref, IndexedSeq(Not(a),Not(b)),IndexedSeq())))
    //@note This choice is compatible with tactics and has stable positions but is perhaps unreasonably surprising. Could prefer upper choices
    immutable.List(s.updated(pos, And(a,b)),
                   s.updated(pos, And(Not(a),Not(b))))
  }
}


/*********************************************************************************
 * Uniform Substitution Proof Rule
 *********************************************************************************
 */

/**
 * Uniform Substitution Rule.
 * Applies a given uniform substitution to the given original premise (origin).
 * Pseudo application in sequent calculus to conclusion that fits to the Hilbert calculus application (origin->conclusion).
 * This rule interfaces forward Hilbert calculus rule application with backward sequent calculus pseudo-application
 * US uniform substitution.
 * {{{
 *        G |- D
 * -------------------- (US)
 * subst(G) |- subst(D)
 * }}}
 * @param subst the uniform substitution to be applied to origin.
 * @param origin the original premise, to which the uniform substitution will be applied. Thus, origin is the result of pseudo-applying this UniformSubstitution rule in sequent calculus.
 * @note this rule performs a backward substitution step. That is the substitution applied to the conclusion yields the premise
 * @author Andre Platzer
 * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981, 2015."
 */
case class UniformSubstitutionRule(subst: USubst, origin: Sequent) extends Rule {
  val name: String = "Uniform Substitution"

  private def log(msg: =>Any): Unit = {} //println(msg)

  override def toString: String = subst.toString   // name + "(" + subst + ")"

  /**
   * check that conclusion is indeed derived from origin via subst (note that no reordering is allowed since those operations
   * require explicit rule applications)
   * @param conclusion the conclusion in sequent calculus to which the uniform substitution rule will be pseudo-applied, resulting in the premise origin that was supplied to UniformSubstituion.
   */
  def apply(conclusion: Sequent): immutable.List[Sequent] =
    try {
      log("---- " + subst + "\n    " + origin + "\n--> " + subst(origin) + (if (subst(origin) == conclusion) "\n==  " else "\n!=  ") + conclusion)
      if (subst(origin) == conclusion) immutable.List(origin)
      else throw new CoreException(this + "\non premise   " + origin + "\nresulted in  " + subst(origin) + "\nbut expected " + conclusion)
      /*("From\n  " + origin + "\nuniform substitution\n  " + subst +
        "\ndid not conclude the intended\n  " + conclusion + "\nbut instead\n  " + subst(origin))*/
    } catch {
      case exc: SubstitutionClashException => throw exc.inContext(this + "\non premise   " + origin + "\nresulted in  " + "clash " + exc.clashes + "\nbut expected " + conclusion)
    }
}


object AxiomaticRule {
  // immutable list of locally sound axiomatic proof rules (premise, conclusion)
  val rules: immutable.Map[String, (Sequent, Sequent)] = AxiomBase.loadAxiomaticRules()
}

/**
 * Apply a uniform substitution instance of an axiomatic proof rule,
 * i.e. locally sound proof rules that are represented by a pair of concrete formulas, one for the premise and one for the conclusion.
 * Axiomatic proof rules are employed after forming their uniform substitution instances.
 * All available axiomatic rules are listed in [[edu.cmu.cs.ls.keymaerax.core.AxiomaticRule.rules]]
 * @author Andre Platzer
 * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981, 2015."
 */
final case class AxiomaticRule(id: String, subst: USubst) extends Rule {
  val name: String = "Axiomatic Rule " + id + " instance"
  //@todo disable LAX_MODE after tactics have been adapted to Anything. Sound for current axiomatic rules, but generally problematic.
  require(subst.freeVars.isEmpty || LAX_MODE, "Uniform substitution instances of axiomatic rule " + id + " cannot currently introduce free variables " + subst.freeVars + " in\n" + this)

  override def toString: String = name + "(" + subst + ")"

  private val (rulepremise: Sequent, ruleconclusion: Sequent) = AxiomaticRule.rules.get(id) match {
    case Some(pair) => pair
    case _ => throw new InapplicableRuleException("Axiomatic Rule " + id + " does not exist in:\n" + AxiomaticRule.rules.mkString("\n"), this)
  }

  /**
   * check that conclusion is indeed the indicated substitution instance from the axiomatic rule's conclusion.
   * Leads to same substitution instance of axiomatic rule's premise.
   * @param conclusion the conclusion in sequent calculus to which the uniform substitution rule will be pseudo-applied, resulting in the premise origin that was supplied to UniformSubstituion.
   */
  def apply(conclusion: Sequent): immutable.List[Sequent] =
    try {
      if (subst(ruleconclusion) == conclusion) immutable.List(subst(rulepremise))
      else throw new CoreException("Desired conclusion\n  " + conclusion + "\nis not a uniform substitution instance of\n" + ruleconclusion +
        "\nwith uniform substitution\n  " + subst + "\nwhich would be the instance\n  " + subst(ruleconclusion) + "\ninstead of\n  " + conclusion)
    } catch {
      case exc: SubstitutionClashException => throw exc.inContext(this + " for intended conclusion\n" + conclusion)
    }

}


/**
 * Uniformly rename all occurrences of variable what (and its associated DifferentialSymbol) to repl.
 * @param what What variable to replace (along with its associated DifferentialSymbol).
 * @param repl The target variable to replace what with.
 * @requires repl is fresh in the sequent.
 * @author Andre Platzer
 */
case class UniformRenaming(what: Variable, repl: Variable) extends Rule {
  require(what.sort == repl.sort, "Uniform renaming only to variables of the same sort")
  val name: String = "Uniform Renaming"
  private val renaming: URename = URename(what, repl)

  override def toString: String = name + "(" + what + "~>" + repl + ")"

  def apply(s: Sequent): immutable.List[Sequent] = List(renaming(s))
}

/**
 * Performs bound renaming renaming all occurrences of variable what
 * (and its associated DifferentialSymbol) to repl.
 * @param what What variable (and its associated DifferentialSymbol) to replace.
 * @param repl The target variable to replace what with.
 * @requires repl is fresh in the sequent.
 * @author smitsch
 * @author Andre Platzer
 */
case class BoundRenaming(what: Variable, repl: Variable) extends Rule {
  require(what.sort == repl.sort, "Bounding renaming only to variables of the same sort")
  val name: String = "Bound Renaming"

  private val renaming = URename(what, repl)

  /** @todo Code Review: change to false: This is a slight euphemism for do you mind being possibly unsound */
  //@note turn to false after telling alphaRenamingT and globalAlphaRenamingT to add the stutter by axiom if needed
  private val compatibilityMode = LAX_MODE

  override def toString: String = name + "(" + what + "~>" + repl + ")"

  def apply(s: Sequent): immutable.List[Sequent] =
    immutable.List(Sequent(s.pref, s.ante.map(ghostify), s.succ.map(ghostify)))

  def apply(f: Formula): Formula = {
    if (StaticSemantics(f).bv.intersect(SetLattice(Set[NamedSymbol](what, DifferentialSymbol(what)))).isEmpty) {
      // old name is not bound anywhere in f, so no bound renaming needed/possible
      f
    } else {
      // old name is bound somewhere in f -> check that new name is admissible (does not occur)
      if (admissible(f)) {if (what==repl) f else renaming(f)}
      else throw new BoundRenamingClashException("Bound renaming only to fresh names but name " +
        repl + " is not fresh", this.toString, f.prettyString)
    }
  }

  /**
   * Introduce a ghost for the target variable as needed to remember the value of the previous variable.
   * If what is bound at f, rename, otherwise introduce stuttering [what:=what] before renaming,
   * leading to [repl:=what] after renaming.
   * Ensures that the bound variable is literally bound on the top level, when in doubt by introducing a stutter.
   */
  private def ghostify(f: Formula): Formula =
    if (!StaticSemantics(f).bv.intersect(SetLattice(Set[NamedSymbol](what, DifferentialSymbol(what)))).isEmpty) {
      // old name is bound somewhere in f -> lazy check by ensuring that new name is admissible (does not occur)
      f match {
        case Forall(vars, _) if vars.contains(what) => apply(f)
        case Exists(vars, _) if vars.contains(what) => apply(f)
        case Box(Assign(x, y), _) if x == y && x == repl => apply(f)
        case Diamond(Assign(x, y), _) if x == y && x == repl => apply(f)
        case _ => if (compatibilityMode) {
          //println("LAX: BoundRenaming: Change alphaRenamingT and disable compatibilityMode" + (if (what==repl) " stutter " else "non-stutter") + "\nfor " + this + " in " + f.prettyString + " led to " + Box(Assign(repl, what), apply(f)).prettyString)
          if (Provable.DEBUG && repl != what) {println("LAX: BoundRenaming: Change alphaRenamingT and disable compatibilityMode" + (if (what==repl) " stutter " else "non-stutter") + "\nfor " + this + " in " + f.prettyString + " led to " + Box(Assign(repl, what), apply(f)).prettyString)}
          Box(Assign(repl, what), apply(f))
        } else throw new BoundRenamingClashException("Bound renaming only to bound variables " +
          what + " is not bound", this.toString, f.prettyString)
    } } ensuring(admissible(f)) else {
      // old name is not bound anywhere in f, so no bound renaming needed/possible
      f
    }

  /**
   * Introduce a ghost for the target variable to remember the value of the previous variable.
   */
  //private def ghostifyDiamond(f: Formula) = DiamondModality(Assign(Variable(repl, rIdx, Real), Variable(what, wIdx, Real)), apply(f))

  /**
   * Check whether this renaming is admissible for expression e, i.e.
   * the new name repl does not already occur (or the renaming was the identity).
   * @note identity renaming is merely allowed to enable BoundVariableRenaming to introduce stutter.
   * @note This implementation currently errors if repl.sort!=Real
   */
  private def admissible(e: Expression): Boolean =
    what == repl ||
      StaticSemantics.symbols(e).intersect(Set(repl, DifferentialSymbol(repl))).isEmpty
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
 * ---------------------------- (Skolemize) provided x not in G,D
 * G |- \forall x . p(x), D
 * }}}
 * {{{
 * G, p(x) |- D
 * ---------------------------- (Skolemize) provided x not in G,D
 * G, \exists x . p(x) |- D
 * }}}
 * @note Could replace by uniform substitution rule application mechanism for rule "all generalization"
 * along with tactics expanding scope of quantifier with axiom "all quantifier scope" at the cost of propositional repacking and unpacking.
 *      p(x)
 *  ---------------all generalize
 *  \forall x. p(x)
 * Kept because of the incurred cost.
 */
case class Skolemize(pos: SeqPos) extends PositionRule {
  val name: String = "Skolemize"
  override def apply(s: Sequent): immutable.List[Sequent] = {
    // all symbols anywhere else in the sequent, i.e. except at the quantifier position
    // note: this skolemization will be by identity, not to a new name, so no clashes can be caused from s(pos)
    val taboos = StaticSemantics.symbols(s.updated(pos, True))
    val (v,phi) = s(pos) match {
      case Forall(qv, qphi) if pos.isSucc => (qv, qphi)
      case Exists(qv, qphi) if pos.isAnte => (qv, qphi)
      case _ => throw new InapplicableRuleException("Skolemization only applicable to universal quantifiers in the succedent or to existential quantifiers in the antecedent", this, s)
    }
    if (taboos.intersect(v.toSet).isEmpty) immutable.List(s.updated(pos, phi))
    else throw new SkolemClashException("Variables to be skolemized should not appear anywhere else in the sequent. BoundRenaming required.",
        taboos.intersect(v.toSet), v.toString, s.toString)
  }

}

/*********************************************************************************
 * Lookup Axioms
 *********************************************************************************
 */

/** Finite list of axioms. */
object Axiom {
  // immutable list of sound axioms
  val axioms: immutable.Map[String, Formula] = AxiomBase.loadAxioms
}
/**
 * Look up an axiom named id.
 * Sound axioms are valid formulas of differential dynamic logic.
 * All available axioms are listed in [[edu.cmu.cs.ls.keymaerax.core.Axiom.axioms]].
 * @author nfulton
 * @author Andre Platzer
 * @author smitsch
 * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981, 2015."
 * @see "Andre Platzer. The complete proof theory of hybrid systems. ACM/IEEE Symposium on Logic in Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 541-550. IEEE 2012"
 */
case class Axiom(id: String) extends Rule with ClosingRule {
  val name: String = "Axiom " + id
  def apply(s: Sequent): immutable.List[Sequent] = {
    Axiom.axioms.get(id) match {
      case Some(f) => immutable.List(new Sequent(s.pref, s.ante, s.succ.filter(_ != f)))
        if (s.ante.isEmpty && s.succ.size == 1 && s.succ.contains(f)) Nil
        else throw new InapplicableRuleException("Axiom " + f + " is not sole formula in:\n", this, s)
      case _ => throw new InapplicableRuleException("Axiom " + id + " does not exist in:\n" + Axiom.axioms.mkString("\n"), this, s)
    }
  } ensuring (r => r.isEmpty, "axiom lookup should close")
}

/*********************************************************************************
 * Real Arithmetic
 *********************************************************************************
 */

/** Real arithmetic */
object RCF {
  /** List of the class names of all external tools whose answers KeYmaera X would believe */
  private val trustedTools: immutable.List[String] =
    "edu.cmu.cs.ls.keymaerax.tools.Mathematica" ::
    "edu.cmu.cs.ls.keymaerax.tools.Z3" :: Nil

  /**
   * Proves a formula f in real arithmetic using an external tool for quantifier elimination.
   * @param t The tool.
   * @param f The formula.
   * @return a Lemma with a quantifier-free formula equivalent to f and evidence as provided by the tool.
   * @todo Change structure around such that quantifier elimination tools already come back with whatever evidence they can provide.
   */
  def proveArithmetic(t: QETool, f: Formula): Lemma = {
    require(trustedTools.contains(t.getClass.getCanonicalName), "Trusted tool required: " + t.getClass.getCanonicalName)

    // Quantifier elimination determines (quantifier-free) equivalent of f.
    val (equivalent, input, output) = t.qeInOut(f)

    // soundness-critical
    val fact = Provable.toolFact(new Sequent(
      Nil,
      immutable.IndexedSeq(),
      immutable.IndexedSeq(Equiv(f, equivalent))))

    Lemma(fact, new ToolEvidence(immutable.Map("input" -> input, "output" -> output)) :: Nil)
  }
}

/*********************************************************************************
 * Lemma Mechanism Rules
 *********************************************************************************
 */

/** Lemma mechanism */
object LookupLemma {
  /**
   * Add given new lemma to the given lemma database.
   * @param lemmaDB Lemma database to insert into.
   * @param lemma The lemma whose Provable will be inserted under its name.
   * @return Internal lemma identifier.
   * @requires if (lemma.name==Some(n)) then !lemmaDB.contains(n)
   */
  def addLemma(lemmaDB: LemmaDB, lemma: Lemma): String = lemmaDB.add(lemma)

}
/**
 * Lookup a lemma that has been proved previously or by an external arithmetic tool.
 * @author nfulton
 * @author Stefan Mitsch
 * @see [[edu.cmu.cs.ls.keymaerax.core.LemmaDB.get()]]
 */
case class LookupLemma(lemmaDB: LemmaDB, lemmaID: String) extends Rule {
  val name: String = "Lookup Lemma"
  /** Get the lemma that this lookup lemma rule will apply */
  def lemma: Lemma = {
    require(lemmaDB.contains(lemmaID), "Cannot lookup lemmas that have not been added to the LemmaDB")
    lemmaDB.get(lemmaID).get
  }
  def apply(s : Sequent): immutable.List[Sequent] = {
    val lem = lemma
    if (s.sameSequentAs(lem.fact.conclusion)) lem.fact.subgoals.toList
    else throw new IllegalArgumentException("Lemma " + lemmaID + " with conclusion " + lem.fact.conclusion + " not " +
      "applicable for sequent " + s)
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
 * @NOTE When using hybrid games axiomatization
 */
case class DualFree(pos: SuccPos) extends RightRule with ClosingRule {
  val name: String = "dual-free"
  /** Prove [a]true by showing that a is dual-free */
  override def apply(s: Sequent): immutable.List[Sequent] = {
    s(pos) match {
      case Box(a, True) if dualFree(a) => Nil
      case _ => throw new InapplicableRuleException("DualFree is not applicable to " + s + " at " + pos, this, s)
    }
  } ensuring (s(pos).isInstanceOf[Box] && s(pos).asInstanceOf[Box].child==True && dualFree(s(pos).asInstanceOf[Box].program) && pos.isSucc && _.isEmpty, "closed if applicable")

  /** Check whether given program is dual-free, so a hybrid system and not a hybrid game */
  private def dualFree(program: Program): Boolean = program match {
    case a: ProgramConst             => false /* @note false Unless USubst rejects Duals as substitutues for ProgramConst */
    case Assign(x, e)                => true
    case DiffAssign(DifferentialSymbol(x), e) => true
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
 * CoHide left.
 * {{{
 *      p |-
 * ------------- (CoHide left)
 *   p, G |- D
 * }}}
 * @derived
 */
case class CoHideLeft(pos: AntePos) extends LeftRule {
  val name: String = "CoHideLeft"
  /** co-weakening left = co-hide left (all but indicated position) */
  def apply(s: Sequent): immutable.List[Sequent] = {
    immutable.List(Sequent(s.pref, immutable.IndexedSeq(s.ante(pos.getIndex)), immutable.IndexedSeq()))
  } ensuring (_.forall(r => r.subsequentOf(s)), "structural rule subsequents")
}

/**
 * CoHide right.
 * {{{
 *     |- p
 * ------------- (CoHide right)
 *   G |- p, D
 * }}}
 * @derived
 */
case class CoHideRight(pos: SuccPos) extends RightRule {
  val name: String = "CoHideRight"
  /** co-weakening right = co-hide right (all but indicated position) */
  def apply(s: Sequent): immutable.List[Sequent] = {
    immutable.List(Sequent(s.pref, immutable.IndexedSeq(), immutable.IndexedSeq(s.succ(pos.getIndex))))
  } ensuring (_.forall(r => r.subsequentOf(s)), "structural rule subsequents")
}

/**
 * CoHide2 hides all but the two indicated positions.
 * {{{
 *      p |- q
 * --------------- (CoHide2)
 *   p, G |- q, D
 * }}}
 * @derived
 */
case class CoHide2(pos1: AntePos, pos2: SuccPos) extends TwoPositionRule {
  val name: String = "CoHide2"
  /** co-weakening = co-hide all but the indicated positions */
  def apply(s: Sequent): immutable.List[Sequent] = {
    immutable.List(Sequent(s.pref, immutable.IndexedSeq(s.ante(pos1.getIndex)), immutable.IndexedSeq(s.succ(pos2.getIndex))))
  } ensuring (_.forall(r => r.subsequentOf(s)), "structural rule subsequents")
}


/**
 * Cut in the given formula c in place of p.
 * {{{
 * G |- c, D    G |- c->p, D
 * ------------------------- (Cut right)
 *        G |- p, D
 * }}}
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
 * Cut in the given formula c in place of p
 * {{{
 * c, G |- D    G |- p->c, D
 * -------------------------
 *        p, G |- D
 * }}}
 * @note this would perhaps surprising that inconsistent posititioning within this rule, unlike in ImplyLeft?
 * @derived(cut(p->c) & <(ImplyLeft & <(HideLeft, CloseId), HideLeft))
 */
case class CutLeft(c: Formula, pos: AntePos) extends Rule {
  val name: String = "cut Left"
  def apply(s: Sequent): immutable.List[Sequent] = {
    val p = s(pos)
    immutable.List(s.updated(pos, c),
                   s.updated(pos, Sequent(s.pref, immutable.IndexedSeq(), immutable.IndexedSeq(Imply(p, c)))))
    /* immutable.List(s.updated(pos, Sequent(s.pref, immutable.IndexedSeq(c), immutable.IndexedSeq())),
                   s.updated(pos, Sequent(s.pref, immutable.IndexedSeq(), immutable.IndexedSeq(Imply(p, c))))) */
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
  val name: String = "->2<-> Equivify Right"
  def apply(s: Sequent): immutable.List[Sequent] = {
    val Imply(a,b) = s(pos)
    immutable.List(s.updated(pos, Equiv(a, b)))
  }
}

/**
 * Commute equivalence left
 * {{{
 * G, b<->a |-  D
 * -------------
 * G, a<->b |-  D
 * }}}
 * @derived
 */
case class CommuteEquivLeft(pos: AntePos) extends LeftRule {
  val name: String = "c<-> commute equivalence Left"
  def apply(s: Sequent): immutable.List[Sequent] = {
    val Equiv(a,b) = s(pos)
    immutable.List(s.updated(pos, Equiv(b, a)))
  }
}

/**
 * Commute equivalence right
 * {{{
 * G |- b<->a, D
 * -------------
 * G |- a<->b,  D
 * }}}
 * @derived
 */
case class CommuteEquivRight(pos: SuccPos) extends RightRule {
  val name: String = "c<-> commute equivalence Right"
  def apply(s: Sequent): immutable.List[Sequent] = {
    val Equiv(a,b) = s(pos)
    immutable.List(s.updated(pos, Equiv(b, a)))
  }
}
