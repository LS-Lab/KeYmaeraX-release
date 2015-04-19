/**
 * Sequent prover, proof rules, and axioms of KeYmaera X.
 * @note Soundness-critical: Only provide sound proof rule application mechanisms.
 * @author Jan-David Quesel
 * @author aplatzer
 * @author nfulton
 * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981, 2015."
 * @see "Andre Platzer. The complete proof theory of hybrid systems. ACM/IEEE Symposium on Logic in Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 541-550. IEEE 2012"
 */
package edu.cmu.cs.ls.keymaera.core

// require favoring immutable Seqs for soundness

import scala.collection.immutable.Seq
import scala.collection.immutable.IndexedSeq

import scala.collection.immutable.List
import scala.collection.immutable.Map
import scala.collection.immutable.Set

import scala.annotation.{unspecialized, elidable}
import scala.annotation.elidable._
import edu.cmu.cs.ls.keymaera.core.Number.NumberObj

import edu.cmu.cs.ls.keymaera.parser.KeYmaeraPrettyPrinter  // external
import edu.cmu.cs.ls.keymaera.parser.KeYmaeraParser  // external
import edu.cmu.cs.ls.keymaera.parser.LoadedKnowledgeTools  // external
import edu.cmu.cs.ls.keymaera.parser.ToolEvidence  // external

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
  def isAnte: Boolean
  def isSucc: Boolean

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
  def getPos: Int = if (isAnte) {-(getIndex+1)} else {assert(isSucc); getIndex+1}

  /**
   * Check whether index of this position is defined in given sequent.
   */
  final def isIndexDefined(s: Sequent): Boolean =
    if (isAnte)
      getIndex < s.ante.length
    else {
      assert(isSucc)
      getIndex < s.succ.length
    }

  override def toString: String = "(" + (if (isAnte) "Ante" else "Succ") + ", " + getIndex + ")" //= "(" + getPos + ")"
}

/**
 * Antecedent Positions of formulas in a sequent.
 * @param index the position base 0 in antecedent.
 */
case class AntePos(private[core] val index: Int) extends SeqPos {
  def isAnte = true
  def isSucc = false
  def getIndex = index
}

/**
 * Antecedent Positions of formulas in a sequent.
 * @param index the position base 0 in antecedent.
 */
case class SuccPos(private[core] val index: Int) extends SeqPos {
  def isAnte = false
  def isSucc = true
  def getIndex = index
}

object SeqPos {
  /**
   * @param signedPos the signed integer position of the formula in the antecedent or succedent, respectively.
   *  Negative numbers indicate antecedent positions, -1, -2, -3, ....
   *  Positive numbers indicate succedent positions, 1, 2, 3.
   *  Zero is a degenerate case indicating whole sequent 0.
   */
  def SeqPos(signedPos: Int) = if (signedPos>0) {SuccPos(signedPos-1)} else {assert(signedPos<0);AntePos(-signedPos+1)}

}

/**
 * Sequents
 * @author aplatzer
 */
final case class Sequent(val pref: scala.collection.immutable.Seq[NamedSymbol],
                         val ante: scala.collection.immutable.IndexedSeq[Formula],
                         val succ: scala.collection.immutable.IndexedSeq[Formula]) {
  applicable
  @elidable(ASSERTION) def applicable = require(pref.isEmpty, "only empty sequent prefix supported so far " + pref)

  // Could use scala.collection.immutable.Seq instead of IndexedSeq, since equivalent except for performance. But many KeYmaera parts construct Sequents, so safer for performance.
  override def equals(e: Any): Boolean = e match {
    case Sequent(p, a, s) => pref == p && ante == a && succ == s
    case _ => false
  }

  //override def hashCode: Int = HashFn.hash(251, pref, ante, succ)

  // reading information

  /**
   * Retrieves the formula in sequent at a given position.
   * @param p the position of the formula
   * @return the formula at the given position either from the antecedent or the succedent
   */
  def apply(p: SeqPos): Formula = {
    if (p.isAnte) {
      require(p.getIndex < ante.length, "Position " + p + " is invalid in sequent " + this) // @elidable
      ante(p.getIndex)
    } else {
      assert (p.isSucc)
      require(p.getIndex < succ.length, "Position " + p + " is invalid in sequent " + this) // @elidable
      succ(p.getIndex)
    }
  }

  //@todo enable quicker apply(AntePos) and apply(SeqPos) after resolving ambiguous implicit conversion from Position.
//  /**
//   * Retrieves the formula in sequent at a given succedent position.
//   * @param pos the succedent position of the formula
//   * @return the formula at the given position from the succedent
//   * @note slightly faster version with the same result as #apply(SeqPos)
//   */
//  def apply(pos: AntePos): Formula = {
//    //assert (pos.isAnte)  // @elidable
//    //require(pos.getIndex < ante.length, "Position " + pos + " is invalid in sequent " + this) // @elidable
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
//    //assert (pos.isSucc)  // @elidable
//    //require(pos.getIndex < succ.length, "Position " + pos + " is invalid in sequent " + this) // @elidable
//    succ(pos.getIndex)
//  } ensuring (r => r == apply(pos.asInstanceOf[SeqPos]), "consistent retrieving")

  // transformations giving copies of sequents
  
  /**
   * A copy of this sequent concatenated with given sequent s.
   * Sequent(pref, A,S) glue Sequent(pref, B,T) == Sequent(pref, A++B, S++T)
   * @param s the sequent whose antecedent to append to ours and whose succedent to append to ours.
   * @returns a copy of this sequent concatenated with s.
   * Results in a least upper bound with respect to subsets of this and s.
   */
  def glue(s: Sequent) : Sequent = {
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
   * @returns a copy of this sequent with the formula at position p replaced by f.
   */
  def updated(p: SeqPos, f: Formula) : Sequent = {
    if (p.isAnte) {
      require(p.getIndex < ante.length, "Position " + p + " is invalid in sequent " + this) //@TODO might be @elidable
      Sequent(pref, ante.updated(p.getIndex, f), succ)
    } else {
      assert(p.isSucc)
      require(p.getIndex < succ.length, "Position " + p + " is invalid in sequent " + this) //@TODO might be @elidable
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
  def updated(p: SeqPos, s: Sequent) : Sequent = {
    if (p.isAnte) {
      require(p.getIndex < ante.length, "Position " + p + " is invalid in sequent " + this) //@TODO might be @elidable
      Sequent(pref, ante.patch(p.getIndex, Nil, 1), succ).glue(s)
    } else {
      assert(p.isSucc)
      require(p.getIndex < succ.length, "Position " + p + " is invalid in sequent " + this) //@TODO might be @elidable
      Sequent(pref, ante, succ.patch(p.getIndex, Nil, 1)).glue(s)
    }
  } ensuring(r=> if (p.isAnte)
    r.glue(Sequent(pref,IndexedSeq(this(p)),IndexedSeq())).sameSequentAs(this.glue(s))
  else
    r.glue(Sequent(pref,IndexedSeq(),IndexedSeq(this(p)))).sameSequentAs(this.glue(s)),
    "result after re-including updated formula is equivalent to " + this + " glue " + s
    )

  /**
   * Check whether this sequent is a subsequent of the given sequent r (considered as sets)
   */
  def subsequentOf(r: Sequent) : Boolean = (pref == r.pref && ante.toSet.subsetOf(r.ante.toSet) && succ.toSet.subsetOf(r.succ.toSet))

  /**
   * Check whether this sequent is a equivalent to the given sequent r (considered as sets)
   */
  def sameSequentAs(r: Sequent) : Boolean = (this.subsequentOf(r) && r.subsequentOf(this))

  override def toString: String = "Sequent[{(" + pref.map(_.prettyString).mkString(", ") + "), " +
    ante.map(_.prettyString()).mkString(", ") + " ==> " + succ.map(_.prettyString()).mkString(", ") + "}]"

}


/*********************************************************************************
  * Provables as certificates of provability.
  *********************************************************************************
  */

object Provable {
  private[core] val debugProver = false

  /**
   * Begin a new proof for the desired conclusion goal
   * @param goal the desired conclusion.
   * @result a Provable whose subgoals need to be all proved in order to prove goal.
   * @note soundness-critical
   */
  def startProof(goal : Sequent) = {
    Provable(goal, scala.collection.immutable.IndexedSeq(goal))
  } ensuring(
    r => !r.isProved && r.subgoals == IndexedSeq(r.conclusion), "correct initial proof start")
}

/**
 * Provable(conclusion, subgoals) represents certified provability of
 * conclusion from all the premises in subgoals.
 * If subgoals is an empty list, conclusion is provable.
 * Otherwise conclusion is provable from the assumptions subgoals.
 * @param conclusion the conclusion that follows if all subgoals are valid.
 * @param subgoals the premises that, if they are all valid, imply the conclusion.
 * @note soundness-critical
 * @note Only private constructor calls for soundness
 * @author aplatzer
 * @TODO Subgoals as an immutable list or an immutable IndexedSeq?
 */
final case class Provable private (val conclusion: Sequent,
                                   val subgoals: scala.collection.immutable.IndexedSeq[Sequent]) {
  //override def hashCode: Int = HashFn.hash(271, conclusion, subgoals)
  if (Provable.debugProver && subgoals.distinct.size != subgoals.size) print("WARNING: repeated subgoals may warrant set construction in Provable " + this)

  /**
   * Position types for the subgoals of a Provable.
   * @todo Not sure how to make this type visible outside as well
   */
  type Subgoal = Int

  /**
   * Checks whether this Provable proves its conclusion.
   * @return true if conclusion is proved by this Provable,
   *         false if subgoals are missing that need to be proved first.
   * @note soundness-critical
   */
  final def isProved : Boolean = (subgoals.isEmpty)

  /**
   * What conclusion this Provable proves if isProved.
   * @requires(isProved)
   */
  final def proved : Sequent = {
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
  final def apply(rule : Rule, subgoal : Subgoal) : Provable = {
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
   * Merge: Replace premise by the given derivation.
   * Use the given provable derivation in place of the indicated subgoal of this Provable, returning the resulting concatenated Provable
   * @param subderivation the Provable derivation that proves premise subgoal.
   * @param subgoal the index of our subgoal that the given subderivation concludes.
   * @return A Provable derivation that joins our derivation and subderivation to a joint derivation of our conclusion using subderivation to show our subgoal.
   * Will return a Provable with the same conclusion but an updated set of premises.
   * @requires(0 <= subgoal && subgoal < subgoals.length)
   * @requires(subderivation.conclusion == subgoals(subgoal))
   * @note soundness-critical
   */
  final def apply(subderivation : Provable, subgoal : Subgoal) : Provable = {
    require(0 <= subgoal && subgoal < subgoals.length, "derivation " + subderivation + " can only be applied to an index " + subgoal + " within the subgoals " + subgoals)
    require(subderivation.conclusion == subgoals(subgoal), "merging Provables requires the given derivation to conclude " + subderivation.conclusion + " and has to conclude our indicated subgoal " + subgoals(subgoal))
    if (subderivation.conclusion != subgoals(subgoal)) throw new CoreException("ASSERT: Provables not concluding the required subgoal cannot be joined")
    subderivation.subgoals.toList match {  //@TODO Avoid awkward list conversion
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
   * Sub-Provable: Get a sub-Provable corresponding to a Provable with the given subgoal as conclusion.
   * Provables resulting from the returned subgoal can be merged into this Provable to prove said subgoal.
   * @note not soundness-critical only completeness-critical
   */
  def sub(subgoal : Subgoal) : Provable = {
    require(0 <= subgoal && subgoal < subgoals.length, "Subprovable can only be applied to an index " + subgoal + " within the subgoals " + subgoals)
    Provable.startProof(subgoals(subgoal))
  } ensuring (r => r.conclusion == subgoals(subgoal), "sub yields Provable with expected subgoal " + subgoals(subgoal) + " as the conclusion") ensuring (
    r => r.subgoals == List(r.conclusion), "sub Provable is an unfinished Provable")

  override def toString() = "Provable(conclusion\n" + conclusion + "\nfrom subgoals\n" + subgoals.mkString(",\n") + ")"
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
sealed abstract class Rule(val name: String) extends (Sequent => scala.collection.immutable.List[Sequent]) {
  //@TODO Augment apply with contract "ensuring instanceOf[ClosingRule](_) || (!_.isEmpty)" to ensure only closing rules can ever come back with an empty list of premises

  override def toString: String = name
}

sealed trait ClosingRule {}

abstract class PositionRule(name: String, val pos: SeqPos) extends Rule(name) {
  override def toString: String = name + " at " + pos
}

abstract class LeftRule(name: String, val pos: AntePos) extends Rule(name) {
    override def toString: String = name + " at " + pos
}

abstract class RightRule(name: String, val pos: SuccPos) extends Rule(name) {
  override def toString: String = name + " at " + pos
}

abstract class AssumptionRule(name: String, val aPos: SeqPos, pos: SeqPos) extends PositionRule(name, pos) {
  override def toString: String = name + " at " + pos + " assumption at " + aPos
}

abstract class TwoPositionRule(name: String, val pos1: SeqPos, val pos2: SeqPos) extends Rule(name) {
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

// weakening left = hide left
// remove duplicate antecedent (this should be a tactic)
//@TODO Change type to LeftRule: AntePos => Rule
object HideLeft extends (AntePos => Rule) {
  def apply(p: AntePos): Rule = new HideLeft(p)
}
class HideLeft(p: AntePos) extends LeftRule("HideLeft", p) {
  def apply(s: Sequent): List[Sequent] = {
    List(Sequent(s.pref, s.ante.patch(p.getIndex, Nil, 1), s.succ))
  } ensuring (_.forall(r => r.subsequentOf(s)), "structural rule subsequents")
}

// weakening right = hide right
// remove duplicate succedent (this should be a tactic)
//@TODO Change type to RightRule: SuccPos => Rule
object HideRight extends (SuccPos => Rule) {
  def apply(p: SuccPos): Rule = new HideRight(p)
}
class HideRight(p: SuccPos) extends RightRule("HideRight", p) {
  def apply(s: Sequent): List[Sequent] = {
    List(Sequent(s.pref, s.ante, s.succ.patch(p.getIndex, Nil, 1)))
  } ensuring (_.forall(r => r.subsequentOf(s)), "structural rule subsequents")
}

// co-weakening left = co-hide left (all but indicated position)
object CoHideLeft extends (AntePos => Rule) {
  def apply(p: AntePos): Rule = new CoHideLeft(p)
}
class CoHideLeft(p: AntePos) extends LeftRule("CoHideLeft", p) {
  def apply(s: Sequent): List[Sequent] = {
    List(Sequent(s.pref, IndexedSeq(s.ante(p.getIndex)), IndexedSeq()))
  } ensuring (_.forall(r => r.subsequentOf(s)), "structural rule subsequents")
}

// co-weakening right = co-hide right (all but indicated position)
object CoHideRight extends (SuccPos => Rule) {
  def apply(p: SuccPos): Rule = new CoHideRight(p)
}
class CoHideRight(p: SuccPos) extends RightRule("CoHideRight", p) {
  def apply(s: Sequent): List[Sequent] = {
    List(Sequent(s.pref, IndexedSeq(), IndexedSeq(s.succ(p.getIndex))))
  } ensuring (_.forall(r => r.subsequentOf(s)), "structural rule subsequents")
}

// co-weakening = co-hide all but the indicated positions
object CoHide2 extends ((AntePos, SuccPos) => Rule) {
  def apply(p1: AntePos, p2: SuccPos): Rule = new CoHide2(p1, p2)
}
class CoHide2(p1: AntePos, p2: SuccPos) extends TwoPositionRule("CoHide2", p1, p2) {
  def apply(s: Sequent): List[Sequent] = {
    List(Sequent(s.pref, IndexedSeq(s.ante(p1.getIndex)), IndexedSeq(s.succ(p2.getIndex))))
  } ensuring (_.forall(r => r.subsequentOf(s)), "structural rule subsequents")
}


// Exchange left rule reorders antecedent
object ExchangeLeft {
  def apply(p1: AntePos, p2: AntePos): Rule = new ExchangeLeftRule(p1, p2)

  private class ExchangeLeftRule(p1: AntePos, p2: AntePos) extends TwoPositionRule("ExchangeLeft", p1, p2) {
    def apply(s: Sequent): List[Sequent] = {
      List(Sequent(s.pref, s.ante.updated(p1.getIndex, s.ante(p2.getIndex)).updated(p2.getIndex, s.ante(p1.getIndex)), s.succ))
    } ensuring (_.forall(r => r.subsequentOf(s)), "structural rule subsequents")
  }
}

// Exchange right rule reorders succedent
object ExchangeRight {
  def apply(p1: SuccPos, p2: SuccPos): Rule = new ExchangeRightRule(p1, p2)

  private class ExchangeRightRule(p1: SuccPos, p2: SuccPos) extends TwoPositionRule("ExchangeRight", p1, p2) {
    def apply(s: Sequent): List[Sequent] = {
      List(Sequent(s.pref, s.ante, s.succ.updated(p1.getIndex, s.succ(p2.getIndex)).updated(p2.getIndex, s.succ(p1.getIndex))))
    } ensuring (_.forall(r => r.subsequentOf(s)), "structural rule subsequents")
  }
}

// Contraction right rule duplicates a formula in the succedent
/*
object ContractionRight {
  def apply(p: Position): Rule = new ContractionRightRule(p)

  private class ContractionRightRule(p: Position) extends PositionRule("ContractionRight", p) {
    require(!p.isAnte && p.inExpr == HereP, "Rule is only applicable to a position in the succedent " + this)
    def apply(s: Sequent): List[Sequent] = {
      List(Sequent(s.pref, s.ante, s.succ :+ s.succ(p.getIndex)))
    } ensuring (_.forall(r => r.subsequentOf(s)), "structural rule subsequents")
  }
}

// Contraction left rule duplicates a formula in the succedent

object ContractionLeft {
  def apply(p: Position): Rule = new ContractionLeftRule(p)

  private class ContractionLeftRule(p: Position) extends PositionRule("ContractionLeft", p) {
    require(p.isAnte && p.inExpr == HereP, "Rule is only applicable to a position in the antecedent " + this)
    def apply(s: Sequent): List[Sequent] = {
      List(Sequent(s.pref, s.ante :+ s.ante(p.getIndex), s.succ))
    } ensuring (_.forall(r => r.subsequentOf(s)), "structural rule subsequents")
  }
}
*/

/*********************************************************************************
 * Sequent Proof Rules for identity/closing and cut
 *********************************************************************************
 */

// Ax Axiom close / Identity rule
object Close extends ((AntePos, SuccPos) => Rule) {
  def apply(assume: AntePos, p: SuccPos): Rule = new Close(assume, p)
}


class Close(assume: AntePos, p: SuccPos) extends AssumptionRule("Axiom", assume, p) with ClosingRule {
  def apply(s: Sequent): List[Sequent] = {
    if (s(assume) == s(p)) {
        assert (assume.isAnte && p.isSucc)
        // close goal
        Nil
    } else {
        throw new InapplicableRuleException("The referenced formulas are not identical. Thus cannot close goal. " + s(assume) + " not the same as " + s(p), this, s)
    }
  } ensuring (_.isEmpty, "closed if applicable")
}

// close by true
object CloseTrue {
  def apply(p: SuccPos): RightRule = new CloseTrue(p)
}

class CloseTrue(p: SuccPos) extends RightRule("CloseTrue", p) with ClosingRule {
  override def apply(s: Sequent): List[Sequent] = {
    require(s.succ.length > p.getIndex, "Position " + p + " invalid in " + s) // @elidable
    if (s(p) == True) Nil
    else throw new InapplicableRuleException("CloseTrue is not applicable to " + s + " at " + p, this, s)
  } ensuring (_.isEmpty, "closed if applicable")
}

// close by false
object CloseFalse {
  def apply(p: AntePos): LeftRule = new CloseFalse(p)
}

class CloseFalse(p: AntePos) extends LeftRule("CloseFalse", p) with ClosingRule {
  override def apply(s: Sequent): List[Sequent] = {
    require(s.ante.length > p.getIndex, "Position " + p + " invalid in " + s) //@elidable
    if (s(p) == False) Nil
    else throw new InapplicableRuleException("CloseFalse is not applicable to " + s + " at " + p, this, s)
  } ensuring (_.isEmpty, "closed if applicable")
}


// cut
object Cut {
  // Cut in the given formula c
  def apply(c: Formula) : Rule = new Cut(c)
  private class Cut(c: Formula) extends Rule("cut") {
    def apply(s: Sequent): List[Sequent] = {
      val use = new Sequent(s.pref, s.ante :+ c, s.succ)
      val show = new Sequent(s.pref, s.ante, s.succ :+ c)
      //@TODO Switch branches around to (show, use) and reformulate using glue()
      List(use, show)
    } ensuring(r => r.length==2 && s.subsequentOf(r(0)) && s.subsequentOf(r(1)), "subsequent of subgoals of cuts")
  }
}

/*********************************************************************************
 * Propositional Sequent Proof Rules
 *********************************************************************************
 */

// !R Not right
object NotRight extends (SuccPos => Rule) {
  def apply(p: SuccPos): Rule = new NotRight(p)
}

class NotRight(p: SuccPos) extends RightRule("Not Right", p) {
  def apply(s: Sequent): List[Sequent] = {
    val Not(a) = s(p)
    List(s.updated(p, Sequent(s.pref, IndexedSeq(a), IndexedSeq())))
  }
}

// !L Not left
object NotLeft extends (AntePos => Rule) {
  def apply(p: AntePos): Rule = new NotLeft(p)
}

class NotLeft(p: AntePos) extends LeftRule("Not Left", p) {
  def apply(s: Sequent): List[Sequent] = {
    val Not(a) = s(p)
    List(s.updated(p, Sequent(s.pref, IndexedSeq(), IndexedSeq(a))))
  }
}

// |R Or right
object OrRight extends (SuccPos => Rule) {
  def apply(p: SuccPos): Rule = new OrRight(p)
}
class OrRight(p: SuccPos) extends RightRule("Or Right", p) {
  def apply(s: Sequent): List[Sequent] = {
    val Or(a,b) = s(p)
    List(s.updated(p, Sequent(s.pref, IndexedSeq(), IndexedSeq(a,b))))
  }
}

// |L Or left
object OrLeft extends (AntePos => Rule) {
  def apply(p: AntePos): Rule = new OrLeft(p)
}

class OrLeft(p: AntePos) extends LeftRule("Or Left", p) {
  def apply(s: Sequent): List[Sequent] = {
    val Or(a,b) = s(p)
    List(s.updated(p, a), s.updated(p, b))
  }
}

// &R And right
object AndRight extends (SuccPos => Rule) {
  def apply(p: SuccPos): Rule = new AndRight(p)
}
class AndRight(p: SuccPos) extends RightRule("And Right", p) {
  def apply(s: Sequent): List[Sequent] = {
    val And(a,b) = s(p)
    List(s.updated(p, a), s.updated(p, b))
  }
}

// &L And left
object AndLeft extends (AntePos => Rule) {
  def apply(p: AntePos): Rule = new AndLeft(p)
}

class AndLeft(p: AntePos) extends LeftRule("And Left", p) {
  def apply(s: Sequent): List[Sequent] = {
    val And(a,b) = s(p)
    List(s.updated(p, Sequent(s.pref, IndexedSeq(a,b), IndexedSeq())))
  }
}

// ->R Implication right
object ImplyRight extends (SuccPos => Rule) {
  def apply(p: SuccPos): Rule = new ImplyRight(p)
}

class ImplyRight(p: SuccPos) extends RightRule("Imply Right", p) {
  def apply(s: Sequent): List[Sequent] = {
    val Imply(a,b) = s(p)
    List(s.updated(p, Sequent(s.pref, IndexedSeq(a), IndexedSeq(b))))
  }
}


// ->L Implication left
object ImplyLeft extends (AntePos => Rule) {
  def apply(p: AntePos): Rule = new ImplyLeft(p)
}
class ImplyLeft(p: AntePos) extends LeftRule("Imply Left", p) {
  def apply(s: Sequent): List[Sequent] = {
    val Imply(a,b) = s(p)
    //@TODO Surprising that both positions change.
    List(s.updated(p, Sequent(s.pref, IndexedSeq(), IndexedSeq(a))),
         s.updated(p, Sequent(s.pref, IndexedSeq(b), IndexedSeq())))
  }
}

// <->R Equiv right
object EquivRight extends (SuccPos => Rule) {
  def apply(p: SuccPos): Rule = new EquivRight(p)
}
class EquivRight(p: SuccPos) extends RightRule("Equiv Right", p) {
  def apply(s: Sequent): List[Sequent] = {
    val Equiv(a,b) = s(p)
    //List(s.updated(p, And(Imply(a,b), Imply(b,a))))  // and then AndRight ~ ImplyRight
    List(s.updated(p, Sequent(s.pref, IndexedSeq(a),IndexedSeq(b))),
         s.updated(p, Sequent(s.pref, IndexedSeq(b),IndexedSeq(a))))
  }
}

// <->L Equiv left
object EquivLeft extends (AntePos => Rule) {
  def apply(p: AntePos): Rule = new EquivLeft(p)
}

class EquivLeft(p: AntePos) extends LeftRule("Equiv Left", p) {
  def apply(s: Sequent): List[Sequent] = {
    val Equiv(a,b) = s(p)
    //List(s.updated(p, Or(And(a,b), And(Not(a),Not(b)))))  // and then OrLeft ~ AndLeft
    // List(s.updated(p, Sequent(s.pref, IndexedSeq(a,b),IndexedSeq())),
    //      s.updated(p, Sequent(s.pref, IndexedSeq(Not(a),Not(b)),IndexedSeq())))
    //@TODO This choice is compatible with tactics but is unreasonable. Prefer upper choices
    List(s.updated(p, And(a,b)),
         s.updated(p, And(Not(a),Not(b))))
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
 * @param substitution the uniform substitution to be applied to origin.
 * @param origin the original premise, to which the uniform substitution will be applied. Thus, origin is the result of pseudo-applying this UniformSubstitution rule in sequent calculus.
 * @author aplatzer
 */
// uniform substitution
// this rule performs a backward substitution step. That is the substitution applied to the conclusion yields the premise
object UniformSubstitutionRule {
  def apply(subst: USubst, origin: Sequent) : Rule = new UniformSubstitutionRule(subst, origin)

  @elidable(FINEST) private def log(msg: =>Any) = {} //println(msg)

  private class UniformSubstitutionRule(val subst: USubst, val origin: Sequent) extends Rule("Uniform Substitution") {
    /**
     * check that conclusion is indeed derived from origin via subst (note that no reordering is allowed since those operations
     * require explicit rule applications)
     * @param conclusion the conclusion in sequent calculus to which the uniform substitution rule will be pseudo-applied, resulting in the premise origin that was supplied to UniformSubstituion.
     */
    def apply(conclusion: Sequent): List[Sequent] = {
      try {
        log("---- " + subst + "\n    " + origin + "\n--> " + subst(origin) + (if (subst(origin) == conclusion) "\n==  " else "\n!=  ") + conclusion)
        if (subst(origin) == conclusion) {
          List(origin)
        } else {
          throw new CoreException("From\n  " + origin + "\nuniform substitution\n  " + subst + "\ndid not conclude the intended\n  " + conclusion + "\nbut instead\n  " + subst(origin))
        }
      } catch {
        case exc: SubstitutionClashException => throw exc.inContext("while applying " + this + " to conclusion\n" + conclusion)
      }
    }
  }
}



/**
 * Performs alpha conversion renaming all occurrences of symbol name_idx
 * to a symbol target_tIdx.
 * @param what What name to replace.
 * @param wIdx What index of the name to replace.
 * @param repl The target name to replace what with.
 * @param rIdx The index of the target name as replacement.
 * @requires target name with target index tIdx is fresh in the sequent.
 * @author smitsch
 */
class BoundRenaming(what: String, wIdx: Option[Int], repl: String, rIdx: Option[Int])
  extends Rule("Bound Renaming") {

  //@TODO Unclear. Remove?
  @unspecialized
  override def compose[A](g: (A) => _root_.edu.cmu.cs.ls.keymaera.core.Sequent): (A) => scala.List[_root_.edu.cmu.cs.ls.keymaera.core.Sequent] = super.compose(g)

  def apply(s: Sequent): List[Sequent] =
      List(Sequent(s.pref, s.ante.map(ghostify), s.succ.map(ghostify)))

  def apply(f: Formula): Formula = {
    if (StaticSemantics(f).bv.exists(v => v.name == what && v.index == wIdx)) {
      // allow self renaming to get stuttering
      if ((what != repl || wIdx != rIdx) && allNames(f).exists(v => v.name == repl && v.index == rIdx))
        throw new BoundRenamingClashException("Bound renaming only to fresh names but " + repl + "_" + rIdx + " is not fresh", this.toString, f.prettyString())
      rename(f)
    } else f
  }

  /**
   * Introduce a ghost for the target variable to remember the value of the previous variable.
   */
  private def ghostify(f: Formula) =
    if (StaticSemantics(f).bv.exists(v => v.name == what && v.index == wIdx)) f match {
      case Forall(vars, _) if vars.exists(v => v.name == what && v.index == wIdx) => apply(f)
      case Exists(vars, _) if vars.exists(v => v.name == what && v.index == wIdx) => apply(f)
      case BoxModality(Assign(x: Variable, y), _) if x == y && x.name == repl && x.index == rIdx => apply(f)
      case DiamondModality(Assign(x: Variable, y), _) if x == y && x.name == repl && x.index == rIdx => apply(f)
      case _ => BoxModality(Assign(Variable(repl, rIdx, Real), Variable(what, wIdx, Real)), apply(f))
    } else f

  /**
   * Introduce a ghost for the target variable to remember the value of the previous variable.
   */
  //private def ghostifyDiamond(f: Formula) = DiamondModality(Assign(Variable(repl, rIdx, Real), Variable(what, wIdx, Real)), apply(f))

  /**
   * Performing alpha conversion renaming in a term
   */
  private def rename(t: Term): Term = t match {
    // base cases
    case x: Variable => renameVar(x)
    case CDot => CDot
    case Nothing => Nothing
    case Anything => Anything
    case x@Number(_, _) => x
    case Apply(f, theta) => Apply(f, rename(theta))
    // homomorphic cases
    case Neg(s, l) => Neg(s, rename(l))
    case Add(s, l, r) => Add(s, rename(l), rename(r))
    case Subtract(s, l, r) => Subtract(s, rename(l), rename(r))
    case Multiply(s, l, r) => Multiply(s, rename(l), rename(r))
    case Divide(s, l, r) => Divide(s, rename(l), rename(r))
    case Power(s, l, r) => Power(s, rename(l), rename(r))
    case Pair(dom, l, r) => Pair(dom, rename(l), rename(r))

    case Derivative(s, e) => Derivative(s, rename(e))
  }

  private def renameVar(e: Variable): Variable =
    //@TODO Comparison without sort is intended?
    if (e.name == what && e.index == wIdx) Variable(repl, rIdx, e.sort)
    else e

  private def rename(e: NamedSymbol): NamedSymbol = e match {
    case v: Variable => renameVar(v)
    case DifferentialSymbol(v: Variable) => DifferentialSymbol(renameVar(v))
    case _ => throw new IllegalArgumentException("Bound renaming only supported for variables so far")
  }

  /**
   * Performing alpha conversion renaming in a formula
   */
  private def rename(f: Formula): Formula = f match {
    // homomorphic base cases
    case Equals(d, l, r) => Equals(d, rename(l), rename(r))
    case NotEquals(d, l, r) => NotEquals(d, rename(l), rename(r))
    case GreaterEqual(d, l, r) => GreaterEqual(d, rename(l), rename(r))
    case GreaterThan(d, l, r) => GreaterThan(d, rename(l), rename(r))
    case LessEqual(d, l, r) => LessEqual(d, rename(l), rename(r))
    case LessThan(d, l, r) => LessThan(d, rename(l), rename(r))

    case ApplyPredicate(fn, theta) => ApplyPredicate(fn, rename(theta))

    // homomorphic cases
    case Not(g) => Not(rename(g))
    case And(l, r) => And(rename(l), rename(r))
    case Or(l, r) => Or(rename(l), rename(r))
    case Imply(l, r) => Imply(rename(l), rename(r))
    case Equiv(l, r) => Equiv(rename(l), rename(r))

    case Forall(vars, phi) => Forall(vars.map(rename), rename(phi))
    case Exists(vars, phi) => Exists(vars.map(rename), rename(phi))

    case BoxModality(p, phi) => BoxModality(rename(p), rename(phi))
    case DiamondModality(p, phi) => DiamondModality(rename(p), rename(phi))

    case FormulaDerivative(g) => FormulaDerivative(rename(g))

    case True | False => f
  }

  /**
   * Performing alpha conversion renaming in a program
   */
  private def rename(p: Program): Program = p match {
    case Assign(v: Variable, t) => Assign(renameVar(v), rename(t))
    case Assign(Derivative(s, v: Variable), t) => Assign(Derivative(s, renameVar(v)), rename(t))
    case NDetAssign(v: Variable) => NDetAssign(renameVar(v))
    case Test(phi) => Test(rename(phi))
    case ode: DifferentialProgram => renameODE(ode)
    case Sequence(a, b) => Sequence(rename(a), rename(b))
    case Choice(a, b) => Choice(rename(a), rename(b))
    case Loop(a) => Loop(rename(a))
    // extended cases
    case IfThen(cond, thenT) => IfThen(rename(cond), rename(thenT))
    case IfThenElse(cond, thenT, elseT) => IfThenElse(rename(cond), rename(thenT), rename(elseT))
  }

  private def renameODE(p: DifferentialProgram): DifferentialProgram = p match {
      case AtomicODE(Derivative(dd, Variable(n, i, d)), t) if n == what && i == wIdx =>
        AtomicODE(Derivative(dd, Variable(repl, rIdx, d)), rename(t))
      case AtomicODE(dv@Derivative(_, Variable(n, i, _)), t) if n != what || i != wIdx =>
        AtomicODE(dv, rename(t))
      case ODEProduct(a, b) => ODEProduct(renameODE(a), renameODE(b))
      case ODESystem(d, a, h) => ODESystem(d, renameODE(a), rename(h))
      case _: EmptyODE => p
      case _: DifferentialProgramConstant => p
  }

  /**
   * @TODO Difference to StaticSemantics? Could possibly converge, for example by tracking names in SetLattice even after isTop() and then providing a way of getting the literally occurring symbols from the SetLattice.
   * @TODO Or let .symbols only return literally occurring symbols without tops? Unlike free variables.
   */
  private def allNames(f: Formula): Set[NamedSymbol] = f match {
    // homomorphic cases
    case Equals(d, l, r) => allNames(l) ++ allNames(r)
    case NotEquals(d, l, r) => allNames(l) ++ allNames(r)
    case GreaterEqual(d, l, r) => allNames(l) ++ allNames(r)
    case GreaterThan(d, l, r) => allNames(l) ++ allNames(r)
    case LessEqual(d, l, r) => allNames(l) ++ allNames(r)
    case LessThan(d, l, r) => allNames(l) ++ allNames(r)

    case Not(g) => allNames(g)
    case And(l, r) => allNames(l) ++ allNames(r)
    case Or(l, r) => allNames(l) ++ allNames(r)
    case Imply(l, r) => allNames(l) ++ allNames(r)
    case Equiv(l, r) => allNames(l) ++ allNames(r)
    case FormulaDerivative(df) => allNames(df) ++ allNames(df).map(DifferentialSymbol(_))

    case Forall(vars, g) => vars.toSet ++ allNames(g)
    case Exists(vars, g) => vars.toSet ++ allNames(g)

    case BoxModality(p, g) => allNames(p) ++ allNames(g)
    case DiamondModality(p, g) => allNames(p) ++ allNames(g)

    // base cases
    case ApplyPredicate(p, arg) => Set(p) ++ allNames(arg)
    case True | False => Set.empty
    case _ => throw new UnknownOperatorException("Not implemented", f)
  }

  private def allNames(t: Term): Set[NamedSymbol] = t match {
    // homomorphic cases
    case Neg(s, l) => allNames(l)
    case Add(s, l, r) => allNames(l) ++ allNames(r)
    case Subtract(s, l, r) => allNames(l) ++ allNames(r)
    case Multiply(s, l, r) => allNames(l) ++ allNames(r)
    case Divide(s, l, r) => allNames(l) ++ allNames(r)
    case Power(s, l, r) => allNames(l) ++ allNames(r)
    case Pair(dom, l, r) => allNames(l) ++ allNames(r)
    case Derivative(s, e) => allNames(e)
    // base cases
    case Apply(f, arg) => Set(f) ++ allNames(arg)
    case x: Variable => Set(x)
    case CDot => Set(CDot)
    case nd: DifferentialSymbol => Set(nd)
    case _: NumberObj | Nothing | Anything => Set.empty
  }

  private def allNames(p: Program): Set[NamedSymbol] = p match {
    case Assign(x: Variable, e) => Set(x) ++ allNames(e)
    case Assign(Derivative(_, x : NamedSymbol), e) => Set(x) ++ allNames(e)
    case Assign(x : DifferentialSymbol, e) => Set(x) ++ allNames(e)
    case NDetAssign(x: Variable) => Set(x)
    case Test(f) => allNames(f)
    case IfThen(cond, thenT) => allNames(cond) ++ allNames(thenT)
    case AtomicODE(Derivative(_, x: Variable), e) => Set(x) ++ allNames(e)
    case ODEProduct(a, b) => allNames(a) ++ allNames(b)
    case ODESystem(vars, a, h) => allNames(a) ++ allNames(h)
    case _: EmptyODE => Set()
    case Sequence(a, b) => allNames(a) ++ allNames(b)
    case Choice(a, b) => allNames(a) ++ allNames(b)
    case Loop(a) => allNames(a)
    case prg: ProgramConstant => Set(prg)
    case prg: DifferentialProgramConstant  => Set(prg)
    case _ => throw new UnknownOperatorException("Not implemented", p)
  }
}


/*********************************************************************************
 * Skolemization Proof Rule
 *********************************************************************************
 */

/**
 * Skolemization assumes that the names of the quantified variables to be skolemized are unique within the sequent.
 * This can be ensured by finding a unique name and renaming the bound variable through alpha conversion.
 * @TODO Could replace by uniform substitution rule application mechanism for rule "all generalization"
 * along with tactics expanding scope of quantifier with axiom "all quantifier scope" at the cost of propositional repacking and unpacking.
 *      p(x)
 *  ---------------all generalize
 *  \forall x. p(x)
 */
class Skolemize(p: SeqPos) extends PositionRule("Skolemize", p) {
  override def apply(s: Sequent): List[Sequent] = {
    // Other names underneath p are forbidden as well, but the variables v that are to be skolemized are fine as Skolem function names.
    val vars = allNamesExceptAt(s, p)
    val (v,phi) = s(p) match {
      case Forall(qv, qphi) if !p.isAnte => (qv,qphi)
      case Exists(qv, qphi) if p.isAnte => (qv,qphi)
      case _ => throw new InapplicableRuleException("Skolemization in antecedent is only applicable to existential quantifiers/in succedent only to universal quantifiers", this, s)
    }
    if (vars.intersect(v.toSet).nonEmpty)
      throw new SkolemClashException("Variables to be skolemized should not appear anywhere else in the sequent. BoundRenaming required.",
        vars.intersect(v.toSet))
    // TODO append v to prefix for merge or existential quantifier handling
    List(s.updated(p, phi))
    /*List(if (p.isAnte) Sequent(s.pref /*++ v*/, s.ante.updated(p.getIndex, phi), s.succ)
         else Sequent(s.pref /*++ v*/, s.ante, s.succ.updated(p.getIndex, phi)))*/
  }

  private def allNamesExceptAt(s: Sequent, p: SeqPos) = {
    val fs = if (p.isAnte) s.ante.slice(0, p.getIndex) ++ s.ante.slice(p.getIndex + 1, s.ante.length) ++ s.succ
    else s.ante ++ s.succ.slice(0, p.getIndex) ++ s.succ.slice(p.getIndex + 1, s.ante.length)
    fs.flatMap(StaticSemantics.symbols).toSet
  }
}

/*********************************************************************************
 * Lookup Axioms
 *********************************************************************************
 */

/**
 * Look up an axiom,
 * i.e. sound axioms are valid formulas of differential dynamic logic.
 * @author nfulton
 * @author aplatzer
 * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981, 2015."
 * @see "Andre Platzer. The complete proof theory of hybrid systems. ACM/IEEE Symposium on Logic in Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 541-550. IEEE 2012"
 */
object Axiom {
  // immutable list of sound axioms
  val axioms: scala.collection.immutable.Map[String, Formula] = loadAxiomFile

  /**
   * lookup axiom named id
   */
  final def apply(id: String): Rule = new Rule("Axiom " + id) {
    def apply(s: Sequent): List[Sequent] = {
      axioms.get(id) match {
        case Some(f) => List(new Sequent(s.pref, s.ante :+ f, s.succ))
        case _ => throw new InapplicableRuleException("Axiom " + id + " does not exist in:\n" + axioms.mkString("\n"), this, s)
      }
    } ensuring (r => !r.isEmpty && r.forall(s.subsequentOf(_)), "axiom lookup adds formulas")
  }

  /**
   * parse the axiom file and add all loaded knowledge to the axioms map.
   * @TODO In the long run, could benefit from asserting expected parse of axioms to remove parser from soundness-critical core. This, obviously, introduces redundancy.
   */
  private def loadAxiomFile: Map[String, Formula] = {
    val parser = new KeYmaeraParser(false)
    val alp = parser.ProofFileParser
    val src = AxiomBase.loadAxioms()   //io.Source.fromInputStream(getClass.getResourceAsStream("axioms.txt")).mkString
    val res = alp.runParser(src)

    //Ensure that there are no doubly named axioms.
    val distinctAxiomNames = res.map(k => k.name).distinct
    assert(res.length == distinctAxiomNames.length)

    (for(k <- res)
      yield (k.name -> k.formula)).toMap
  } ensuring(assertCheckAxiomFile _, "checking parse of axioms against expected outcomes")

  @elidable(ASSERTION) private def assertCheckAxiomFile(axs : Map[String, Formula]) = {
    val x = Variable("x", None, Real)
    val aP0 = ApplyPredicate(Function("p", None, Unit, Bool), Nothing)
    val aPn = ApplyPredicate(Function("p", None, Real, Bool), Anything)
    val aQn = ApplyPredicate(Function("q", None, Real, Bool), Anything)
    val aC = Apply(Function("c", None, Unit, Real), Nothing)
    val aF = Apply(Function("f", None, Real, Real), Anything)
    val aG = Apply(Function("g", None, Real, Real), Anything)
    val a = ProgramConstant("a")
    val b = ProgramConstant("b")
    // soundness-critical that these are for p() not for p(x) or p(?)
    assert(axs("vacuous all quantifier") == Equiv(aP0, Forall(IndexedSeq(x), aP0)), "vacuous all quantifier")
    assert(axs("vacuous exists quantifier") == Equiv(aP0, Exists(IndexedSeq(x), aP0)), "vacuous exists quantifier")
    assert(axs("V vacuous") == Imply(aP0, Modality(BoxModality(a), aP0)), "V vacuous")
    
    assert(axs("[++] choice") == Equiv(Modality(BoxModality(Choice(a,b)), aPn), And(Modality(BoxModality(a), aPn), Modality(BoxModality(b), aPn))), "[++] choice")
    assert(axs("[;] compose") == Equiv(Modality(BoxModality(Sequence(a,b)), aPn), Modality(BoxModality(a), Modality(BoxModality(b), aPn))), "[;] compose")
    
    assert(axs("c()' derive constant fn") == Equals(Real, Derivative(Real, aC), Number(0)), "c()' derive constant fn")
    assert(axs("-' derive minus") == Equals(Real, Derivative(Real, Subtract(Real, aF, aG)), Subtract(Real, Derivative(Real, aF), Derivative(Real, aG))), "-' derive minus")
    assert(axs("*' derive product") == Equals(Real, Derivative(Real, Multiply(Real, aF, aG)), Add(Real, Multiply(Real, Derivative(Real, aF), aG), Multiply(Real, aF, Derivative(Real, aG)))), "*' derive product")
    assert(axs("!=' derive !=") == Equiv(FormulaDerivative(NotEquals(Real, aF, aG)), Equals(Real, Derivative(Real, aF), Derivative(Real, aG))), "!=' derive !=")
    assert(axs("|' derive or") == Equiv(FormulaDerivative(Or(aPn, aQn)), And(FormulaDerivative(aPn), FormulaDerivative(aQn))), "|' derive or")
    true
  }
}

/**
 * Apply a uniform substitution instance of an axiomatic proof rule,
 * i.e. locally sound proof rules that are represented by a pair of concrete formulas, one for the premise and one for the conclusion.
 * Axiomatic proof rules are employed after forming their uniform substitution instances.
 * @author aplatzer
 * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981, 2015."
 */
object AxiomaticRule {
  // immutable list of locally sound axiomatic proof rules (premise, conclusion)
  val rules: scala.collection.immutable.Map[String, (Sequent, Sequent)] = AxiomBase.loadAxiomaticRules()

  // apply uniform substitution instance subst of "axiomatic" rule named id
  final def apply(id: String, subst: USubst): Rule = new AxiomaticRuleInstance(id, subst)

  private final class AxiomaticRuleInstance(val id: String, val subst: USubst) extends Rule("Axiomatic Rule " + id + " instance") {
    private val (rulepremise,ruleconclusion) = rules.get(id) match {
      case Some(pair) => pair
      case _ => throw new InapplicableRuleException("Rule " + id + " does not exist in:\n" + rules.mkString("\n"), this)
    }

    /**
     * check that conclusion is indeed the indicated substitution instance from the axiomatic rule's conclusion.
     * Leads to same substitution instance of axiomatic rule's premise.
     * @param conclusion the conclusion in sequent calculus to which the uniform substitution rule will be pseudo-applied, resulting in the premise origin that was supplied to UniformSubstituion.
     */
    def apply(conclusion: Sequent): List[Sequent] = {
      try {
        if (subst(ruleconclusion) == conclusion) {
          List(subst(rulepremise))
        } else {
          throw new CoreException("Desired conclusion\n  " + conclusion + "\nis not a uniform substitution instance of\n" + ruleconclusion + "\nwith uniform substitution\n  " + subst + "\nwhich would be the instance\n  " + subst(ruleconclusion) + "\ninstead of\n  " + conclusion)
        }
      } catch {
        case exc: SubstitutionClashException => throw exc.inContext("while applying " + this + " for intended conclusion\n" + conclusion)
      }
    }
  }

}


/*********************************************************************************
 * Lemma Mechanism Rules
 *********************************************************************************
 */

// Lookup Lemma (different justifications: Axiom, Lemma with proof, Oracle Lemma)


/**
 * Lookup a lemma that has been proved previously or by an external arithmetic tool.
 * @author nfulton
 *@TODO Review
 */
object LookupLemma {
  lazy val lemmadbpath = {
    val file = new java.io.File(System.getProperty("user.home") + "/lemmadb")
    file.mkdirs
    file
  }

  def apply(file : java.io.File, name : String):Rule = new LookupLemma(file,name)
  private class LookupLemma(file : java.io.File, name : String) extends Rule("Lookup Lemma") {
    def apply(s : Sequent) = {
      val parser = new KeYmaeraParser()
      val knowledge = parser.ProofFileParser.runParser(scala.io.Source.fromFile(file).mkString)
      val formula = LoadedKnowledgeTools.fromName(knowledge)(name).head.formula
      //@TODO Are lemmas fine in every context? Including any s.pref?
      val newSequent = new Sequent(s.pref, s.ante :+ formula, s.succ) //TODO-nrf not sure about this.
      List(newSequent)
    }
  }

  def addRealArithLemma (t : Tool, f : Formula) : Option[(java.io.File, String, Formula)] = {
    //Find the solution
    t match {
      case x: Mathematica if x.isInitialized =>
        val (solution, input, output) = x.cricitalQE.qeInOut(f)
        val result = Equiv(f,solution)

        //Save the solution to a file.
        //TODO-nrf create an interface for databases.
        def getUniqueLemmaFile(idx:Int=0):java.io.File = {
          val f = new java.io.File(lemmadbpath, "QE" + t.name + idx.toString() + ".alp")
          if(f.exists()) getUniqueLemmaFile(idx+1)
          else f
        }
        val file = LookupLemma.synchronized {
          // synchronize on file creation to make sure concurrent uses use new file names
          val newFile = getUniqueLemmaFile()
          newFile.createNewFile
          newFile
        }
        val evidence = new ToolEvidence(Map(
          "input" -> input, "output" -> output))
        KeYmaeraPrettyPrinter.saveProof(file, result, evidence)

        //Return the file where the result is saved, together with the result.
        Some((file, file.getName, result))

      case x: Z3 if x.isInitialized =>
        val (solution, input, output) = x.cricitalQE.qeInOut(f)
        val result = Equiv(f,solution)

        //Save the solution to a file.
        //TODO-nrf create an interface for databases.
        def getUniqueLemmaFile(idx:Int=0):java.io.File = {
          val f = new java.io.File(lemmadbpath, "QE" + t.name + idx.toString() + ".alp")
          if(f.exists()) getUniqueLemmaFile(idx+1)
          else f
        }
        val file = LookupLemma.synchronized {
          // synchronize on file creation to make sure concurrent uses use new file names
          val newFile = getUniqueLemmaFile()
          newFile.createNewFile
          newFile
        }
        val evidence = new ToolEvidence(Map(
          "input" -> input, "output" -> output))
        KeYmaeraPrettyPrinter.saveProof(file, result, evidence)

        //Return the file where the result is saved, together with the result.
        Some((file, file.getName, result))

      case _ => None
    }
  }
}

/*********************************************************************************
  * Derived Sequent Proof Rules, merely for efficiency
  *********************************************************************************
  */

//@derived(cut(c->p) & <(ImplyLeft & <(CloseId, HideRight), HideRight))
object CutRight extends ((Formula, SuccPos) => Rule) {
  /**
   * Cut in the given formula c in place of p.
   * G |- c, D    G |- c->p, D
   * -------------------------
   *        G |- p, D
   */
  def apply(c: Formula, pos: SuccPos) : Rule = new CutRight(c, pos)
  //@todo convert all rules to case classes since unmodifiable values and componentwise equality?
  //@todo convert rules to private[core] to make them easier to change? Ruins access though?
  private class CutRight(c: Formula, pos: SuccPos) extends Rule("cut Right") {
    def apply(s: Sequent): List[Sequent] = {
      val p = s(pos)
      List(s.updated(pos, c), s.updated(pos, Imply(c, p)))
    } //ensuring(r => r.length==2 && s.subsequentOf(r(0)) && s.subsequentOf(r(1)), "subsequent of subgoals of cuts except for pos")
  }
}

//@derived(cut(p->c) & <(ImplyLeft & <(HideLeft, CloseId), HideLeft))
object CutLeft extends ((Formula, AntePos) => Rule) {
  /**
   * Cut in the given formula c in place of p
   * G, c |- D    G |- p->c, D
   * -------------------------
   *        G, p |- D
   */
  def apply(c: Formula, pos: AntePos) : Rule = new CutLeft(c, pos)
  private class CutLeft(c: Formula, pos: AntePos) extends Rule("cut Left") {
    def apply(s: Sequent): List[Sequent] = {
      val p = s(pos)
      List(s.updated(pos, c), s.updated(pos, Sequent(s.pref, IndexedSeq(), IndexedSeq(Imply(c, p)))))
    } //ensuring(r => r.length==2 && s.subsequentOf(r(0)) && s.subsequentOf(r(1)), "subsequent of subgoals of cuts except for pos")
  }
}

// ->2<-> Equivify Right: Equivalencify Implication Right
//@derived(cut(a<->b) & prop...)
object EquivifyRight extends (SuccPos => Rule) {
  /**
   * Equivify Right: Convert implication to equivalence.
   * G |- a<->b, D
   * -------------
   * G |- a->b,  D
   */
  def apply(pos: SuccPos): Rule = new EquivifyRight(pos)
}

private[core] class EquivifyRight(pos: SuccPos) extends RightRule("->2<-> Equivify Right", pos) {
  def apply(s: Sequent): List[Sequent] = {
    val Imply(a,b) = s(pos)
    List(s.updated(pos, Equiv(a, b)))
  }
}

// vim: set ts=4 sw=4 et:
