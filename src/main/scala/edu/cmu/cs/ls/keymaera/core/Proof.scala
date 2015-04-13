/**
 * Sequent prover, proof rules, and axioms of KeYmaera
 * @author Jan-David Quesel
 * @author aplatzer
 * @author nfulton
 * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981, 2015."
 */
package edu.cmu.cs.ls.keymaera.core

// require favoring immutable Seqs for soundness

import java.io.File

import scala.collection.immutable.Seq
import scala.collection.immutable.IndexedSeq

import scala.collection.immutable.List
import scala.collection.immutable.Map
import scala.collection.immutable.Set

import scala.annotation.{unspecialized, elidable}
import scala.annotation.elidable._
import scala.collection.immutable.HashMap
import edu.cmu.cs.ls.keymaera.parser.KeYmaeraPrettyPrinter
import edu.cmu.cs.ls.keymaera.core.ExpressionTraversal.{FTPG, TraverseToPosition, StopTraversal, ExpressionTraversalFunction}
import edu.cmu.cs.ls.keymaera.parser._
import edu.cmu.cs.ls.keymaera.core.Number.NumberObj

import scala.collection.GenTraversableOnce

/*--------------------------------------------------------------------------------*/
/*--------------------------------------------------------------------------------*/

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

  override def hashCode: Int = HashFn.hash(251, pref, ante, succ)

  /**
   * Retrieves the formula in sequent at a given position. Note that this ignores p.inExpr
   * @param p the position of the formula
   * @return the formula at the given position either from the antecedent or the succedent ignoring p.inExpr
   */
  def apply(p: Position): Formula = {
    //@TODO require(p.inExpr == HereP, "Can only retrieve top level formulas")
    if (p.inExpr != HereP) println("INFO: Should only retrieve top level formulas")
    if(p.isAnte) {
      require(p.getIndex < ante.length, "Position " + p + " is invalid in sequent " + this)
      ante(p.getIndex)
    } else {
      require(p.getIndex < succ.length, "Position " + p + " is invalid in sequent " + this)
      succ(p.getIndex)
    }
  }
  
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
  def updated(p: Position, f: Formula) : Sequent = {
//    require(p.inExpr == HereP, "Can only update top level formulas")
    if (p.isAnte)
        Sequent(pref, ante.updated(p.getIndex, f), succ)
    else
        Sequent(pref, ante, succ.updated(p.getIndex, f))
  }
  
  /**
   * A copy of this sequent with the indicated position replaced by gluing the sequent s.
   * @param p the position of the replacement
   * @param s the sequent glued / concatenated to this sequent after dropping p.
   * @returns a copy of this sequent with the formula at position p removed and the sequent s appended.
   * @see #updated(Position,Formula)
   * @see #glue(Sequent)
   */
  def updated(p: Position, s: Sequent) : Sequent = {
//    require(p.inExpr == HereP, "Can only update top level formulas")
    if (p.isAnte)
        Sequent(pref, ante.patch(p.getIndex, Nil, 1), succ).glue(s)
    else
        Sequent(pref, ante, succ.patch(p.getIndex, Nil, 1)).glue(s)
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

  override def toString: String = "Sequent[{(" + pref.map(_.prettyString).mkString(", ") + "),\n " +
    ante.map(_.prettyString()).mkString(",\n ") + "\n\n==>\n\n " + succ.map(_.prettyString()).mkString(",\n ") + "}]"
}


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

object Provable {
  /**
   * Begin a new proof for the desired conclusion goal
   * @param goal the desired conclusion.
   * @result a Provable whose subgoals need to be all proved in order to prove goal.
   * @note soundness-critical
   */
  def startProof(goal : Sequent) = Provable(goal, scala.collection.immutable.IndexedSeq(goal))
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
final case class Provable private (val conclusion: Sequent, val subgoals: scala.collection.immutable.IndexedSeq[Sequent]) {
  //override def hashCode: Int = HashFn.hash(271, conclusion, subgoals)

  /**
   * Checks whether this Provable proves its conclusion.
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
   * Apply given proof rule to the indicated subgoal of this Provable, returning the resulting Provable
   * @param rule the proof rule to apply to the indicated subgoal of this Provable derivation.
   * @param subgoal which of our subgoals to apply the given proof rule to.
   * @return A Provable derivation that proves the premise subgoal by using the given proof rule.
   * Will return a Provable with the same conclusion but an updated set of premises.
   * @requires(0 <= subgoal && subgoal < subgoals.length)
   */
  final def apply(rule : Rule, subgoal : Int) : Provable = {
    require(0 <= subgoal && subgoal < subgoals.length, "Rules " + rule + " can only be applied to an index " + subgoal + " within the subgoals " + subgoals)
    rule(subgoals(subgoal)) match {
      case Nil => new Provable(conclusion, subgoals.drop(subgoal))
      case fml :: rest => new Provable(conclusion, subgoals.updated(subgoal, fml) ++ rest)
    }
  } ensuring(r => r.conclusion == conclusion, "Same conclusion after applying proof rules") ensuring (
    r => subgoals.drop(subgoal).toSet.subsetOf(r.subgoals.toSet),
    "All previous premises still around except the one that the proof rule has been applied to") ensuring (
    r => rule(subgoals(subgoal)).toSet.subsetOf(r.subgoals.toSet), "All premises generated by rule application are new subgoals")

  /**
   * Replace premise by the given derivation.
   * Use the given provable derivation in place of the indicated subgoal of this Provable, returning the resulting concatenated Provable
   * @param subderivation the Provable derivation that proves premise subgoal.
   * @param subgoal the index of our subgoal that the given subderivation concludes.
   * @return A Provable derivation that joins our derivation and subderivation to a joint derivation of our conclusion using subderivation to show our subgoal.
   * Will return a Provable with the same conclusion but an updated set of premises.
   * @requires(0 <= subgoal && subgoal < subgoals.length)
   * @requires(subderivation.conclusion == subgoals(subgoal))
   */
  final def apply(subderivation : Provable, subgoal : Int) : Provable = {
    require(0 <= subgoal && subgoal < subgoals.length, "derivation " + subderivation + " can only be applied to an index " + subgoal + " within the subgoals " + subgoals)
    require(subderivation.conclusion == subgoals(subgoal), "the given derivation concludes " + subderivation.conclusion + " and has to conclude our indicated subgoal " + subgoals(subgoal))
    if (subderivation.conclusion != subgoals(subgoal)) throw new CoreException("ASSERT: Provables not concluding the required subgoal cannot be joined")
    subderivation.subgoals.toList match {  //@TODO Avoid awkward list conversion
      case Nil => new Provable(conclusion, subgoals.drop(subgoal))
      case fml :: rest => new Provable(conclusion, subgoals.updated(subgoal, fml) ++ rest)
    }
  } ensuring(r => r.conclusion == conclusion, "Same conclusion after joining derivations") ensuring (
    r => subgoals.drop(subgoal).toSet.subsetOf(r.subgoals.toSet),
    "All previous premises still around except the one replaced by a derivation") ensuring (
    r => subderivation.subgoals.toSet.subsetOf(r.subgoals.toSet), "All premises in joined derivation are new subgoals")

}




  /*********************************************************************************
   * Categorize Kinds of Proof Rules
   *********************************************************************************
   */

abstract class PositionRule(name: String, val pos: Position) extends Rule(name) {
    override def toString: String = name + " at " + pos
}

abstract class AssumptionRule(name: String, val aPos: Position, pos: Position) extends PositionRule(name, pos) {
  override def toString: String = name + " at " + pos + " assumption at " + aPos
}

abstract class TwoPositionRule(name: String, val pos1: Position, val pos2: Position) extends Rule(name) {
  override def toString: String = name + " at " + pos1 + " and " + pos2
}

/*********************************************************************************
 * Positioning information within expressions, i.e. formulas / terms / programs
 *********************************************************************************
 */

@deprecated("Remove from prover core. But needed in AlphaConversion?")
case class PosInExpr(pos: List[Int] = Nil) {
  require(pos forall(_>=0), "all nonnegative positions")
  def first:  PosInExpr = new PosInExpr(pos :+ 0)
  def second: PosInExpr = new PosInExpr(pos :+ 1)
  def third:  PosInExpr = new PosInExpr(pos :+ 2)

  def isPrefixOf(p: PosInExpr): Boolean = p.pos.startsWith(pos)
  def child: PosInExpr = PosInExpr(pos.tail)
}

// observe that HereP and PosInExpr([]) will be equals, since PosInExpr is a case class
object HereP extends PosInExpr

/**
 * @param index the number of the formula in the antecedent or succedent, respectively.
 * @param inExpr the position in said formula.
 * @TODO this position class will be unnecessary after removal of deprecated rules. Or rather: the PosInExpr part is irrelevant for rules, merely for tactics.
 * Thus simplify into just a positive or negative integer type with some antecedent/succedent accessor sugar for isAnte etc around.
 */
abstract class Position(val index: Int, val inExpr: PosInExpr = HereP) {
  require (index >= 0, "nonnegative index " + index)
  def isAnte: Boolean
  def getIndex: Int = index

  /**
   * Check whether index of this position is defined in given sequent (ignoring inExpr).
   */
  def isIndexDefined(s: Sequent): Boolean =
    if(isAnte)
      s.ante.length > getIndex
    else
      s.succ.length > getIndex

  /**
   * Top level position of this position
   * @return A position with the same index but on the top level (i.e., inExpr == HereP)
   */
  def topLevel: Position = {
    clone(index)
  } ensuring (r => r.isAnte==isAnte && r.index==index && r.inExpr == HereP)

  /**
   * Whether this position is a top-level position of a sequent.
   */
  def isTopLevel: Boolean = inExpr == HereP

  def +(i: Int): Position

  def first: Position
  def second: Position
  def third: Position

  protected def clone(i: Int, e: PosInExpr = HereP): Position

  override def toString: String = "(" + (if (isAnte) "Ante" else "Succ") + ", " + getIndex + ", " + inExpr + ")"
}

class AntePosition(index: Int, inExpr: PosInExpr = HereP) extends Position(index, inExpr) {
  def isAnte = true
  protected def clone(i: Int, e: PosInExpr): Position = new AntePosition(i, e)
  def +(i: Int) = AntePosition(index + i, inExpr)
  def first: Position = AntePosition(index, inExpr.first)
  def second: Position = AntePosition(index, inExpr.second)
  def third: Position = AntePosition(index, inExpr.third)
}

object AntePosition {
  def apply(index: Int, inExpr: PosInExpr = HereP): Position = new AntePosition(index, inExpr)
}

class SuccPosition(index: Int, inExpr: PosInExpr = HereP) extends Position(index, inExpr) {
  def isAnte = false
  protected def clone(i: Int, e: PosInExpr): Position = new SuccPosition(i, e)
  def +(i: Int) = SuccPosition(index + i, inExpr)
  def first: Position = SuccPosition(index, inExpr.first)
  def second: Position = SuccPosition(index, inExpr.second)
  def third: Position = SuccPosition(index, inExpr.third)
}

object SuccPosition {
  def apply(index: Int, inExpr: PosInExpr = HereP): Position = new SuccPosition(index, inExpr)
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
object HideLeft extends (Position => Rule) {
  def apply(p: Position): Rule = {
    require(p.isAnte && p.inExpr == HereP, "Hide left should be done in the antecendent and on top level. Not on " + p)
    new Hide(p)
  }
}
// weakening right = hide right
// remove duplicate succedent (this should be a tactic)
object HideRight extends (Position => Rule) {
  def apply(p: Position): Rule = {
    require(!p.isAnte && p.inExpr == HereP, "Hide right should be done in succedent and on top level. Not on " + p)
    new Hide(p)
  }
}
class Hide(p: Position) extends PositionRule("Hide", p) {
  require(p.inExpr == HereP)
  def apply(s: Sequent): List[Sequent] = {
    if (p.isAnte)
      List(Sequent(s.pref, s.ante.patch(p.getIndex, Nil, 1), s.succ))
    else
      List(Sequent(s.pref, s.ante, s.succ.patch(p.getIndex, Nil, 1)))
  } ensuring (_.forall(r => r.subsequentOf(s)), "structural rule subsequents")
}

// co-weakening left = co-hide left (all but indicated position)
object CoHideLeft extends (Position => Rule) {
  def apply(p: Position): Rule = {
    require(p.isAnte && p.inExpr == HereP)
    new CoHide(p)
  }
}
// co-weakening right = co-hide right (all but indicated position)
object CoHideRight extends (Position => Rule) {
  def apply(p: Position): Rule = {
    require(!p.isAnte && p.inExpr == HereP)
    new CoHide(p)
  }
}
class CoHide(p: Position) extends PositionRule("CoHide", p) {
  require(p.inExpr == HereP)
  def apply(s: Sequent): List[Sequent] = {
    if (p.isAnte)
      List(Sequent(s.pref, IndexedSeq(s.ante(p.getIndex)), IndexedSeq()))
    else
      List(Sequent(s.pref, IndexedSeq(), IndexedSeq(s.succ(p.getIndex))))
  } ensuring (_.forall(r => r.subsequentOf(s)), "structural rule subsequents")
}


// Exchange left rule reorders antecedent
object ExchangeLeft {
  def apply(p1: Position, p2: Position): Rule = new ExchangeLeftRule(p1, p2)

  private class ExchangeLeftRule(p1: Position, p2: Position) extends TwoPositionRule("ExchangeLeft", p1, p2) {
    require(p1.isAnte && p1.inExpr == HereP && p2.isAnte && p2.inExpr == HereP, "Rule is only applicable to two positions in the antecedent " + this)
    def apply(s: Sequent): List[Sequent] = {
      List(Sequent(s.pref, s.ante.updated(p1.getIndex, s.ante(p2.getIndex)).updated(p2.getIndex, s.ante(p1.getIndex)), s.succ))
      //throw new InapplicableRuleException("Rule is only applicable to two positions in the antecedent", this, s)
    } ensuring (_.forall(r => r.subsequentOf(s)), "structural rule subsequents")
  }
}

// Exchange right rule reorders succcedent
object ExchangeRight {
  def apply(p1: Position, p2: Position): Rule = new ExchangeRightRule(p1, p2)

  private class ExchangeRightRule(p1: Position, p2: Position) extends TwoPositionRule("ExchangeRight", p1, p2) {
    require(!p1.isAnte && p1.inExpr == HereP && !p2.isAnte && p2.inExpr == HereP, "Rule is only applicable to two positions in the succedent " + this)
    def apply(s: Sequent): List[Sequent] = {
      List(Sequent(s.pref, s.ante, s.succ.updated(p1.getIndex, s.succ(p2.getIndex)).updated(p2.getIndex, s.succ(p1.getIndex))))
    } ensuring (_.forall(r => r.subsequentOf(s)), "structural rule subsequents")
  }
}

// Contraction right rule duplicates a formula in the succedent

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


/*********************************************************************************
 * Sequent Proof Rules for identity/closing and cut
 *********************************************************************************
 */

// Ax Axiom close / Identity rule
object Close extends ((Position, Position) => Rule) {
  def apply(ass: Position, p: Position): Rule = new Close(ass, p)
}


class Close(assume: Position, p: Position) extends AssumptionRule("Axiom", assume, p) with ClosingRule {
  require(p.isAnte != assume.isAnte, "Axiom close can only be applied to one formula in the antecedent and one in the succedent")
  require(p.inExpr == HereP && assume.inExpr == HereP, "Axiom close can only be applied to top level formulas")

  def apply(s: Sequent): List[Sequent] = {
    require(p.isAnte != assume.isAnte, "axiom close applies to different sides of sequent")
    if(p.isAnte != assume.isAnte && s(assume) == s(p)) {
        // close goal
        Nil
    } else {
        throw new InapplicableRuleException("The referenced formulas are not identical. Thus cannot close goal. " + s(assume) + " not the same as " + s(p), this, s)
    }
  } ensuring (_.isEmpty, "closed if applicable")
}

// close by true
object CloseTrue {
  def apply(p: Position): PositionRule = new CloseTrue(p)
}

class CloseTrue(p: Position) extends PositionRule("CloseTrue", p) with ClosingRule {
  require(!p.isAnte && p.inExpr == HereP, "CloseTrue only works in the succedent on top-level")
  override def apply(s: Sequent): List[Sequent] = {
    require(s.succ.length > p.getIndex, "Position " + p + " invalid in " + s)
    if(!p.isAnte && s.succ(p.getIndex) == True) Nil
    else throw new InapplicableRuleException("CloseTrue is not applicable to " + s + " at " + p, this, s)
  } ensuring (_.isEmpty, "closed if applicable")
}

// close by false
object CloseFalse {
  def apply(p: Position): PositionRule = new CloseFalse(p)
}

class CloseFalse(p: Position) extends PositionRule("CloseFalse", p) with ClosingRule {
  require(p.isAnte && p.inExpr == HereP, "CloseFalse only works in the antecedent on top-level")
  override def apply(s: Sequent): List[Sequent] = {
    require(s.ante.length > p.getIndex, "Position " + p + " invalid in " + s)
    if(p.isAnte && s.ante(p.getIndex) == False) Nil
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
object NotRight extends (Position => Rule) {
  def apply(p: Position): Rule = new NotRight(p)
}

class NotRight(p: Position) extends PositionRule("Not Right", p) {
  require(!p.isAnte && p.inExpr == HereP, "Not Right is only applicable to top-level formulas in the succedent not to: " + p)
  def apply(s: Sequent): List[Sequent] = {
    val Not(a) = s(p)
    List(s.updated(p, Sequent(s.pref, IndexedSeq(a), IndexedSeq())))
  }
}

// !L Not left
object NotLeft extends (Position => Rule) {
  def apply(p: Position): Rule = new NotLeft(p)
}

class NotLeft(p: Position) extends PositionRule("Not Left", p) {
  require(p.isAnte && p.inExpr == HereP, "Not Left is only applicable to top-level formulas in the antecedent not to: " + p)
  def apply(s: Sequent): List[Sequent] = {
    val Not(a) = s(p)
    List(s.updated(p, Sequent(s.pref, IndexedSeq(), IndexedSeq(a))))
  }
}

// |R Or right
object OrRight extends (Position => Rule) {
  def apply(p: Position): Rule = new OrRight(p)
}
class OrRight(p: Position) extends PositionRule("Or Right", p) {
  require(!p.isAnte && p.inExpr == HereP, "Or Right is only applicable to top-level formulas in the succedent not to: " + p)
  def apply(s: Sequent): List[Sequent] = {
    val Or(a,b) = s(p)
    List(s.updated(p, Sequent(s.pref, IndexedSeq(), IndexedSeq(a,b))))
  }
}

// |L Or left
object OrLeft extends (Position => Rule) {
  def apply(p: Position): Rule = new OrLeft(p)
}

class OrLeft(p: Position) extends PositionRule("Or Left", p) {
  require(p.isAnte && p.inExpr == HereP, "Or Left is only applicable to top-level formulas in the antecedent not to: " + p)
  def apply(s: Sequent): List[Sequent] = {
    val Or(a,b) = s(p)
    List(s.updated(p, a), s.updated(p, b))
  }
}

// &R And right
object AndRight extends (Position => Rule) {
  def apply(p: Position): Rule = new AndRight(p)
}
class AndRight(p: Position) extends PositionRule("And Right", p) {
  require(!p.isAnte && p.inExpr == HereP, "And Right is only applicable to top-level formulas in the succedent not to: " + p)
  def apply(s: Sequent): List[Sequent] = {
    val And(a,b) = s(p)
    List(s.updated(p, a), s.updated(p, b))
  }
}

// &L And left
object AndLeft extends (Position => Rule) {
  def apply(p: Position): Rule = new AndLeft(p)
}

class AndLeft(p: Position) extends PositionRule("And Left", p) {
  require(p.isAnte && p.inExpr == HereP, "And Left is only applicable to top-level formulas in the antecedent not to: " + p)
  def apply(s: Sequent): List[Sequent] = {
    val And(a,b) = s(p)
    List(s.updated(p, Sequent(s.pref, IndexedSeq(a,b), IndexedSeq())))
  }
}

// ->R Implication right
object ImplyRight extends (Position => Rule) {
  def apply(p: Position): Rule = new ImplyRight(p)
}

class ImplyRight(p: Position) extends PositionRule("Imply Right", p) {
  require(!p.isAnte && p.inExpr == HereP, "Imply Right is only applicable to top-level formulas in the succedent not to: " + p)
  def apply(s: Sequent): List[Sequent] = {
    val Imply(a,b) = s(p)
    List(s.updated(p, Sequent(s.pref, IndexedSeq(a), IndexedSeq(b))))
  }
}


// ->L Implication left
object ImplyLeft extends (Position => Rule) {
  def apply(p: Position): Rule = new ImplyLeft(p)
}
class ImplyLeft(p: Position) extends PositionRule("Imply Left", p) {
  require(p.isAnte && p.inExpr == HereP, "Imply Left is only applicable to top-level formulas in the antecedent not to: " + p)
  def apply(s: Sequent): List[Sequent] = {
    val Imply(a,b) = s(p)
    //@TODO Surprising that both positions change.
    List(s.updated(p, Sequent(s.pref, IndexedSeq(), IndexedSeq(a))),
         s.updated(p, Sequent(s.pref, IndexedSeq(b), IndexedSeq())))
  }
}

// <->R Equiv right
object EquivRight extends (Position => Rule) {
  def apply(p: Position): Rule = new EquivRight(p)
}
class EquivRight(p: Position) extends PositionRule("Equiv Right", p) {
  require(!p.isAnte && p.inExpr == HereP, "Equivalence Right is only applicable to top-level formulas in the succedent not to: " + p)
  def apply(s: Sequent): List[Sequent] = {
    val Equiv(a,b) = s(p)
    //List(s.updated(p, And(Imply(a,b), Imply(b,a))))  // and then AndRight ~ ImplyRight
    List(s.updated(p, Sequent(s.pref, IndexedSeq(a),IndexedSeq(b))),
         s.updated(p, Sequent(s.pref, IndexedSeq(b),IndexedSeq(a))))
  }
}

// <->L Equiv left
object EquivLeft extends (Position => Rule) {
  def apply(p: Position): Rule = new EquivLeft(p)
}

class EquivLeft(p: Position) extends PositionRule("Equiv Left", p) {
  require(p.isAnte && p.inExpr == HereP, "Equivalence Left is only applicable to top-level formulas in the antecedent not to: " + p)
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
 * @param pos The position where to perform alpha conversion.
 *            If Some(p), p must point to a position that binds
 *            name_idx (either a quantifier or a box/diamond modality).
 *            If None, then prepend a modality [target_tIdx:=name_idx].
 * @requires target name with target index tIdx is fresh in the sequent.
 * @author smitsch
 */
class AlphaConversion(what: String, wIdx: Option[Int], repl: String, rIdx: Option[Int], pos: Option[Position])
  extends Rule("Alpha Conversion") {

  @unspecialized
  override def compose[A](g: (A) => _root_.edu.cmu.cs.ls.keymaera.core.Sequent): (A) => scala.List[_root_.edu.cmu.cs.ls.keymaera.core.Sequent] = super.compose(g)

  def apply(s: Sequent): List[Sequent] = pos match {
    case Some(p) =>
      //@TODO Should be able to get rid of this case by using CE.
      // BoundRenamingClashException will be checked within renameAt
      //@TODO Should return List(s.updated(p.topLevel, renameAt(s(p.topLevel), p.inExpr)) in place
      val formula = renameAt(s(p.topLevel), p.inExpr)
      if (p.isAnte) List(Sequent(s.pref, s.ante :+ formula, s.succ))
      else List(Sequent(s.pref, s.ante, s.succ :+ formula))
    case None =>
      List(Sequent(s.pref, s.ante.map(ghostify), s.succ.map(ghostify)))
  }

  def apply(f: Formula): Formula = {
    if (allNames(f).exists(v => v.name == repl && v.index == rIdx))
      throw new BoundRenamingClashException("Renaming only to fresh names but " + repl + "_" + rIdx + " is not fresh", this, f.prettyString())
    rename(f)
  }

  /**
   * Introduce a ghost for the target variable to remember the value of the previous variable.
   */
  private def ghostify(f: Formula) = BoxModality(Assign(Variable(repl, rIdx, Real), Variable(what, wIdx, Real)), apply(f))

  /**
   * Introduce a ghost for the target variable to remember the value of the previous variable.
   */
  private def ghostifyDiamond(f: Formula) = DiamondModality(Assign(Variable(repl, rIdx, Real), Variable(what, wIdx, Real)), apply(f))

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
    case _ => throw new IllegalArgumentException("Alpha conversion only supported for variables so far")
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

//  private def renameQuantifier[T <: Quantifier](vars: Seq[NamedSymbol], phi: Formula,
//                                                factory: (Seq[NamedSymbol], Formula) => T) = {
//    // assumes that variables in a quantifier block are unique
//    vars.find(v => v.name == name && v.index == idx) match {
//      case Some(oldVar) => factory(vars.map(rename), rename(phi))
//        //@TODO Can't we always use the upper case? So get rid of the private def altogether.
//      case None => factory(vars, rename(phi))
//    }
//  }


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

  // rename at a target position

  private def renameAt(f: Formula, p: PosInExpr): Formula =
    if (p == HereP) {
      if (allNames(f).exists(v => v.name == repl && v.index == rIdx))
        throw new BoundRenamingClashException("Renaming only to fresh names but " + repl + "_" + rIdx + " is not fresh", this.toString, f.prettyString())
      f match {
        // only allow renaming at a specific position if the name to be replaced is bound there
        // (needed for skolemization and renaming of quantified parts inside a formula)
        case Forall(vars, _) if vars.exists(v => v.name == what && v.index == wIdx) => rename(f)
        case Exists(vars, _) if vars.exists(v => v.name == what && v.index == wIdx) => rename(f)
        // if program may bind var, then rename with stored initial value
        case BoxModality(a, _) if StaticSemantics(a).bv.exists(v => v.name == what && v.index == wIdx) =>
          ghostify(f)
        case DiamondModality(a, _) if StaticSemantics(a).bv.exists(v => v.name == what && v.index == wIdx) =>
          ghostifyDiamond(f)
        case _ => f //@TODO throw new CoreException since this is a bug if it happens?
      }
    } else f match {
      // homomorphic cases
      case Not(g) => Not(renameAt(g, p.child))
      case And(l, r) => if (p.pos.head == 0) And(renameAt(l, p.child), r) else And(l, renameAt(r, p.child))
      case Or(l, r) => if (p.pos.head == 0) Or(renameAt(l, p.child), r) else Or(l, renameAt(r, p.child))
      case Imply(l, r) => if (p.pos.head == 0) Imply(renameAt(l, p.child), r) else Imply(l, renameAt(r, p.child))
      case Equiv(l, r) => if (p.pos.head == 0) Equiv(renameAt(l, p.child), r) else Equiv(l, renameAt(r, p.child))
      case FormulaDerivative(df) => FormulaDerivative(renameAt(df, p.child))

      case Forall(vars, g) => if (p.pos.head == 0) Forall(vars, renameAt(g, p.child)) else throw new IllegalArgumentException("Cannot traverse to " + p.pos.head + " in quantifier, only 0 allowed")
      case Exists(vars, g) => if (p.pos.head == 0) Exists(vars, renameAt(g, p.child)) else throw new IllegalArgumentException("Cannot traverse to " + p.pos.head + " in quantifier, only 0 allowed")

      case BoxModality(prg, g) => if (p.pos.head == 0) BoxModality(renameAt(prg, p.child), g) else BoxModality(prg, renameAt(g, p.child))
      case DiamondModality(prg, g) => if (p.pos.head == 0) DiamondModality(renameAt(prg, p.child), g) else DiamondModality(prg, renameAt(g, p.child))

      // base cases
      case a => throw new IllegalArgumentException("Unable to traverse deeper, reached non-formula" + a + " but would still need to traverse to " + p)
  }

  private def renameAt(prg: Program, p: PosInExpr): Program =
    if (p == HereP) throw new IllegalArgumentException("Position " + p + " is program " + prg + ", not a formula")
    else prg match {
      case Test(f) => if (p.pos.head == 0) Test(renameAt(f, p.child)) else throw new IllegalArgumentException("Cannot traverse to " + p.pos.head + " in test, only 0 allowed")
      case ODESystem(vars, a, h) => if (p.pos.head == 2) ODESystem(vars, a, renameAt(h, p.child)) else throw new IllegalArgumentException("Cannot traverse to " + p.pos.head + " in ODE system, only 2 allowed")
      case Sequence(a, b) => if (p.pos.head == 0) Sequence(renameAt(a, p.child), b) else Sequence(a, renameAt(b, p.child))
      case Choice(a, b) => if (p.pos.head == 0) Choice(renameAt(a, p.child), b) else Choice(a, renameAt(b, p.child))
      case Loop(a) => if (p.pos.head == 0) Loop(renameAt(a, p.child)) else throw new IllegalArgumentException("Cannot traverse to " + p.pos.head + " in loop, only 0 allowed")
      case IfThen(cond, thenT) => if (p.pos.head == 0) IfThen(renameAt(cond, p.child), thenT) else IfThen(cond, renameAt(thenT, p.child))
      case a => throw new IllegalArgumentException("Unable to traverse deeper, reached non-formula " + a + " but would still need to traverse to " + p)
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
class Skolemize(p: Position) extends PositionRule("Skolemize", p) {
  require(p.inExpr == HereP, "Can only skolemize top level formulas")
  override def apply(s: Sequent): List[Sequent] = {
    // Other names underneath p are forbidden as well, but the variables v that are to be skolemized are fine as Skolem function names.
    val vars = BindingAssessment.allNamesExceptAt(s, p)
    val (v,phi) = s(p) match {
      case Forall(qv, qphi) if !p.isAnte => (qv,qphi)
      case Exists(qv, qphi) if p.isAnte => (qv,qphi)
      case _ => throw new InapplicableRuleException("Skolemization in antecedent is only applicable to existential quantifiers/in succedent only to universal quantifiers", this, s)
    }
    if (vars.intersect(v.toSet).nonEmpty)
      throw new SkolemClashException("Variables to be skolemized should not appear anywhere else in the sequent. AlphaConversion required.",
        vars.intersect(v.toSet))
    // TODO append v to prefix for merge or existential quantifier handling
    List(if (p.isAnte) Sequent(s.pref /*++ v*/, s.ante.updated(p.index, phi), s.succ)
         else Sequent(s.pref /*++ v*/, s.ante, s.succ.updated(p.index, phi)))
  }
}

/**
 * Skolemization assumes that the names of the quantified variables to be skolemized are unique within the sequent.
 * This can be ensured by finding a unique name and renaming the bound variable through alpha conversion.
 * @TODO Replace by uniform substitution rule application mechanism for rule "all generalization" for functions
 * along with tactics expanding scope of quantifier with axiom "all quantifier scope".
 *      p(c())
 *  ---------------US c()~>x
 *      p(x)
 *  ---------------all generalize
 *  \forall x. p(x)
 * @TODO Or replace by AxiomaticRule with context padding using uniform substitution
 *  Gamma |- p(c()), Delta
 *  --------------- when c\not\in signature(Gamma,Delta)
 *  Gamma |- \forall x. p(x), Delta
 * And derive Skolemize from that by US.
 */
@deprecated("Replace by tactics performing uniform substitution c()~>z after a Skolemize that introduced variable z")
class SkolemizeToFn(p: Position) extends PositionRule("Skolemize2Fn", p) {
  require(p.inExpr == HereP, "Can only skolemize top level formulas")

  override def apply(s: Sequent): List[Sequent] = {
    // Other names underneath p are forbidden as well, but the variables v that are to be skolemized are fine as Skolem function names.

    val vars = BindingAssessment.allNamesExceptAt(s, p)
    val (fn, phi) = s(p) match {
      case Forall(qvs, qphi) if !p.isAnte => (qvs.map(qv => Function(qv.name, qv.index, Unit, qv.sort)), varsToFnIn(qvs, qphi))
      case Exists(qvs, qphi) if p.isAnte => (qvs.map(qv => Function(qv.name, qv.index, Unit, qv.sort)), varsToFnIn(qvs, qphi))
      case _ => throw new InapplicableRuleException("Skolemization in antecedent is only applicable to existential quantifiers/in succedent only to universal quantifiers", this, s)
    }
    if (vars.intersect(fn.toSet).nonEmpty)
      throw new SkolemClashException("Variables to be skolemized should not appear anywhere else in the sequent. AlphaConversion required.",
        vars.intersect(fn.toSet))
    // TODO append v to prefix for merge or existential quantifier handling
    List(if (p.isAnte) Sequent(s.pref /*++ fn*/, s.ante.updated(p.index, phi), s.succ)
    else Sequent(s.pref /*++ fn*/, s.ante, s.succ.updated(p.index, phi)))
  }

  // TODO flat implementation, get rid of expression traversal
  import ExpressionTraversal.traverse
  private def varsToFnIn(vs: Seq[NamedSymbol], f: Formula) = traverse(new ExpressionTraversalFunction {
      override def preT(p: PosInExpr, t: Term): Either[Option[StopTraversal], Term] = t match {
        case v: Variable if vs.contains(v) => Right(Apply(Function(v.name, v.index, Unit, v.sort), Nothing))
        case _ => Left(None)
      }
    }, f) match {
    case Some(frm) => frm
    case _ => throw new IllegalArgumentException("Skolemization was unable to replace quantified variables with constant function symbols")
  }

}

/*********************************************************************************
 * Block Quantifier Decomposition
 *********************************************************************************
 */

/**
 * decompose quantifiers.
 * @NOTE Currently not used. Delete
 * @TODO Can turn into axiom once list quantifiers and cons in list quantifier are parsable.
 * @TODO Should simplify implementation substantially by only applying at top-level.
 */
@deprecated
object DecomposeQuantifiers {
  def apply(p: Position): Rule = new DecomposeQuantifiers(p)
}

@deprecated("Remove or change")
class DecomposeQuantifiers(pos: Position) extends PositionRule("Decompose Quantifiers", pos) {
  override def apply(s: Sequent): List[Sequent] = {
    val fn = new ExpressionTraversalFunction {
      override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = if(p == pos.inExpr) Left(None) else Right(e)
      override def postF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = e match {
        case Forall(vars, f) if vars.length >= 2 => Right(Forall(vars.take(1), Forall(vars.drop(1), f)))
        case Exists(vars, f) if vars.length >= 2 => Right(Exists(vars.take(1), Exists(vars.drop(1), f)))
        case _ => throw new InapplicableRuleException("Can only decompose quantifiers with at least 2 variables. Not: " + e.prettyString(), DecomposeQuantifiers.this, s)
      }
    }
    val f = ExpressionTraversal.traverse(TraverseToPosition(pos.inExpr, fn), s(pos)) match {
      case Some(form) => form
      case _ => throw new InapplicableRuleException("Can only decompose quantifiers with at least 2 variables. Not: " + s(pos).prettyString() + " at " + pos, this, s)
    }
    if(pos.isAnte)
      List(Sequent(s.pref, s.ante.updated(pos.getIndex, f), s.succ))
    else
      List(Sequent(s.pref, s.ante, s.succ.updated(pos.getIndex, f)))
  }
}

/*********************************************************************************
 * Lookup Axioms
 *********************************************************************************
 */

object Axiom {
  // immutable list of sound axioms
  val axioms: scala.collection.immutable.Map[String, Formula] = loadAxiomFile

  def axiomFileLocation() : String = {
    val resource = this.getClass().getResource("axioms.key.alp")
    val fileLocation : String = {
      if(resource == null) {
        throw new Exception("KeYmaera Axioms file could not be found.")
      }
      else {
        resource.getFile()
      }
    }
    assert(new java.io.File(fileLocation).exists());
    fileLocation
  }

  //TODO-nrf here, parse the axiom file and add all loaded knowledge to the axioms map.
  //@TODO In the long run, could benefit from asserting expected parse of axioms to remove parser from soundness-critical core. This, obviously, introduces redundancy.
  private def loadAxiomFile: Map[String, Formula] = {
    val parser = new KeYmaeraParser(false)
    val alp = parser.ProofFileParser
    val src = io.Source.fromFile(axiomFileLocation()).mkString
    val res = alp.runParser(src)

    //Ensure that there are no doubly named axioms.
    val distinctAxiomNames = res.map(k => k.name).distinct
    assert(res.length == distinctAxiomNames.length)

    (for(k <- res)
      yield (k.name -> k.formula)).toMap
  } ensuring(assertCheckAxiomFile _, "checking parse of axioms against expected outcomes")

  // lookup axiom named id
  final def apply(id: String): Rule = new Rule("Axiom " + id) {
    def apply(s: Sequent): List[Sequent] = {
      axioms.get(id) match {
        case Some(f) => List(new Sequent(s.pref, s.ante :+ f, s.succ))
        case _ => throw new InapplicableRuleException("Axiom " + id + " does not exist in:\n" + axioms.mkString("\n"), this, s)
      }
    } ensuring (r => !r.isEmpty && r.forall(s.subsequentOf(_)), "axiom lookup adds formulas")
  }
  
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
  val rules: scala.collection.immutable.Map[String, (Sequent, Sequent)] = loadRuleFile()

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

  /**
   * KeYmaera Axiomatic Proof Rules.
   * @note Soundness-critical: Only return locally sound proof rules.
   * @author aplatzer
   */
  private def loadRuleFile() = {
    val x = Variable("x_", None, Real)
    val px = ApplyPredicate(Function("p_", None, Real, Bool), x)
    val pny = ApplyPredicate(Function("p_", None, Real, Bool), Anything)
    val qx = ApplyPredicate(Function("q_", None, Real, Bool), x)
    val qny = ApplyPredicate(Function("q_", None, Real, Bool), Anything)
    val fny = Apply(Function("f_", None, Real, Real), Anything)
    val gny = Apply(Function("g_", None, Real, Real), Anything)
    val ctxt = Function("ctx_", None, Real, Real)
    val ctxf = Function("ctx_", None, Real, Bool)
    val context = Function("ctx_", None, Bool, Bool)//@TODO eisegesis  should be Function("ctx_", None, Real->Bool, Bool) //@TODO introduce function types or the Predicational datatype
    val a = ProgramConstant("a_")
    val fmlny = ApplyPredicate(Function("F_", None, Real, Bool), Anything)
    
    scala.collection.immutable.Map(
      /* @deprecated/@derived("Could use CQ equation congruence with p(.)=(ctx_(.)=ctx_(g_(x))) and reflexivity of = instead.") */
      ("CT term congruence",
        (Sequent(Seq(), IndexedSeq(), IndexedSeq(Equals(Real, fny, gny))),
         Sequent(Seq(), IndexedSeq(), IndexedSeq(Equals(Real, Apply(ctxt, fny), Apply(ctxt, gny)))))),
      ("CQ equation congruence",
        (Sequent(Seq(), IndexedSeq(), IndexedSeq(Equals(Real, fny, gny))),
         Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(ApplyPredicate(ctxf, fny), ApplyPredicate(ctxf, gny)))))),
      ("CE congruence",
        (Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(pny, qny))),
         Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(ApplyPredicational(context, pny), ApplyPredicational(context, qny)))))),
      ("all generalization",
        (Sequent(Seq(), IndexedSeq(), IndexedSeq(px)),
          Sequent(Seq(), IndexedSeq(), IndexedSeq(Forall(Seq(x), px))))),
      ("all monotone",
         (Sequent(Seq(), IndexedSeq(px), IndexedSeq(qx)),
          Sequent(Seq(), IndexedSeq(Forall(Seq(x), px)), IndexedSeq(Forall(Seq(x), qx))))),
      ("[] monotone",
        (Sequent(Seq(), IndexedSeq(pny), IndexedSeq(qny)),
          Sequent(Seq(), IndexedSeq(BoxModality(a, pny)), IndexedSeq(BoxModality(a, qny))))),
      ("<> monotone",
        (Sequent(Seq(), IndexedSeq(pny), IndexedSeq(qny)),
          Sequent(Seq(), IndexedSeq(DiamondModality(a, pny)), IndexedSeq(DiamondModality(a, qny))))),
      //@deprecated("Use CE instead.")
      ("all congruence",
        (Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(px, qx))),
         Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(Forall(Seq(x), px), Forall(Seq(x), qx)))))),
      //@deprecated("Use CE instead.")
      ("exists congruence",
        (Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(px, qx))),
         Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(Exists(Seq(x), px), Exists(Seq(x), qx)))))),
      //@deprecated("Use [] monotone twice or just use CE equivalence congruence")
      //@TODO likewise for the other congruence rules.
      ("[] congruence",
        (Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(pny, qny))),
          Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(BoxModality(a, pny), BoxModality(a, qny)))))),
          //@deprecated("Use CE instead.")
      ("<> congruence",
        (Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(pny, qny))),
          Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(DiamondModality(a, pny), DiamondModality(a, qny)))))),
      //@deprecated Use "CE equivalence congruence" instead of all these congruence rules.
      // Derived axiomatic rules
      ("-> congruence",
        (Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(pny, qny))),
          Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(Imply(fmlny, pny), Imply(fmlny, qny)))))),
          //@deprecated("Use CE instead.")
      ("<-> congruence",
        (Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(pny, qny))),
          Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(Equiv(fmlny, pny), Equiv(fmlny, qny)))))),
          //@deprecated("Use CE instead.")
      ("& congruence",
        (Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(pny, qny))),
          Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(And(fmlny, pny), And(fmlny, qny)))))),
          //@deprecated("Use CE instead.")
      ("| congruence",
        (Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(pny, qny))),
          Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(Or(fmlny, pny), Or(fmlny, qny)))))),
          //@deprecated("Use CE instead.")
      ("! congruence",
        (Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(pny, qny))),
          Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(Not(pny), Not(qny)))))),
      /* UNSOUND FOR HYBRID GAMES */
      ("Goedel", /* unsound for hybrid games */
        (Sequent(Seq(), IndexedSeq(), IndexedSeq(pny)),
         Sequent(Seq(), IndexedSeq(), IndexedSeq(BoxModality(a, pny)))))
    )
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
      case x: Mathematica =>
        val (solution, input, output) = x.cricitalQE.qeInOut(f)
        val result = Equiv(f,solution)

        //Save the solution to a file.
        //TODO-nrf create an interface for databases.
        def getUniqueLemmaFile(idx:Int=0):java.io.File = {
          val lemmadbpath = new java.io.File("lemmadb")
          lemmadbpath.mkdirs
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

      case x: Z3 =>
        val (solution, input, output) = x.cricitalQE.qeInOut(f)
        val result = Equiv(f,solution)

        //Save the solution to a file.
        //TODO-nrf create an interface for databases.
        def getUniqueLemmaFile(idx:Int=0):java.io.File = {
          val lemmadbpath = new java.io.File("lemmadb")
          lemmadbpath.mkdirs
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

// vim: set ts=4 sw=4 et:
