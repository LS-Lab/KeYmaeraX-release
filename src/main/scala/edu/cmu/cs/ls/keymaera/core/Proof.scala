/**
 * Sequent prover, proof rules, and axioms of KeYmaera
 * @author Jan-David Quesel
 * @author aplatzer
 * @author nfulton
 */
package edu.cmu.cs.ls.keymaera.core

// require favoring immutable Seqs for soundness

import scala.collection.immutable.Seq
import scala.collection.immutable.IndexedSeq

import scala.collection.immutable.List
import scala.collection.immutable.Map
import scala.collection.immutable.Set

import scala.annotation.elidable
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
 * Sequent notation
 */

final case class Sequent(val pref: scala.collection.immutable.Seq[NamedSymbol], val ante: scala.collection.immutable.IndexedSeq[Formula], val succ: scala.collection.immutable.IndexedSeq[Formula]) {
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
    //require(p.inExpr == HereP, "Can only retrieve top level formulas")  //@TODO Could relax
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
    //require(p.inExpr == HereP, "Can only update top level formulas")
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
    //require(p.inExpr == HereP, "Can only update top level formulas")
    if (p.isAnte)
        Sequent(pref, ante.patch(p.getIndex, Nil, 1), succ).glue(s)
    else
        Sequent(pref, ante, succ.patch(p.getIndex, Nil, 1)).glue(s)
    } ensuring(r=> if (p.isAnte)
         r.glue(Sequent(pref,IndexedSeq(this(p)),IndexedSeq())).equivalent(this.glue(s))
     else
         r.glue(Sequent(pref,IndexedSeq(),IndexedSeq(this(p)))).equivalent(this.glue(s)),
         "result after re-including updated formula is equivalent to " + this + " glue " + s
     )
  
  /**
   * Check whether this sequent is a subsequent of the given sequent r (considered as sets)
   */
  def subsequentOf(r: Sequent) : Boolean = (pref == r.pref && ante.toSet.subsetOf(r.ante.toSet) && succ.toSet.subsetOf(r.succ.toSet))

  /**
   * Check whether this sequent is a equivalent to the given sequent r (considered as sets)
   */
  def equivalent(r: Sequent) : Boolean = (this.subsequentOf(r) && r.subsequentOf(this))

  override def toString: String = "Sequent[{(" + pref.map(_.prettyString).mkString(", ") + "), " +
    ante.map(_.prettyString()).mkString(", ") + " ==> " + succ.map(_.prettyString()).mkString(", ") + "}]"
}

/*
object Sequent {
  def apply(pref: scala.collection.immutable.Seq[NamedSymbol], ante: scala.collection.immutable.IndexedSeq[Formula], succ: scala.collection.immutable.IndexedSeq[Formula]) : Sequent = new Sequent(pref, ante, succ)

  def unapply(e: Sequent): Option[(scala.collection.immutable.Seq[NamedSymbol], scala.collection.immutable.IndexedSeq[Formula], scala.collection.immutable.IndexedSeq[Formula])] = e match {
    case s: Sequent => Some((s.pref,s.ante,s.succ))
    case _ => None
  }

  }*/


/**
 * Subclasses represent all proof rules.
 * A proof rule is ultimately a named mapping from sequents to lists of sequents.
 * The resulting list of sequents represent the subgoal/premise and-branches all of which need to be proved
 * to prove the current sequent (desired conclusion).
 */
  sealed abstract class Rule(val name: String) extends (Sequent => List[Sequent]) {
    override def toString: String = name
  }

  sealed abstract class Status
    case object Success       extends Status
    case object Failed        extends Status // counterexample found
    case object Unfinished    extends Status
    case object LimitExceeded extends Status
    case object Pruned        extends Status
    case object ParentClosed  extends Status

  /**
   * Proof Tree
   *============
   */

  /**
   * Additional proof node information payload for tactics.
   * @TODO Make branchLabels more general (and more typed) by allowing certain combinations of lables or modifiers to apply. Such as "cutShowLbl"&"invisible" for an invisible branch that proves a cut formula.
   */
  class ProofNodeInfo(var infos: Map[String, String], val proofNode: ProofNode) {
       //@TODO Role of closed and status is unclear. Who ever closes that? What does it have to do with the proof? It's just status information, not closed in the sense of proved. Maybe rename to done? Also possibly move into mixin trait as separate non-core feature?
    //@TODO Is this an invariant closed <=> status==Success || status==Failed || status==ParentClosed?
    @volatile private[this] var closed : Boolean = false
    @volatile var status               : Status  = Unfinished

    def isLocalClosed: Boolean = closed

    //@TODO Purpose and function unclear
    //@TODO rename to doneNode since it's not about closed in the sense of proved. Only closed in the sense of done with it even if disproved.
    def closeNode(s : Status) =
      this.synchronized {
        if (!closed) {
          closed = true
          status = s
          } else {
            assert (status == s, "status unchanged when closing already closed ProofNode with status " + status + " to " + s + " for " + this)
          }
      }

      //@TODO Purpose and function unclear
    def checkParentClosed() : Boolean = {
      var node = proofNode
      while (node != null && !node.tacticInfo.isLocalClosed) node = node.parent
      if (node == null) {
        return false
      } else {
        node = proofNode
        while (node != null && !node.tacticInfo.isLocalClosed) {
          node.tacticInfo.closeNode(ParentClosed)
          node = node.parent
        }
        return true
      }
    }
  }

  class ProofStepInfo(var infos: Map[String, String])

  object ProofNode {
    /**
     * Represents a deduction step in a proof using the indicated rule which leads to the given conjunctive list of subgoals.
     * Note that only ProofNode.apply is allowed to construct proof steps.
     * @param goal - parent of the step
     * @param subgoals - children of the step
     */
    sealed case class ProofStep private[ProofNode] (rule : Rule, goal : ProofNode, subgoals : scala.collection.immutable.List[ProofNode], tacticInfo: ProofStepInfo = new ProofStepInfo(Map())) {
      justifiedByProofRule
      @elidable(ASSERTION) def justifiedByProofRule = {
        // println("Checking " + this)
        // println("Reapply  " + rule(goal.sequent))
        require(rule(goal.sequent) == subgoals.map(_.sequent), "ProofStep " + this + " is justified by said proof rule application")
        // println("Checked  " + this)
      }

    }
  }

  sealed class ProofNode protected (val sequent : Sequent, val parent : ProofNode) {


    @volatile private[this] var alternatives : List[ProofNode.ProofStep] = Nil

    /**
     * Soundness-critical invariant that all alternative proof steps have us as their goal.
     * Dropping alternatives is sound, but adding alternatives requires passing this invariant.
     */
    private def checkInvariant = 
      assert(alternatives.forall(_.goal == this), "all alternatives are children of this goal")
      
    /**
     * List of all current or-branching alternatives of proving this proof node.
     * Result can change over time as new alternative or-branches are added.
     */
    def children: scala.collection.immutable.List[ProofNode.ProofStep] = {
      checkInvariant
      alternatives
    }

    def hasAlternative : Boolean = alternatives != Nil
    def nextAlternative : ProofNode.ProofStep = {
      require(hasAlternative, "apply proof rule before calling nextAlternative")
      alternatives match {
        case List(h, t) => h
        case Nil        => throw new IllegalArgumentException("getStep can only be invoked when there is at least one alternative.")
      //@TODO change exception type to a prover exception.
      }
    }

    def pruneAlternative(n : Int) {
      this.synchronized {
        if (n < alternatives.length)
          alternatives = alternatives.take(n-1) ++ alternatives.drop(n)
        else
          throw new IllegalArgumentException("Pruning an alternative from a proof tree requires this alternative to exists.")
      }
    }

    /**
     * Apply the given proof rule to this ProofNode.
     * Return the resulting list of subgoals (after including them as an or-branch alternative for proving this ProofNode).
     * Soundness-critical proof rule application mechanism.
     */
    final def apply(rule : Rule) : ProofNode.ProofStep = {
      // ProofNodes for the respective sequents resulting from applying rule to sequent.
      val subgoals = rule(sequent).map(new ProofNode(_, this))
      val proofStep = ProofNode.ProofStep(rule, this, subgoals)
      // Add as or-branching alternative
      this.synchronized {
        alternatives = alternatives :+ proofStep
      }
      checkInvariant
      proofStep
    }

    // TODO: there should be a TestCase that checks that this field is never read in the prover core
    val tacticInfo: ProofNodeInfo = new ProofNodeInfo(if(parent == null) Map() else parent.tacticInfo.infos, this)

    override def toString = "ProofNode(" + sequent + "\nfrom " + parent + ")"

    /**
     * @return true iff the node is closed.
     */
    def isClosed(): Boolean =
      children.map((f: ProofNode.ProofStep) =>  f.subgoals.foldLeft(true)(_ && _.isClosed())).contains(true)

    /**
     * Retrieves a list of open goals.
     * @return the list of all childless proof nodes in a proof tree.
     */
    def openGoals() : List[ProofNode] = {
      children match {
        case Nil => if(isClosed()) Nil else this :: Nil
        case _   => children.flatMap(_.subgoals.flatMap(_.openGoals()))
      }
    }
  }

  /**
   * The root node (conclusion) where a sequent derivation starts.
   */
  class RootNode(sequent : Sequent) extends ProofNode(sequent, null) {

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

case class PosInExpr(pos: List[Int] = Nil) {
  require(pos forall(_>=0), "all nonnegative positions")
  def first:  PosInExpr = new PosInExpr(pos :+ 0)
  def second: PosInExpr = new PosInExpr(pos :+ 1)
  def third:  PosInExpr = new PosInExpr(pos :+ 2)

  def isPrefixOf(p: PosInExpr): Boolean = p.pos.startsWith(pos)
}

// observe that HereP and PosInExpr([]) will be equals, since PosInExpr is a case class
object HereP extends PosInExpr

/**
 * @param index the number of the formula in the antecedent or succedent, respectively.
 * @param inExpr the position in said formula.
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

//abstract class Signature

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

  //@TODO Why is this not a TwoPositionRule?
  private class ExchangeLeftRule(p1: Position, p2: Position) extends Rule("ExchangeLeft") {
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

  //@TODO Why is this not a TwoPositionRule?
  private class ExchangeRightRule(p1: Position, p2: Position) extends Rule("ExchangeRight") {
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
 * Lookup Axioms
 *********************************************************************************
 */

object Axiom {
  // immutable list of axioms
  val axioms: scala.collection.immutable.Map[String, Formula] = loadAxiomFile

  //TODO-nrf here, parse the axiom file and add all loaded knowledge to the axioms map.
  //@TODO In the long run, could benefit from asserting expected parse of axioms to remove parser from soundness-critical core. This, obviously, introduces redundancy.
  private def loadAxiomFile: Map[String, Formula] = {
    val parser = new KeYmaeraParser(false)
    val alp = parser.ProofFileParser
    val src = io.Source.fromFile("src/main/scala/edu/cmu/cs/ls/keymaera/core/axioms.key.alp").mkString
    val res = alp.runParser(src)

    //Ensure that there are no doubly named axioms.
    val distinctAxiomNames = res.map(k => k.name).distinct
    assert(res.length == distinctAxiomNames.length)

    (for(k <- res)
      yield (k.name -> k.formula)).toMap
  }

  final def apply(id: String): Rule = new Rule("Axiom " + id) {
    def apply(s: Sequent): List[Sequent] = {
      axioms.get(id) match {
        case Some(f) => List(new Sequent(s.pref, s.ante :+ f, s.succ))
        case _ => throw new InapplicableRuleException("Axiom " + id + " does not exist in:\n" + axioms.mkString("\n"), this, s)
      }
    } ensuring (r => !r.isEmpty && r.forall(s.subsequentOf(_)), "axiom lookup adds formulas")
  }
}

/*********************************************************************************
 * Sequent Proof Rules for identity/closing and cut
 *********************************************************************************
 */

//@TODO Mark these rules as ClosingRules and add contract "ensuring (!_.isEmpty)" globally to all rules that are not ClosingRules

// Ax Axiom close / Identity rule
object AxiomClose extends ((Position, Position) => Rule) {
  def apply(ass: Position, p: Position): Rule = new AxiomClose(ass, p)
}


class AxiomClose(ass: Position, p: Position) extends AssumptionRule("Axiom", ass, p) {
  require(p.isAnte != ass.isAnte, "Axiom close can only be applied to one formula in the antecedent and one in the succedent")
  require(p.inExpr == HereP && ass.inExpr == HereP, "Axiom close can only be applied to top level formulas")

  def apply(s: Sequent): List[Sequent] = {
    require(p.isAnte != ass.isAnte, "axiom close applies to different sides of sequent")
    if(p.isAnte != ass.isAnte && s(ass) == s(p)) {
        // close goal
        Nil
    } else {
        throw new InapplicableRuleException("The referenced formulas are not identical. Thus cannot close goal. " + s(ass) + " not the same as " + s(p), this, s)
    }
  } ensuring (_.isEmpty, "closed if applicable")
}

// close by true
object CloseTrue {
  def apply(p: Position): PositionRule = new CloseTrue(p)
}

class CloseTrue(p: Position) extends PositionRule("CloseTrue", p) {
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

class CloseFalse(p: Position) extends PositionRule("CloseFalse", p) {
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

/************************************************************************
 * Other Proof Rules
 */

/*********************************************************************************
 * Congruence Rewriting Proof Rule
 *********************************************************************************
 */

// equality/equivalence rewriting
//@TODO Review
/**
 * Rewrites position ``p" according to ``ass"; for instance, if p="f" and ass="f=g" then this equality-rewrites p to g.
 * @param ass The position of the equality (should be in the antecedent) @todo rename.
 * @param p The position of an occurance of the (l?)hs of ``ass"
 */
class EqualityRewriting(ass: Position, p: Position) extends AssumptionRule("Equality Rewriting", ass, p) {
  import Helper._
  override def apply(s: Sequent): List[Sequent] = {
    require(ass.isAnte && ass.inExpr == HereP)
    val (blacklist, fn) = s.ante(ass.getIndex) match {
      case Equals(d, a, b) =>
        (names(a) ++ names(b),
        new ExpressionTraversalFunction {
          override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term]  =
            if(e == a) Right(b)
            else if(e == b) Right(a)
            else throw new IllegalArgumentException("Equality Rewriting not applicable")
        })
      case ProgramEquals(a, b) =>
        (names(a) ++ names(b),
        new ExpressionTraversalFunction {
          override def preP(p: PosInExpr, e: Program): Either[Option[StopTraversal], Program]  =
            if(e == a) Right(b)
            else if(e == b) Right(a)
            else throw new IllegalArgumentException("Equality Rewriting not applicable")
        })
      case Equiv(a, b) =>
        (names(a) ++ names(b),
        new ExpressionTraversalFunction {
          override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula]  = {
            if (e == a) Right(b)
            else if (e == b) Right(a)
            else throw new IllegalArgumentException("Equality Rewriting not applicable")
          }
        })
      case _ => throw new IllegalArgumentException("Equality Rewriting not applicable")
    }
    val trav = TraverseToPosition(p.inExpr, fn, blacklist)
    ExpressionTraversal.traverse(trav, s(p)) match {
      case Some(x: Formula) => if(p.isAnte) List(Sequent(s.pref, s.ante :+ x, s.succ)) else List(Sequent(s.pref, s.ante, s.succ :+ x))
      case a => throw new IllegalArgumentException("Equality Rewriting not applicable. Result is " + a + " " + a.getClass)
    }
  }
}

/*********************************************************************************
 * Uniform Substitution Proof Rule
 *********************************************************************************
 */

/**
 * Representation of a substitution replacing n with t.
 *
 * @param n the expression to be replaced. n can have one of the following forms:
 *          - Variable
 *          - PredicateConstant
 *          - ApplyPredicate(p:Function, x:Variable) where the variable x is meant as a \lambda abstraction in "\lambda x . p(x)"
 *          - Apply(f:Function, x:Variable) where the variable x is meant as a \lambda abstraction in "\lambda x . f(x)"
 *          - ProgramConstant
 *          - Derivative(...)
 * @param t the expression to be used in place of n
 * @TODO Rename n to match or something
 * @TODO Rename t to repl or something
 */
sealed class SubstitutionPair (val n: Expr, val t: Expr) {
  applicable
  // identity substitution would be correct but is usually unintended except for systematic constructions of substitutions that happen to produce identity substitutions. In order to avoid special casing, allow identity substitutions.
  //require(n != t, "Unexpected identity substitution " + n + " by equal " + t)
  
  @elidable(ASSERTION) def applicable = {
    // identity substitution would be correct but is usually unintended except for systematic constructions of substitutions that happen to produce identity substitutions. In order to avoid special casing, allow identity substitutions.
    if (!(n != t)) println("INFO: Unnecessary identity substitution " + n + " by equal " + t + "\n(non-critical, just indicates a possible tactics inefficiency)")
    require(n.sort == t.sort, "Sorts have to match in substitution pairs: " + n.sort + " != " + t.sort)
    require(n match {
      case CDot => true
      case Anything => true
      case _:ProgramConstant => true
      case _:ContEvolveProgramConstant => true
      case Derivative(_, _:Variable) => true
      case ApplyPredicate(_:Function, CDot | Nothing | Anything) => true
      case Apply(_:Function, CDot | Nothing | Anything) => true
      case Nothing => t == Nothing
      case _ => false
      }, "Substitutable expression required, found " + n)
  }

  override def toString: String = "(" + n.prettyString() + ", " + t.prettyString() + ")"
}
object SubstitutionPair {
  def apply(n: Expr, t: Expr): SubstitutionPair = new SubstitutionPair(n, t)
  def unapply(e: Any): Option[(Expr,Expr)] = e match {
    case x: SubstitutionPair => Some((x.n,x.t))
    case _ => None
  }
}

object SetLattice {
  def apply[A](e: A): SetLattice[A] = new SetLattice(Right(Set(e)))
  def apply[A](s: Set[A]): SetLattice[A] = new SetLattice(Right(s))
  def apply[A](s: Seq[A]): SetLattice[A] = new SetLattice(Right(s.toSet))
  def bottom[A] = new SetLattice(Right(Set.empty[A]))
  def top[A]: SetLattice[A] = new SetLattice[A](Left(null))
}
class SetLattice[A](val s: Either[Null, Set[A]]) {
  def intersect(other: SetLattice[A]): SetLattice[A] = s match {
    case Left(_) => other
    case Right(ts) => other.s match {
      case Left(_) => this
      case Right(os) => SetLattice(ts.intersect(os))
    }
  }
  def intersect(other: Set[A]): SetLattice[A] = s match {
    case Left(_) => SetLattice(other)
    case Right(ts) => SetLattice(ts.intersect(other))
  }
  def subsetOf(other: SetLattice[A]): Boolean = s match {
    case Left(_) => other.s.isLeft  /* top is subset of top */
    case Right(ts) => other.s match {
      case Left(_) => true         /* everything else is subset of top */
      case Right(os) => ts.subsetOf(os)
    }
  }
  def contains(elem: A): Boolean = s match {
    case Left(_) => true /* top contains everything */
    case Right(ts) => ts.contains(elem)
  }
  def isEmpty: Boolean = s match {
    case Left(_) => false /* top is not empty */
    case Right(ts) => ts.isEmpty
  }
  def exists(pred: A => Boolean): Boolean = s match {
    case Left(_) => true /* top contains everything that's imaginable */
    case Right(ts) => ts.exists(pred)
  }
  def +(elem: A): SetLattice[A] = s match {
    case Left(_) => this /* top remains top */
    case Right(ts) => SetLattice(ts+elem)
  }
  def -(elem: A): SetLattice[A] = s match {
    case Left(_) => this /* top remains top */
    case Right(ts) => SetLattice(ts-elem)
  }
  def ++(other: SetLattice[A]): SetLattice[A] = s match {
    case Left(_) => this
    case Right(ts) => other.s match {
      case Left(_) => other
      case Right(os) => SetLattice(ts ++ os)
    }
  }
  def ++(other: GenTraversableOnce[A]): SetLattice[A] = s match {
    case Left(_) => this
    case Right(ts) => SetLattice(ts ++ other)
  }
  def --(other: SetLattice[A]): SetLattice[A] = s match {
    case Left(_) => other.s match {
      case Left(_) => SetLattice.bottom /* top -- top == bottom */
      case _ => this /* top -- _ == top */
    }
    case Right(ts) => other.s match {
      case Left(_) => SetLattice.bottom /* _ -- top == bottom */
      case Right(os) => SetLattice(ts -- os)
    }
  }
  def --(other: GenTraversableOnce[A]): SetLattice[A] = s match {
    case Left(_) => this /* top -- _ == top */
    case Right(ts) => SetLattice(ts -- other)
  }
  override def toString = s match {
    case Left(_) => "top"
    case Right(ts) => ts.toString()
  }
  override def equals(other: Any): Boolean = other match {
    case ls: SetLattice[A] => s match {
      case Left(_) => ls.s.isLeft
      case Right(ts) => ls.s match {
        case Left(_) => false
        case Right(os) => ts == os
      }
    }
    case os: Set[A] => s match {
      case Left(_) => false
      case Right(ts) => ts == os
    }
  }
}

object BindingAssessment {
  /**
   * Records which names are free or bound.
   * @param fv Free names (maybe read)
   * @param bv Bound names (maybe written)
   */
  sealed case class VC2(fv: SetLattice[NamedSymbol],
                        bv: SetLattice[NamedSymbol])

  /**
   * Records which names are free, bound, or must-bound.
   * @param fv Free names (maybe read)
   * @param bv Bound names (maybe written)
   * @param mbv Must-bound names (certainly written).
   */
  sealed case class VC3(fv: SetLattice[NamedSymbol],
                        bv: SetLattice[NamedSymbol],
                        mbv: SetLattice[NamedSymbol])

  /**
   * Categorizes the names of formula f into free variables FV and bound variables BV.
   * @param f The formula to categorize.
   * @return The names in f categorized into free and bound names.
   */
  def catVars(f: Formula): VC2 = f match {
    // homomorphic cases
    case Equals(d, l, r) => VC2(fv = freeVariables(l) ++ freeVariables(r), bv = SetLattice.bottom)
    case NotEquals(d, l, r) => VC2(fv = freeVariables(l) ++ freeVariables(r), bv = SetLattice.bottom)
    case GreaterEqual(d, l, r) => VC2(fv = freeVariables(l) ++ freeVariables(r), bv = SetLattice.bottom)
    case GreaterThan(d, l, r) => VC2(fv = freeVariables(l) ++ freeVariables(r), bv = SetLattice.bottom)
    case LessEqual(d, l, r) => VC2(fv = freeVariables(l) ++ freeVariables(r), bv = SetLattice.bottom)
    case LessThan(d, l, r) => VC2(fv = freeVariables(l) ++ freeVariables(r), bv = SetLattice.bottom)

    case Not(g) => VC2(fv = catVars(g).fv, bv = catVars(g).bv)
    case And(l, r) => VC2(fv = catVars(l).fv ++ catVars(r).fv, bv = catVars(l).bv ++ catVars(r).bv)
    case Or(l, r) => VC2(fv = catVars(l).fv ++ catVars(r).fv, bv = catVars(l).bv ++ catVars(r).bv)
    case Imply(l, r) => VC2(fv = catVars(l).fv ++ catVars(r).fv, bv = catVars(l).bv ++ catVars(r).bv)
    case Equiv(l, r) => VC2(fv = catVars(l).fv ++ catVars(r).fv, bv = catVars(l).bv ++ catVars(r).bv)
    // TODO formuladerivative not mentioned in Definition 7 and 8
    case FormulaDerivative(df) => VC2(fv = catVars(df).fv, bv = catVars(df).bv) //@todo eisegesis

    // binding cases add bound variables to u
    case Forall(vars, g) => VC2(fv = catVars(g).fv -- vars, bv = catVars(g).bv ++ vars)
    case Exists(vars, g) => VC2(fv = catVars(g).fv -- vars, bv = catVars(g).bv ++ vars)

    case BoxModality(p, g) => VC2(fv = catVars(p).fv ++ (catVars(g).fv -- catVars(p).mbv), bv = catVars(p).bv ++ catVars(g).bv)
    case DiamondModality(p, g) => VC2(fv = catVars(p).fv ++ (catVars(g).fv -- catVars(p).mbv), bv = catVars(p).bv ++ catVars(g).bv)

    // base cases
    case ApplyPredicate(p, arg) => VC2(fv = freeVariables(arg), bv = SetLattice.bottom)
    case True | False => VC2(fv = SetLattice.bottom, bv = SetLattice.bottom)
    case _ => throw new UnknownOperatorException("Not implemented", f)
  }

  /**
   * The set of all (may) free variables whose value t depends on (syntactically).
   */
  def freeVariables(t: Term): SetLattice[NamedSymbol] = t match {
    // homomorphic cases
    case Neg(s, l) => freeVariables(l)
    case Add(s, l, r) => freeVariables(l) ++ freeVariables(r)
    case Subtract(s, l, r) => freeVariables(l) ++ freeVariables(r)
    case Multiply(s, l, r) => freeVariables(l) ++ freeVariables(r)
    case Divide(s, l, r) => freeVariables(l) ++ freeVariables(r)
    case Exp(s, l, r) => freeVariables(l) ++ freeVariables(r)
    case Pair(dom, l, r) => freeVariables(l) ++ freeVariables(r)
    // base cases
    case x: Variable => SetLattice(x)
    case CDot => SetLattice(CDot)
    // TODO x' and f(x) are not in Definition 8
    case Derivative(s, e) => freeVariables(e) //@todo eisegesis
    case Apply(f, arg) => SetLattice[NamedSymbol](f) ++ freeVariables(arg) //@todo eisegesis
    case True | False | _: NumberObj | Nothing | Anything => SetLattice.bottom
  }

  def catVars(p: Program): VC3 = { p match {
    case Assign(x: Variable, e) => VC3(fv = freeVariables(e), bv = SetLattice(x), mbv = SetLattice(x))
    // TODO CDot and derivative not mentioned in Definition 9
    case Assign(Derivative(_, x: Variable), e) => VC3(fv = freeVariables(e), bv = SetLattice(x), mbv = SetLattice(x)) //@todo eisegesis
    // TODO x:=* not mentioned in Definition 9
    case NDetAssign(x: Variable) => VC3(fv = SetLattice.bottom, bv = SetLattice(x), mbv = SetLattice(x)) //@todo eisegesis
    case Test(f) => VC3(fv = catVars(f).fv, bv = SetLattice.bottom, mbv = SetLattice.bottom)
    case NFContEvolve(vars, Derivative(_, x: Variable), e, h) =>
      VC3(fv = SetLattice[NamedSymbol](x) ++ freeVariables(e) ++ catVars(h).fv, bv = SetLattice(x), mbv = SetLattice(x))
    // TODO system of ODE cases not mentioned in Definition 9
    case ContEvolveProduct(a, b) => VC3(fv = catVars(a).fv ++ catVars(b).fv, bv = catVars(a).bv ++ catVars(b).bv,
      mbv = catVars(a).mbv ++ catVars(b).mbv) //@todo eisegesis
    case IncompleteSystem(a) => catVars(a) //@todo eisegesis
    case CheckedContEvolveFragment(a) => catVars(a) //@todo eisegesis
    case _: EmptyContEvolveProgram => VC3(fv = SetLattice.bottom, bv = SetLattice.bottom, mbv = SetLattice.bottom) //@todo eisegesis
    case Sequence(a, b) => VC3(fv = catVars(a).fv ++ (catVars(b).fv -- catVars(a).mbv),
      bv = catVars(a).bv ++ catVars(b).bv, mbv = catVars(a).mbv ++ catVars(b).mbv)
    case Choice(a, b) => VC3(fv = catVars(a).fv ++ catVars(b).fv, bv = catVars(a).bv ++ catVars(b).bv,
      mbv = catVars(a).mbv.intersect(catVars(b).mbv))
    case Loop(a) => VC3(fv = catVars(a).fv, bv = catVars(a).bv, mbv = SetLattice.bottom)
    case _: ProgramConstant => VC3(fv = SetLattice.top, bv = SetLattice.top, mbv = SetLattice.bottom)
    case _: ContEvolveProgramConstant => VC3(fv = SetLattice.top, bv = SetLattice.top, mbv = SetLattice.bottom)
    case _ => throw new UnknownOperatorException("Not implemented", p)
  }} ensuring(r => { val VC3(_, bv, mbv) = r; mbv.subsetOf(bv) }, s"Result MBV($p) not a subset of BV($p)")

  def primedVariables(ode: ContEvolveProgram): Set[NamedSymbol] = ode match {
    case ContEvolveProduct(a, b) => primedVariables(a) ++ primedVariables(b)
    case IncompleteSystem(a) => primedVariables(a)
    case NFContEvolve(_, Derivative(_, x: Variable), _, _) => Set(x)
    case _: EmptyContEvolveProgram => Set.empty
    case _: ContEvolveProgramConstant => Set.empty
  }
}

/**
 * Static access to functions of Substitution.
 * @author Stefan Mitsch
 */
object Substitution {
  /** Returns the set of names maybe free in term t (same as certainly free). */
  def maybeFreeVariables(t: Term): Set[NamedSymbol] = BindingAssessment.freeVariables(t).s match {
    case Right(ts) => ts
    case Left(_) => ???
  }
  /** Returns the set of names maybe free in formula f. */
  def maybeFreeVariables(f: Formula): Set[NamedSymbol] = BindingAssessment.catVars(f).fv.s match {
    case Right(ts) => ts
    case Left(_) => ???
  }
  /** Returns the set of names maybe free in program p. */
  def maybeFreeVariables(p: Program): Set[NamedSymbol] = BindingAssessment.catVars(p).fv.s match {
    case Right(ts) => ts
    case Left(_) => ???
  }
  /** Returns the set of names certainly free in program p. */
  def freeVariables(p: Program): Set[NamedSymbol] = {
    val ba = BindingAssessment.catVars(p)
    (ba.fv -- (ba.mbv ++ ba.bv)).s match {
      case Right(ts) => ts
      case Left(_) => ???
    }
  }
  /** Returns the set of names maybe bound in program p. */
  def maybeBoundVariables(p: Program): Set[NamedSymbol] = BindingAssessment.catVars(p).bv.s match {
    case Right(ts) => ts
    case Left(_) => ???
  }
}
/**
 * A Uniform Substitution.
 * Implementation of applying uniform substitutions to terms, formulas, programs.
 * Explicit construction computing bound variables on the fly.
 * Used for UniformSubstitution rule.
 * @author aplatzer
 * @author Stefan Mitsch
 */
sealed case class Substitution(subsDefs: scala.collection.immutable.Seq[SubstitutionPair]) {
  applicable

  import BindingAssessment._

  /**
   * Records the result of uniform substitution in a program.
   * @param o The ignore set.
   * @param u The taboo set.
   * @param p The program.
   */
  private[core] sealed case class USR(o: SetLattice[NamedSymbol],
                        u: SetLattice[NamedSymbol],
                        p: Program)

  /**
   * @param rarg the argument in the substitution.
   * @param instArg the argument to instantiate rarg with in the occurrence.
   */
  private def instantiate(rarg: Term, instArg: Term) = new Substitution(List(new SubstitutionPair(rarg, instArg)))

  // unique left hand sides in l
  @elidable(ASSERTION) def applicable = {
    // check that we never replace n by something and then again replacing the same n by something
    val lefts = subsDefs.map(sp=>sp.n).toList
    require(lefts.distinct.size == lefts.size, "no duplicate substitutions with same substitutees " + subsDefs)
    // check that we never replace p(x) by something and also p(t) by something
    val lambdaNames = subsDefs.map(sp=>sp.n match {
      case ApplyPredicate(p:Function, _:Variable) => List(p)
      case Apply(f:Function, _:Variable) => List(f)
      case _ => Nil
      }).fold(Nil)((a,b)=>a++b)
      //@TODO check that we never replace p(x) by something and also p(t) by something
    require(lambdaNames.distinct.size == lambdaNames.size, "no duplicate substitutions with same substitutee modulo alpha-renaming of lambda terms " + subsDefs)
  }
  
  @elidable(FINEST-1) private def log(msg: =>String) {}  //= println(msg)
  

  override def toString: String = "Subst(" + subsDefs.mkString(", ") + ")"

  // uniform substitution on terms
  def apply(t: Term): Term = {
    try {
      usubst(SetLattice.bottom[NamedSymbol], SetLattice.bottom[NamedSymbol], t)
    } catch {
      case ex: IllegalArgumentException =>
        throw new SubstitutionClashException(ex.getMessage, this, t, t.prettyString()).initCause(ex)
    }
  } ensuring (_ == new GlobalSubstitution(subsDefs).usubst(t),
    s"Local substitution result ${usubst(SetLattice.bottom[NamedSymbol], SetLattice.bottom[NamedSymbol], t)} " +
      s"does not agree with global result ${new GlobalSubstitution(subsDefs).usubst(t)}")

  def apply(f: Formula): Formula = {
    log("\tSubstituting " + f.prettyString + " using " + this)
    try {
      val res = usubst(SetLattice.bottom[NamedSymbol], SetLattice.bottom[NamedSymbol], f)
      log("\tSubstituted  " + res.prettyString)
      res
    } catch {
      case ex: IllegalArgumentException =>
        throw new SubstitutionClashException(ex.getMessage, this, f, f.prettyString()).initCause(ex)
    }
  } ensuring (_ == new GlobalSubstitution(subsDefs).usubst(f),
      s"Local substitution result ${usubst(SetLattice.bottom[NamedSymbol], SetLattice.bottom[NamedSymbol], f)} " +
        s"does not agree with global result ${new GlobalSubstitution(subsDefs).usubst(f)}")

  def apply(s: Sequent): Sequent = {
    try {
      Sequent(s.pref, s.ante.map(apply), s.succ.map(apply))
    } catch {
      case ex: IllegalArgumentException =>
        throw new SubstitutionClashException(ex.getMessage, this, null, s.toString()).initCause(ex)
    }
  }

  // uniform substitution on programs
  def apply(p: Program): Program = {
    try {
      usubst(SetLattice.bottom[NamedSymbol], SetLattice.bottom[NamedSymbol], p).p
    } catch {
      case ex: IllegalArgumentException =>
        throw new SubstitutionClashException(ex.getMessage, this, p, p.toString()).initCause(ex)
    }
  } ensuring (_ == new GlobalSubstitution(subsDefs).usubst(p),
    s"Local substitution result ${usubst(SetLattice.bottom[NamedSymbol], SetLattice.bottom[NamedSymbol], p)} " +
      s"does not agree with global result ${new GlobalSubstitution(subsDefs).usubst(p)}")

  private def substDiff(s: Seq[SubstitutionPair], names: SetLattice[NamedSymbol]) =
    new Substitution(s.filter(_.n match { case en: NamedSymbol => !names.contains(en) case _ => true }))

  /**
   * Check whether the function in right matches with the function in left, i.e. they have the same head.
   */
  def sameHead(left: SubstitutionPair, right: Expr) = left.n match {
    case Apply(lf, CDot | Anything | Nothing) => right match { case Apply(rf, _) => lf == rf case _ => false }
    case ApplyPredicate(lf, CDot | Anything | Nothing) => right match { case ApplyPredicate(rf, _) => lf == rf case _ => false }
    case _ => false
  }

  /**
   * Get the unique element in c to which pred applies.
   * Protests if that element is not unique because pred applies to more than one element in c or if there is none.
   */
  private def uniqueElementOf[E](c: Iterable[E], pred: E => Boolean): E = {
    require(c.count(pred) == 1)
    c.filter(pred).head
  }

  /**
   * @param u the set of taboo symbols that would clash substitutions if they occurred since they have been bound outside.
   */
  private[core] def usubst(o: SetLattice[NamedSymbol], u: SetLattice[NamedSymbol], t: Term): Term = {
    def subst(t: Term) = subsDefs.find(_.n == t).get.t.asInstanceOf[Term]
    t match {
      // homomorphic cases
      case Neg(s, e) => Neg(s, usubst(o, u, e))
      case Add(s, l, r) => Add(s, usubst(o, u, l), usubst(o, u, r))
      case Subtract(s, l, r) => Subtract(s, usubst(o, u, l), usubst(o, u, r))
      case Multiply(s, l, r) => Multiply(s, usubst(o, u, l), usubst(o, u, r))
      case Divide(s, l, r) => Divide(s, usubst(o, u, l), usubst(o, u, r))
      case Exp(s, l, r) => Exp(s, usubst(o, u, l), usubst(o, u, r))
      // TODO not mentioned in substitution
      case Pair(dom, l, r) => Pair(dom, usubst(o, u, l), usubst(o, u, r)) // @todo eisegesis
      // uniform substitution base cases
      case x: Variable => require(!subsDefs.exists(_.n == x), s"Substitution of variables not supported: $x"); x
      // TODO not mentioned in substitution
      case CDot if !subsDefs.exists(_.n == CDot) || o.contains(CDot) => CDot //@todo eisegesis
      case CDot if  substDiff(subsDefs, o).subsDefs.exists(_.n == CDot) => //@todo eisegesis
        require((SetLattice[NamedSymbol](CDot) ++ freeVariables(subst(CDot))).intersect(u).isEmpty,
          s"Substitution clash: ({CDot} ∪ ${freeVariables(subst(CDot))}) ∩ $u is not empty")
        subst(CDot)
      case dx@Derivative(s, e) => //@todo eisegesis
        // TODO what is our requirement here?
        freeVariables(usubst(o, u, e)).intersect(u).isEmpty
        Derivative(s, usubst(o, u, e))
      case app@Apply(_, theta) if subsDefs.exists(sameHead(_, app)) =>
        val subs = uniqueElementOf[SubstitutionPair](subsDefs, sameHead(_, app))
        val (rArg, rTerm) =
          (subs.n match { case Apply(_, v: NamedSymbol) => v
                          case _ => throw new IllegalArgumentException(
                            s"Substitution of f(theta)=${app.prettyString()} for arbitrary theta=$theta not supported") },
           subs.t match { case t: Term => t
                          case _ => throw new IllegalArgumentException(
                            s"Can only substitute terms for ${app.prettyString()}")}
          )
        require(freeVariables(rTerm).intersect(u).isEmpty,
          s"Substitution clash: ${freeVariables(subs.t.asInstanceOf[Term])} ∩ $u is not empty")
        instantiate(rArg, usubst(o, u, theta)).usubst(SetLattice.bottom, SetLattice.bottom, rTerm)
      case app@Apply(g, theta) if !subsDefs.exists(sameHead(_, app)) => Apply(g, usubst(o, u, theta))
      case Anything => Anything
      case Nothing => Nothing
      case x: Atom => x
      case _ => throw new UnknownOperatorException("Not implemented yet", t)
    }
  }

  private[core] def usubst(o: SetLattice[NamedSymbol], u: SetLattice[NamedSymbol], f: Formula): Formula = f match {
      // homomorphic cases
    case Not(g) => Not(usubst(o, u, g))
    case And(l, r) => And(usubst(o, u, l), usubst(o, u, r))
    case Or(l, r) => Or(usubst(o, u, l), usubst(o, u, r))
    case Imply(l, r) => Imply(usubst(o, u, l), usubst(o, u, r))
    case Equiv(l, r) => Equiv(usubst(o, u, l), usubst(o, u, r))

    case Equals(d, l, r) => Equals(d, usubst(o, u, l), usubst(o, u, r))
    case NotEquals(d, l, r) => NotEquals(d, usubst(o, u, l), usubst(o, u, r))
    case GreaterEqual(d, l, r) => GreaterEqual(d, usubst(o, u, l), usubst(o, u, r))
    case GreaterThan(d, l, r) => GreaterThan(d, usubst(o, u, l), usubst(o, u, r))
    case LessEqual(d, l, r) => LessEqual(d, usubst(o, u, l), usubst(o, u, r))
    case LessThan(d, l, r) => LessThan(d, usubst(o, u, l), usubst(o, u, r))

    // binding cases add bound variables to u
    case Forall(vars, g) => Forall(vars, usubst(o ++ vars, u ++ vars, g))
    case Exists(vars, g) => Exists(vars, usubst(o ++ vars, u ++ vars, g))

    case BoxModality(p, g) => val USR(q, v, sp) = usubst(o, u, p); BoxModality(sp, usubst(q, v, g))
    case DiamondModality(p, g) => val USR(q, v, sp) = usubst(o, u, p); DiamondModality(sp, usubst(q, v, g))

    // uniform substitution base cases
    case app@ApplyPredicate(_, Anything) if subsDefs.exists(sameHead(_, app)) =>
      val rFormula = uniqueElementOf[SubstitutionPair](subsDefs, sameHead(_, app)).t.asInstanceOf[Formula]
      Substitution(List()).usubst(SetLattice.bottom, SetLattice.bottom, rFormula)
    case app@ApplyPredicate(_, Anything) if !subsDefs.exists(sameHead(_, app)) => f
    case app@ApplyPredicate(_, theta) if subsDefs.exists(sameHead(_, app)) =>
      val subs = uniqueElementOf[SubstitutionPair](subsDefs, sameHead(_, app))
      val (rArg, rFormula) = (
        subs.n match { case ApplyPredicate(_, v: NamedSymbol) => v
                       case _ => throw new IllegalArgumentException(
                         s"Substitution of p(theta)=${app.prettyString()} for arbitrary theta=$theta not supported")},
        subs.t match { case f: Formula => f
                       case _ => throw new IllegalArgumentException(
                         s"Can only substitute formulas for ${app.prettyString()}")}
        )
      val restrictedU = rArg match { case CDot => u case _ => u-rArg }
      require(catVars(rFormula).fv.intersect(restrictedU).isEmpty,
        s"Substitution clash: ${catVars(rFormula).fv} ∩ $restrictedU is not empty")
      instantiate(rArg, usubst(o, u, theta)).usubst(SetLattice.bottom, SetLattice.bottom, rFormula)
    case app@ApplyPredicate(p, theta) if !subsDefs.exists(sameHead(_, app)) => ApplyPredicate(p, usubst(o, u, theta))
    // TODO not mentioned in uniform substitution
    case FormulaDerivative(g) => ???
    case x: Atom => x
    case _ => throw new UnknownOperatorException("Not implemented yet", f)
  }

  /**
   *  uniform substitution on a program p with the set of bound variables u
   *  return only the result components of the private case class USR
   *  used for testing only, may need a better solution
   */
  private def usubstComps(o: Set[NamedSymbol], u: Set[NamedSymbol], p: Program) = {
    val r = usubst(SetLattice(o), SetLattice(u), p); (r.o, r.u, r.p)
  }

  /**
   *
   */
  private[core] def usubst(o: SetLattice[NamedSymbol], u: SetLattice[NamedSymbol], p: Program): USR = { p match {
    case Assign(x: Variable, e) => USR(o+x, u+x, Assign(x, usubst(o, u, e)))
    case Assign(d@Derivative(_, x: Variable), e) => USR(o+x, u+x, Assign(d, usubst(o, u, e))) //@todo eisegesis
    case NDetAssign(x: Variable) => USR(o+x, u+x, p)
    case Test(f) => USR(o, u, Test(usubst(o, u, f)))
    case ode: ContEvolveProgram => val x = primedVariables(ode); val sode = usubstODE(o, u, x, ode); USR(o++SetLattice(x), u++SetLattice(x), sode)
    case Sequence(a, b) => val USR(q, v, as) = usubst(o, u, a); val USR(r, w, bs) = usubst(q, v, b); USR(r, w, Sequence(as, bs))
    case Choice(a, b) =>
      val USR(q, v, as) = usubst(o, u, a); val USR(r, w, bs) = usubst(o, u, b)
      // TODO remove when proof of uniform substitution is done
      require(((q == SetLattice.bottom && v == SetLattice.top) || q == v)
        && ((r == SetLattice.bottom && w == SetLattice.top) || r == w),
        s"Programs where not all branches write the same variables are not yet supported: q=$q ==? v=$v, r=$r ==? w=$w")
      USR(q.intersect(r), v++w, Choice(as, bs))
    case Loop(a) =>
      val USR(q, v, _) = usubst(o, u, a)
      val USR(r, w, as) = usubst(o, v, a)
      // TODO remove when proof of uniform substitution is done
      require((r == SetLattice.bottom && w == SetLattice.top) || r == w,
        s"Programs where loop does not write all variables on all branches are not yet supported: r=$r ==? w=$w")
      USR(o, w, Loop(as)) ensuring (
        o.subsetOf(q), s"Non-monotonic o: $o not subset of $q") ensuring(
        q == r, s"Unstable O: $q not equal to $r") ensuring(
        u.subsetOf(v), s"Non-monotonic u: $u not subset of $v") ensuring(
        v == w, s"Unstable U: $v not equal to $w") ensuring (
        usubst(r, w, a).o == r, s"Unstable O: ${usubst(r, w, a).o} not equal to $r") ensuring(
        usubst(r, w, a).u == w, s"Unstable U: ${usubst(r, w, a).u} not equal to $w")

    //@TODO check implementation
    case a: ProgramConstant if  subsDefs.exists(_.n == p) =>
      val sigmaP = subsDefs.find(_.n == p).get.t.asInstanceOf[Program]
      // programs don't have a side condition, since their meaning does not depend on state
      USR(o++catVars(sigmaP).mbv, u++catVars(sigmaP).bv, sigmaP)
    case a: ProgramConstant if !subsDefs.exists(_.n == p) => USR(o++catVars(a).mbv, u++catVars(a).bv, p)
    case _ => throw new UnknownOperatorException("Not implemented yet", p)
  }} ensuring (r => { val USR(q, v, _) = r; q.subsetOf(v) }, s"Result O not a subset of result U")

  /**
   * Substitution in (systems of) differential equations.
   * @param o The ignore list.
   * @param u The taboo list.
   * @param primed The primed names (all primed names in the ODE system).
   * @param p The ODE.
   * @return The substitution result.
   */
  private def usubstODE(o: SetLattice[NamedSymbol], u: SetLattice[NamedSymbol], primed: Set[NamedSymbol], p: ContEvolveProgram):
    ContEvolveProgram = p match {
      case ContEvolveProduct(a, b) => ContEvolveProduct(usubstODE(o, u, primed, a), usubstODE(o, u, primed, b))
      case NFContEvolve(v, d@Derivative(_, x: Variable), e, h) => if (v.isEmpty) {
        NFContEvolve(v, d, usubst(o++SetLattice(primed), u++SetLattice(primed), e), usubst(o++SetLattice(primed), u++SetLattice(primed), h))
      } else throw new UnknownOperatorException("Check implementation whether passing v is correct.", p)
      case _: EmptyContEvolveProgram => p
      case IncompleteSystem(s) => IncompleteSystem(usubstODE(o, u, primed, s))
      case CheckedContEvolveFragment(s) => CheckedContEvolveFragment(usubstODE(o, u, primed, s))
      case a: ContEvolveProgramConstant if  subsDefs.exists(_.n == p) =>
        val repl = subsDefs.find(_.n == p).get.t
        repl match {
          case replODE: ContEvolveProgram => replODE
          case _ => throw new IllegalArgumentException("Can only substitute continuous programs for " +
            s"continuous program constants: $repl not allowed for $a")
        }
      case a: ContEvolveProgramConstant if !subsDefs.exists(_.n == p) => p
    }
}

/**
 * A Uniform Substitution.
 * Implementation of applying uniform substitutions to terms, formulas, programs.
 * Global version that checks admissibility eagerly at bound variables rather than computing bounds on the fly and checking upon occurrence.
 * Used for UniformSubstitution rule.
 * @author aplatzer
 */
sealed case class GlobalSubstitution(subsDefs: scala.collection.immutable.Seq[SubstitutionPair]) {
  applicable()

  // unique left hand sides in l
  @elidable(ASSERTION) def applicable() = {
    // check that we never replace n by something and then again replacing the same n by something
    val lefts = subsDefs.map(_.n).toList
    require(lefts.distinct.size == lefts.size, "no duplicate substitutions with same substitutees " + subsDefs)
    // check that we never replace p(x) by something and also p(t) by something
    val lambdaNames = subsDefs.map(_.n match {
      case ApplyPredicate(p: Function, _: Variable) => List(p)
      case Apply(f: Function, _: Variable) => List(f)
      case _ => Nil
    }).fold(Nil)((a,b) => a++b)
    require(lambdaNames.distinct.size == lambdaNames.size, "no duplicate substitutions with same substitutee modulo alpha-renaming of lambda terms " + subsDefs)
  }

  @elidable(FINEST-1) private def log(msg: =>String) {}  //= println(msg)

    import BindingAssessment._

  override def toString: String = "GlobSubst(" + subsDefs.mkString(", ") + ")"

  def apply(t: Term): Term = {
    usubst(t)
  } ensuring(_ == new Substitution(subsDefs).usubst(SetLattice.bottom[NamedSymbol], SetLattice.bottom[NamedSymbol], t),
    s"Global substitution result ${usubst(t)} does not agree with local result " +
      s"${new Substitution(subsDefs).usubst(SetLattice.bottom[NamedSymbol], SetLattice.bottom[NamedSymbol], t)}")
  def apply(f: Formula): Formula = {
    usubst(f)
  } ensuring(_ == new Substitution(subsDefs).usubst(SetLattice.bottom[NamedSymbol], SetLattice.bottom[NamedSymbol], f),
    s"Global substitution result ${usubst(f)} does not agree with local result " +
      s"${new Substitution(subsDefs).usubst(SetLattice.bottom[NamedSymbol], SetLattice.bottom[NamedSymbol], f)}")
  def apply(p: Program): Program = {
    usubst(p)
  } ensuring(_ == new Substitution(subsDefs).usubst(SetLattice.bottom[NamedSymbol], SetLattice.bottom[NamedSymbol], p).p,
    s"Global substitution result ${usubst(p)} does not agree with local result " +
      s"${new Substitution(subsDefs).usubst(SetLattice.bottom[NamedSymbol], SetLattice.bottom[NamedSymbol], p)}")

  // uniform substitution on terms
  private[core] def usubst(t: Term): Term = {
    try {
      t match {
        // uniform substitution base cases
        case x: Variable => require(!subsDefs.exists(_.n == x), s"Substitution of variables not supported: $x"); x
        case xp@Derivative(Real, x: Variable) => require(!subsDefs.exists(_.n == xp),
          s"Substitution of differential symbols not supported: $xp"); xp
        case app@Apply(_, theta) if subsDefs.exists(sameHead(_, app)) =>
          val subs = uniqueElementOf[SubstitutionPair](subsDefs, sameHead(_, app))
          val (rArg, rTerm) =
            (subs.n match { case Apply(_, v: NamedSymbol) => v
                            case _ => throw new IllegalArgumentException(
                              s"Substitution of f(theta)=${app.prettyString()} for arbitrary theta=$theta not supported") },
             subs.t match { case t: Term => t
                            case _ => throw new IllegalArgumentException(
                              s"Can only substitute terms for ${app.prettyString()}")}
            )
          GlobalSubstitution(SubstitutionPair(rArg, usubst(theta)) :: Nil).usubst(rTerm)
        case app@Apply(g, theta) if !subsDefs.exists(sameHead(_, app)) => Apply(g, usubst(theta))
        case Anything => Anything // TODO check
        case Nothing => Nothing // TODO check
        case CDot if !subsDefs.exists(_.n == CDot) => CDot // TODO check (should be case x = sigma x for variable x)
        case CDot if  subsDefs.exists(_.n == CDot) => // TODO check (should be case x = sigma x for variable x)
          subsDefs.find(_.n == CDot).get.t match {
            case t: Term => t
            case _ => throw new IllegalArgumentException("Can only substitute terms for .")
          }
        case n@Number(_, _) => n
        //@TODO any way of ensuring for the following that top-level(t)==top-level(\result)
         // homomorphic cases
        case Neg(s, e) => Neg(s, usubst(e))
        case Add(s, l, r) => Add(s, usubst(l), usubst(r))
        case Subtract(s, l, r) => Subtract(s, usubst(l), usubst(r))
        case Multiply(s, l, r) => Multiply(s, usubst(l), usubst(r))
        case Divide(s, l, r) => Divide(s, usubst(l), usubst(r))
        case Exp(s, l, r) => Exp(s, usubst(l), usubst(r))
        case der@Derivative(Real, e) =>
          require(admissible(SetLattice.top[NamedSymbol], e),
            s"Substitution clash when substituting derivative ${der.prettyString()}")
          Derivative(Real, usubst(e))
      }
    } catch {
      case ex: IllegalArgumentException =>
        throw new SubstitutionClashException(ex.getMessage, this, t, t.prettyString()).initCause(ex)
    }
  }

  private[core] def usubst(f: Formula): Formula = {
    log(s"Substituting ${f.prettyString()} using $this")
    try {
      f match {
        case app@ApplyPredicate(_, theta) if subsDefs.exists(sameHead(_, app)) =>
          val subs = uniqueElementOf[SubstitutionPair](subsDefs, sameHead(_, app))
          val (rArg, rFormula) = (
            subs.n match { case ApplyPredicate(_, v: NamedSymbol) => v
                           case _ => throw new IllegalArgumentException(
                            s"Substitution of p(theta)=${app.prettyString()} for arbitrary theta=${theta.prettyString()} not supported")},
            subs.t match { case f: Formula => f
                           case _ => throw new IllegalArgumentException(
                             s"Can only substitute formulas for ${app.prettyString()}")
            })
          GlobalSubstitution(SubstitutionPair(rArg, usubst(theta)) :: Nil).usubst(rFormula)
        case app@ApplyPredicate(q, theta) if !subsDefs.exists(sameHead(_, app)) => ApplyPredicate(q, usubst(theta))
        case True | False => f

        //@TODO any way of ensuring for the following that  top-level(f)==top-level(\result)
        case Equals(d, l, r) => Equals(d, usubst(l), usubst(r))
        case NotEquals(d, l, r) => NotEquals(d, usubst(l), usubst(r))
        case GreaterEqual(d, l, r) => GreaterEqual(d, usubst(l), usubst(r))
        case GreaterThan(d, l, r) => GreaterThan(d, usubst(l), usubst(r))
        case LessEqual(d, l, r) => LessEqual(d, usubst(l), usubst(r))
        case LessThan(d, l, r) => LessThan(d, usubst(l), usubst(r))

        // homomorphic cases
        case Not(g) => Not(usubst(g))
        case And(l, r) => And(usubst(l), usubst(r))
        case Or(l, r) => Or(usubst(l), usubst(r))
        case Imply(l, r) => Imply(usubst(l), usubst(r))
        case Equiv(l, r) => Equiv(usubst(l), usubst(r))

        // binding cases add bound variables to u
        case Forall(vars, g) => require(admissible(vars, g),
          s"Substitution clash: {x}=$vars when substituting forall ${g.prettyString()}")
            Forall(vars, usubst(g))
        case Exists(vars, g) => require(admissible(vars, g),
          s"Substitution clash: {x}=$vars when substituting exists ${g.prettyString()}")
            Exists(vars, usubst(g))

        case BoxModality(p, g) => require(admissible(catVars(usubst(p)).bv, g),
          s"Substitution clash: BV(sigma a)=${catVars(usubst(p)).bv} when substituting [${p.prettyString()}]${g.prettyString()}")
            BoxModality(usubst(p), usubst(g))
        case DiamondModality(p, g) => require(admissible(catVars(usubst(p)).bv, g),
          s"Substitution clash: BV(sigma a)=${catVars(usubst(p)).bv} when substituting <${p.prettyString()}>${g.prettyString()}")
            DiamondModality(usubst(p), usubst(g))
      }
    } catch {
      case ex: IllegalArgumentException =>
        throw new SubstitutionClashException(ex.getMessage, this, f, f.prettyString()).initCause(ex)
    }
  }

  // uniform substitution on programs
  private[core] def usubst(p: Program): Program = {
    try {
      p match {
        case a: ProgramConstant if subsDefs.exists(_.n == a) =>
          subsDefs.find(_.n == a).get.t.asInstanceOf[Program]
        case a: ProgramConstant if !subsDefs.exists(_.n == a) => a
        case Assign(x: Variable, e) => Assign(x, usubst(e))
        case Assign(xp@Derivative(_, x: Variable), e) => Assign(xp, usubst(e))
        case NDetAssign(x: Variable) => NDetAssign(x)
        case Test(f) => Test(usubst(f))
        case ode: ContEvolveProgram =>
          // redundant with the checks on NFContEvolve in usubst(ode, primed)
          require(admissible(scala.collection.immutable.Seq(primedVariables(ode).toSeq: _*), ode),
            s"Substitution clash in ODE: {x}=${primedVariables(ode)} when substituting ${ode.prettyString()}")
          usubstODE(ode, primedVariables(ode))
        case Choice(a, b) => Choice(usubst(a), usubst(b))
        case Sequence(a, b) => require(admissible(catVars(usubst(a)).bv, b),
          s"Substitution clash: BV(sigma a)=${catVars(usubst(a)).bv} when substituting ${a.prettyString()} ; ${b.prettyString()}")
          Sequence(usubst(a), usubst(b))
        case Loop(a) => require(admissible(catVars(usubst(a)).bv, a),
          s"Substitution clash: BV(sigma a)=${catVars(usubst(a)).bv} when substituting ${a.prettyString()} *")
          Loop(usubst(a))
      }
    } catch {
      case ex: IllegalArgumentException =>
        throw new SubstitutionClashException(ex.getMessage, this, p, p.toString()).initCause(ex)
    }
  }

  private def usubstODE(ode: ContEvolveProgram, primed: Set[NamedSymbol]): ContEvolveProgram = ode match {
    case ContEvolveProduct(a, b) => ContEvolveProduct(usubstODE(a, primed), usubstODE(b, primed))
    case NFContEvolve(v, dv: Derivative, t, h) =>
      require(admissible(scala.collection.immutable.Seq(primed.toSeq: _*), t),
        s"Substitution clash in ODE: {x}=$primed clash with ${t.prettyString()}")
      require(admissible(scala.collection.immutable.Seq(primed.toSeq: _*), h),
        s"Substitution clash in ODE: {x}=$primed clash with ${h.prettyString()}")
      if (v.isEmpty) NFContEvolve(v, dv, usubst(t), usubst(h))
      else throw new UnknownOperatorException("Check implementation whether passing v is correct.", ode)
    case IncompleteSystem(s) => usubstODE(s, primed)
    case CheckedContEvolveFragment(s) => usubstODE(s, primed)
    case c: ContEvolveProgramConstant if  subsDefs.exists(_.n == c) =>
      val repl = subsDefs.find(_.n == c).get.t
      repl match {
        case replODE: ContEvolveProgram => replODE
        case _ => throw new IllegalArgumentException("Can only substitute continuous programs for " +
          s"continuous program constants: $repl not allowed for $c")
      }
    case c: ContEvolveProgramConstant if !subsDefs.exists(_.n == c) => c
    case _: EmptyContEvolveProgram => ode
  }
  
  def apply(s: Sequent): Sequent = {
    try {
      Sequent(s.pref, s.ante.map(apply), s.succ.map(apply))
    } catch {
      case ex: IllegalArgumentException =>
        throw new SubstitutionClashException(ex.getMessage, this, null, s.toString()).initCause(ex)
    }
  }

  // check whether this substitution is U-admissible for an expression with the given occurrences of functions/predicates/program constants
  private def admissible(U: SetLattice[NamedSymbol], occurrences: Set[NamedSymbol]) : Boolean = {
    // if  no function symbol f in sigma with FV(sigma f(.)) /\ U != empty
    // and no predicate symbol p in sigma with FV(sigma p(.)) /\ U != empty
    // occurs in theta (or phi or alpha)
    def intersectsU(sigma: SubstitutionPair): Boolean = (sigma.t match {
        case t: Term => sigma.n match {
          case Apply(_, Anything) => SetLattice.bottom[NamedSymbol]
          // if ever extended with f(x,y,z): freeVariables(t) -- {x,y,z}
          case _ => freeVariables(t)
        }
        case f: Formula => sigma.n match {
          case ApplyPredicate(_, Anything) => SetLattice.bottom[NamedSymbol]
          // if ever extended with p(x,y,z): freeVariables(f) -- {x,y,z}
          case _ => catVars(f).fv
        }
        case p: Program => SetLattice.bottom[NamedSymbol] // programs are always admissible, since their meaning doesn't depend on state
      }).intersect(U) != SetLattice.bottom

    def nameOf(symbol: Expr): NamedSymbol = symbol match {
      case Derivative(_, v: Variable) => v // TODO check
      case ApplyPredicate(fn, _) => fn
      case Apply(fn, _) => fn
      case s: NamedSymbol => s
      case _ => throw new IllegalArgumentException(s"Unexpected ${symbol.prettyString()} in substitution pair")
    }

    subsDefs.filter(sigma => intersectsU(sigma)).map(sigma => nameOf(sigma.n)).forall(fn => !occurrences.contains(fn))
  }

  private def admissible(U: SetLattice[NamedSymbol], t: Term) : Boolean = admissible(U, fnPredPrgSymbolsOf(t))
  private def admissible(U: SetLattice[NamedSymbol], f: Formula) : Boolean = admissible(U, fnPredPrgSymbolsOf(f))
  private def admissible(U: SetLattice[NamedSymbol], p: Program) : Boolean = admissible(U, fnPredPrgSymbolsOf(p))
  private def admissible(U: scala.collection.immutable.Seq[NamedSymbol], t: Term) : Boolean = admissible(SetLattice(U.toSet), t)
  private def admissible(U: scala.collection.immutable.Seq[NamedSymbol], f: Formula) : Boolean = admissible(SetLattice(U.toSet), f)
  private def admissible(U: scala.collection.immutable.Seq[NamedSymbol], p: Program) : Boolean = admissible(SetLattice(U), p)

  private def fnPredPrgSymbolsOf(f: Formula): Set[NamedSymbol] = f match {
    case Not(g) => fnPredPrgSymbolsOf(g)
    case And(l, r) => fnPredPrgSymbolsOf(l) ++ fnPredPrgSymbolsOf(r)
    case Or(l, r) => fnPredPrgSymbolsOf(l) ++ fnPredPrgSymbolsOf(r)
    case Imply(l, r) => fnPredPrgSymbolsOf(l) ++ fnPredPrgSymbolsOf(r)
    case Equiv(l, r) => fnPredPrgSymbolsOf(l) ++ fnPredPrgSymbolsOf(r)

    case Equals(d, l, r) => fnPredPrgSymbolsOf(l) ++ fnPredPrgSymbolsOf(r)
    case NotEquals(d, l, r) => fnPredPrgSymbolsOf(l) ++ fnPredPrgSymbolsOf(r)
    case GreaterEqual(d, l, r) => fnPredPrgSymbolsOf(l) ++ fnPredPrgSymbolsOf(r)
    case GreaterThan(d, l, r) => fnPredPrgSymbolsOf(l) ++ fnPredPrgSymbolsOf(r)
    case LessEqual(d, l, r) => fnPredPrgSymbolsOf(l) ++ fnPredPrgSymbolsOf(r)
    case LessThan(d, l, r) => fnPredPrgSymbolsOf(l) ++ fnPredPrgSymbolsOf(r)

    case ApplyPredicate(fn, theta) => Set(fn) ++ fnPredPrgSymbolsOf(theta)

    case Forall(vars, phi) => fnPredPrgSymbolsOf(phi)
    case Exists(vars, phi) => fnPredPrgSymbolsOf(phi)

    case BoxModality(p, phi) => fnPredPrgSymbolsOf(p) ++ fnPredPrgSymbolsOf(phi)
    case DiamondModality(p, phi) => fnPredPrgSymbolsOf(p) ++ fnPredPrgSymbolsOf(phi)

    case True | False => Set()
  }

  private def fnPredPrgSymbolsOf(t: Term): Set[NamedSymbol] = t match {
    case Neg(s, l) => fnPredPrgSymbolsOf(l)
    case Add(s, l, r) => fnPredPrgSymbolsOf(l) ++ fnPredPrgSymbolsOf(r)
    case Subtract(s, l, r) => fnPredPrgSymbolsOf(l) ++ fnPredPrgSymbolsOf(r)
    case Multiply(s, l, r) => fnPredPrgSymbolsOf(l) ++ fnPredPrgSymbolsOf(r)
    case Divide(s, l, r) => fnPredPrgSymbolsOf(l) ++ fnPredPrgSymbolsOf(r)
    case Exp(s, l, r) => fnPredPrgSymbolsOf(l) ++ fnPredPrgSymbolsOf(r)
    case Pair(dom, l, r) => fnPredPrgSymbolsOf(l) ++ fnPredPrgSymbolsOf(r)
    case Derivative(s, e) => fnPredPrgSymbolsOf(e)
    case Apply(f, theta) => Set(f) ++ fnPredPrgSymbolsOf(theta)
    case _: Variable => Set()
    case CDot => Set(CDot)
    case Nothing => Set()
    case Anything => Set()
    case Number(_, _) => Set()
  }

  private def fnPredPrgSymbolsOf(p: Program): Set[NamedSymbol] = p match {
    case Assign(_, t) => fnPredPrgSymbolsOf(t)
    case Test(phi) => fnPredPrgSymbolsOf(phi)
    case NFContEvolve(_, _, t, h) => fnPredPrgSymbolsOf(t) ++ fnPredPrgSymbolsOf(h)
    case ContEvolveProduct(a, b) => fnPredPrgSymbolsOf(a) ++ fnPredPrgSymbolsOf(b)
    case IncompleteSystem(a) => fnPredPrgSymbolsOf(a)
    case Sequence(a, b) => fnPredPrgSymbolsOf(a) ++ fnPredPrgSymbolsOf(b)
    case Choice(a, b) => fnPredPrgSymbolsOf(a) ++ fnPredPrgSymbolsOf(b)
    case Loop(a) => fnPredPrgSymbolsOf(a)
    case c: ContEvolveProgramConstant => Set(c)
    case c: ProgramConstant => Set(c)
    case NDetAssign(_) => Set()
    case _: EmptyContEvolveProgram => Set()
  }

  // @TODO The following are the same cop&paste as in UniformSubstitution. Copy somewhere
  /**
   * Check whether the function in right matches with the function in left, i.e. they have the same head.
   */
  def sameHead(left: SubstitutionPair, right: Expr) = left.n match {
    case Apply(lf, CDot | Anything | Nothing) => right match { case Apply(rf, _) => lf == rf case _ => false }
    case ApplyPredicate(lf, CDot | Anything | Nothing) => right match { case ApplyPredicate(rf, _) => lf == rf case _ => false }
    case _ => false
  }

  /**
   * Get the unique element in c to which pred applies.
   * Protests if that element is not unique because pred applies to more than one element in c or if there is none.
   */
  private def uniqueElementOf[E](c: Iterable[E], pred: E => Boolean): E = {
    require(c.count(pred) == 1)
    c.filter(pred).head
  }
}

/******************************************************************/


/**
 * A Uniform Substitution.
 * Implementation of applying uniform substitutions to terms, formulas, programs.
 * Old implementation.
 */
sealed case class OSubstitution(l: scala.collection.immutable.Seq[SubstitutionPair]) {
  applicable

  /**
   *
   * @param source should be a tuple of substitutable things
   * @param target should be a tuple of the same dimension donating the right sides
   * @return
   */
  private def constructSubst(source: Expr, target: Expr): OSubstitution = new OSubstitution(collectSubstPairs(source, target))


  // unique left hand sides in l
  @elidable(ASSERTION) def applicable = {
    // check that we never replace n by something and then again replacing the same n by something
    val lefts = l.map(sp=>sp.n).toList
    require(lefts.distinct.size == lefts.size, "no duplicate substitutions with same substitutees " + l)
    // check that we never replace p(x) by something and also p(t) by something
    val lambdaNames = l.map(sp=>sp.n match {
      case ApplyPredicate(p:Function, _:Variable) => List(p)
      case Apply(f:Function, _:Variable) => List(f)
      case _ => Nil
      }).fold(Nil)((a,b)=>a++b)
      //@TODO check that we never replace p(x) by something and also p(t) by something
    require(lambdaNames.distinct.size == lambdaNames.size, "no duplicate substitutions with same substitutee modulo alpha-renaming of lambda terms " + l)
  }

  override def toString: String = "Subst(" + l.mkString(", ") + ")"

  private def collectSubstPairs(source: Expr, target: Expr): List[SubstitutionPair] =
    if(source != target)
      source match {
      case Pair(dom, a, b) => target match {
        case Pair(dom2, c, d) => collectSubstPairs(a, c) ++ collectSubstPairs(b, d)
        case _ => throw new IllegalArgumentException("Type error. A pair: " + source + " must not be replaced by a non pair: " + target)
      }
      case _: Variable => List(new SubstitutionPair(source, target))
      case _: PredicateConstant => List(new SubstitutionPair(source, target))
      case _: ProgramConstant => List(new SubstitutionPair(source, target))
      case _ => throw new UnknownOperatorException("Unknown base case " + source + " of sort " + source.sort, source)
    } else Nil

  def names(pairs: Seq[SubstitutionPair]): Seq[NamedSymbol] = (for(p <- pairs) yield names(p)).flatten.distinct
  def names(pair: SubstitutionPair): Seq[NamedSymbol] = (names(pair.n) ++ names(pair.t)).filter(!boundNames(pair.n).contains(_))

  /**
   * This method returns the names that are bound in the source of a substitution
   * @param n the source of a substitution
   * @return the names bound on the source side of a substitution
   * @TODO namesToBeBound or something like this for uniform substitution purposes could be a better name? Because it's not just the bound variables of a formula.
   */
  def boundNames(n: Expr): Seq[NamedSymbol] = n match {
    case ApplyPredicate(_, args) => names(args)
    case Apply(_, args) => names(args)
    case _ => Nil
  }

  /**
   * Return all the named elements in a sequent
   * @param e
   * @return
   * @TODO maybe rename to freeNames, but make naming compatible with boundNames
   */
  def names(e: Expr): scala.collection.immutable.Seq[NamedSymbol] = e match {
    case x: NamedSymbol => Vector(x)
    case x: Unary => names(x.child)
    case x: Binary => names(x.left) ++ names(x.right)
    case x: Ternary => names(x.fst) ++ names(x.snd) ++ names(x.thd)
    case x: NFContEvolve => x.vars ++ names(x.x) ++ names(x.theta) ++ names(x.f)
    case IncompleteSystem(s) => names(s)
    case x: Atom => Nil
    case IncompleteSystem(system) => names(system)
  }

  // uniform substitution on formulas
  //@TODO Use the outermost call to apply(Formula) as a wrapper that adds the full formula o as exception.inContext(o) on exception.
  def apply(f: Formula): Formula = f match {
      // homomorphic cases
    case Not(c) => Not(apply(c))
    case And(l, r) => And(apply(l), apply(r))
    case Or(l, r) => Or(apply(l), apply(r))
    case Imply(l, r) => Imply(apply(l), apply(r))
    case Equiv(l, r) => Equiv(apply(l), apply(r))

    // binding cases
    /*
     * For quantifiers just check that there is no name clash, throw an exception if there is
     */
    case Forall(vars, form) => if(vars.intersect(names(l)).isEmpty) Forall(vars, apply(form))
    else throw new SubstitutionClashException("There is a name clash in uniform substitution " + vars.map(_.prettyString()) + " and " + l + " applied to " + f.prettyString(), this, f)

    case Exists(vars, form) => if(vars.intersect(names(l)).isEmpty) Exists(vars, apply(form))
    else throw new SubstitutionClashException("There is a name clash in uniform substitution " + vars.map(_.prettyString()) + " and " + l + " applied to " + f.prettyString(), this, f)

    case x: Modality => if(x.writes.intersect(names(l)).isEmpty) x match {
      case BoxModality(p, f) => BoxModality(apply(p), apply(f))
      case DiamondModality(p, f) => DiamondModality(apply(p), apply(f))
      case _ => ???
    } else throw new SubstitutionClashException("There is a name clash in uniform substitution " + l + "\napplied to modality " + f.prettyString() + "\nwhich writes " + x.writes.map(_.prettyString()) + " leading to a clash in variables " + x.writes.intersect(names(l)).map(_.prettyString()), this, f)

    //@TODO Concise way of asserting that there can be only one
    case _: PredicateConstant => for(p <- l) { if(f == p.n) return p.t.asInstanceOf[Formula]}; return f

    // if we find a match, we bind the arguments of our match to what is in the current term
    // then we apply it to the codomain of the substitution
    case ApplyPredicate(func, arg) => for(p <- l) {
      p.n match {
        case ApplyPredicate(pf, parg) if(func == pf) => return constructSubst(parg, arg)(p.t.asInstanceOf[Formula])
        case _ =>
      }
    }; return ApplyPredicate(func, apply(arg))

    // homomorphic cases
    case Equals(d, l, r) => (l,r) match {
      case (a: Term,b: Term) => Equals(d, apply(a), apply(b))
      case _ => throw new IllegalArgumentException("Don't know how to handle case " + f)
    }
    case NotEquals(d, l, r) => (l,r) match {
      case (a: Term,b: Term) => NotEquals(d, apply(a), apply(b))
      case _ => throw new IllegalArgumentException("Don't know how to handle case" + f)
    }
    case ProgramEquals(l, r) => (l,r) match {
      case (a: Program,b: Program) => ProgramEquals(apply(a), apply(b))
      case _ => throw new IllegalArgumentException("Don't know how to handle case" + f)
    }
    case ProgramNotEquals(l, r) => (l,r) match {
      case (a: Program,b: Program) => ProgramNotEquals(apply(a), apply(b))
      case _ => throw new IllegalArgumentException("Don't know how to handle case" + f)
    }
    case GreaterThan(d, l, r) => (l,r) match {
      case (a: Term,b: Term) => GreaterThan(d, apply(a), apply(b))
      case _ => throw new IllegalArgumentException("Don't know how to handle case" + f)
    }
    case GreaterEqual(d, l, r) => (l,r) match {
      case (a: Term,b: Term) => GreaterEqual(d, apply(a), apply(b))
      case _ => throw new IllegalArgumentException("Don't know how to handle case" + f)
    }
    case LessEqual(d, l, r) => (l,r) match {
      case (a: Term,b: Term) => LessEqual(d, apply(a), apply(b))
      case _ => throw new IllegalArgumentException("Don't know how to handle case" + f)
    }
    case LessThan(d, l, r) => (l,r) match {
      case (a: Term,b: Term) => LessThan(d, apply(a), apply(b))
      case _ => throw new IllegalArgumentException("Don't know how to handle case" + f)
    }
    case x: Atom => x
    case _ => throw new UnknownOperatorException("Not implemented yet", f)
  }
  
  // uniform substitution on terms
  def apply(t: Term): Term = t match {
      // homomorphic cases
    case Neg(s, c) => Neg(s, apply(c))
    case Add(s, l, r) => Add(s, apply(l), apply(r))
    case Subtract(s, l, r) => Subtract(s, apply(l), apply(r))
    case Multiply(s, l, r) => Multiply(s, apply(l), apply(r))
    case Divide(s, l, r) => Divide(s, apply(l), apply(r))
    case Exp(s, l, r) => Exp(s, apply(l), apply(r))
    case Pair(dom, l, r) => Pair(dom, apply(l), apply(r))
    // applying uniform substitutions
    case Derivative(s, child) => for(p <- l) { if(t == p.n) return p.t.asInstanceOf[Term]}; return Derivative(s, this(child))
    case Variable(_, _, _) => for(p <- l) { if(t == p.n) return p.t.asInstanceOf[Term]}; return t
    // if we find a match, we bind the arguments of our match to what is in the current term
    // then we apply it to the codomain of the substitution
    case Apply(func, arg) => for(p <- l) {
      p.n match {
        case Apply(pf, parg) if(func == pf) => return constructSubst(parg, arg)(p.t.asInstanceOf[Term])
        case _ =>
      }
    }; return Apply(func, apply(arg))
    case x: Atom => require(!x.isInstanceOf[Variable], "variables have been substituted already"); x
    case _ => throw new UnknownOperatorException("Not implemented yet", t)
  }

  // uniform substitution on programs
  def apply(p: Program): Program = {
      require(p.writes.intersect(names(l)).isEmpty)
      p match {
        case Loop(c) => Loop(apply(c))
        case Sequence(a, b) => Sequence(apply(a), apply(b))
        case Choice(a, b) => Choice(apply(a), apply(b))
        case Parallel(a, b) => Parallel(apply(a), apply(b))
        case IfThen(a, b) => IfThen(apply(a), apply(b))
        case IfThenElse(a, b, c) => IfThenElse(apply(a), apply(b), apply(c))
        case Assign(a, b) => Assign(a, apply(b))  //@TODO assert that a is a variable (so far) and assert that a not in names(l)
        case NDetAssign(a) => p
        case Test(a) => Test(apply(a))
        case ContEvolve(a) => ContEvolve(apply(a))
        case NFContEvolve(v, x, t, f) => if(v.intersect(names(l)).isEmpty) NFContEvolve(v, x, apply(t), apply(f))
          else throw new SubstitutionClashException("There is a name clash in uniform substitution " + l + " applied on " + p + " because of quantified disturbance " + v.mkString(","), this, p)
        case x: ProgramConstant => for(pair <- l) { if(p == pair.n) return pair.t.asInstanceOf[Program]}; return p
        case _ => throw new UnknownOperatorException("Not implemented yet", p)
     }
  }
}

/**
 * Uniform Substitution Rule.
 * Applies a given uniform substitution to the given original premise (origin).
 * Pseudo application in sequent calculus to conclusion that fits to the Hilbert calculus application (origin->conclusion).
 * This rule interfaces forward Hilbert calculus rule application with backward sequent calculus pseudo-application
 * @param substitution the uniform substitution to be applied to origin.
 * @param origin the original premise, to which the uniform substitution will be applied. Thus, origin is the result of pseudo-applying this UniformSubstitution rule in sequent calculus.
 */
// uniform substitution
// this rule performs a backward substitution step. That is the substitution applied to the conclusion yields the premise
object UniformSubstitution {
  def apply(substitution: Substitution, origin: Sequent) : Rule = new UniformSubstitution(substitution, origin)

  @elidable(FINEST) private def log(msg: =>String) = {} //println(msg)

  private class UniformSubstitution(subst: Substitution, origin: Sequent) extends Rule("Uniform Substitution") {
    /**
     * check that s is indeed derived from origin via subst (note that no reordering is allowed since those operations
     * require explicit rule applications)
     * @param conclusion the conclusion in sequent calculus to which the uniform substitution rule will be pseudo-applied, resulting in the premise origin that was supplied to UniformSubstituion.
     */
    def apply(conclusion: Sequent): List[Sequent] = {
      log("---- " + subst + "\n    " + origin + "\n--> " + subst(origin) + (if(subst(origin)==conclusion) "\n==  " else "\n!=  ") + conclusion)
      val substAtOrigin = subst(origin) //just for debugging.
      if (subst(origin) == conclusion) {
        assert(alternativeAppliesCheck(conclusion), "uniform substitution application mechanisms agree")
        List(origin)
      } else {
        assert(!alternativeAppliesCheck(conclusion), "uniform substitution application mechanisms agree")
        throw new CoreException("From\n  " + origin + "\nuniform substitution\n  " + subst + "\ndid not conclude\n  " + conclusion + "\nbut instead\n  " + subst(origin))
      }
    } 
    
    private def alternativeAppliesCheck(conclusion: Sequent) : Boolean = {
      //val subst = new OSubstitution(this.subst.l)
      //val singleSideMatch = ((acc: Boolean, p: (Formula, Formula)) => {val a = subst(p._1); println("-------- Uniform " + subst + "\n" + p._1.prettyString + "\nbecomes\n" + a.prettyString + (if (a==p._2) "\nis equal to expected conclusion\n" else "\nshould have been equal to expected conclusion\n") + p._2.prettyString); a == p._2})
      val singleSideMatch = ((acc: Boolean, p: (Formula, Formula)) => { subst(p._1) == p._2})
      (conclusion.pref == origin.pref // universal prefix is identical
        && origin.ante.length == conclusion.ante.length && origin.succ.length == conclusion.succ.length  // same length makes sure zip is exhaustive
        && (origin.ante.zip(conclusion.ante)).foldLeft(true)(singleSideMatch)  // formulas in ante results from substitution
        && (origin.succ.zip(conclusion.succ)).foldLeft(true)(singleSideMatch)) // formulas in succ results from substitution
    }
  }
}

/**
 * Global Uniform Substitution Rule.
 * Applies a given uniform substitution to the given original premise (origin).
 * Pseudo application in sequent calculus to conclusion that fits to the Hilbert calculus application (origin->conclusion).
 * This rule interfaces forward Hilbert calculus rule application with backward sequent calculus pseudo-application
 * @param substitution the uniform substitution to be applied to origin.
 * @param origin the original premise, to which the uniform substitution will be applied. Thus, origin is the result of pseudo-applying this UniformSubstitution rule in sequent calculus.
 */
// uniform substitution
// this rule performs a backward substitution step. That is the substitution applied to the conclusion yields the premise
object GlobalUniformSubstitution {
  def apply(subst: GlobalSubstitution, origin: Sequent) : Rule = new GlobalUniformSubstitution(subst, origin)

  @elidable(FINEST) private def log(msg: =>String) = {} //println(msg)

  private class GlobalUniformSubstitution(subst: GlobalSubstitution, origin: Sequent) extends Rule("Uniform Substitution") {
    /**
     * check that s is indeed derived from origin via subst (note that no reordering is allowed since those operations
     * require explicit rule applications)
     * @param conclusion the conclusion in sequent calculus to which the uniform substitution rule will be pseudo-applied, resulting in the premise origin that was supplied to UniformSubstituion.
     */
    def apply(conclusion: Sequent): List[Sequent] = {
      log("---- " + subst + "\n    " + origin + "\n--> " + subst(origin) + (if(subst(origin)==conclusion) "\n==  " else "\n!=  ") + conclusion)
      val substAtOrigin = subst(origin) //just for debugging.
      if (subst(origin) == conclusion) {
        assert(alternativeAppliesCheck(conclusion), "uniform substitution application mechanisms agree")
        List(origin)
      } else {
        assert(!alternativeAppliesCheck(conclusion), "uniform substitution application mechanisms agree")
        throw new CoreException("From\n  " + origin + "\nuniform substitution\n  " + subst + "\ndid not conclude\n  " + conclusion + "\nbut instead\n  " + subst(origin))
      }
    }

    private def alternativeAppliesCheck(conclusion: Sequent) : Boolean = {
      //val subst = new OSubstitution(this.subst.l)
      //val singleSideMatch = ((acc: Boolean, p: (Formula, Formula)) => {val a = subst(p._1); println("-------- Uniform " + subst + "\n" + p._1.prettyString + "\nbecomes\n" + a.prettyString + (if (a==p._2) "\nis equal to expected conclusion\n" else "\nshould have been equal to expected conclusion\n") + p._2.prettyString); a == p._2})
      val singleSideMatch = ((acc: Boolean, p: (Formula, Formula)) => { subst(p._1) == p._2})
      (conclusion.pref == origin.pref // universal prefix is identical
        && origin.ante.length == conclusion.ante.length && origin.succ.length == conclusion.succ.length  // same length makes sure zip is exhaustive
        && (origin.ante.zip(conclusion.ante)).foldLeft(true)(singleSideMatch)  // formulas in ante results from substitution
        && (origin.succ.zip(conclusion.succ)).foldLeft(true)(singleSideMatch)) // formulas in succ results from substitution
    }
  }
}

// alpha conversion

class AlphaConversion(name: String, idx: Option[Int], target: String, tIdx: Option[Int], pos: Option[Position])
  extends Rule("Alpha Conversion") {

  import BindingAssessment._

  def apply(s: Sequent): List[Sequent] = pos match {
    case Some(p) =>
      // only allow renaming at a specific position if the name to be replaced is bound there
      // (needed for skolemization and renaming of quantified parts inside a formula)
      val formula = ExpressionTraversal.traverse(TraverseToPosition(p.inExpr, new ExpressionTraversalFunction {
        override def preF(pos: PosInExpr, f: Formula): Either[Option[StopTraversal], Formula] = f match {
          case Forall(vars, _) if vars.exists(v => v.name == name && v.index == idx) => Right(apply(f))
          case Exists(vars, _) if vars.exists(v => v.name == name && v.index == idx) => Right(apply(f))
          // if ODE binds var, then rename with stored initial value
          case BoxModality(ode: ContEvolveProgram, _) if catVars(ode).bv.exists(v => v.name == name && v.index == idx) =>
            Right(BoxModality(Assign(Variable(target, tIdx, Real), Variable(name, idx, Real)), apply(f)))
          // if loop binds var, then rename with stored initial value
          case BoxModality(Loop(a), _) if catVars(a).bv.exists(v => v.name == name && v.index == idx) =>
            Right(BoxModality(Assign(Variable(target, tIdx, Real), Variable(name, idx, Real)), apply(f)))
          case _ => Left(Some(ExpressionTraversal.stop))
        }
      }), s(p)) match {
        case Some(f) => f
        case None => throw new IllegalArgumentException("Alpha renaming at position only applicable on quantifiers")
      }
      if (p.isAnte) List(Sequent(s.pref, s.ante :+ formula, s.succ))
      else List(Sequent(s.pref, s.ante, s.succ :+ formula))
    case None =>
      val ante = for (f <- s.ante) yield BoxModality(Assign(Variable(target, tIdx, Real), Variable(name, idx, Real)), apply(f))
      val succ = for (f <- s.succ) yield BoxModality(Assign(Variable(target, tIdx, Real), Variable(name, idx, Real)), apply(f))
      List(Sequent(s.pref, ante, succ))
  }

  def apply(f: Formula): Formula = {
    require(!Helper.names(f).exists(v => v.name == target && v.index == tIdx), s"Name ${target}_$tIdx not fresh in $f")
    rename(f)
  }

  def rename(f: Formula): Formula = f match {
    case Not(g) => Not(rename(g))
    case And(l, r) => And(rename(l), rename(r))
    case Or(l, r) => Or(rename(l), rename(r))
    case Imply(l, r) => Imply(rename(l), rename(r))
    case Equiv(l, r) => Equiv(rename(l), rename(r))

    case Equals(d, l, r) => Equals(d, rename(l), rename(r))
    case NotEquals(d, l, r) => NotEquals(d, rename(l), rename(r))
    case GreaterEqual(d, l, r) => GreaterEqual(d, rename(l), rename(r))
    case GreaterThan(d, l, r) => GreaterThan(d, rename(l), rename(r))
    case LessEqual(d, l, r) => LessEqual(d, rename(l), rename(r))
    case LessThan(d, l, r) => LessThan(d, rename(l), rename(r))

    case ApplyPredicate(fn, theta) => ApplyPredicate(fn, rename(theta))

    case Forall(vars, phi) => renameQuantifier(vars, phi, Forall.apply)
    case Exists(vars, phi) => renameQuantifier(vars, phi, Exists.apply)

    case BoxModality(p, phi) => BoxModality(rename(p), rename(phi))
    case DiamondModality(p, phi) => DiamondModality(rename(p), rename(phi))

    case True | False => f
  }

  def rename(t: Term): Term = t match {
    case Neg(s, l) => Neg(s, rename(l))
    case Add(s, l, r) => Add(s, rename(l), rename(r))
    case Subtract(s, l, r) => Subtract(s, rename(l), rename(r))
    case Multiply(s, l, r) => Multiply(s, rename(l), rename(r))
    case Divide(s, l, r) => Divide(s, rename(l), rename(r))
    case Exp(s, l, r) => Exp(s, rename(l), rename(r))
    case Pair(dom, l, r) => Pair(dom, rename(l), rename(r))
    case Derivative(s, e) => Derivative(s, rename(e))
    case Apply(f, theta) => Apply(f, rename(theta))
    case x: Variable => renameVar(x)
    case CDot => CDot
    case Nothing => Nothing
    case x@Number(_, _) => x
  }

  def rename(p: Program): Program = p match {
    case Assign(v: Variable, t) => Assign(renameVar(v), rename(t))
    case Assign(Derivative(s, v: Variable), t) => Assign(Derivative(s, renameVar(v)), rename(t))
    case NDetAssign(v: Variable) => NDetAssign(renameVar(v))
    case Test(phi) => Test(rename(phi))
    case ode: ContEvolveProgram => renameODE(ode)
    case Sequence(a, b) => Sequence(rename(a), rename(b))
    case Choice(a, b) => Choice(rename(a), rename(b))
    case Loop(a) => Loop(rename(a))
  }

  private def renameODE(p: ContEvolveProgram): ContEvolveProgram = p match {
      case NFContEvolve(v, Derivative(dd, Variable(n, i, d)), t, h) if n == name && i == idx =>
        NFContEvolve(v, Derivative(dd, Variable(target, tIdx, d)), rename(t), rename(h))
      case NFContEvolve(v, dv@Derivative(_, Variable(n, i, _)), t, h) if n != name || i != idx =>
        NFContEvolve(v, dv, rename(t), rename(h))
      case ContEvolveProduct(a, b) => ContEvolveProduct(renameODE(a), renameODE(b))
      case _: EmptyContEvolveProgram => p
      case IncompleteSystem(a) => IncompleteSystem(renameODE(a))
      case _: ContEvolveProgramConstant => p
  }

  private def renameVar(e: Variable): Variable =
    if (e.name == name && e.index == idx) Variable(target, tIdx, e.sort)
    else e

  private def rename(e: NamedSymbol): NamedSymbol = e match {
    case v: Variable => renameVar(v)
    case _ => throw new IllegalArgumentException("Alpha conversion only supported for variables so far")
  }

  private def renameQuantifier[T <: Quantifier](vars: Seq[NamedSymbol], phi: Formula,
                                                factory: (Seq[NamedSymbol], Formula) => T) = {
    vars.find(v => v.name == name && v.index == idx) match {
      case Some(oldVar) => factory(vars.map(rename), rename(phi))
      case None => factory(vars, rename(phi))
    }
  }
}

// skolemize
/**
 * Skolemization assumes that the names of the quantified variables to be skolemized are unique within the sequent.
 * This can be ensured by finding a unique name and renaming the bound variable through alpha conversion.
 */
class Skolemize(p: Position) extends PositionRule("Skolemize", p) {
  require(p.inExpr == HereP, "Can only skolemize top level formulas")
  import Helper._
  override def apply(s: Sequent): List[Sequent] = {
    // Other names underneath p are forbidden as well, but the variables v that are to be skolemized are fine as Skolem function names.
    val vars = namesIgnoringPosition(s, p)
    val (v,phi) = s(p) match {
      case Forall(qv, qphi) if !p.isAnte => (qv,qphi)
      case Exists(qv, qphi) if p.isAnte => (qv,qphi)
      case _ => throw new InapplicableRuleException("Skolemization in antecedent is only applicable to existential quantifiers/in succedent only to universal quantifiers", this, s)
    }
    if (vars.intersect(v.toSet).nonEmpty)
      throw new SkolemClashException("Variables to be skolemized should not appear anywhere else in the sequent. AlphaConversion required.",
        vars.intersect(v.toSet))
    List(if (p.isAnte) Sequent(s.pref ++ v, s.ante.updated(p.index, phi), s.succ)
         else Sequent(s.pref ++ v, s.ante, s.succ.updated(p.index, phi)))
  }
}

/**
 * Assignment as equation
 * Assumptions: We assume that the variable has been made unique through alpha conversion first. That way, we can just
 * replace the assignment by an equation without further checking
 * @TODO Review. Will turn into an axiom.
 */
class AssignmentRule(p: Position) extends PositionRule("AssignmentRule", p) {
  import Helper._
  override def apply(s: Sequent): List[Sequent] = {
    // we need to make sure that the variable does not occur in any other formula in the sequent
    val vars = namesIgnoringPosition(s, p)
    // TODO: we have to make sure that the variable does not occur in the formula itself
    // if we want to have positions different from HereP
    require(p.inExpr == HereP, "we can only deal with assignments on the top-level for now")
    val (exp, res, rhs) = s(p) match {
      case BoxModality(Assign(l, r), post) => (l, Imply(Equals(l.sort, l, r), post), r)
      case DiamondModality(Assign(l, r), post) => (l, Imply(Equals(l.sort, l, r), post), r)
      case _ => throw new InapplicableRuleException("The assigment rule is only applicable to box and diamond modalities" +
        "containing a single assignment", this, s)
    }
    // check that v is not contained in any other formula
    val rhsVars = names(rhs)
    val v = exp match {
      case x: Variable if(!vars.contains(x) && !rhsVars.contains(x)) => x
      case x: Variable if(vars.contains(x) || rhsVars.contains(x)) => throw new IllegalArgumentException("Varible " + x + " is not unique in the sequent")
      case _ => throw new UnknownOperatorException("Assignment handling is only implemented for varibles right now, not for " + exp.toString(), exp) //?
    }

    List(if(p.isAnte) Sequent(s.pref :+ v, s.ante.updated(p.index, res), s.succ) else Sequent(s.pref :+ v, s.ante, s.succ.updated(p.index, res)))
  }
}

/**
 * @author Nathan Fulton
 * @param p
 */
class DerivativeAssignmentRule(p: Position) extends PositionRule("AssignmentRule", p) {

  import Helper._

  override def apply(s: Sequent): List[Sequent] = {
    // we need to make sure that the variable does not occur in any other formula in the sequent
    val vars = namesIgnoringPosition(s, p)

    // TODO: we have to make sure that the variable does not occur in the formula itself
    // if we want to have positions different from HereP
    require(p.inExpr == HereP, "we can only deal with assignments on the top-level for now")

    //exp = the left-hand side of the assignment (i.e., the x' in x' := t).
    //res = result of assignment (i.e., x'=t -> post)
    //rhs = the right-hnd side of the assignment.
    val (exp, res, rhs) = s(p) match {
      case BoxModality(Assign(l:Derivative, r), post) => (l, Imply(Equals(l.sort, l, r), post), r)
      case DiamondModality(Assign(l:Derivative, r), post) => (l, Imply(Equals(l.sort, l, r), post), r)
      case _ => throw new InapplicableRuleException("The assigment rule is only applicable to box and diamond modalities" +
        "containing a single assignment", this, s)
    }

    // check that v is not contained in any other formula
    val rhsVars = names(rhs)
    val v: Variable = exp match {
      case Derivative(dsort, Variable(name, idx, sort)) => {
        val x: Variable = Variable(name, idx, sort)
        if(!vars.contains(x) && !rhsVars.contains(x))
          x
        else if(vars.contains(x) || rhsVars.contains(x))
          throw new IllegalArgumentException("Varible " + x + " is not unique in the sequent")
        else
          ???
      }
      case _ => throw new UnknownOperatorException("Assignment handling is only implemented for varibles right now, not for " + exp.toString(), exp) //?
    }

    //Return the sequent with the appropriate position updated to the result (i.e., res).
    List(
      if (p.isAnte)
        Sequent(s.pref :+ v, s.ante.updated(p.index, res), s.succ)
      else
        Sequent(s.pref :+ v, s.ante, s.succ.updated(p.index, res)))
  }
}

// @TODO Review. Will turn into axiom QuantifierAbstraction.
class AbstractionRule(pos: Position) extends PositionRule("AbstractionRule", pos) {
  override def apply(s: Sequent): List[Sequent] = {
    val fn = new ExpressionTraversalFunction {
      val factory: (Seq[NamedSymbol], Formula) => Quantifier = if (pos.isAnte) Exists.apply else Forall.apply
      override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = e match {
          case BoxModality(prg, f) => Right(factory(prg.writes, f))
          case DiamondModality(prg, f) => Right(factory(prg.writes, f))
          case _ => throw new InapplicableRuleException("The abstraction rule is not applicable to " + e, AbstractionRule.this, s)
      }
    }
    ExpressionTraversal.traverse(TraverseToPosition(pos.inExpr, fn), s(pos)) match {
      case Some(x: Formula) => if(pos.isAnte) List(Sequent(s.pref, s.ante :+ x, s.succ)) else List(Sequent(s.pref, s.ante, s.succ :+ x))
      case _ => throw new InapplicableRuleException("No abstraction possible for " + s(pos), this, s)
    }
  }
}

/*********************************************************************************
 * Rules for derivatives that are not currently expressible as axioms
 *********************************************************************************
 */
object DeriveConstant {
  def apply(t: Term): Rule = new DeriveConstant(t)
}
/**
 * Derive a numeral / number constant n.
 * Observe that derivative n'=0 is added to top-level, which is sound, because number constants are constants, so rigid.
 */
class DeriveConstant(t: Term) extends Rule("Derive Constant") {
  val Derivative(Real, Number(Real, n)) = t
  override def apply(s: Sequent): List[Sequent] =
    List(s.glue(Sequent(s.pref, IndexedSeq(Equals(Real, t, Number(Real, 0))), IndexedSeq())))
}

object DeriveMonomial {
  def apply(t: Term): Rule = new DeriveMonomial(t)
}

//@TODO Inaccurate for n=0, because unlike the input, the result would be undefined for base=0.
class DeriveMonomial(t: Term) extends Rule("Derive Monomial") {
  val Derivative(Real, Exp(Real, base, Number(Real, n))) = t
  override def apply(s: Sequent): List[Sequent] =
    List(s.glue(Sequent(s.pref, IndexedSeq(Equals(Real, t, Multiply(Real, Number(n), Exp(Real, base, Number(n - 1))))), IndexedSeq())))
}

// the following rules will turn into axioms

//@TODO Removal suggested since better axiom exists.
class DiffCut(p: Position, h: Formula) extends PositionRule("Differential Cut", p) {
  require(!p.isAnte)
  override def apply(s: Sequent): List[Sequent] = {
    val prgFn = new ExpressionTraversalFunction {
      override def postP(pos: PosInExpr, prg: Program) = prg match {
        case ContEvolveProduct(NFContEvolve(v, x, theta, hh), e: EmptyContEvolveProgram) =>
          Right(ContEvolveProduct(NFContEvolve(v, x, theta, And(hh, h)), e))
        case ContEvolve(f) => Right(ContEvolve(And(f, h)))
        case _ => super.postP(pos, prg)
      }
    }
    val fn = new ExpressionTraversalFunction {
      override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = e match {
        case BoxModality(ev@ContEvolve(evolve), f) => Right(And(BoxModality(ev, h),
          BoxModality(ContEvolve(And(evolve, h)), f)))
        case BoxModality(ev@NFContEvolve(vs, x, t, dom), f) => Right(And(BoxModality(ev, h),
          BoxModality(NFContEvolve(vs, x, t, And(dom, h)), f)))
        // append to evolution domain constraint of rightmost (NF)ContEvolve in product
        case BoxModality(ev@ContEvolveProduct(a, b), f) =>
          val rightMostCut = ExpressionTraversal.traverse(HereP, prgFn, ev) match {
            case Some(prg) => prg
            case None => throw new IllegalArgumentException("Unexpected program type at rightmost position in " +
              "ContEvolveProduct")
          }
          Right(And(BoxModality(ev, h), BoxModality(rightMostCut, f)))
        case _ => ???
      }
    }
    ExpressionTraversal.traverse(TraverseToPosition(p.inExpr, fn), s(p)) match {
      case Some(f) => List(s.updated(p, f))
      case a => throw new IllegalStateException("Unexpected traversal result " + a)
    }
  }
}

/**
 * [x' = t, H]p <- (H -> [x' = t]p')
 * @author Jan
 *         @author nfulton added case where there's no domain constraint.
 * @param p
 * @TODO Looks unsound. Removal suggested. Missing p. And occurrence constraints do not seem to be enforced.
 */
class DiffInd(p: Position) extends PositionRule("Differential Induction", p) {
  override def apply(s: Sequent): List[Sequent] = {
    val fn = new ExpressionTraversalFunction {
      override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = e match {
        case BoxModality(ev@ContEvolve(And(Equals(s, xp@Derivative(_, _), t), h)), f) =>
          //TODO: require that t and h do not contain derivatives
          Right(BoxModality(ev, Imply(h, BoxModality(Assign(xp, t), FormulaDerivative(f)))))
        case BoxModality(evolution@ContEvolve(Equals(s, xp@Derivative(_, _), t)), f) =>
          //TODO: require that t and h do not contain derivatives
          Right(
            BoxModality(evolution, BoxModality(Assign(xp, t), FormulaDerivative(f)))
          )
        case _ => ???
      }
    }
    ExpressionTraversal.traverse(TraverseToPosition(p.inExpr, fn), s(p)) match {
      case Some(f) => List(s.updated(p, f))
      case a => throw new IllegalStateException("Unexpected traversal result " + a)
    }
  }
}

/*********************************************************************************
 * Block Quantifier Decomposition
 *********************************************************************************
 */

object DecomposeQuantifiers {
  def apply(p: Position): Rule = new DecomposeQuantifiers(p)
}

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
 * Lemma Mechanism Rules
 *********************************************************************************
 */

// Lookup Lemma (different justifications: Axiom, Lemma with proof, Oracle Lemma)


//@TODO Review
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
      case _ => None
    }
  }
}

/*********************************************************************************
 * Helper code
 *********************************************************************************
 */

//@TODO Review
object Helper {
  /**
   * Collect all NamedSymbols occurring in a formula/term/program/game
   */
  def names(s: Sequent): Set[NamedSymbol] =  Set() ++ (s.ante ++ s.succ).map((f: Formula) => names(f)).flatten

  def names[A: FTPG](a: A): Set[NamedSymbol] = names(a, false)

  /**
   * Collect all NamedSymbols occurring in a formula/term/program/game ignoring (potentially) bound ones
   */
  def freeNames[A: FTPG](a: A): Set[NamedSymbol] = names(a, true)

  /**
   * Collect all NamedSymbols occurring in a formula/term/program/game ignoring those that definitely bound
   * That is, we add all those written by modalities just to be sure to capture all those that might be read
   */
  def certainlyFreeNames[A: FTPG](a: A): Set[NamedSymbol] = names(a, true, true)

  /**
   * Collect all NamedSymbols occurring in a formula/term/program/game
   * @param a
   * @param onlyFree
   * @tparam A
   * @return
   */
  def names[A: FTPG](a: A, onlyFree: Boolean, certainlyFree: Boolean = false): Set[NamedSymbol] = {
    var vars: Set[NamedSymbol] = Set.empty
    val fn = new ExpressionTraversalFunction {
      override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = {
        e match {
          case x: Variable => vars += x
          case x: ProgramConstant => vars += x
          case Apply(f, _) => vars += f
          case _ =>
        }
        Left(None)
      }

      override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = {
        e match {
          case x: PredicateConstant => vars += x
          case ApplyPredicate(f, _) => vars += f
          case _ =>
        }
        Left(None)
      }

      override def postF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = {
        if(onlyFree) {
          e match {
            case Forall(v, f) => vars = vars.filter(!v.contains(_))
            case Exists(v, f) => vars = vars.filter(!v.contains(_))
            case x: Modality if(!certainlyFree) => vars = vars.filter(!x.writes.contains(_))
            case _ =>
          }
        }
        Left(None)
      }
    }
    ExpressionTraversal.traverse(fn, a)
    vars
  }

  /**
   * Finds all names in a sequent, ignoring those in the formula at top-level position p.
   */
  def namesIgnoringPosition(s: Sequent, p: Position): Set[NamedSymbol] = {
    require(p.inExpr == HereP, "namesIgnoringPosition only implemented for top-level positions HereP");
    var vars: Set[NamedSymbol] = Set.empty
    for(i <- 0 until s.ante.length) {
      if(!(p.isAnte && i == p.getIndex)) {
        vars ++= names(s.ante(i))
      }
    }
    for(i <- 0 until s.succ.length) {
      if(!(!p.isAnte && i == p.getIndex)) {
        vars ++= names(s.succ(i))
      }
    }
    vars
  }


}

// vim: set ts=4 sw=4 et:
