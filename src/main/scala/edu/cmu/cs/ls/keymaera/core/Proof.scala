/**
 * Sequent prover, proof rules, and axioms of KeYmaera
 * @author Jan-David Quesel
 * @author aplatzer
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

  /** 
   * Represents a deduction step in a proof using the indicated rule which leads to the given conjunctive list of subgoals.
   * @TODO Is there a way of proctecting constructor access so that only ProofNode.apply can construct ProofSteps?
   * @param goal - parent of the step
   * @param subgoals - children of the step
   */
  sealed case class ProofStep(rule : Rule, goal : ProofNode, subgoals : scala.collection.immutable.List[ProofNode], tacticInfo: ProofStepInfo = new ProofStepInfo(Map())) {
    justifiedByProofRule
    @elidable(ASSERTION) def justifiedByProofRule = {
      // println("Checking " + this)
      // println("Reapply  " + rule(goal.sequent))
      require(rule(goal.sequent) == subgoals.map(_.sequent), "ProofStep " + this + " is justified by said proof rule application")
      // println("Checked  " + this)
    }

  }

  class ProofStepInfo(var infos: Map[String, String])
  
  sealed class ProofNode protected (val sequent : Sequent, val parent : ProofNode) {

    @volatile private[this] var alternatives : List[ProofStep] = Nil

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
    def children: scala.collection.immutable.List[ProofStep] = {
      checkInvariant
      alternatives
    }

    def hasAlternative : Boolean = alternatives != Nil
    def nextAlternative : ProofStep = {
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
    final def apply(rule : Rule) : ProofStep = {
      // ProofNodes for the respective sequents resulting from applying rule to sequent.
      val subgoals = rule(sequent).map(new ProofNode(_, this))
      val proofStep = ProofStep(rule, this, subgoals)
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
      children.map((f: ProofStep) =>  f.subgoals.foldLeft(true)(_ && _.isClosed())).contains(true)
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
  override def toString: String = name + " at " + pos + " assumtion at " + aPos
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
  private def loadAxioms: Map[String, Formula] = {
    var m = new HashMap[String, Formula]
    val a = ProgramConstant("a")
    val b = ProgramConstant("b")
    val p = PredicateConstant("p")
    val pair = ("[++] choice", Equiv(BoxModality(Choice(a, b), p),And(BoxModality(a, p), BoxModality(b, p))))
    m = m + pair
    
    val aA = ProgramConstant("a")
    val aB = ProgramConstant("b")
    val aP = PredicateConstant("p")
    val pair2 = ("[;] compose", Equiv(BoxModality(Sequence(aA, aB), aP), BoxModality(aA, BoxModality(aB, aP))))
    m = m + pair2
    
    // [?H]p <-> (H -> p)
    val aH = PredicateConstant("H")
    val pair3 = ("[?] test", Equiv(BoxModality(Test(aH), aP), Imply(aH, aP)))
    m = m + pair3

    val x = Variable("x", None, Real)
    val t = Variable("t", None, Real)
    val p1 = Function("p", None, Real, Bool)
    val pair4 = ("Quantifier Instantiation", Imply(Forall(Seq(x), ApplyPredicate(p1, x)), ApplyPredicate(p1, t)))
    m = m + pair4
    
    val pair5 = ("I induction", Imply(And(p, BoxModality(Loop(a), Imply(p, BoxModality(a, p)))), BoxModality(Loop(a), p)))
    m = m + pair5

    val aQ = PredicateConstant("q")
    //[a](p->q) -> (([a]p) -> ([a]q))
    val pair6 = ("K modal modus ponens", Imply(BoxModality(aA, Imply(aP, aQ)), Imply(BoxModality(aA, aP), BoxModality(aA, aQ))))
    m = m + pair6
    
    val pair7 = ("[:*] assignment", Equiv(BoxModality(NDetAssign(x), ApplyPredicate(p1, x)), Forall(Seq(x), ApplyPredicate(p1, x))))
    m = m + pair7
    
    //[x:=t]p(x) <-> \forall x . (x=t -> p(x))
    val pair8 = ("[:=] assignment equal", Equiv(BoxModality(Assign(x, t), ApplyPredicate(p1, x)), Forall(Seq(x), Imply(Equals(Real, x,t), ApplyPredicate(p1, x)))))
    m = m + pair8

    // val y = Variable("y", None, Real)
    // //[x:=t]p(x) <-> \forall y . (y=t -> p(y))
    // val pair8 = ("[:=] assignment equal", Equiv(BoxModality(Assign(x, t), ApplyPredicate(p1, x)), Forall(Seq(y), Imply(Equals(Real, y,t), ApplyPredicate(p1, y)))))
    // m = m + pair8
    
    m
  }

  private def loadAxiomFile: Map[String, Formula] = {
    val parser = new KeYmaeraParser(false)
    val alp = parser.ProofFileParser
    val src = io.Source.fromFile("src/main/scala/edu/cmu/cs/ls/keymaera/core/axioms.key.alp").mkString
    val res = alp.runParser(src)
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
 */
sealed class SubstitutionPair (val n: Expr, val t: Expr) {
  applicable
  // identity substitution would be correct but is usually unintended
  //require(n != t, "Unexpected identity substitution " + n + " by equal " + t)
  
  @elidable(ASSERTION) def applicable = {
    if (!(n != t)) println("INFO: Unexpected identity substitution " + n + " by equal " + t + "\n(non-critical, indicates possible tactics inefficiency)")
    require(n.sort == t.sort, "Sorts have to match in substitution pairs: " + n.sort + " != " + t.sort)
    require(n match {
      case _:Variable => true
      case _:PredicateConstant => true
      case _:ProgramConstant => true
      case Derivative(_, _:Variable) => true
      case ApplyPredicate(_:Function, _:Variable) => true
      case Apply(_:Function, _:Variable) => true
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


/**
 * A Uniform Substitution.
 * Implementation of applying uniform substitutions to terms, formulas, programs.
 * Explicit construction computing bound variables on the fly.
 * Used for UniformSubstitution rule.
 * @author aplatzer
 */
sealed case class Substitution(l: scala.collection.immutable.Seq[SubstitutionPair]) {
  applicable

  /**
   * @param rarg the argument in the substitution.
   * @param instArg the argument to instantiate rarg with in the occurrence.
   */
  private def instantiate(rarg: Term, instArg: Term) = new Substitution(List(new SubstitutionPair(rarg, instArg)))

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
  
  @elidable(FINEST-1) private def log(msg: =>String) {}  //= println(msg)
  

  override def toString: String = "Subst(" + l.mkString(", ") + ")"

  // helper

  /**
   * The set of all (may) free variables whose value t depends on (syntactically).
   */
  def freeVariables(t: Term) : Set[NamedSymbol] = t match {
    // homomorphic cases
    case Neg(s, l) => freeVariables(l)
    case Add(s, l, r) => freeVariables(l) ++ freeVariables(r)
    case Subtract(s, l, r) => freeVariables(l) ++ freeVariables(r)
    case Multiply(s, l, r) => freeVariables(l) ++ freeVariables(r)
    case Divide(s, l, r) => freeVariables(l) ++ freeVariables(r)
    case Exp(s, l, r) => freeVariables(l) ++ freeVariables(r)
    case Pair(dom, l, r) => freeVariables(l) ++ freeVariables(r)
    // base cases
    case x:Variable => Set(x)
    case Derivative(s, e) => freeVariables(e)
    case Apply(f, arg) => Set(f) ++ freeVariables(arg)
    case x: Atom => require(!x.isInstanceOf[Variable], "variables have been substituted already"); Set.empty
  }
  
  private def freeVariables(u: Set[NamedSymbol], t: Term) : Set[NamedSymbol] = freeVariables(t)--u

  /**
   * The set of all (may) free variables whose value f depends on (syntactically).
   */
  def freeVariables(f: Formula) : Set[NamedSymbol] = freeVariables(Set.empty[NamedSymbol], f)

  private def freeVariables(u: Set[NamedSymbol], f: Formula) : Set[NamedSymbol] = f match {
    // homomorphic cases
  case Not(g) => freeVariables(u, g)
  case And(l, r) => freeVariables(u, l) ++ freeVariables(u, r)
  case Or(l, r) => freeVariables(u, l) ++ freeVariables(u, r)
  case Imply(l, r) => freeVariables(u, l) ++ freeVariables(u, r)
  case Equiv(l, r) => freeVariables(u, l) ++ freeVariables(u, r)

  case Equals(d, l, r) => freeVariables(l) ++ freeVariables(r)
  case NotEquals(d, l, r) => freeVariables(l) ++ freeVariables(r)
  case GreaterEqual(d, l, r) => freeVariables(l) ++ freeVariables(r)
  case GreaterThan(d, l, r) => freeVariables(l) ++ freeVariables(r)
  case LessEqual(d, l, r) => freeVariables(l) ++ freeVariables(r)
  case LessThan(d, l, r) => freeVariables(l) ++ freeVariables(r)

  // binding cases add bound variables to u
  case Forall(vars, g) => freeVariables(u ++ vars, g)
  case Exists(vars, g) => freeVariables(u ++ vars, g)

  case BoxModality(p, g) => val (mb,v,fv) = freeVariables(u, p); fv++freeVariables(u++mb, g)
  case DiamondModality(p, g) => val (mb,v,fv) = freeVariables(u, p); fv++freeVariables(u++mb, g)

  // base cases
  case p: PredicateConstant => Set(p)
  case ApplyPredicate(p, arg) => Set(p) ++ freeVariables(arg)
  case x: Atom => ???
  case _ => throw new UnknownOperatorException("Not implemented", f)
  }

  /**
   * Returns set of symbols bound by p (must bound = definitely written), (may bound = possibly written), and set of symbols free in p (may free = possibly read).
   * @TODO In principle we could also compute must free, but that doesn't seem useful.
   */
  private def freeVariables(u: Set[NamedSymbol], p:Program) : (Set[NamedSymbol], Set[NamedSymbol], Set[NamedSymbol]) = {p match {
    case Choice(a, b) => val (mv,v,fv)=freeVariables(u,a); val (mw,w,fw)=freeVariables(u,b); (mv.intersect(mw), v++w, fv++fw)
    case Sequence(a, b) => {val (mv,v,fv)=freeVariables(u,a); val (mw,w1,fw)=freeVariables(mv,b); val (mw2,w,fw2)=freeVariables(v,b); 
      assert(mw.subsetOf(mw2), "must bound monotonicity");
      assert(fw2.subsetOf(fw), "free variable antitonicity");
      assert(w1.subsetOf(w), "may bound monotonicity");
      (mw, w, fv++fw)
    }
    case Loop(a) => val (mv,v,fv)=freeVariables(u, a); (u,v,fv)
    case Test(f) => (u, u, freeVariables(u,f))
    case Assign(x:Variable, e) => (u+x, u+x, freeVariables(u, e))
    case NDetAssign(x:Variable) => (u+x, u+x, Set.empty)
    case NFContEvolve(v, x:Variable, e, h) => (u+x,u+x,
      Set(x) ++ freeVariables(u+x, e) ++ freeVariables(u+x, h))
    
    //@TODO check implementation
    case a: ProgramConstant => (u, u, Set.empty)
    case _ => throw new UnknownOperatorException("Not implemented", p)
  }} //@TODO ensuring (r=>{val (mv,v,fv)=r; u.subsetOf(mv) && mv.subsetOf(v)})

  // uniform substitution on terms
  def apply(t: Term): Term = {
    try {
      usubst(Set.empty, t)
    } catch {
      case ex: SubstitutionClashException => throw ex.inContext(t.prettyString)
    }
  }
  
  /**
   * Return replacement t after checking for clashes with names in u.
   */
  private def clashChecked(u: Set[NamedSymbol], original: Term, t: Term) : Term = {
    if (freeVariables(t).intersect(u).isEmpty) t
    else throw new SubstitutionClashException("Clash in uniform substitution because free variables " + freeVariables(t).intersect(u).map(_.prettyString) + " have been bound when applying replacement " + t.prettyString, this, original)
  }
  /**
   * Return replacement f after checking for clashes with names in u.
   */
  private def clashChecked(u: Set[NamedSymbol], original:Formula, f: Formula) : Formula = {
    if (freeVariables(f).intersect(u).isEmpty) f
    else throw new SubstitutionClashException("Clash in uniform substitution because free variables " + freeVariables(f).intersect(u).map(_.prettyString) + " have been bound when applying replacement " + f.prettyString, this, original)
  }
  

  /**
   * @param u the set of taboo symbols that would clash substitutions if they occurred since they have been bound outside.
   */
  private def usubst(u: Set[NamedSymbol], t: Term) : Term = t match {
      // homomorphic cases
    case Neg(s, e) => Neg(s, usubst(u, e))
    case Add(s, l, r) => Add(s, usubst(u, l), usubst(u, r))
    case Subtract(s, l, r) => Subtract(s, usubst(u, l), usubst(u, r))
    case Multiply(s, l, r) => Multiply(s, usubst(u, l), usubst(u, r))
    case Divide(s, l, r) => Divide(s, usubst(u, l), usubst(u, r))
    case Exp(s, l, r) => Exp(s, usubst(u, l), usubst(u, r))
    case Pair(dom, l, r) => Pair(dom, usubst(u, l), usubst(u, r))
    // uniform substitution base cases
    case x:Variable => if (u.contains(x)) return x else for(p <- l) { if(x == p.n) return clashChecked(u, t, p.t.asInstanceOf[Term])}; return x
    case Derivative(s, e) => for(p <- l) { if(t == p.n) return clashChecked(u, t, p.t.asInstanceOf[Term])}; return Derivative(s, usubst(u, e))
    case Apply(f, arg) => for(rp <- l) {
      rp.n match {
        //@TODO clashChecked(u, t, rp.t.asInstanceOf[Term]) is unnecessarily conservative, because it would not matter if rarg appeared in rp.t or not. clashChecked(u-rarg,t, rp.t.asInstanceOf[Term]) achieves this. But a better fix might be to use special variable names for denoting uniform substitution lambda abstraction terms right away so that this never happens.
        case Apply(rf, rarg:Variable) if (f == rf) => return instantiate(rarg, arg).usubst(Set.empty, clashChecked(u-rarg, t, rp.t.asInstanceOf[Term]))
        case _ => // skip to next
      }
    }; return Apply(f, usubst(u, arg))
    case x: Atom => require(!x.isInstanceOf[Variable], "variables have been substituted already"); x
    case _ => throw new UnknownOperatorException("Not implemented yet", t)
  }
  
  def apply(f: Formula): Formula = {
    log("\tSubstituting " + f.prettyString + " using " + this)
    try {
      val res = usubst(Set.empty[NamedSymbol], f)
      log("\tSubstituted  " + res.prettyString)
      res
    } catch {
      case ex: SubstitutionClashException => throw ex.inContext(f.prettyString)
    }
  }
  
  def apply(s: Sequent): Sequent = {
    try {
      Sequent(s.pref, s.ante.map(apply), s.succ.map(apply))
    } catch {
      case ex: SubstitutionClashException => throw ex.inContext(s.toString)
    }
  }
  
  private def usubst(u:Set[NamedSymbol], f: Formula): Formula = f match {
      // homomorphic cases
    case Not(g) => Not(usubst(u, g))
    case And(l, r) => And(usubst(u, l), usubst(u, r))
    case Or(l, r) => Or(usubst(u, l), usubst(u, r))
    case Imply(l, r) => Imply(usubst(u, l), usubst(u, r))
    case Equiv(l, r) => Equiv(usubst(u, l), usubst(u, r))

    case Equals(d, l, r) => Equals(d, usubst(u, l), usubst(u, r))
    case NotEquals(d, l, r) => NotEquals(d, usubst(u, l), usubst(u, r))
    case GreaterEqual(d, l, r) => GreaterEqual(d, usubst(u, l), usubst(u, r))
    case GreaterThan(d, l, r) => GreaterThan(d, usubst(u, l), usubst(u, r))
    case LessEqual(d, l, r) => LessEqual(d, usubst(u, l), usubst(u, r))
    case LessThan(d, l, r) => LessThan(d, usubst(u, l), usubst(u, r))

    // binding cases add bound variables to u
    case Forall(vars, g) => Forall(vars, usubst(u ++ vars, g))
    case Exists(vars, g) => Exists(vars, usubst(u ++ vars, g))

    case BoxModality(p, g) => val (v,q) = usubst(u, p); BoxModality(q, usubst(v, g))
    case DiamondModality(p, g) => val (v,q) = usubst(u, p); DiamondModality(q, usubst(v, g))

    // uniform substitution base cases
    case _: PredicateConstant => for(p <- l) { if (f == p.n) return clashChecked(u, f, p.t.asInstanceOf[Formula])}; return f
    case ApplyPredicate(p, arg) => for(rp <- l) {
      rp.n match {
        //@TODO clashChecked(u, f, rp.t.asInstanceOf[Formula]) is unnecessarily conservative, because it would not matter if rarg appeared in rp.t or not. clashChecked(u-rarg,f, rp.t.asInstanceOf[Formula]) achieves this. But a better fix might be to use special variable names for denoting uniform substitution lambda abstraction terms right away so that this never happens.
        case ApplyPredicate(rf, rarg:Variable) if (p == rf) => return instantiate(rarg, arg).usubst(Set.empty, clashChecked(u-rarg, f, rp.t.asInstanceOf[Formula]))
        case _ => // skip to next
      }
    }; return ApplyPredicate(p, usubst(u, arg))
    
    // 
    case FormulaDerivative(g) => FormulaDerivative(usubst(u, g))
    case x: Atom => x
    case _ => throw new UnknownOperatorException("Not implemented yet", f)
  }

  // uniform substitution on programs
  def apply(p: Program): Program = {
    try {
      usubst(Set.empty[NamedSymbol], p)._2
    } catch {
      case ex: SubstitutionClashException => throw ex.inContext(p.prettyString)
    }
  }
      
  
  /**
   *
   */
  private def usubst(u: Set[NamedSymbol], p:Program) : (Set[NamedSymbol], Program) = { p match {
    case Choice(a, b) => val (v,as)=usubst(u,a); val (w,bs)=usubst(u,b); (v++w, Choice(as, bs))
    case Sequence(a, b) => val (v,as)=usubst(u,a); val (w,bs)=usubst(v,b); (w, Sequence(as, bs))
    case Loop(a) => val (v,_)=usubst(u,a); val (w,as)=usubst(v,a); (w,Loop(as)) ensuring usubst(w,a)._1==w
    case Test(f) => (u, Test(usubst(u,f)))
    case Assign(x:Variable, e) => (u+x, Assign(x, usubst(u,e)))
    case NDetAssign(x:Variable) => (u+x, p)
    case NFContEvolve(v, x:Variable, e, h) => if (v.isEmpty) {
      if (!u.contains(x)) for (pair <- l) {if (x == pair.n) throw new SubstitutionClashException("Variable " + x + " will be replaced but occurs as differential equation", this, p)}
      (u+x, NFContEvolve(v, x, usubst(u++v+x, e), usubst(u++v+x,h)))
    } else throw new UnknownOperatorException("Check implementation whether passing v is correct.", p)
    
    //@TODO check implementation
    case a: ProgramConstant => for(pair <- l) { if(p == pair.n) return (u,pair.t.asInstanceOf[Program])}; return (u,p)
    case _ => throw new UnknownOperatorException("Not implemented yet", p)
  }} ensuring (r=>{val (v,as)=r; u.subsetOf(v)})


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
    case x: Atom => Nil
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
      if (subst(origin) == conclusion) {
        assert(alternativeAppliesCheck(conclusion), "uniform substitution application mechanisms agree")
        List(origin)
      } else {
        assert(!alternativeAppliesCheck(conclusion), "uniform substitution application mechanisms agree")
        throw new CoreException("Uniform substitution " + subst + " did not conclude  \n" + conclusion + "\nfrom\n  " + origin + "\nbut instead\n  " + subst(origin))
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

/**
 * Alpha conversion works on exactly four positions:
 * (1) Forall(v, phi)
 * (2) Exists(v, phi)
 * (3) Modality(BoxModality(Assign(x, e)), phi)
 * (4) Modality(DiamondModality(Assign(x, e)), phi)
 * (5) Modality(BoxModality(NDetAssign(x)), phi)
 * (6) Modality(DiamondModality(NDetAssign(x)), phi)
 *
 * It always replaces _every_ occurrence of the name in phi
 * @param tPos
 * @param name
 * @param idx
 * @param target
 * @param tIdx
 * @TODO Review
 */
class AlphaConversion(tPos: Position, name: String, idx: Option[Int], target: String, tIdx: Option[Int]) extends Rule("Alpha Conversion") {
  //require(name != target || idx != tIdx, "unexpected identity renaming " + name + " to " + target + " with same index " + idx)
  {
    if (!(name != target || idx != tIdx)) println("INFO: Unexpected identity renaming " + name + " to " + target + " with same index " + idx)
  }
  def apply(s: Sequent): List[Sequent] = {

    def proceed(f: Formula) = ExpressionTraversal.traverse(new ExpressionTraversalFunction {
      override def postP(p: PosInExpr, e: Program): Either[Option[StopTraversal], Program] = e match {
        case x: ProgramConstant => Right(renameProg(x))
        case _ => Left(None)
      }
      override def postT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = e match {
        case Apply(a, b) => Right(Apply(renameFunc(a), b))
        case x: Variable => Right(renameVar(x))
        case _ => Left(None)
      }
      override def postF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula]  = e match {
        case Forall(v, phi) => Right(Forall(for(i <- v) yield rename(i), phi))
        case Exists(v, phi) => Right(Forall(for(i <- v) yield rename(i), phi))
        case x: PredicateConstant => Right(renamePred(x))
        case ApplyPredicate(a, b) => Right(ApplyPredicate(renameFunc(a), b))
        case _ => Left(None)
      }
    }, f).get
    val fn = new ExpressionTraversalFunction {
      override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula]  = e match {
        case Forall(v, phi) =>
         require(v.map((x: NamedSymbol) => x.name).contains(name), "Symbol to be renamed must be bound in " + e)
          Right(Forall(for (i <- v) yield rename(i), proceed(phi)))
        case Exists(v, phi) =>
          require(v.map((x: NamedSymbol) => x.name).contains(name), "Symbol to be renamed must be bound in " + e)
          Right(Forall(for (i <- v) yield rename(i), proceed(phi)))
        case BoxModality(Assign(a, b), c) =>
          Right(BoxModality(Assign(a match {
            case Variable(n, i, d) if (n == name && i == idx) => Variable(target, tIdx, d)
            case Apply(Function(n, i, d, s), phi) if (n == name && i == idx) => Apply(Function(target, tIdx, d, s), phi)
            case _ => throw new UnknownOperatorException("Unknown Assignment structure", e)
          }, b), proceed(c)))
        case BoxModality(NDetAssign(a), c) =>
          Right(BoxModality(NDetAssign(a match {
            case Variable(n, i, d) if (n == name && i == idx) => Variable(target, tIdx, d)
            case Apply(Function(n, i, d, s), phi) if (n == name && i == idx) => Apply(Function(target, tIdx, d, s), phi)
            case _ => throw new UnknownOperatorException("Unknown Assignment structure", e)
          }), proceed(c)))
        case DiamondModality(Assign(a, b), c) =>
          Right(DiamondModality(Assign(a match {
            case Variable(n, i, d) if (n == name && i == idx) => Variable(target, tIdx, d)
            case Apply(Function(n, i, d, s), phi) if (n == name && i == idx) => Apply(Function(target, tIdx, d, s), phi)
            case _ => throw new UnknownOperatorException("Unknown Assignment structure", e)
          }, b), proceed(c)))
        case DiamondModality(NDetAssign(a), c) =>
          Right(DiamondModality(NDetAssign(a match {
            case Variable(n, i, d) if (n == name && i == idx) => Variable(target, tIdx, d)
            case Apply(Function(n, i, d, s), phi) if (n == name && i == idx) => Apply(Function(target, tIdx, d, s), phi)
            case _ => throw new UnknownOperatorException("Unknown Assignment structure", e)
          }), proceed(c)))
        case _ => throw new UnknownOperatorException("Unknown Assignment structure", e)
      }
    }
    ExpressionTraversal.traverse(TraverseToPosition(tPos.inExpr, fn), s(tPos)) match {
      case Some(x: Formula) =>
        if (tPos.isAnte) List(Sequent(s.pref, s.ante :+ x, s.succ)) else List(Sequent(s.pref, s.ante, s.succ :+ x))
      case _ => throw new CoreException("No alpha renaming possible in " + s(tPos))
    }
  }

  def renameVar(e: Variable): Variable = if(e.name == name && e.index == idx) Variable(target, tIdx, e.sort) else e

  def renamePred(e: PredicateConstant): PredicateConstant = if(e.name == name && e.index == idx) PredicateConstant(target, tIdx) else e

  def renameProg(e: ProgramConstant): ProgramConstant = if(e.name == name && e.index == idx) ProgramConstant(target, tIdx) else e

  def renameFunc(e: Function): Function = if(e.name == name && e.index == idx) Function(target, tIdx, e.domain, e.sort) else e

  def rename(e: NamedSymbol): NamedSymbol = e match {
    case v: Variable => renameVar(v)
    case p: PredicateConstant => renamePred(p)
    case p: ProgramConstant => renameProg(p)
    case f: Function => renameFunc(f)
  }
}

// skolemize
/**
 * Skolemization assumes that the names of the quantified variables to be skolemized are unique within the sequent.
 * This can be ensured by finding a unique name and renaming the bound variable through alpha conversion.
 */
class Skolemize(p: Position) extends PositionRule("Skolemize", p) {
  require(p.inExpr == HereP, "Can only skolemize top level formulas");
  import Helper._
  override def apply(s: Sequent): List[Sequent] = {
    // Other names underneath p are forbidden as well, but the variables v that are to be skolemized are fine as Skolem function names.
    val vars = namesIgnoringPosition(s, p)
    val (v,phi) = s(p) match {
      case Forall(v, phi) if (!p.isAnte) => (v,phi)
      case Exists(v, phi) if (p.isAnte) => (v,phi)
      case _ => throw new InapplicableRuleException("Skolemization in antecedent is only applicable to existential quantifiers", this, s)
    }
    if (vars.map(v.contains).contains(true))
      throw new SkolemClashException("Variables to be skolemized should not appear anywhere else in the sequent. AlphaConversion required.",
        vars.intersect(v.toSet))
    List(if(p.isAnte) Sequent(s.pref ++ v, s.ante.updated(p.index, phi), s.succ) else Sequent(s.pref ++ v, s.ante, s.succ.updated(p.index, phi)))
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

// @TODO Review. Will turn into axiom.
class AbstractionRule(pos: Position) extends PositionRule("AbstractionRule", pos) {
  override def apply(s: Sequent): List[Sequent] = {
    val fn = new ExpressionTraversalFunction {
      override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = e match {
          case BoxModality(p, f) => Right(Forall(p.writes, f))
          case DiamondModality(p, f) => Right(Forall(p.writes, f))
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
 * Rules for derivatives that are not expressible as axioms
 *********************************************************************************
 */
object DeriveConstant {
  def apply(t: Term): Rule = new DeriveConstant(t)
}
class DeriveConstant(t: Term) extends Rule("Derive Constant") {
  val Derivative(Real, Number(Real, n)) = t
  override def apply(s: Sequent): List[Sequent] =
    List(s.glue(Sequent(s.pref, IndexedSeq(Equals(Real, t, Number(Real, 0))), IndexedSeq())))
}

object DeriveMonomial {
  def apply(t: Term): Rule = new DeriveMonomial(t)
}

class DeriveMonomial(t: Term) extends Rule("Derive Monomial") {
  val Derivative(Real, Exp(Real, base, Number(Real, n))) = t
  override def apply(s: Sequent): List[Sequent] =
    List(s.glue(Sequent(s.pref, IndexedSeq(Equals(Real, t, Multiply(Real, Number(n), Exp(Real, base, Number(n - 1))))), IndexedSeq())))
}

// the following rules will turn into axioms

class DiffCut(p: Position, h: Formula) extends PositionRule("Differential Cut", p) {
  require(!p.isAnte)
  override def apply(s: Sequent): List[Sequent] = {
    val fn = new ExpressionTraversalFunction {
      override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = e match {
        case BoxModality(ev@ContEvolve(evolve), f) => Right(And(BoxModality(ev, h),
          BoxModality(ContEvolve(And(evolve, h)), f)))
        case BoxModality(ev@NFContEvolve(vs, x, t, dom), f) => Right(And(BoxModality(ev, h),
          BoxModality(NFContEvolve(vs, x, t, And(dom, h)), f)))
        case _ => ???
      }
    }
    ExpressionTraversal.traverse(TraverseToPosition(p.inExpr, fn), s(p)) match {
      case Some(f) => List(s.updated(p, f))
      case a => throw new IllegalStateException("Unexpected traversal result " + a)
    }
  }
}

class DiffInd(p: Position) extends PositionRule("Differential Induction", p) {
  override def apply(s: Sequent): List[Sequent] = {
       val fn = new ExpressionTraversalFunction {
      override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = e match {
        case BoxModality(ev@ContEvolve(And(Equals(s, xp@Derivative(_, _), t), h)), f) =>
          //TODO: require that t and h do not contain derivatives
          Right(BoxModality(ev, Imply(h, BoxModality(Assign(xp, t), FormulaDerivative(f)))))
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
