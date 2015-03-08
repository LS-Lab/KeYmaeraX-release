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


/**
 * Subclasses represent all proof rules.
 * A proof rule is ultimately a named mapping from sequents to lists of sequents.
 * The resulting list of sequents represent the subgoal/premise and-branches all of which need to be proved
 * to prove the current sequent (desired conclusion).
 */
  sealed abstract class Rule(val name: String) extends (Sequent => scala.collection.immutable.List[Sequent]) {
    override def toString: String = name
  }

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
 * conclusion from all the premisses in subgoals.
 * @param conclusion the conclusion that follows if all subgoals are valid.
 * @param subgoals the premisses that, if they are all valid, imply the conclusion.
 * @note soundness-critical
 * @note Only private constructor calls for soundness
 * @author aplatzer
 */
final case class Provable private (val conclusion: Sequent, val subgoals: scala.collection.immutable.IndexedSeq[Sequent]) {
  // has the conclusion of this Provable been proved?
  final def isProved : Boolean = (subgoals.isEmpty)

  // what conclusion has been proved if isProved
  final def proved : Sequent = {
    require(isProved, "Only Provables that have been proved have a proven conclusion " + this)
    if (isProved) conclusion else throw new CoreException("Provables with remaining subgoals are not proved yet " + this)
  }

  // apply proof rule to the indicated subgoal of this Provable, returning the resulting Provable
  final def apply(rule : Rule, subgoal : Int) : Provable = {
    require(0 <= subgoal && subgoal < subgoals.length, "Rules " + rule + " can only be applied to an index " + subgoal + " within the subgoals " + subgoals)
    rule(subgoals(subgoal)) match {
      case Nil => new Provable(conclusion, subgoals.drop(subgoal))
      case fml :: rest => new Provable(conclusion, subgoals.updated(subgoal, fml) ++ rest)
    }
  } ensuring(r => r.conclusion == conclusion, "Same conclusion after applying proof rules") ensuring (
    r => subgoals.drop(subgoal).toSet.subsetOf(r.subgoals.toSet),
    "All previous premisses except the one that the proof rule has been applied to") ensuring (
    r => rule(subgoals(subgoal)).toSet.subsetOf(r.subgoals.toSet), "All premisses generated by rule application are new subgoals")
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

    override def toString = "ProofNode(" + sequent + " by " +
      (if (parent != null) parent.tacticInfo.infos.get("Executing tactic")
       else "") +
      "\nfrom " + parent + ")"

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

  // lookup axiom named id
  //@TODO Hasn't this been replaced by an axiom lookup rule that closes if axiom occurs in antecedent?
  final def apply(id: String): Rule = new Rule("Axiom " + id) {
    def apply(s: Sequent): List[Sequent] = {
      axioms.get(id) match {
        case Some(f) => List(new Sequent(s.pref, s.ante :+ f, s.succ))
        case _ => throw new InapplicableRuleException("Axiom " + id + " does not exist in:\n" + axioms.mkString("\n"), this, s)
      }
    } ensuring (r => !r.isEmpty && r.forall(s.subsequentOf(_)), "axiom lookup adds formulas")
  }
}

/**
 * Apply a uniform substitution instance of an axiomatic proof rule.
 * @author aplatzer
 */
object AxiomaticRule {
  // immutable list of locally sound axiomatic proof rules (premise, conclusion)
  val rules: scala.collection.immutable.Map[String, (Sequent, Sequent)] = loadRuleFile()

  // apply uniform substitution instance subst of "axiomatic" rule named id
  final def apply(id: String, subst: Substitution): Rule = new AxiomaticRuleInstance(id, subst)

  private final class AxiomaticRuleInstance(id: String, subst: Substitution) extends Rule("Axiomatic Rule " + id + " instance") {
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
      if (subst(ruleconclusion) == conclusion) {
        List(subst(rulepremise))
      } else {
        throw new CoreException("Desired conclusion\n  " + conclusion + "\nis not a uniform substitution instance of\n" + ruleconclusion + "\nwith uniform substitution\n  " + subst + "\nwhich would be the instance\n  " + subst(ruleconclusion) + "\ninstead of\n  " + conclusion)
      }
    }
  }

  /**
   * KeYmaera Axiomatic Proof Rules.
   * @note Soundness-critical: Only return locally sound proof rules.
   * @author aplatzer
   */
  private def loadRuleFile() = {
    val x = Variable("x", None, Real)
    val p = Function("p", None, Real, Bool)
    val q = Function("q", None, Real, Bool)
    val anyt = Anything
    val a = ProgramConstant("a")
    Map(
      ("all generalization",
        (Sequent(Seq(), IndexedSeq(), IndexedSeq(ApplyPredicate(p, x))),
          Sequent(Seq(), IndexedSeq(), IndexedSeq(Forall(Seq(x), ApplyPredicate(p, x)))))),
      ("[] monotone",
        (Sequent(Seq(), IndexedSeq(ApplyPredicate(p, anyt)), IndexedSeq(ApplyPredicate(q, anyt))),
          Sequent(Seq(), IndexedSeq(BoxModality(a, ApplyPredicate(p, anyt))), IndexedSeq(BoxModality(a, ApplyPredicate(q, anyt)))))),
      ("<> monotone",
        (Sequent(Seq(), IndexedSeq(ApplyPredicate(p, anyt)), IndexedSeq(ApplyPredicate(q, anyt))),
          Sequent(Seq(), IndexedSeq(DiamondModality(a, ApplyPredicate(p, anyt))), IndexedSeq(DiamondModality(a, ApplyPredicate(q, anyt)))))),
      ("[] congruence",
        (Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(ApplyPredicate(p, anyt), ApplyPredicate(q, anyt)))),
          Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(BoxModality(a, ApplyPredicate(p, anyt)), BoxModality(a, ApplyPredicate(q, anyt))))))),
      ("<> congruence",
        (Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(ApplyPredicate(p, anyt), ApplyPredicate(q, anyt)))),
          Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(DiamondModality(a, ApplyPredicate(p, anyt)), DiamondModality(a, ApplyPredicate(q, anyt))))))),
      ("Goedel", /* unsound for hybrid games */
        (Sequent(Seq(), IndexedSeq(), IndexedSeq(ApplyPredicate(p, anyt))),
          Sequent(Seq(), IndexedSeq(), IndexedSeq(BoxModality(a, ApplyPredicate(p, anyt))))))
    )
  }

}

/*********************************************************************************
 * Sequent Proof Rules for identity/closing and cut
 *********************************************************************************
 */

//@TODO Mark these rules as ClosingRules and add contract "ensuring (!_.isEmpty)" globally to all rules that are not ClosingRules

// Ax Axiom close / Identity rule
//@TODO Rename to Close or so to avoid confusion with Axiom
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
 * Rewrites position ``p" according to assumption; for instance, if p="f" and assumption="f=g" then this
 * equality-rewrites p to g.
 * @param assumption The position of the equality (should be in the antecedent)
 * @param p The position of an occurance of the (l?)hs of assumption
 * @TODO replace by congruence rule derived from two uses of rule "monotone" via tactic or by a flat rule implementation
 */
class EqualityRewriting(assumption: Position, p: Position) extends AssumptionRule("Equality Rewriting", assumption, p) {
  import BindingAssessment.allNames
  override def apply(s: Sequent): List[Sequent] = {
    require(assumption.isAnte && assumption.inExpr == HereP)
    val (blacklist, fn) = s.ante(assumption.getIndex) match {
      case Equals(d, a, b) =>
        (allNames(a) ++ allNames(b),
        new ExpressionTraversalFunction {
          override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term]  =
            if(e == a) Right(b)
            else if(e == b) Right(a)
            else throw new IllegalArgumentException("Equality Rewriting not applicable")
        })
      case ProgramEquals(a, b) =>
        (allNames(a) ++ allNames(b),
        new ExpressionTraversalFunction {
          override def preP(p: PosInExpr, e: Program): Either[Option[StopTraversal], Program]  =
            if(e == a) Right(b)
            else if(e == b) Right(a)
            else throw new IllegalArgumentException("Equality Rewriting not applicable")
        })
      case Equiv(a, b) =>
        (allNames(a) ++ allNames(b),
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
 * @param what the expression to be replaced. what can have one of the following forms:
 *          - CDot
 *          - Nothing/Anything
 *          - ApplyPredicate(p:Function, CDot/Nothing/Anything)
 *          - Apply(f:Function, CDot/Nothing/Anything)
 *          - ProgramConstant/ContEvolveProgramConstant
 *          - Derivative(...)
 * @param repl the expression to be used in place of what
 */
sealed class SubstitutionPair (val what: Expr, val repl: Expr) {
  applicable
  // identity substitution would be correct but is usually unintended except for systematic constructions of substitutions that happen to produce identity substitutions. In order to avoid special casing, allow identity substitutions.
  //require(n != t, "Unexpected identity substitution " + n + " by equal " + t)
  
  @elidable(ASSERTION) def applicable = {
    // identity substitution would be correct but is usually unintended except for systematic constructions of substitutions that happen to produce identity substitutions. In order to avoid special casing, allow identity substitutions.
    if(false) { //@todo Nathan suppressed this for now...
      if (what == repl) println("INFO: Unnecessary identity substitution " + what + " by equal " + repl + "\n(non-critical, just indicates a possible tactics inefficiency)")
    }
    require(what.sort == repl.sort, "Sorts have to match in substitution pairs: " + what.sort + " != " + repl.sort)
    require(what match {
      case CDot => true
      case Anything => true
      case _:ProgramConstant => true
      case _:ContEvolveProgramConstant => true
      case Derivative(_, _:Variable) => true
      case ApplyPredicate(_:Function, CDot | Nothing | Anything) => true
      case Apply(_:Function, CDot | Nothing | Anything) => true
      case Nothing => repl == Nothing
      case _ => false
      }, "Substitutable expression required, found " + what)
  }

  override def toString: String = "(" + what.prettyString() + ", " + repl.prettyString() + ")"
}
object SubstitutionPair {
  def apply(n: Expr, t: Expr): SubstitutionPair = new SubstitutionPair(n, t)
  def unapply(e: Any): Option[(Expr,Expr)] = e match {
    case x: SubstitutionPair => Some((x.what,x.repl))
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

    case Not(g) => val vg = catVars(g); VC2(fv = vg.fv, bv = vg.bv)
    case And(l, r) => val vl = catVars(l); val vr = catVars(r); VC2(fv = vl.fv ++ vr.fv, bv = vl.bv ++ vr.bv)
    case Or(l, r) => val vl = catVars(l); val vr = catVars(r); VC2(fv = vl.fv ++ vr.fv, bv = vl.bv ++ vr.bv)
    case Imply(l, r) => val vl = catVars(l); val vr = catVars(r); VC2(fv = vl.fv ++ vr.fv, bv = vl.bv ++ vr.bv)
    case Equiv(l, r) => val vl = catVars(l); val vr = catVars(r); VC2(fv = vl.fv ++ vr.fv, bv = vl.bv ++ vr.bv)
    // TODO formuladerivative not mentioned in Definition 7 and 8
    case FormulaDerivative(df) => val vdf = catVars(df); VC2(fv = vdf.fv, bv = vdf.bv) //@todo eisegesis

    // binding cases add bound variables to u
    case Forall(vars, g) => val vg = catVars(g); VC2(fv = vg.fv -- vars, bv = vg.bv ++ vars)
    case Exists(vars, g) => val vg = catVars(g); VC2(fv = vg.fv -- vars, bv = vg.bv ++ vars)

    case BoxModality(p, g) => val vp = catVars(p); val vg = catVars(g)
      VC2(fv = vp.fv ++ (vg.fv -- vp.mbv), bv = vp.bv ++ vg.bv)
    case DiamondModality(p, g) => val vp = catVars(p); val vg = catVars(g)
      VC2(fv = vp.fv ++ (vg.fv -- vp.mbv), bv = vp.bv ++ vg.bv)

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
    case NamedDerivative(x : NamedSymbol) => SetLattice(NamedDerivative(x))
    case Derivative(s, x:NamedSymbol) => SetLattice(NamedDerivative(x))
    case Derivative(s, e) => freeVariables(e)
    case Apply(f, arg) => freeVariables(arg)
    case True | False | _: NumberObj | Nothing | Anything => SetLattice.bottom
  }

  def catVars(p: Program): VC3 = { p match {
    case Assign(x: Variable, e) => VC3(fv = freeVariables(e), bv = SetLattice(x), mbv = SetLattice(x))
    // TODO CDot and derivative not mentioned in Definition 9
      //@todo wrong eisegesis:?
//    case Assign(Derivative(_, x: Variable), e) => VC3(fv = freeVariables(e), bv = SetLattice(x), mbv = SetLattice(x)) //@todo eisegesis
    case Assign(Derivative(_, x : NamedSymbol), e) => VC3(fv = freeVariables(e), bv = SetLattice(NamedDerivative(x)), mbv = SetLattice(NamedDerivative(x)))
    case Assign(x : NamedDerivative, e) => {throw new Exception("wasn't expecting to get here."); VC3(fv = freeVariables(e), bv = SetLattice(x), mbv = SetLattice(x))}
    // TODO x:=* not mentioned in Definition 9
    case NDetAssign(x: Variable) => VC3(fv = SetLattice.bottom, bv = SetLattice(x), mbv = SetLattice(x)) //@todo eisegesis
    case Test(f) => VC3(fv = catVars(f).fv, bv = SetLattice.bottom, mbv = SetLattice.bottom)
    case NFContEvolve(vars, Derivative(_, x: Variable), e, h) =>
      VC3(fv = SetLattice[NamedSymbol](x) ++ freeVariables(e) ++ catVars(h).fv, bv = SetLattice[NamedSymbol](x) ++ SetLattice[NamedSymbol](NamedDerivative(x)), mbv = SetLattice[NamedSymbol](x) ++ SetLattice[NamedSymbol](NamedDerivative(x)))
    // TODO system of ODE cases not mentioned in Definition 9
    case ContEvolveProduct(a, b) => val va = catVars(a); val vb = catVars(b)
      VC3(fv = va.fv ++ vb.fv, bv = va.bv ++ vb.bv, mbv = va.mbv ++ vb.mbv) //@todo eisegesis
    case IncompleteSystem(a) => catVars(a) //@todo eisegesis
    case CheckedContEvolveFragment(a) => catVars(a) //@todo eisegesis
    case _: EmptyContEvolveProgram => VC3(fv = SetLattice.bottom, bv = SetLattice.bottom, mbv = SetLattice.bottom) //@todo eisegesis
    case Sequence(a, b) => val va = catVars(a); val vb = catVars(b)
      VC3(fv = va.fv ++ (vb.fv -- va.mbv), bv = va.bv ++ vb.bv, mbv = va.mbv ++ vb.mbv)
    case Choice(a, b) => val va = catVars(a); val vb = catVars(b)
      VC3(fv = va.fv ++ vb.fv, bv = va.bv ++ vb.bv, mbv = va.mbv.intersect(vb.mbv))
    case Loop(a) => val va = catVars(a); VC3(fv = va.fv, bv = va.bv, mbv = SetLattice.bottom)
    case _: ProgramConstant => VC3(fv = SetLattice.top, bv = SetLattice.top, mbv = SetLattice.bottom)
    case _: ContEvolveProgramConstant => VC3(fv = SetLattice.top, bv = SetLattice.top, mbv = SetLattice.bottom)
    case _ => throw new UnknownOperatorException("Not implemented", p)
  }} ensuring(r => { val VC3(_, bv, mbv) = r; mbv.subsetOf(bv) }, s"Result MBV($p) not a subset of BV($p)")

  def primedVariables(ode: ContEvolveProgram): Set[NamedSymbol] = ode match {
    case CheckedContEvolveFragment(child) => primedVariables(child) //@todo eisegesis
    case ContEvolveProduct(a, b) => primedVariables(a) ++ primedVariables(b)
    case IncompleteSystem(a) => primedVariables(a)
    case NFContEvolve(_, Derivative(_, x: Variable), _, _) => Set(x)
    case _: EmptyContEvolveProgram => Set.empty
    case _: ContEvolveProgramConstant => Set.empty
  }

  // all variables x and their differential symbols x' occurring in the ode.
  def coprimedVariables(ode: ContEvolveProgram): Set[NamedSymbol] = ode match {
    case CheckedContEvolveFragment(child) => coprimedVariables(child) //@todo eisegesis
    case ContEvolveProduct(a, b) => coprimedVariables(a) ++ coprimedVariables(b)
    case IncompleteSystem(a) => coprimedVariables(a)
    case NFContEvolve(_, Derivative(_, x: Variable), _, _) => Set(x,NamedDerivative(x))
    case _: EmptyContEvolveProgram => Set.empty
    case _: ContEvolveProgramConstant => Set.empty
  }

  def allNames(f: Formula): Set[NamedSymbol] = f match {
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
    case FormulaDerivative(df) => allNames(df)

    case Forall(vars, g) => vars.toSet ++ allNames(g)
    case Exists(vars, g) => vars.toSet ++ allNames(g)

    case BoxModality(p, g) => allNames(p) ++ allNames(g)
    case DiamondModality(p, g) => allNames(p) ++ allNames(g)

    // base cases
    case ApplyPredicate(p, arg) => Set(p) ++ allNames(arg)
    case True | False => Set.empty
    case _ => throw new UnknownOperatorException("Not implemented", f)
  }

  def allNames(t: Term): Set[NamedSymbol] = t match {
    // homomorphic cases
    case Neg(s, l) => allNames(l)
    case Add(s, l, r) => allNames(l) ++ allNames(r)
    case Subtract(s, l, r) => allNames(l) ++ allNames(r)
    case Multiply(s, l, r) => allNames(l) ++ allNames(r)
    case Divide(s, l, r) => allNames(l) ++ allNames(r)
    case Exp(s, l, r) => allNames(l) ++ allNames(r)
    case Pair(dom, l, r) => allNames(l) ++ allNames(r)
    case Derivative(s, e) => allNames(e)
    // base cases
    case Apply(f, arg) => Set(f) ++ allNames(arg)
    case x: Variable => Set(x)
    case CDot => Set(CDot)
    case nd: NamedDerivative => Set(nd)
    case True | False | _: NumberObj | Nothing | Anything => Set.empty
  }

  def allNames(p: Program): Set[NamedSymbol] = p match {
    case Assign(x: Variable, e) => Set(x) ++ allNames(e)
    case Assign(Derivative(_, x : NamedSymbol), e) => Set(x) ++ allNames(e)
    case Assign(x : NamedDerivative, e) => Set(x) ++ allNames(e)
    case NDetAssign(x: Variable) => Set(x)
    case Test(f) => allNames(f)
    case NFContEvolve(vars, Derivative(_, x: Variable), e, h) => Set(x) ++ allNames(e) ++ allNames(h)
    case ContEvolveProduct(a, b) => allNames(a) ++ allNames(b)
    case IncompleteSystem(a) => allNames(a)
    case CheckedContEvolveFragment(a) => allNames(a)
    case _: EmptyContEvolveProgram => Set()
    case Sequence(a, b) => allNames(a) ++ allNames(b)
    case Choice(a, b) => allNames(a) ++ allNames(b)
    case Loop(a) => allNames(a)
    case prg: ProgramConstant => Set(prg)
    case prg: ContEvolveProgramConstant => Set(prg)
    case _ => throw new UnknownOperatorException("Not implemented", p)
  }

  def allNamesExceptAt(s: Sequent, p: Position) = {
    val fs = if (p.isAnte) s.ante.slice(0, p.index) ++ s.ante.slice(p.index + 1, s.ante.length) ++ s.succ
             else s.ante ++ s.succ.slice(0, p.index) ++ s.succ.slice(p.index + 1, s.ante.length)
    fs.flatMap(BindingAssessment.allNames).toSet
  }
}

/**
 * A Uniform Substitution.
 * Implementation of applying uniform substitutions to terms, formulas, programs.
 * Fast application explicit construction computing bound variables on the fly.
 * Used for UniformSubstitution rule.
 * @author aplatzer
 * @author Stefan Mitsch
 * @TODO Rename to FastSubstitution
 */
final case class Substitution(subsDefs: scala.collection.immutable.Seq[SubstitutionPair]) {
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
    val lefts = subsDefs.map(sp=>sp.what).toList
    require(lefts.distinct.size == lefts.size, "no duplicate substitutions with same substitutees " + subsDefs)
    // check that we never replace p(x) by something and also p(t) by something
    val lambdaNames = subsDefs.map(sp=>sp.what match {
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
    new Substitution(s.filter(_.what match { case en: NamedSymbol => !names.contains(en) case _ => true }))

  /**
   * Check whether the function in right matches with the function in left, i.e. they have the same head.
   */
  def sameHead(left: SubstitutionPair, right: Expr) = left.what match {
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
    def subst(t: Term) = subsDefs.find(_.what == t).get.repl.asInstanceOf[Term]
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
      case x: Variable => require(!subsDefs.exists(_.what == x), s"Substitution of variables not supported: $x"); x
      // TODO not mentioned in substitution
      case CDot if !subsDefs.exists(_.what == CDot) || o.contains(CDot) => CDot //@todo eisegesis
      case CDot if  substDiff(subsDefs, o).subsDefs.exists(_.what == CDot) => //@todo eisegesis
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
          (subs.what match { case Apply(_, v: NamedSymbol) => v
                          case _ => throw new IllegalArgumentException(
                            s"Substitution of f(theta)=${app.prettyString()} for arbitrary theta=$theta not supported") },
           subs.repl match { case t: Term => t
                          case _ => throw new IllegalArgumentException(
                            s"Can only substitute terms for ${app.prettyString()}")}
          )
        val restrictedU = theta match { case CDot => u case Anything => SetLattice.bottom[NamedSymbol] case _ => u-rArg }
        require(freeVariables(rTerm).intersect(restrictedU).isEmpty,
          s"Substitution clash: ${freeVariables(subs.repl.asInstanceOf[Term])} ∩ $u is not empty")
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
      val rFormula = uniqueElementOf[SubstitutionPair](subsDefs, sameHead(_, app)).repl.asInstanceOf[Formula]
      Substitution(List()).usubst(SetLattice.bottom, SetLattice.bottom, rFormula)
    case app@ApplyPredicate(_, Anything) if !subsDefs.exists(sameHead(_, app)) => f
    case app@ApplyPredicate(_, theta) if subsDefs.exists(sameHead(_, app)) =>
      val subs = uniqueElementOf[SubstitutionPair](subsDefs, sameHead(_, app))
      val (rArg, rFormula) = (
        subs.what match { case ApplyPredicate(_, v: NamedSymbol) => v
                       case _ => throw new IllegalArgumentException(
                         s"Substitution of p(theta)=${app.prettyString()} for arbitrary theta=$theta not supported")},
        subs.repl match { case f: Formula => f
                       case _ => throw new IllegalArgumentException(
                         s"Can only substitute formulas for ${app.prettyString()}")}
        )
      val restrictedU = theta match { case CDot => u case Anything => SetLattice.bottom[NamedSymbol] case _ => u-rArg }
      require(catVars(rFormula).fv.intersect(restrictedU).isEmpty,
        s"Substitution clash: ${catVars(rFormula).fv} ∩ $restrictedU is not empty")
      instantiate(rArg, usubst(o, u, theta)).usubst(SetLattice.bottom, SetLattice.bottom, rFormula)
    case app@ApplyPredicate(p, theta) if !subsDefs.exists(sameHead(_, app)) => ApplyPredicate(p, usubst(o, u, theta))
    case FormulaDerivative(g) => FormulaDerivative(usubst(o, u, g))
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
    case Assign(d@Derivative(_, x: Variable), e) => USR(o+NamedDerivative(x), u+NamedDerivative(x), Assign(d, usubst(o, u, e))) //@todo eisegesis
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
    case a: ProgramConstant if  subsDefs.exists(_.what == p) =>
      val sigmaP = subsDefs.find(_.what == p).get.repl.asInstanceOf[Program]
      // programs don't have a side condition, since their meaning does not depend on state
      USR(o++catVars(sigmaP).mbv, u++catVars(sigmaP).bv, sigmaP)
    case a: ProgramConstant if !subsDefs.exists(_.what == p) => USR(o++catVars(a).mbv, u++catVars(a).bv, p)
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
    ContEvolveProgram = {
    val primedPrimed : Set[NamedSymbol] = primed.map(NamedDerivative(_)) //primed is a list of "Variable"s that are primed; this is the list of the acutally primed variables.
    p match {
      case ContEvolveProduct(a, b) => ContEvolveProduct(usubstODE(o, u, primed, a), usubstODE(o, u, primed, b))
      case NFContEvolve(v, d@Derivative(_, x: Variable), e, h) => if (v.isEmpty) {
        NFContEvolve(v, d, usubst(o ++ SetLattice(primed) ++ SetLattice(primedPrimed),
          u ++ SetLattice(primed) ++ SetLattice(primedPrimed), e),
          usubst(o ++ SetLattice(primed), u ++ SetLattice(primed), h)) //@todo for something like x' := y' +1 we'll need to add primedPrimed to the back lists as well.
      } else throw new UnknownOperatorException("Check implementation whether passing v is correct.", p)
      case _: EmptyContEvolveProgram => p
      case IncompleteSystem(s) => IncompleteSystem(usubstODE(o, u, primed, s))
      case CheckedContEvolveFragment(s) => CheckedContEvolveFragment(usubstODE(o, u, primed, s))
      case a: ContEvolveProgramConstant if subsDefs.exists(_.what == p) =>
        val repl = subsDefs.find(_.what == p).get.repl
        repl match {
          case replODE: ContEvolveProgram => replODE
          case _ => throw new IllegalArgumentException("Can only substitute continuous programs for " +
            s"continuous program constants: $repl not allowed for $a")
        }
      case a: ContEvolveProgramConstant if !subsDefs.exists(_.what == p) => p
    }
  }
}

/**
 * A Uniform Substitution.
 * Implementation of applying uniform substitutions to terms, formulas, programs.
 * Global version that checks admissibility eagerly at bound variables rather than computing bounds on the fly and checking upon occurrence.
 * Used for UniformSubstitution rule.
 * @author aplatzer
 * @see GlobalUniformSubstitution
 * @TODO Rename to Substitution. Or USubst?
 */
final case class GlobalSubstitution(subsDefs: scala.collection.immutable.Seq[SubstitutionPair]) {
  applicable()

  // unique left hand sides in l
  @elidable(ASSERTION) def applicable() = {
    // check that we never replace n by something and then again replacing the same n by something
    val lefts = subsDefs.map(_.what).toList
    require(lefts.distinct.size == lefts.size, "no duplicate substitutions with same substitutees " + subsDefs)
    // check that we never replace p(x) by something and also p(t) by something
    val lambdaNames = subsDefs.map(_.what match {
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
        case x: Variable => require(!subsDefs.exists(_.what == x), s"Substitution of variables not supported: $x"); x
        case xp@Derivative(Real, x: Variable) => require(!subsDefs.exists(_.what == xp),
          s"Substitution of differential symbols not supported: $xp"); xp
        case app@Apply(_, theta) if subsDefs.exists(sameHead(_, app)) =>
          val subs = uniqueElementOf[SubstitutionPair](subsDefs, sameHead(_, app))
          val (rArg, rTerm) =
            (subs.what match { case Apply(_, v: NamedSymbol) => v
                            case _ => throw new IllegalArgumentException(
                              s"Substitution of f(theta)=${app.prettyString()} for arbitrary theta=$theta not supported") },
             subs.repl match { case t: Term => t
                            case _ => throw new IllegalArgumentException(
                              s"Can only substitute terms for ${app.prettyString()}")}
            )
          GlobalSubstitution(SubstitutionPair(rArg, usubst(theta)) :: Nil).usubst(rTerm)
        case app@Apply(g, theta) if !subsDefs.exists(sameHead(_, app)) => Apply(g, usubst(theta))
        case Anything => Anything // TODO check
        case Nothing => Nothing // TODO check
        case CDot if !subsDefs.exists(_.what == CDot) => CDot // TODO check (should be case x = sigma x for variable x)
        case CDot if  subsDefs.exists(_.what == CDot) => // TODO check (should be case x = sigma x for variable x)
          subsDefs.find(_.what == CDot).get.repl match {
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
            subs.what match { case ApplyPredicate(_, v: NamedSymbol) => v
                           case _ => throw new IllegalArgumentException(
                            s"Substitution of p(theta)=${app.prettyString()} for arbitrary theta=${theta.prettyString()} not supported")},
            subs.repl match { case f: Formula => f
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

        case FormulaDerivative(g) => FormulaDerivative(usubst(g))

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
        case a: ProgramConstant if subsDefs.exists(_.what == a) =>
          subsDefs.find(_.what == a).get.repl.asInstanceOf[Program]
        case a: ProgramConstant if !subsDefs.exists(_.what == a) => a
        case Assign(x: Variable, e) => Assign(x, usubst(e))
        case Assign(xp@Derivative(_, x: Variable), e) => Assign(xp, usubst(e))
        case NDetAssign(x: Variable) => NDetAssign(x)
        case Test(f) => Test(usubst(f))
        case ode: ContEvolveProgram =>
          // redundant with the checks on NFContEvolve in usubst(ode, primed)
          require(admissible(scala.collection.immutable.Seq(coprimedVariables(ode).toSeq: _*), ode),
            s"Substitution clash in ODE: {x}=${coprimedVariables(ode)} when substituting ${ode.prettyString()}")
          usubstODE(ode, coprimedVariables(ode))
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
    case IncompleteSystem(s) => IncompleteSystem(usubstODE(s, primed))
    case CheckedContEvolveFragment(s) => CheckedContEvolveFragment(usubstODE(s, primed))
    case c: ContEvolveProgramConstant if  subsDefs.exists(_.what == c) =>
      val repl = subsDefs.find(_.what == c).get.repl
      repl match {
        case replODE: ContEvolveProgram => replODE
        case _ => throw new IllegalArgumentException("Can only substitute continuous programs for " +
          s"continuous program constants: $repl not allowed for $c")
      }
    case c: ContEvolveProgramConstant if !subsDefs.exists(_.what == c) => c
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
    def intersectsU(sigma: SubstitutionPair): Boolean = (sigma.repl match {
        case t: Term => sigma.what match {
          case Apply(_, Anything) => SetLattice.bottom[NamedSymbol]
          // if ever extended with f(x,y,z): freeVariables(t) -- {x,y,z}
          case _ => freeVariables(t)
        }
        case f: Formula => sigma.what match {
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

    subsDefs.filter(sigma => intersectsU(sigma)).map(sigma => nameOf(sigma.what)).forall(fn => !occurrences.contains(fn))
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

    //@todo eisegesis
    case FormulaDerivative(x) => fnPredPrgSymbolsOf(x)
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
    case CheckedContEvolveFragment(c) => fnPredPrgSymbolsOf(c) //@todo eisegesis
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
  def sameHead(left: SubstitutionPair, right: Expr) = left.what match {
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

/*@TODO Replace by flat implementation*/
class AlphaConversion(name: String, idx: Option[Int], target: String, tIdx: Option[Int], pos: Option[Position])
  extends Rule("Alpha Conversion") {

  import BindingAssessment._

  @unspecialized
  override def compose[A](g: (A) => _root_.edu.cmu.cs.ls.keymaera.core.Sequent): (A) => scala.List[_root_.edu.cmu.cs.ls.keymaera.core.Sequent] = super.compose(g)

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
          case DiamondModality(ode: ContEvolveProgram, _) if catVars(ode).bv.exists(v => v.name == name && v.index == idx) =>
            Right(DiamondModality(Assign(Variable(target, tIdx, Real), Variable(name, idx, Real)), apply(f)))
          // if loop binds var, then rename with stored initial value
          case BoxModality(Loop(a), _) if catVars(a).bv.exists(v => v.name == name && v.index == idx) =>
            Right(BoxModality(Assign(Variable(target, tIdx, Real), Variable(name, idx, Real)), apply(f)))
          case DiamondModality(Loop(a), _) if catVars(a).bv.exists(v => v.name == name && v.index == idx) =>
            Right(DiamondModality(Assign(Variable(target, tIdx, Real), Variable(name, idx, Real)), apply(f)))

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
    require(!BindingAssessment.allNames(f).exists(v => v.name == target && v.index == tIdx), s"Name ${target}_$tIdx not fresh in $f")
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
    case Anything => Anything
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
      case CheckedContEvolveFragment(a) => CheckedContEvolveFragment(renameODE(a))
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
 * @TODO Could replace by uniform substitution rule application mechanism for rule "all generalization"
 * along with tactics expanding scope of quantifier with axiom "all quantifier scope".
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
    List(if (p.isAnte) Sequent(s.pref ++ v, s.ante.updated(p.index, phi), s.succ)
         else Sequent(s.pref ++ v, s.ante, s.succ.updated(p.index, phi)))
  }
}

/**
 * Skolemization assumes that the names of the quantified variables to be skolemized are unique within the sequent.
 * This can be ensured by finding a unique name and renaming the bound variable through alpha conversion.
 * @TODO Replace by uniform substitution rule application mechanism for rule "all generalization" for functions
 * along with tactics expanding scope of quantifier with axiom "all quantifier scope".
 */
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
    List(if (p.isAnte) Sequent(s.pref ++ fn, s.ante.updated(p.index, phi), s.succ)
    else Sequent(s.pref ++ fn, s.ante, s.succ.updated(p.index, phi)))
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

  /**
   * @TODO Review. Might turn into axiom QuantifierAbstraction.
   * @deprecated Use [] monotone and <> monotone or Goedel rule instead.
   */
class AbstractionRule(pos: Position) extends PositionRule("AbstractionRule", pos) {
  override def apply(s: Sequent): List[Sequent] = {
    val fn = new ExpressionTraversalFunction {
      val factory: (Seq[NamedSymbol], Formula) => Quantifier = if (pos.isAnte) Exists.apply else Forall.apply
      override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = e match {
          //@TODO Do not use @deprecated .writes functions
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
    List(s.glue(Sequent(s.pref,
      IndexedSeq(Equals(Real, t, Multiply(Real, Multiply(Real, Number(n), Exp(Real, base, Number(n - 1))), Derivative(Real, base)))),
      IndexedSeq())))
}

// the following rules will turn into axioms

//@TODO Removal suggested since better axiom DC differential cut exists.
//@deprecated
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

// vim: set ts=4 sw=4 et:
