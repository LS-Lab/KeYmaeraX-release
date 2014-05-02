package edu.cmu.cs.ls.keymaera.tactics

import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.Tactics.{ApplyRule, ApplyPositionTactic, PositionTactic, Tactic}
import scala.Unit

/**
 * In this object we collect wrapper tactics around the basic rules and axioms.
 *
 * Created by Jan-David Quesel on 4/28/14.
 */
object TacticLibrary {


  /** *******************************************
    * Basic Tactics
    * *******************************************
    */

  def findPosAnte(posT: PositionTactic): Tactic = new ApplyPositionTactic("FindPosAnte (" + posT.name + ")", posT) {
    override def applicable(p: ProofNode): Boolean = {
      for (i <- 0 until p.sequent.ante.length) {
        val pos = new Position(true, i)
        if (posT.applies(p.sequent, pos)) return true
      }
      return false
    }

    override def findPosition(s: Sequent): Option[Position] = {
      for (i <- 0 until s.ante.length) {
        val pos = new Position(true, i)
        if(posT.applies(s, pos)) {
          return Some(pos)
        }
      }
      return None
    }
  }

  def findPosSucc(posT: PositionTactic): Tactic = new ApplyPositionTactic("FindPosSucc (" + posT.name + ")", posT) {
    override def applicable(p: ProofNode): Boolean = {
      for (i <- 0 until p.sequent.succ.length) {
        val pos = new Position(true, i)
        if (posT.applies(p.sequent, pos)) return true
      }
      return false
    }

    override def findPosition(s: Sequent): Option[Position] = {
      for (i <- 0 until s.succ.length) {
        val pos = new Position(true, i)
        if(posT.applies(s, pos)) {
          return Some(pos)
        }
      }
      return None
    }
  }

  def AndLeftT: PositionTactic = new PositionTactic("AndLeft") {
    def applies(s: Sequent, p: Position) = if (p.isAnte) s.ante(p.index) match {
      case And(_, _) => true
      case _ => false
    } else false

    def apply(pos: Position): Tactic = new Tactics.ApplyRule(AndLeft(pos)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)
    }
  }

  def AndLeftFindT: Tactic = findPosAnte(AndLeftT)

  def AndRightT: PositionTactic = new PositionTactic("AndRight") {
    def applies(s: Sequent, p: Position) = if (!p.isAnte) s.succ(p.index) match {
      case And(_, _) => true
      case _ => false
    } else false

    def apply(pos: Position): Tactic = new Tactics.ApplyRule(AndRight(pos)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)
    }
  }

  def AndRightFindT: Tactic = findPosSucc(AndRightT)

  def OrLeftT: PositionTactic = new PositionTactic("OrLeft") {
    def applies(s: Sequent, p: Position) = if (p.isAnte) s.ante(p.index) match {
      case Or(_, _) => true
      case _ => false
    } else false

    def apply(pos: Position): Tactic = new Tactics.ApplyRule(OrLeft(pos)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)
    }
  }

  def OrLeftFindT: Tactic = findPosAnte(OrLeftT)

  def OrRightT: PositionTactic = new PositionTactic("OrRight") {
    def applies(s: Sequent, p: Position) = if (!p.isAnte) s.succ(p.index) match {
      case Or(_, _) => true
      case _ => false
    } else false

    def apply(pos: Position): Tactic = new Tactics.ApplyRule(OrRight(pos)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)
    }
  }

  def OrRightFindT: Tactic = findPosSucc(OrRightT)

  def ImplyLeftT: PositionTactic = new PositionTactic("ImplyLeft") {
    def applies(s: Sequent, p: Position) = if (p.isAnte) s.ante(p.index) match {
      case Imply(_, _) => true
      case _ => false
    } else false

    def apply(pos: Position): Tactic = new Tactics.ApplyRule(ImplyLeft(pos)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)
    }
  }

  def ImplyLeftFindT: Tactic = findPosAnte(ImplyLeftT)

  def ImplyRightT: PositionTactic = new PositionTactic("ImplyRight") {
    def applies(s: Sequent, p: Position) = if (!p.isAnte) s.succ(p.index) match {
      case Imply(_, _) => true
      case _ => false
    } else false

    def apply(pos: Position): Tactic = new Tactics.ApplyRule(ImplyRight(pos)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)
    }
  }

  def ImplyRightFindT: Tactic = findPosSucc(ImplyRightT)

  def NotLeftT: PositionTactic = new PositionTactic("NotLeft") {
    def applies(s: Sequent, p: Position) = if (p.isAnte) s.ante(p.index) match {
      case Not(_) => true
      case _ => false
    } else false

    def apply(pos: Position): Tactic = new Tactics.ApplyRule(NotLeft(pos)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)
    }
  }

  def NotLeftFindT: Tactic = findPosAnte(NotLeftT)

  def NotRightT: PositionTactic = new PositionTactic("NotRight") {
    def applies(s: Sequent, p: Position) = if (!p.isAnte) s.succ(p.index) match {
      case Not(_) => true
      case _ => false
    } else false

    def apply(pos: Position): Tactic = new Tactics.ApplyRule(NotRight(pos)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)
    }
  }

  def NotRightFindT: Tactic = findPosSucc(NotRightT)

  def hideT: PositionTactic = new PositionTactic("Hide") {
    def applies(s: Sequent, p: Position) = true

    def apply(pos: Position): Tactic = new Tactics.ApplyRule(if (pos.isAnte) HideLeft(pos) else HideRight(pos)) {
      override def applicable(node: ProofNode): Boolean = true
    }
  }

  def cutT(g: (ProofNode => Option[Formula])): Tactic = new Tactic("Cut") {
    def applicable(pn: ProofNode): Boolean = g(pn) match {
      case Some(_) => true
      case _ => false
    }

    def apply(tool: Tool, p: ProofNode): Unit = g(p) match {
      case Some(t) => {
        val apTactic = new Tactics.ApplyRule(Cut(t)) {
          override def applicable(node: ProofNode): Boolean = node == p
        };
        apTactic.continuation = continuation
        apTactic.dispatch(this, p)
      }
      case _ => continuation(this, Failed, Seq(p))
    }
  }

  def cutT(f: Formula): Tactic = cutT((x: ProofNode) => Some(f))

  def AxiomCloseT: Tactic = new Tactic("AxiomClose") {
    def apply(tool: Tool, p: ProofNode): Unit = findPositions(p.sequent) match {
      case Some((a, b)) => {
        val t = new Tactics.ApplyRule(AxiomClose(a, b)) {
          override def applicable(node: ProofNode): Boolean = node == p
        }
        t.continuation = continuation
        t.dispatch(this, p)
      }
      case None => continuation(this, Failed, Seq(p))
    }

    def findPositions(s: Sequent): Option[(Position, Position)] = {
      for (f <- s.ante; g <- s.succ)
        if (f == g) return Some((new Position(true, s.ante.indexOf(f)), new Position(false, s.succ.indexOf(g))))
      None
    }

    override def applicable(node: ProofNode): Boolean = findPositions(node.sequent) match {
      case Some(_) => true
      case _ => false
    }
  }

  def axiomT(id: String): Tactic = new Tactic("Axiom " + id) {
    def applicable(pn: ProofNode): Boolean = true

    def apply(tool: Tool, p: ProofNode): Unit = Axiom.axioms.get(id) match {
      case Some(_) => new Tactics.ApplyRule(Axiom(id)) {
        override def applicable(node: ProofNode): Boolean = (node == p)
      }
      case _ => continuation(this, Failed, Seq(p))
    }
  }


  def uniformSubstT(subst: Substitution, delta: (Map[Formula, Formula])) = new Tactic("Uniform Substitution") {
    def applicable(pn: ProofNode) = true

    def apply(tool: Tool, p: ProofNode): Unit = {
      val ante = for (f <- p.sequent.ante) yield delta.get(f) match {
        case Some(frm) => frm
        case _ => f
      }
      val succ = for (f <- p.sequent.succ) yield delta.get(f) match {
        case Some(frm) => frm
        case _ => f
      }
      val t = new Tactics.ApplyRule(UniformSubstitution(subst, Sequent(p.sequent.pref, ante, succ))) {
        override def applicable(node: ProofNode): Boolean = node == p
      }
      t.continuation = continuation
      t.dispatch(this, p)
    }

  }

  // assignment tactic (alpha renaming and then assignment rule)
  def assignmentFindAnte = findPosAnte(assignment)
  def assignmentFindSucc = findPosSucc(assignment)
  def assignmentFind = assignmentFindSucc | assignmentFindAnte
  // it would be great if we could access the same position to apply the imply right rule
  // FIXME: this only works for toplevel positions since there the positions are stable
  def assignmentFindImpl = findPosSucc(assignment & ImplyRightT) | findPosAnte(assignment & ImplyLeftT)

  def assignment = new PositionTactic("Assignment") {
    // for now only on top level
    override def applies(s: Sequent, p: Position): Boolean = {
      (p.inExpr == HereP) && ((if (p.isAnte) s.ante else s.succ)(p.index) match {
        case BoxModality(Variable(_, _, _), _) => true
        case DiamondModality(Variable(_, _, _), _) => true
        case _ => false
      })
    }

    override def apply(p: Position): Tactic = Tactics.seqT(uniquify(p), new ApplyRule(new AssignmentRule(p)) {
      override def applicable(n: ProofNode): Boolean = applies(n.sequent, p)
    })
  }

  def uniquify = new PositionTactic("Uniquify") {
    // for now only on top level
    override def applies(s: Sequent, p: Position): Boolean = {
      (p.inExpr == HereP) && ((if (p.isAnte) s.ante else s.succ)(p.index) match {
        case BoxModality(Variable(_, _, _), _) => true
        case DiamondModality(Variable(_, _, _), _) => true
        case _ => false
      })
    }

    override def apply(p: Position): Tactic = new Tactic(this.name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def apply(tool: Tool, node: ProofNode): Unit = {
        val (n, idx) = (if (p.isAnte) node.sequent.ante else node.sequent.succ)(p.index) match {
          case BoxModality(Assign(Variable(name, i, _), _)) => (name, i)
          case DiamondModality(Assign(Variable(name, i, _), _)) => (name, i)
          case a => throw new UnsupportedOperationException("Cannot apply to " + a)
        }
        val vars = Helper.variables(node.sequent).filter((ns: NamedSymbol) => ns.name == n)
        require(vars.size > 0, "The variable we want to rename was not found in the sequent all together " + n + " " + node.sequent)
        // we do not have to rename if there are no name clashes
        if(vars.size > 1) {
          val maxIdx: Option[Int] = (vars.map((ns: NamedSymbol) => ns.index)).foldLeft(None: Option[Int])((acc: Option[Int], i: Option[Int]) => acc match {
            case Some(a) => i match {
              case Some(b) => if (a < b) Some(b) else Some(a)
              case None => Some(a)
            }
            case None => i
          })
          val tIdx: Option[Int] = maxIdx match {
            case None => Some(0)
            case Some(a) => Some(a+1)
          }
          // dispatch alpha conversion tactic
          new ApplyRule(new AlphaConversion(p, n, idx, n, tIdx)) {
            override def applicable(n: ProofNode): Boolean = n == node
          }.dispatch(this, node)
        }

      }
    }

  }

  // exhaustive equality rewriting

  // axiom wrappers

}
