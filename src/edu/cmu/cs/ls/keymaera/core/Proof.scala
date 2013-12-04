package edu.cmu.cs.ls.keymaera.core

object Proof {
  type Formula = Term[Bool.type]

sealed class ProofNode protected (val s: Sequent, val p: ProofNode) {
  /**
  * The rule that has been applied to the current node
  */
  private[this] var rule: Rule = null

  /**
  * The resulting sub goals from the rule application
  */
  private[this] var children: Seq[ProofNode] = Nil

  def apply(rule: Rule) = null
  def apply(r: PositionRule, p: Position): Seq[ProofNode] = {
    rule = r(p)
    children = for (ns <- rule(s)) 
      yield new ProofNode(ns, this)
    children
  }
  def apply(rule: AssumptionRule, assumption: Position, p: Position) = null

  def getRule = rule
  def getChildren = children
}

class RootNode(override val s: Sequent) extends ProofNode(s, null)

sealed abstract class Rule extends (Sequent => Seq[Sequent])

abstract class PositionRule extends (Position => Rule)

abstract class AssumptionRule extends (Position => PositionRule)

class Position(val ante: Boolean, val index: Int) {
  def isAnte = ante
  def getIndex: Int = index
}

abstract class Signature

// this only works if all quantifiers are the same, otherwise we have distinguish here
class Sequent(val pref: Seq[(String, Sort)], val ante: IndexedSeq[Formula], val succ: IndexedSeq[Formula])

object Sequent {
  def apply(pref: Seq[(String, Sort)], ante: IndexedSeq[Formula], succ: IndexedSeq[Formula]) : Sequent = new Sequent(pref, ante, succ)
}

// proof rules:

// reorder antecedent

// reorder succedent

// cut
object Cut {
  def apply(f: Formula) : Rule = new Cut(f)
  private class Cut(f: Formula) extends Rule {
    def apply(s: Sequent): Seq[Sequent] = {
      val l = new Sequent(s.pref, s.ante :+ f, s.succ)
      val r = new Sequent(s.pref, s.ante, s.succ :+ f)
      List(l, r)
    }

    def name: String = "cut"

    def parameter: Formula = f
  }
}

// equality/equivalence rewriting

class SubstitutionPair[A <: Sort] (val n: Name[A], val t: Term[A]) 

class Substitution(l: List[SubstitutionPair[_]])

// uniform substitution
// this rule performs a backward substitution step. That is the substition applied to the conclusion yields the premise
object UniformSubstition {
  def apply(substitution: Substitution) : Rule = new UniformSubstition(substitution)

  private class UniformSubstition(subst: Substitution) extends Rule {
    def apply(s: Sequent): Seq[Sequent] = Vector(s)
  }
}

// AX close
object AxiomClose extends AssumptionRule {
  def apply(ass: Position): PositionRule = new AxiomClosePos(ass)

  private class AxiomClosePos(ass: Position) extends PositionRule {
    def apply(p: Position): Rule = {
      require(p.isAnte != ass.isAnte, "Axiom close can only be applied to one formula in the antecedent and one in the succedent")
      new AxiomClose(ass, p)
    }
  }

  private class AxiomClose(ass: Position, p: Position) extends Rule {

    def apply(s: Sequent): Seq[Sequent] = {
      if(ass.isAnte) {
        if(s.ante(ass.getIndex) == s.succ(p.getIndex)) {
          // close
          Nil
        } else {
          throw new IllegalArgumentException("The referenced formulas are not identical. Thus the current goal cannot be closed. " + s.ante(ass.getIndex) + " not the same as " + s.succ(p.getIndex))
        }
      } else {
        if(s.succ(ass.getIndex) == s.ante(p.getIndex)) {
          // close
          Nil
        } else {
          throw new IllegalArgumentException("The referenced formulas are not identical. Thus the current goal cannot be closed. " + s.succ(ass.getIndex) + " not the same as " + s.ante(p.getIndex))
        }
      }
    }
  }
}

// Impl right

object ImplRight extends PositionRule {
  def apply(p: Position): Rule = {
    assert(!p.isAnte)
    new ImplRight(p)
  }
  private class ImplRight(p: Position) extends Rule {
    def apply(s: Sequent): Seq[Sequent] = {
      val f = s.succ(p.getIndex)
      f match {
        case Implies(a, b) => List(Sequent(s.pref, s.ante :+ a, s.succ.updated(p.getIndex, b)))
        case _ => throw new IllegalArgumentException("Implies-Right can only be applied to implications. Tried to apply to: " + f)
      }
    }
  }
}

// Impl left
object ImplLeft extends PositionRule {
  def apply(p: Position): Rule = {
    assert(p.isAnte)
    new ImplLeft(p)
  }
  private class ImplLeft(p: Position) extends Rule {
    def apply(s: Sequent): Seq[Sequent] = {
      val f = s.ante(p.getIndex)
      f match {
        case Implies(a, b) => List(Sequent(s.pref, s.ante.updated(p.getIndex, a), s.succ), Sequent(s.pref, s.ante.patch(p.getIndex, Nil, 1), s.succ :+ a))
        case _ => throw new IllegalArgumentException("Implies-Left can only be applied to implications. Tried to apply to: " + f)
      }
    }
  }
}

// Not right
object NotRight extends PositionRule {
  def apply(p: Position): Rule = {
    assert(!p.isAnte)
    new NotRight(p)
  }
  private class NotRight(p: Position) extends Rule {
    def apply(s: Sequent): Seq[Sequent] = {
      val f = s.succ(p.getIndex)
      f match {
        case Not(a) => List(Sequent(s.pref, s.ante :+ a, s.succ.patch(p.getIndex, Nil, 1)))
        case _ => throw new IllegalArgumentException("Not-Right can only be applied to negation. Tried to apply to: " + f)
      }
    }
  }
}

// Not left
object NotLeft extends PositionRule {
  def apply(p: Position): Rule = {
    assert(p.isAnte)
    new NotLeft(p)
  }
  private class NotLeft(p: Position) extends Rule {
    def apply(s: Sequent): Seq[Sequent] = {
      val f = s.ante(p.getIndex)
      f match {
        case Not(a) => List(Sequent(s.pref, s.ante.patch(p.getIndex, Nil, 1), s.succ :+ a))
        case _ => throw new IllegalArgumentException("Not-Left can only be applied to negation. Tried to apply to: " + f)
      }
    }
  }
}

// And right
object AndRight extends PositionRule {
  def apply(p: Position): Rule = {
    assert(!p.isAnte)
    new AndRight(p)
  }
  private class AndRight(p: Position) extends Rule {
    def apply(s: Sequent): Seq[Sequent] = {
      val f = s.succ(p.getIndex)
      f match {
        case And(a, b) => List(Sequent(s.pref, s.ante, s.succ.updated(p.getIndex,a)), Sequent(s.pref, s.ante, s.succ.updated(p.getIndex, b)))
        case _ => throw new IllegalArgumentException("And-Right can only be applied to conjunctions. Tried to apply to: " + f)
      }
    }
  }
}

// And left
object AndLeft extends PositionRule {
  def apply(p: Position): Rule = {
    assert(p.isAnte)
    new AndLeft(p)
  }
  private class AndLeft(p: Position) extends Rule {
    def apply(s: Sequent): Seq[Sequent] = {
      val f = s.ante(p.getIndex)
      f match {
        case And(a, b) => List(Sequent(s.pref, s.ante.updated(p.getIndex, a) :+ b, s.succ))
        case _ => throw new IllegalArgumentException("And-Left can only be applied to conjunctions. Tried to apply to: " + f)
      }
    }
  }
}

// Or right
object OrRight extends PositionRule {
  def apply(p: Position): Rule = {
    assert(!p.isAnte)
    new OrRight(p)
  }
  private class OrRight(p: Position) extends Rule {
    def apply(s: Sequent): Seq[Sequent] = {
      val f = s.succ(p.getIndex)
      f match {
        case Or(a, b) => List(Sequent(s.pref, s.ante, s.succ.updated(p.getIndex, a) :+ b))
        case _ => throw new IllegalArgumentException("Or-Right can only be applied to disjunctions. Tried to apply to: " + f)
      }
    }
  }
}

// Or left
object OrLeft extends PositionRule {
  def apply(p: Position): Rule = {
    assert(p.isAnte)
    new OrLeft(p)
  }
  private class OrLeft(p: Position) extends Rule {
    def apply(s: Sequent): Seq[Sequent] = {
      val f = s.ante(p.getIndex)
      f match {
        case Or(a, b) => List(Sequent(s.pref, s.ante.updated(p.getIndex,a), s.succ), Sequent(s.pref, s.ante.updated(p.getIndex, b), s.succ))
        case _ => throw new IllegalArgumentException("Or-Left can only be applied to disjunctions. Tried to apply to: " + f)
      }
    }
  }
}

// Lookup Lemma (different justifications: Axiom, Lemma with proof, Oracle Lemma)

// remove duplicate antecedent (this should be a tactic)
// remove duplicate succedent (this should be a tactic)
// hide
object HideLeft extends PositionRule {
  def apply(p: Position): Rule = {
    assert(p.isAnte)
    new Hide(p)
  }
}
object HideRight extends PositionRule {
  def apply(p: Position): Rule = {
    assert(!p.isAnte)
    new Hide(p)
  }
}
class Hide(p: Position) extends Rule {
  def apply(s: Sequent): Seq[Sequent] = 
    if(p.isAnte)
      List(Sequent(s.pref, s.ante.patch(p.getIndex, Nil, 1), s.succ))
    else
      List(Sequent(s.pref, s.ante, s.succ.patch(p.getIndex, Nil, 1)))
}


// maybe:

// close by true (do we need this or is this derived?)

// alpha conversion

// quantifier instantiation

// remove known

// skolemize

// unskolemize

// forall-I

// forall-E

// merge sequent (or is this derived?)



}
// vim: set ts=4 sw=4 et:
