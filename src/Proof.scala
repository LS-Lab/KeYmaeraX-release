abstract class Proof

abstract class ProofNode(s: Sequent, p: ProofNode, var ruleName: String, var children: Seq[ProofNode]) {
  def apply(rule: Rule);
  def apply(rule: PositionRule, p: Position);
}

abstract class Rule extends Sequent => Seq[Sequent]

abstract class PositionRule extends Position => Rule

abstract class Position {

  abstract def isAnte: boolean
  abstract def getIndex: Int
}

abstract class Signature

// this only works if all quantifiers are the same, otherwise we have distinguish here
class Sequent(pref: Seq[(Name, Sort)], ante: IndexedSeq[Term], succ: IndexedSeq[Term])

// proof rules:

// reorder antecedent

// reorder succedent

// cut
class Cut(f: Formula) extends Rule {
  def apply(s: Sequent): Seq[Sequent] = {
    val (pref, ante, succ) = s
    val l = Sequent(pref, ante ++ f, succ)
    val r = Sequent(pref, ante, succ ++ f)
    new List(l, r)
  }

  def name: String = "cut"

  def parameter: Formula = f
}

// equality/equivalence rewriting

// uniform substitution

// AX close
// TODO: how do we represent this with just a single position?

// Impl right

object ImplRight extends PositionRule {
  def apply(p: Position) = {
    assert(!p.isAnte)
    new ImplRight(p)
  }
}
class ImplRight(p: Position) extends Rule {
  def apply(s: Sequent): Seq[Sequent] = {
    val f = s.succ(p.getIndex)
    f match {
      case Impl(a, b) => List(Sequent(s.pref, s.ante :+ a, s.succ.updated(p.getIndex, b)))
      case _ => throw new IllegalArgumentException("Implies-Right can only be applied to implications. Tried to apply to: " + f)
    }
  }
}

// Impl left
object ImplLeft extends PositionRule {
  def apply(p: Position) = {
    assert(p.isAnte)
    new ImplLeft(p)
  }
}
class ImplLeft(p: Position) extends Rule {
  def apply(s: Sequent): Seq[Sequent] = {
    val f = s.ante(p.getIndex)
    f match {
      case Impl(a, b) => List(Sequent(s.pref, s.ante.updated(p.getIndex, a), s.succ), Sequent(s.pref, s.ante.patch(p.getIndex, Nil, 1), s.succ :+ a))
      case _ => throw new IllegalArgumentException("Implies-Left can only be applied to implications. Tried to apply to: " + f)
    }
  }
}

// Not right
object NotRight extends PositionRule {
  def apply(p: Position) = {
    assert(!p.isAnte)
    new NotRight(p)
  }
}
class NotRight(p: Position) extends Rule {
  def apply(s: Sequent): Seq[Sequent] = {
    val f = s.succ(p.getIndex)
    f match {
      case Not(a) => List(Sequent(s.pref, s.ante :+ a, s.succ.patch(p.getIndex, Nil, 1)))
      case _ => throw new IllegalArgumentException("Not-Right can only be applied to negation. Tried to apply to: " + f)
    }
  }
}

// Not left
object NotLeft extends PositionRule {
  def apply(p: Position) = {
    assert(p.isAnte)
    new NotLeft(p)
  }
}
class NotLeft(p: Position) extends Rule {
  def apply(s: Sequent): Seq[Sequent] = {
    val f = s.ante(p.getIndex)
    f match {
      case Not(a) => List(Sequent(s.pref, s.ante.patch(p.getIndex, Nil, 1), s.succ :+ a))
      case _ => throw new IllegalArgumentException("Not-Left can only be applied to negation. Tried to apply to: " + f)
    }
  }
}

// And right
object AndRight extends PositionRule {
  def apply(p: Position) = {
    assert(!p.isAnte)
    new AndRight(p)
  }
}
class AndRight(p: Position) extends Rule {
  def apply(s: Sequent): Seq[Sequent] = {
    val f = s.succ(p.getIndex)
    f match {
      case And(a, b) => List(Sequent(s.pref, s.ante, s.succ.updated(p.getIndex,a)), Sequent(s.pref, s.ante, s.succ.updated(p.getIndex, b)))
      case _ => throw new IllegalArgumentException("And-Right can only be applied to conjunctions. Tried to apply to: " + f)
    }
  }
}

// And left
object AndLeft extends PositionRule {
  def apply(p: Position) = {
    assert(p.isAnte)
    new AndLeft(p)
  }
}
class AndLeft(p: Position) extends Rule {
  def apply(s: Sequent): Seq[Sequent] = {
    val f = s.ante(p.getIndex)
    f match {
      case And(a, b) => List(Sequent(s.pref, s.ante.updated(p.getIndex, a) :+ b, s.succ))
      case _ => throw new IllegalArgumentException("And-Left can only be applied to conjunctions. Tried to apply to: " + f)
    }
  }
}

// Or right
object OrRight extends PositionRule {
  def apply(p: Position) = {
    assert(!p.isAnte)
    new OrRight(p)
  }
}
class OrRight(p: Position) extends Rule {
  def apply(s: Sequent): Seq[Sequent] = {
    val f = s.succ(p.getIndex)
    f match {
      case Or(a, b) => List(Sequent(s.pref, s.ante, s.succ.updated(p.getIndex, a) :+ b))
      case _ => throw new IllegalArgumentException("Or-Right can only be applied to disjunctions. Tried to apply to: " + f)
    }
  }
}

// Or left
object OrLeft extends PositionRule {
  def apply(p: Position) = {
    assert(p.isAnte)
    new AndLeft(p)
  }
}
class OrLeft(p: Position) extends Rule {
  def apply(s: Sequent): Seq[Sequent] = {
    val f = s.ante(p.getIndex)
    f match {
      case Or(a, b) => List(Sequent(s.pref, s.ante.updated(p.getIndex,a), s.succ), Sequent(s.pref, s.ante.updated(p.getIndex, b), s.succ))
      case _ => throw new IllegalArgumentException("Or-Left can only be applied to disjunctions. Tried to apply to: " + f)
    }
  }
}

// Lookup Lemma (different justifications: Axiom, Lemma with proof, Oracle Lemma)

// remove duplicate antecedent (this should be a tactic)
// remove duplicate succedent (this should be a tactic)
// hide
object HideLeft extends PositionRule {
  def apply(p: Position) = {
    assert(p.isAnte)
    new Hide(p)
  }
}
object HideRight extends PositionRule {
  def apply(p: Position) = {
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




// vim: set ts=4 sw=4 et:
