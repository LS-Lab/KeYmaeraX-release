abstract class Proof

abstract class ProofNode(s: Sequent, p: ProofNode, var ruleName: String, var children: Seq[ProofNode]) {
  def apply(rule: Rule);
  def apply(rule: PositionRule, p: Position);
}

abstract class Rule extends Sequent => Seq[Sequent]

abstract class PositionRule extends Position => Rule

abstract class Position

abstract class Signature

// this only works if all quantifiers are the same, otherwise we have distinguish here
class Sequent(pref: Seq[(Name, Sort)], ante: IndexedSeq[Term], succ: IndexedSeq[Term])

// proof rules:

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

// Impl left

// Not right

// Not left

// And right

// And left

// Or right

// Or left

// Lookup Lemma (different justifications: Axiom, Lemma with proof, Oracle Lemma)



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
