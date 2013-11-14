abstract class Proof

abstract class ProofNode(s: Sequent, p: ProofNode, var ruleName: String, var children: Seq[ProofNode]) {
  def apply(rule: String, pos: String);
}

abstract class Signature

// this only works if all quantifiers are the same, otherwise we have distinguish here
class Sequent(pref: Seq[(Name, Sort)], ante: Seq[Term], succ: Seq[Term])

// proof rules:

// cut

// alpha conversion

// quantifier instantiation

// AX close

// close by true (do we need this or is this derived?)

// remove known

// skolemize

// unskolemize

// forall-I

// forall-E

// merge sequent (or is this derived?)




// vim: set ts=4 sw=4 et:
