/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.pt

import org.keymaerax.core._

/**
 * A Proof Term is a syntactic internalization of a proof of a differential dynamic logic theorem. Proof Terms can be
 * converted to Provables by the [[ProofChecker]].
 *
 * Created by nfulton on 10/15/15.
 * @see
 *   [[ProofChecker]]
 * @author
 *   Nathan Fulton
 * @author
 *   Brandon Bohrer
 */
sealed abstract class ProofTerm {

  /* HACK: Code elsewhere uses equality tests on ProvableSigs under the assumption that equality depends only on the conclusion and subgoals.
   * we make this more true by considering all proofterms equal to each other.
   * We should consider changing the equality function on ProvableSig, but this is a less invasive change
   * */
  override def equals(other: Any): Boolean = {
    other match {
      case _: ProofTerm => true
      case _ => false
    }
  }

  def prettyString: String = this.toString

  // Number of constructors in the proof term
  def numCons: Int = {
    this match {
      case _: FOLRConstant => 1
      case _: AxiomTerm => 1
      case _: RuleTerm => 1
      case NoProof => 1
      case UsubstProvableTerm(child, _) => child.numCons + 1
      case RuleApplication(child, _, _) => child.numCons + 1
      case ProlongationTerm(child, pro) => child.numCons + pro.numCons + 1
      case ForwardNewConsequenceTerm(child, _, _) => child.numCons + 1
      case URenameTerm(child, _) => child.numCons + 1
      case Sub(child, sub, _) => child.numCons + sub.numCons + 1
      case _: StartProof => 1
    }
  }

  // All axioms that appear in the proof
  def axiomsUsed: Set[String] = {
    this match {
      case AxiomTerm(name) => Set(name)
      case _: FOLRConstant => Set.empty
      case _: RuleTerm => Set.empty
      case NoProof => Set.empty
      case _: StartProof => Set.empty
      case _: URenameTerm => Set.empty
      case UsubstProvableTerm(child, _) => child.axiomsUsed
      case RuleApplication(child, _, _) => child.axiomsUsed
      case ProlongationTerm(child, pro) => child.axiomsUsed ++ pro.axiomsUsed
      case ForwardNewConsequenceTerm(child, _, _) => child.axiomsUsed
      case Sub(child, sub, _) => child.axiomsUsed ++ sub.axiomsUsed

    }
  }

  // All rules that appear in the proof
  def rulesUsed: Set[String] = {
    this match {
      case RuleTerm(name) => Set(name)
      case RuleApplication(child, rule, _) => child.rulesUsed + rule.name
      case _: AxiomTerm => Set.empty
      case _: FOLRConstant => Set.empty
      case NoProof => Set.empty
      case _: StartProof => Set.empty
      case _: URenameTerm => Set.empty
      case UsubstProvableTerm(child, _) => child.rulesUsed
      case ProlongationTerm(child, pro) => child.rulesUsed ++ pro.rulesUsed
      case ForwardNewConsequenceTerm(child, _, _) => child.rulesUsed
      case Sub(child, sub, _) => child.rulesUsed ++ sub.rulesUsed
    }
  }

  // All first-order logic assumptions that appear in the proof
  def arithmeticGoals: Set[Formula] = {
    this match {
      case FOLRConstant(f) => Set(f)
      case _: RuleTerm => Set.empty
      case _: AxiomTerm => Set.empty
      case NoProof => Set.empty
      case _: StartProof => Set.empty
      case _: URenameTerm => Set.empty
      case UsubstProvableTerm(child, _) => child.arithmeticGoals
      case ProlongationTerm(child, pro) => child.arithmeticGoals ++ pro.arithmeticGoals
      case ForwardNewConsequenceTerm(child, _, _) => child.arithmeticGoals
      case RuleApplication(child, _, _) => child.arithmeticGoals
      case Sub(child, sub, _) => child.arithmeticGoals ++ sub.arithmeticGoals
    }
  }

  val wordSize = 8

  private def expBytesEstimate(f: Expression): Int = {
    f match {
      case _: Atomic => 2 * wordSize // poor estimate because different numbers of arguments of different types
      case e: UnaryComposite => 2 * wordSize + expBytesEstimate(e.child)
      case e: BinaryComposite => 3 * wordSize + expBytesEstimate(e.left) + expBytesEstimate(e.right)
      case e: ApplicationOf => 3 * wordSize + 6 * wordSize + expBytesEstimate(e.child) // function is six or so words?
      case _: NamedSymbol => 3 * wordSize // also poor estimate
      case q: Quantified => 3 * wordSize + expBytesEstimate(q.child) // also poor estimate
      case m: Modal => 3 * wordSize + expBytesEstimate(m.child) + expBytesEstimate(m.program)
      case o: ODESystem => 3 * wordSize + expBytesEstimate(o.constraint) + expBytesEstimate(o.ode)
    }
  }

  private def subBytesEstimate(subst: USubst): Int = {
    subst.subsDefsInput.foldLeft(0)((acc, pair) => acc + expBytesEstimate(pair.what) + expBytesEstimate(pair.repl))
  }

  private def sequentBytesEstimate(sequent: Sequent): Int = {
    sequent
      .succ
      .foldLeft(sequent.ante.foldLeft(0)((acc, fml) => acc + expBytesEstimate(fml)))((acc, fml) =>
        acc + expBytesEstimate(fml)
      )
  }

  private def ruleBytesEstimate(rule: Rule): Int = { wordSize }

  private val intSizeEstimate = 2 * wordSize

  private def seqBytesEstimate[T](s: Seq[T]): Int = { (2 + s.length) * wordSize }

  // Estimate of the size in bytes of a proof term
  def bytesEstimate: Int = {
    this match {
      case FOLRConstant(f) => expBytesEstimate(f) + 2 * wordSize // over-estimates due to structure sharing
      case RuleTerm(_) => 2 * wordSize // Assume names are interned
      case AxiomTerm(_) => 2 * wordSize
      case NoProof => wordSize
      case StartProof(seq) => 2 * wordSize + sequentBytesEstimate(seq)
      case UsubstProvableTerm(child, sub) => 3 * wordSize + child.bytesEstimate + subBytesEstimate(sub)
      case ProlongationTerm(child, pro) => 3 * wordSize + child.bytesEstimate + pro.bytesEstimate
      case ForwardNewConsequenceTerm(child, con, rule) => 4 * wordSize + child.bytesEstimate +
          sequentBytesEstimate(con) + ruleBytesEstimate(rule)
      case r @ RuleApplication(child, _, _) => 6 * wordSize + child.bytesEstimate + intSizeEstimate +
          seqBytesEstimate(r.positions) + seqBytesEstimate(r.args)
      case URenameTerm(child, ren) => child.bytesEstimate + seqBytesEstimate(List(ren.what, ren.repl)) // @todo
      case Sub(child, sub, _) => 4 * wordSize + child.bytesEstimate + sub.bytesEstimate + intSizeEstimate
    }
  }
}

case class FOLRConstant(f: Formula) extends ProofTerm

/** Witness for rule application. */
case class RuleApplication(child: ProofTerm, rule: Rule, subgoal: Int) extends ProofTerm {
  val (positions: List[SeqPos], args: List[Expression]) = rule match {
    // @todo do a total pattern match on all rules in the core and produce individualized proof terms for each of them.
    // This is necessary because we need positions where the rule should be applied within the *sequent* in addition to subgoal,
    // which is the position within the *provable*. Alternatively a subtype hierarchy for Rule would do the trick...
    case Close(ante, succ) => (List(ante, succ), List.empty)
    case CoHide2(ante, succ) => (List(ante, succ), List.empty)
    case CutRight(fml, succ) => (List(succ), List(fml))
    case ImplyRight(succ) => (List(succ), List.empty)
    case AndRight(succ) => (List(succ), List.empty)
    case CoHideRight(succ) => (List(succ), List.empty)
    case CommuteEquivRight(succ) => (List(succ), List.empty)
    case EquivifyRight(succ) => (List(succ), List.empty)
    case EquivRight(succ) => (List(succ), List.empty)
    case NotRight(succ) => (List(succ), List.empty)
    case CloseTrue(succ) => (List(succ), List.empty)
    case HideRight(succ) => (List(succ), List.empty)
    case OrRight(succ) => (List(succ), List.empty)

    case OrLeft(ante) => (List(ante), List.empty)
    case AndLeft(ante) => (List(ante), List.empty)
    case HideLeft(ante) => (List(ante), List.empty)
    case CutLeft(fml, ante) => (List(ante), List(fml))
    case ImplyLeft(ante) => (List(ante), List.empty)
    case NotLeft(ante) => (List(ante), List.empty)
    case EquivLeft(ante) => (List(ante), List.empty)
    case CloseFalse(ante) => (List(ante), List.empty)

    case BoundRenaming(what, repl, seq: SeqPos) => (List(seq), List(what, repl))
    case UniformRenaming(what, repl) => (List.empty, List(what, repl))
    case Skolemize(seq: SeqPos) => (List(seq), List.empty)
    case Cut(fml) => (List.empty, List(fml))

    case _ => throw new Exception(
        s"TermProvable.apply(Rule,provable pos) is not completely implemented. Missing case: ${rule.name}"
      ) // See @todo above add cases as necessary...
  }
}

//@todo add to theory.
/* @todo: could unify RuleTerm and AxiomTerm */
case class RuleTerm(name: String) extends ProofTerm

case class UsubstProvableTerm(child: ProofTerm, substitution: USubst) extends ProofTerm

case class AxiomTerm(name: String) extends ProofTerm

case class ForwardNewConsequenceTerm(child: ProofTerm, newConsequence: Sequent, rule: Rule) extends ProofTerm

case class ProlongationTerm(child: ProofTerm, prolongation: ProofTerm) extends ProofTerm

case class StartProof(phi: Sequent) extends ProofTerm

case object NoProof extends ProofTerm

case class URenameTerm(child: ProofTerm, ren: URename) extends ProofTerm

case class Sub(child: ProofTerm, sub: ProofTerm, idx: Int) extends ProofTerm
