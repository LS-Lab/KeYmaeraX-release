package edu.cmu.cs.ls.keymaerax.pt

import edu.cmu.cs.ls.keymaerax.core.{Equiv, Equal, NamedSymbol, USubst, Formula}

/**
 * Created by nfulton on 10/15/15.
 */
sealed abstract class ProofTerm()
case class dlConstant(f : Formula) extends ProofTerm
case class folrConstant(f : Formula) extends ProofTerm
case class AndTerm(left: ProofTerm, right: ProofTerm) extends ProofTerm
case class ApplicationTerm(left: ProofTerm, premise: Formula, right: ProofTerm) extends ProofTerm
case class RightEquivalence(left: ProofTerm, premise: Formula, right: ProofTerm) extends ProofTerm
case class LeftEquivalence(left: ProofTerm, premise: Formula, right: ProofTerm) extends ProofTerm
case class usubstTerm(child: ProofTerm, premise: Formula, substitution: List[USubst]) extends ProofTerm
case class BoundRenamingTerm(child: ProofTerm, premise: Formula, renaming: List[(NamedSymbol, NamedSymbol)]) extends ProofTerm
case class CTTerm(child: Formula, premise: Equal, substitution: List[USubst]) extends ProofTerm
case class CQTerm(child: Formula, premise: Equal, substitution: List[USubst]) extends ProofTerm
case class CETerm(child: Formula, premise: Equiv, substitution: List[USubst]) extends ProofTerm