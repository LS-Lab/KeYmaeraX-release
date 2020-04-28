/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
/**
  * Proof data structures for Kaisar
  * @author Brandon Bohrer
  */
package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import KaisarProof._
import edu.cmu.cs.ls.keymaerax.cdgl.Metric
import edu.cmu.cs.ls.keymaerax.core._

object KaisarProof {
  type Ident = String
  type TimeIdent = String
  type Statements = List[Statement]
}

final case class Proof(ss: List[Statement])

sealed trait Method {}
case class RCF() extends Method {}
case class Auto() extends Method {}
case class Prop() extends Method {}
case class Using(use: List[Selector], method: Method) extends Method {}
case class ByProof(proof: Proof) extends Method {}

sealed trait ProofTerm {}
case class ProofVar(x: Ident) extends ProofTerm {}
case class ProofApp(m: ProofTerm, n: ProofTerm) extends ProofTerm {}
case class ProofInst(m: ProofTerm, t: Term) extends ProofTerm {}

sealed trait Selector {}
case class ForwardSelector(forward: ProofTerm) extends Selector {}
case class PatternSelector(e: Expression) extends Selector {}

sealed trait IdPat
case class NoPat() extends IdPat
case class WildPat() extends IdPat
// @TODO: make ident optional for assignments
case class VarPat(p: Ident, x: Option[Variable] = None) extends IdPat
case class TuplePat(pats: List[IdPat]) extends IdPat

/*sealed trait AssignPat
case class NoAPat() extends IdPat
case class WildAPat() extends IdPat
case class VarAPat(p: Ident, x: Variable) extends IdPat
case class TupleAPat(pats: List[IdPat]) extends IdPat*/

sealed trait Statement {}
case class Assume(x: IdPat, f: Formula) extends Statement
case class Assert(x: IdPat, f: Formula, child: Method) extends Statement
case class Modify(x: IdPat, hp: Either[Term, Unit]) extends Statement
case class Label(st: TimeIdent) extends Statement
case class Note(x: Ident, proof: ProofTerm) extends Statement
case class LetFun(x: Ident, arg: Ident, e: Expression) extends Statement
case class Match(pat: Expression, e: Expression) extends Statement
case class Block(ss: Statements) extends Statement
case class Switch(pats: List[(Expression, Statements)]) extends Statement
case class BoxChoice(left: Statements, right: Statements) extends Statement
case class While(x: IdPat, j: Formula, ss: Statements) extends Statement
case class BoxLoop(s: Statement) extends Statement
case class Ghost(ss: Statements) extends Statement
case class InverseGhost(ss: Statements) extends Statement
case class PrintGoal(msg: String) extends Statement
case class ProveODE(ds: DiffStatement, dc: DomainStatement) extends Statement //de: DifferentialProgram

sealed trait DiffStatement
case class AtomicODEStatement(dp: AtomicODE) extends DiffStatement
case class DiffProductStatement(l: DiffStatement, r: DiffStatement) extends DiffStatement
case class DiffGhostStatement(ds: DiffStatement) extends DiffStatement
case class InverseDiffGhostStatement(ds: DiffStatement) extends DiffStatement

sealed trait DomainStatement
case class DomAssume(x: IdPat, f:Formula) extends DomainStatement
case class DomAssert(x: IdPat, f:Formula, child: Method) extends DomainStatement
case class DomWeak(dc: DomainStatement) extends DomainStatement
case class DomModify(x: IdPat, hp: Assign) extends DomainStatement
case class DomAnd(l: DomainStatement, r: DomainStatement) extends DomainStatement
//case class DomInverseGhost(dc: DomainStatement) extends DomainStatement

//case class For(vj: Ident, j: Formula, m: Ident, init: Term, decr: Term) extends RuleSpec
/*sealed trait InvariantStep extends RuleSpec
case class Invariant(x: Ident, fml: Formula, inv: Proof) extends InvariantStep

sealed trait RuleSpec extends Statement
trait BoxRule extends RuleSpec {}
trait DiamondRule extends RuleSpec {}*/

//case class BSolve(o, vdc: Ident, dc: Formula, vdur: Ident) extends BoxRule
//case class DSolve(ode: DifferentialProgram, vdc: Ident, dcProof: Proof, vdur: Ident, durProof: Proof) extends DiamondRule

// For debugging
//case class Have(x: Ident, f: Formula, just: Method) extends Statement
//case class Show(phi: Formula, proof: Method) extends Statement
//case class BAssignAny(x: Variable) extends BoxRule
//case class Ghost(ghost: Assign) extends InvariantStep
//case class DAssignAny(x: Variable, xVal: Term) extends DiamondRule
//case class Yield() extends RuleSpec

// History records hr
/*abstract class HistChange

case class HCAssign(hp: Assign) extends HistChange {
  def rename(from: Variable, to: Variable): HCAssign = {
    val (name, e) = (hp.x, hp.e)
    HCAssign(Assign(if (name == from) to else name, URename(from, to)(e)))
  }
}

case class HCRename(baseName: BaseVariable, permName: BaseVariable, defn: Option[AntePos] = None) extends HistChange {
  assert(baseName.name == permName.name && baseName.index.isEmpty)
}

case class HCTimeStep(ts: TimeName) extends HistChange*/
/*
case class RBMid(x: Variable, fml: Formula) extends RuleSpec
case class RBAbbrev(xphi: Variable, x: Variable, theta: Term) extends RuleSpec
case class RDMid(fml: Formula) extends RuleSpec
case class RIdent(x: String) extends RuleSpec
 */
//case class Ghost(gvar: Variable, gterm: Term, ginv: Formula, x0: Term, pre: SP, inv: SP, tail: IP) extends IP
//case class Finally(tail: SP) extends IP

