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
import edu.cmu.cs.ls.keymaerax.core._

object KaisarProof {
  type Ident = String
  type TimeIdent = String
}

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


final case class Proof(ss: List[Statement])

//@TODO: More statementy and less expressiony
sealed trait Statement {}
case class Have(x: Ident, f: Formula, just: Method) extends Statement
case class Show(phi: Formula, proof: Method) extends Statement
case class Match(pat: Expression, e: Expression) extends Statement
case class LetFun(x: Ident, arg: Ident, e: Expression) extends Statement
case class Note(x: Variable, proof: ProofTerm) extends Statement
case class Label(st: TimeIdent) extends Statement
case class Block(ss: List[Statement]) extends Statement
case class Step(r: RuleSpec) extends Statement
case class Invariant(ip: List[InvariantStep]) extends Statement
case class BoxChoice(left: List[Statement], right: List[Statement]) extends Statement
case class DiamondLeft(ss: List[Statement]) extends Statement
case class DiamondRight(ss: List[Statement]) extends Statement
case class PatternMatch(pats: List[(Expression, List[Statement])]) extends Statement
// For debugging
case class PrintGoal(msg: String) extends Statement

//case class Ghost(gvar: Variable, gterm: Term, ginv: Formula, x0: Term, pre: SP, inv: SP, tail: IP) extends IP
//case class Finally(tail: SP) extends IP
sealed trait InvariantStep
case class Inv(x: Variable, fml: Formula, pre: Proof, inv: Proof) extends InvariantStep
case class Ghost(ghost: Assign) extends InvariantStep

/*
case class RBMid(x: Variable, fml: Formula) extends RuleSpec
case class RBAbbrev(xphi: Variable, x: Variable, theta: Term) extends RuleSpec
case class RDMid(fml: Formula) extends RuleSpec
case class RIdent(x: String) extends RuleSpec
 */
sealed trait RuleSpec {}
trait BoxRule extends RuleSpec {}
trait DiamondRule extends RuleSpec {}

case class Modify(hp: Assign) extends RuleSpec

case class Assume(x: Ident, f: Formula) extends BoxRule
case class Assert(x: Ident, f: Formula, child: Method) extends DiamondRule
case class BAssignAny(x: Variable) extends BoxRule
case class BSolve(t: Variable, fmlT: Formula, dc: Variable, fmlDC: Formula, sols: List[(Variable, Formula)]) extends BoxRule
case class DAssignAny(x: Variable, xVal: Term) extends DiamondRule
case class DSolve(t: Variable, fmlT: Formula, dc: Variable, fmlDC: Formula, sols: List[(Variable, Formula)]) extends DiamondRule




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

