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
  val at: Function = Function("at", domain = Tuple(Real, Unit), sort = Real, interpreted = true)
  val max: Function = Function("max", domain = Tuple(Real, Real), sort = Real, interpreted = true)
  val min: Function = Function("min", domain = Tuple(Real, Real), sort = Real, interpreted = true)
  val abs: Function = Function("abs", domain = Real, sort = Real, interpreted = true)
  val wild: FuncOf = FuncOf(Function("wild", domain = Unit, sort = Unit, interpreted = true), Nothing)
  val init: FuncOf = FuncOf(Function("init", domain = Unit, sort = Unit, interpreted = true), Nothing)
  def flatten(ss: Statements): Statements = {
    ss match {
      case Block(ss) :: sss  => flatten(ss ++ sss)
      case s :: ss => s :: flatten(ss)
      case Nil => Nil
    }
  }

  def block(ss: Statements): Statement = {
    flatten(ss) match {
      case List(s) => s
      case ss => Block(ss)
    }
  }

}

sealed trait ASTNode {
  var location: Option[Int] = None
  def setLocation(loc: Int): Unit = { location = Some(loc)}
}

final case class Proof(ss: List[Statement])

// A proof-method expresses a single step of unstructured heuristic proof,
// generally as justification of a single step of some structured proof.
sealed trait Method extends ASTNode
// constructive real-closed field arithmetic
case class RCF() extends Method {}
// general-purpose auto heuristic
case class Auto() extends Method {}
// propositional steps
case class Prop() extends Method {}
// introduce an assumption used in method
case class Using(use: List[Selector], method: Method) extends Method {}
// discharge goal with structured proof
case class ByProof(proof: Proof) extends Method {}

sealed trait ProofTerm extends ASTNode
case class ProofVar(x: Ident) extends ProofTerm {}
case class ProofInstance(e: Expression) extends ProofTerm {}
case class ProofApp(m: ProofTerm, n: ProofTerm) extends ProofTerm {}

sealed trait Selector extends ASTNode
case class ForwardSelector(forward: ProofTerm) extends Selector {}
case class PatternSelector(e: Expression) extends Selector {}

sealed trait AsgnPat extends ASTNode
case class NoPat() extends AsgnPat
case class WildPat() extends AsgnPat
// @TODO: make ident optional for assignments
case class VarPat(p: Ident, x: Option[Variable] = None) extends AsgnPat
case class TuplePat(pats: List[AsgnPat]) extends AsgnPat

sealed trait Statement extends ASTNode
// x is a formula pattern in assume and assert
case class Assume(x: Expression, f: Formula) extends Statement
case class Assert(x: Expression, f: Formula, child: Method) extends Statement
case class Modify(x: AsgnPat, hp: Either[Term, Unit]) extends Statement
case class Label(st: TimeIdent) extends Statement
case class Note(x: Ident, proof: ProofTerm) extends Statement
case class LetFun(x: Ident, args: List[Ident], e: Expression) extends Statement
case class Match(pat: Expression, e: Expression) extends Statement
case class Block( ss: Statements) extends Statement
case class Switch(pats: List[(Expression, Statement)]) extends Statement
case class BoxChoice(left: Statement, right: Statement) extends Statement
// x is a pattern
case class While(x: Expression, j: Formula, ss: Statement) extends Statement
case class BoxLoop(s: Statement) extends Statement
case class Ghost(ss: Statement) extends Statement
case class InverseGhost(ss: Statement) extends Statement
case class PrintGoal(msg: String) extends Statement
case class ProveODE(ds: DiffStatement, dc: DomainStatement) extends Statement //de: DifferentialProgram
// Debugging feature. Equivalent to "now" in all respects, annotated with the fact that it was once "was"
// before transformation by the proof checker
case class Was(now: Statement, was: Statement) extends Statement

sealed trait DiffStatement extends ASTNode
case class AtomicODEStatement(dp: AtomicODE) extends DiffStatement
case class DiffProductStatement(l: DiffStatement, r: DiffStatement) extends DiffStatement
case class DiffGhostStatement(ds: DiffStatement) extends DiffStatement
case class InverseDiffGhostStatement(ds: DiffStatement) extends DiffStatement

sealed trait DomainStatement extends ASTNode
// x is formula pattern in assume and assert
case class DomAssume(x: Expression, f:Formula) extends DomainStatement
case class DomAssert(x: Expression, f:Formula, child: Method) extends DomainStatement
case class DomWeak(dc: DomainStatement) extends DomainStatement
case class DomModify(x: AsgnPat, hp: Assign) extends DomainStatement
case class DomAnd(l: DomainStatement, r: DomainStatement) extends DomainStatement

// @TODO: Implement the rest
case class Context (proofVars: Set[String]) {
  val ghostVar: String = "ghost"
  def add(ident: String): Context = Context(proofVars.+(ident))

  def fresh: String = {
    var i = 0
    while(proofVars.contains(ghostVar + i)) {
      i = i + 1
    }
    ghostVar + i
  }

  def next: Context = add(fresh)
}