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

final case class Proof(ss: List[Statement])

sealed trait Method {}
case class RCF() extends Method {}
case class Auto() extends Method {}
case class Prop() extends Method {}
case class Using(use: List[Selector], method: Method) extends Method {}
case class ByProof(proof: Proof) extends Method {}

sealed trait ProofTerm {}
case class ProofVar(x: Ident) extends ProofTerm {}
case class ProofInstance(e: Expression) extends ProofTerm {}
case class ProofApp(m: ProofTerm, n: ProofTerm) extends ProofTerm {}

sealed trait Selector {}
case class ForwardSelector(forward: ProofTerm) extends Selector {}
case class PatternSelector(e: Expression) extends Selector {}

sealed trait IdPat
case class NoPat() extends IdPat
case class WildPat() extends IdPat
// @TODO: make ident optional for assignments
case class VarPat(p: Ident, x: Option[Variable] = None) extends IdPat
case class TuplePat(pats: List[IdPat]) extends IdPat

sealed trait Statement {}
case class Assume(x: IdPat, f: Formula) extends Statement
case class Assert(x: IdPat, f: Formula, child: Method) extends Statement
case class Modify(x: IdPat, hp: Either[Term, Unit]) extends Statement
case class Label(st: TimeIdent) extends Statement
case class Note(x: Ident, proof: ProofTerm) extends Statement
case class LetFun(x: Ident, arg: Ident, e: Expression) extends Statement
case class Match(pat: Expression, e: Expression) extends Statement
case class Block( ss: Statements) extends Statement
case class Switch(pats: List[(Expression, Statement)]) extends Statement
case class BoxChoice(left: Statement, right: Statement) extends Statement
case class While(x: IdPat, j: Formula, ss: Statement) extends Statement
case class BoxLoop(s: Statement) extends Statement
case class Ghost(ss: Statement) extends Statement
case class InverseGhost(ss: Statement) extends Statement
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
