package edu.cmu.cs.ls.keymaerax.bellerophon.parser

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.core.Expression
import edu.cmu.cs.ls.keymaerax.infrastruct.RenUSubst

import scala.collection.immutable._

/**
  * @note Needs some work because the constructors for Belle expressions are far more diverse than
  *       the constructors for KeYmaera X expressions
  */
sealed trait BelleOpSpec {
  val terminal: BelleTerminal
  val precedence: Int
  val leftAssoc: Boolean

  def <(other: BelleOpSpec): Boolean = this.precedence < other.precedence
  def >(other: BelleOpSpec): Boolean = this.precedence > other.precedence
  def ==(other: BelleOpSpec): Boolean = this.precedence == other.precedence
}
case class BelleUnaryOpSpec(terminal: BelleTerminal, precedence: Int, leftAssoc: Boolean) extends BelleOpSpec
case class BelleBinaryOpSpec(terminal: BelleTerminal, precedence: Int, leftAssoc: Boolean) extends BelleOpSpec
case class BelleBranchingOpSpec(terminal: BelleTerminal, precedence: Int, leftAssoc: Boolean, constructor : Seq[BelleExpr] => BelleExpr) extends BelleOpSpec
case class BelleSaturatingOpSpec(terminal: BelleTerminal, precedence: Int, leftAssoc: Boolean, constructor : (BelleExpr, BelleType) => BelleExpr) extends BelleOpSpec
case class BelleRepeatOpSpec(terminal: BelleTerminal, precedence: Int, leftAssoc: Boolean, constructor : (BelleExpr, Int, BelleType) => BelleExpr) extends BelleOpSpec
case class BelleUSubstOpSpec(terminal: BelleTerminal, precedence: Int, leftAssoc: Boolean, constructor : Seq[(BelleType, RenUSubst => BelleExpr)] => BelleExpr) extends BelleOpSpec
case class BelleLetOpSpec(terminal: BelleTerminal, precedence: Int, leftAssoc: Boolean, constructor : (Expression, Expression, BelleExpr) => BelleExpr) extends BelleOpSpec
case class BelleDefTacticOpSpec(terminal: BelleTerminal, precedence: Int, leftAssoc: Boolean, constructor : (String, BelleExpr) => BelleExpr) extends BelleOpSpec

case class BelleUnitOpSpec[T,S](terminal: BelleTerminal, precedence:Int, leftAssoc: Boolean, constructor: T => S) extends BelleOpSpec

object BelleOpSpec {
  private val none = PSEUDO

  val position: BelleOpSpec = BelleUnitOpSpec(none, 100, leftAssoc=false, (x:Any) => ???)

  val base: BelleOpSpec     = BelleUnitOpSpec(none, 0, leftAssoc=false, (s:String) => ???)
  val seq: BelleOpSpec      = BelleBinaryOpSpec(SEQ_COMBINATOR,    200, leftAssoc=false)
  val either: BelleOpSpec   = BelleBinaryOpSpec(EITHER_COMBINATOR, 220, leftAssoc=false)
  val star: BelleOpSpec     = BelleUnaryOpSpec(KLEENE_STAR,        150, leftAssoc=false)
  val saturate: BelleOpSpec = BelleSaturatingOpSpec(SATURATE, 150, leftAssoc=false, (child: BelleExpr, _: BelleType) => SaturateTactic.apply(child))
  val repeat: Int=>BelleOpSpec = (i: Int) => BelleRepeatOpSpec(N_TIMES(i), 150, leftAssoc=false, (child: BelleExpr, times: Int, _: BelleType) => RepeatTactic.apply(child, times))
  val branch: BelleOpSpec   = BelleBranchingOpSpec(BRANCH_COMBINATOR, 100, leftAssoc=false, BranchTactic.apply)
  val partial: BelleOpSpec  = BelleUnaryOpSpec(PARTIAL, 300, leftAssoc=false)
  val onall: BelleOpSpec    = BelleUnaryOpSpec(ON_ALL, 100, leftAssoc=false)
  val usubst: BelleOpSpec   = BelleUSubstOpSpec(US_MATCH, 100, leftAssoc=false, USubstPatternTactic.apply)
  val let: BelleOpSpec      = BelleLetOpSpec(LET, 100, leftAssoc=false, Let.apply)
  val defTactic: BelleOpSpec= BelleDefTacticOpSpec(TACTIC, 100, leftAssoc=false, DefTactic.apply)

  def op(e: BelleExpr): BelleOpSpec = e match {
    case _: SeqTactic      => seq
    case _: EitherTactic   => either
    case _: SaturateTactic => star
    case e: RepeatTactic   => repeat(e.times)
    case _: PartialTactic  => partial
    case _: BranchTactic   => branch
    case _: CaseTactic     => branch
    case _: OnAll          => onall
    case _: USubstPatternTactic => usubst
    case _: DefTactic      => defTactic
    case _: Let            => let
    case _                 => base
  }
}
