package edu.cmu.cs.ls.keymaerax.bellerophon.parser

import edu.cmu.cs.ls.keymaerax.bellerophon._
import scala.collection.immutable._

/**
  * @note Needs some work because the constructors for Belle expressions are far more diverse than
  *       the constructors for KeYmaera X expressions
  */
sealed trait BelleOpSpec {
  val terminal: BelleTerminal
  val precedence: Int
  val leftAssoc: Boolean

  def <(other: BelleOpSpec) = this.precedence < other.precedence
  def >(other: BelleOpSpec) = this.precedence > other.precedence
  def ==(other: BelleOpSpec) = this.precedence == other.precedence
}
case class BelleUnaryOpSpec(terminal: BelleTerminal, precedence: Int, leftAssoc: Boolean) extends BelleOpSpec
case class BelleBinaryOpSpec(terminal: BelleTerminal, precedence: Int, leftAssoc: Boolean) extends BelleOpSpec
case class BelleBranchingOpSpec(terminal: BelleTerminal, precedence: Int, leftAssoc: Boolean, constructor : (Seq[BelleExpr]) => BelleExpr) extends BelleOpSpec
case class BelleSaturatingOpSpec(terminal: BelleTerminal, precedence: Int, leftAssoc: Boolean, constructor : (BelleExpr, BelleType) => BelleExpr) extends BelleOpSpec
case class BelleRepeatOpSpec(terminal: BelleTerminal, precedence: Int, leftAssoc: Boolean, constructor : (BelleExpr, Int, BelleType) => BelleExpr) extends BelleOpSpec
case class BelleUSubstOpSpec(terminal: BelleTerminal, precedence: Int, leftAssoc: Boolean, constructor : (Seq[(BelleType, RenUSubst => BelleExpr)]) => BelleExpr) extends BelleOpSpec

case class BelleUnitOpSpec[T,S](terminal: BelleTerminal, precedence:Int, leftAssoc: Boolean, constructor: T => S) extends BelleOpSpec

object BelleOpSpec {
  private val none = PSEUDO

  val position = BelleUnitOpSpec(none, 100, false, (x:Any) => ???)

  val base     = BelleUnitOpSpec(none, 0, false, (s:String) => ???)
  val seq      = BelleBinaryOpSpec(SEQ_COMBINATOR,    200, false)
  val either   = BelleUnaryOpSpec(EITHER_COMBINATOR, 220, false)
  val star     = BelleUnaryOpSpec(KLEENE_STAR,        100, false)
  val saturate = BelleSaturatingOpSpec(SATURATE, 100, false, SaturateTactic.apply)
  val repeat   = BelleRepeatOpSpec(SATURATE, 100, false, RepeatTactic.apply)
  val branch   = BelleBranchingOpSpec(BRANCH_COMBINATOR, 100, false, BranchTactic.apply)
  val partial  = BelleUnaryOpSpec(PARTIAL, 100, false)
  val usubst   = BelleUSubstOpSpec(US_MATCH, 100, false, USubstPatternTactic.apply)

  def op(e : BelleExpr): BelleOpSpec = e match {
    case e:SeqTactic      => seq
    case e:EitherTactic   => either
    case e:SaturateTactic => star
    case e:RepeatTactic   => repeat
    case e:PartialTactic  => partial
    case e:BranchTactic => branch
    case e:USubstPatternTactic => usubst
    case e:BuiltInTactic       => base
    case e:AppliedPositionTactic => base
    case e:AppliedDependentPositionTactic => base
    case _ => base
  }
}
