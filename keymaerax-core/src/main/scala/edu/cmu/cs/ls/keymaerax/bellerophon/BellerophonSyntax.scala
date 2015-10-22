package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.core.{Formula, SeqPos, Sequent, Provable}
import edu.cmu.cs.ls.keymaerax.pt.ProofTerm

/**
 * Algebraic Data Type whose elements are well-formed Bellephoron expressions.
 * See Table 1 of "Bellerophon: A Typed Language for Automated Deduction in a Uniform Substitution Calculus"
 * @author Nathan Fulton
 */
abstract class BelleExpr {
  // Syntactic sugar for cominators.
  def &(other: BelleExpr)      = SeqTactic(this, other)
  def |(other: BelleExpr)      = EitherTactic(this, other)
  def *(annotation: BelleType) = SaturateTactic(this, annotation)

  /** @todo This should have a formal specification.*/
  val belleType : BelleType = this match {
    case builtIn: BuiltInTactic => builtIn.belleTypeAnnotation
    case builtIn: BuiltInPosTactic => builtIn.belleTypeAnnotation
    case SeqTactic(l,r)  => (l.belleType, r.belleType) match {
      //@todo this case if rather verbose
      //@todo to clean up, just handle the good cases and then do a bunch of conditional logic to report the correct exception message. See Either case below.
      case (ForAllType(lVar, lTyBody), ForAllType(rVar, rTyBody)) => {
        if (lVar == rVar) (l, r) match {
          case (TAbs(leftVar, leftBody), TAbs(rightVar, rightBody)) =>
            if (leftVar == rightVar) ForAllType(leftVar, (leftBody & rightBody).belleType)
            else throw BelleError("Cannot synthesize a type for (\\Lambda x. e) & (\\Lambda y . d) where x != y")
          case _ => throw BelleError("Synthesized a non-\\Lambda expression for a \\ForAll type -- should not happen.")
        }
        else throw BelleError("Cannot implicitly shift quantifiers out of an ~> expression when the types quantify over different variables.")
      }
      case (lType: MappingType, rType: MappingType) => {
        assert(lType.getClass == rType.getClass, "Left and Right tactics of a sequential composition should mappings of the same syntactic category.")
        lType(lType, rType)
      }
      case _ => throw BelleError("Cannot synthesize a type of e & d where e,d aren't either both mappings or else both type abstractions.")
    }
    case EitherTactic(l, r) => (l, r, l.belleType, r.belleType) match {
      case (ForAllType(lv, lType), ForAllType(rv, rType), TAbs(lv2, lBody), TAbs(rv2, rBody)) if(lv == lv2 && rv == rv2 && lv == rv) =>
        ForAllType(lv, (lBody | rBody).belleType)
      case (leftType: MappingType, rightType: MappingType, left, right) if leftType.getClass == rightType.getClass =>
        leftType(left, right)
      case (ForAllType(lv, lType), ForAllType(rv, rType), TAbs(lv2, lBody), TAbs(rv2, rBody)) if(lv != lv2 || rv != rv2) =>
        throw BelleError("Should never encounter \\Lambda x . e : \\ForAll y . T for x!=y")
      case (ForAllType(lv, lType), ForAllType(rv, rType), _, _) =>
        throw BelleError("Cannot synthesize type of e | d when both are of \\ForAll types but one or more isn't a \\Lambda-expr.")
      case (leftType: MappingType, rightType: MappingType, _, _) =>
        throw BelleError("Cannot synthesize a type for e ~> e' | d ~> d' when the e and d mappings are of differing syntactic categories.")
      case _ =>
        throw BelleError("Unknown error when trying the synthesize a type for e | d")
    }
  }
}

abstract case class BuiltInTactic(name: String) extends BelleExpr {
  def apply(provable : Provable) : Provable
  val belleTypeAnnotation : BelleType
}

abstract case class BuiltInPosTactic(name: String) extends BelleExpr {
  def apply(provable: Provable, pos: SeqPos) : Provable
  val belleTypeAnnotation : BelleType
}

case class SeqTactic(left: BelleExpr, right: BelleExpr) extends BelleExpr
case class EitherTactic(left: BelleExpr, right: BelleExpr) extends BelleExpr
//case class ParallelTactic(left: BelleExpr, right: BelleExpr) extends BelleExpr
case class ExactIterTactic(child: BelleExpr, count: Int) extends BelleExpr
case class SaturateTactic(child: BelleExpr, annotation: BelleType) extends BelleExpr
case class BranchTactic(children: Seq[BelleExpr]) extends BelleExpr
case class OptionalTactic(child: BelleExpr) extends BelleExpr
case class USubstPatternTactic(options: Seq[(BelleType, BelleExpr)]) extends BelleExpr

case class TAbs(t: TypeVar, body: BelleExpr) extends BelleExpr
case class TApp(fn : TAbs, arg: BelleType) extends BelleExpr

case class SumProjection(left: BelleExpr, right: BelleExpr) extends BelleExpr

/** @todo eisegesis */
case class Map(e: BelleExpr) extends BelleExpr

abstract trait BelleValue
case class BelleProvable(p : Provable) extends BelleExpr with BelleValue
case class LeftResult(v: BelleValue) extends BelleExpr with BelleValue
case class RightResult(v: BelleValue) extends BelleExpr  with BelleValue

abstract class BelleType

trait MappingType {
  val dom: BelleType
  val cod: BelleType
  def apply(domain: BelleType, codomain: BelleType) : (BelleType with MappingType)
}

case class TypeVar(name: String) extends BelleType
case class ForAllType(v: TypeVar, body: BelleType) extends BelleType
case class ApplyType(abs: ForAllType, body: BelleType) extends BelleType

///** @todo Need types for positional tactics. This is one proposal. */
//case class FormulaType(f: Formula) extends BelleType
//case class Formula(dom: FormulaType, cod: FormulaType) extends BelleType

case class SequentType(ante: Seq[BelleType], succ: Seq[BelleType]) extends BelleType
case class SequentMapping(dom: SequentType, cod: BelleType) extends BelleType with MappingType

case class ProvableType(sequents: Seq[SequentType]) extends BelleType
case class ProvableMapping(dom: ProvableType, cod: BelleType) extends BelleType with MappingType

case class BelleClosedProofType() extends BelleType

case class BelleError(message: String)
  extends Exception(s"[Bellerophon Runtime] $message")

class CompoundException(left: BelleError, right: BelleError)
  extends BelleError(s"Left Message: ${left.getMessage}\nRight Message: ${right.getMessage})")