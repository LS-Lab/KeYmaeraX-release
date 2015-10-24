package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.pt.ProofTerm
import edu.cmu.cs.ls.keymaerax.tactics.SuccPosition

/**
 * Algebraic Data Type whose elements are well-formed Bellephoron expressions.
 * See Table 1 of "Bellerophon: A Typed Language for Automated Deduction in a Uniform Substitution Calculus"
 * @author Nathan Fulton
 */
abstract class BelleExpr {
  // Syntactic sugar for combinators.
  def &(other: BelleExpr)      = SeqTactic(this, other)
  def |(other: BelleExpr)      = EitherTactic(this, other)
  def *(annotation: BelleType) = SaturateTactic(this, annotation)
  def sizeTag : SizeTag = this match {
    case x : BuiltInTactic => x.sizeTagAnnotation
    case x : BuiltInLeftTactic => x.sizeTagAnnotation
    case x: BuiltInRightTactic => x.sizeTagAnnotation
    case x : BuiltInTwoPositionTactic => x.sizeTagAnnotation
    case SeqTactic(l,r) => (l.sizeTag,r.sizeTag) match {
      case (ProvableMappingSizeTag(lDom, lCod), ProvableMappingSizeTag(rDom, rCod)) if(lCod == lDom) =>
        ProvableMappingSizeTag(lDom, rCod)
      case _ => throw BelleError(s"Could not synthesize a size tag for $l & $r")
    }
    case EitherTactic(l,r) =>
      if(l.sizeTag == r.sizeTag) l.sizeTag
      else throw BelleError("Could not synthesize a size tag for | tactic because left and right disagree.")
    case ExactIterTactic(child, count) => child.sizeTag match {
      case ProvableMappingSizeTag(childDom, childCod) if(childDom == childCod) => ProvableMappingSizeTag(childDom, childCod)
      case _ => throw BelleError("Cannot synthesize a size tag for exact iterations of non-mappings or with non-equal domain/codomain sizes")
      case SaturateTactic(child, annotation) => child.sizeTag match {
        case ProvableMappingSizeTag(childDom, childCod) if(childDom == childCod) => ProvableMappingSizeTag(childDom, childCod)
        case _ => throw BelleError("Cannot synthesize a size tag for iterations of non-mappings or with non-equal domain/codomain sizes")
      }
      case BranchTactic(children) => {
        val childrenSizes : Seq[Option[ProvableMappingSizeTag]] =
          children.map(_.sizeTag match {
            case t : ProvableMappingSizeTag => Some(t)
            case _ => None
          })
        if(childrenSizes.contains(None)) throw BelleError("Expected all branch tactics to have mapping types.")
        else {
          val codSize = childrenSizes.reduce((l,r) => l.get.cod + r.get.cod)
          ProvableMappingSizeTag(children.length, codSize)
        }
      }
      case USubstPatternTactic(options) => {
        val codomainSizes = options.map(_._2.sizeTag match {
          case ProvableMappingSizeTag(d,c) => c
          case _ => throw BelleError("Expected all usubst tactics to be provable mappings and to therefore have ProvableMappingSizeTags")
        }).toSet
        //@todo Actually, the ProvableMappingSizeTag of this is unknown.
        if(codomainSizes == 1) ProvableMappingSizeTag(???, codomainSizes.head)
        else throw BelleError("Expected codmains of usubst tactic to all have the same size, but found either no or more than one size tags.")
      }
    }
  }
}

abstract case class BuiltInTactic(name: String) extends BelleExpr {
  def apply(provable : Provable) : Provable
  def sizeTagAnnotation : SizeTag
}
abstract case class BuiltInPositionTactic(name: String) extends BelleExpr {
  def apply(provable: Provable, pos: SeqPos) : Provable
  def sizeTagAnnotation : SizeTag
}
abstract case class BuiltInLeftTactic(name: String) extends BelleExpr {
  def apply(provable: Provable, pos: AntePos) : Provable
  def sizeTagAnnotation : SizeTag
}
abstract case class BuiltInRightTactic(name: String) extends BelleExpr {
  def apply(provable: Provable, pos: SuccPos) : Provable
  def sizeTagAnnotation : SizeTag
}
abstract case class BuiltInTwoPositionTactic(name: String) extends BelleExpr {
  def apply(provable : Provable, posOne: SeqPos, posTwo: SeqPos) : Provable
  def sizeTagAnnotation : SizeTag
}

case class SeqTactic(left: BelleExpr, right: BelleExpr) extends BelleExpr
case class EitherTactic(left: BelleExpr, right: BelleExpr) extends BelleExpr
case class ExactIterTactic(child: BelleExpr, count: Int) extends BelleExpr
case class SaturateTactic(child: BelleExpr, annotation: BelleType) extends BelleExpr
case class BranchTactic(children: Seq[BelleExpr]) extends BelleExpr
//case class OptionalTactic(child: BelleExpr) extends BelleExpr
case class USubstPatternTactic(options: Seq[(BelleType, BelleExpr)]) extends BelleExpr

/** @todo eisegesis */
case class Map(e: BelleExpr) extends BelleExpr

/**
 * Bellerophon expressions that are values.
 */
abstract trait BelleValue
case class BelleProvable(p : Provable) extends BelleExpr with BelleValue
case class LeftResult(v: BelleValue) extends BelleExpr with BelleValue
case class RightResult(v: BelleValue) extends BelleExpr  with BelleValue

////////////////////////////////////////////////////////////////////////////////////////////////////
// Bellerophon Types
////////////////////////////////////////////////////////////////////////////////////////////////////

/** @todo eisegesis -- simple types */
abstract trait BelleType
case class TheType() extends BelleType

////////////////////////////////////////////////////////////////////////////////////////////////////
// Provable Size Tags
////////////////////////////////////////////////////////////////////////////////////////////////////

abstract trait SizeTag
case class ProvableSizeTag(n: Int) extends SizeTag
case class ProvableMappingSizeTag(dom: Int, cod: Int) extends SizeTag

////////////////////////////////////////////////////////////////////////////////////////////////////
// Errors
////////////////////////////////////////////////////////////////////////////////////////////////////

case class BelleError(message: String)
  extends Exception(s"[Bellerophon Runtime] $message")

class CompoundException(left: BelleError, right: BelleError)
  extends BelleError(s"Left Message: ${left.getMessage}\nRight Message: ${right.getMessage})")