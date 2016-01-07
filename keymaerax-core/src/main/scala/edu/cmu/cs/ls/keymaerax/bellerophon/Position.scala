/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.core.{SeqPos, SuccPos, AntePos, Sequent}
import scala.language.implicitConversions
import PosInExpr.HereP

/**
 * Positions identify subexpressions of an expression.
 * A position is a finite sequence of binary numbers where
 * 0 identifies the left or only subexpression of an expression and
 * 1 identifies the right subexpression of an expression.
 * @example
 * {{{
 *   import StringConverter._
 *   val fml = "(x>2 & x+1<9) -> [x:=2*x+1; y:=0;] x^2>=2".asFormula
 *   // explicitly use FormulaAugmentor
 *   print(FormulaAugmentor(fml).sub(PosInExpr(0::0::Nil)))        // x>2

 *   // implicitly use FormulaAugmentor functions on formulas
 *   import Augmentors._
 *   print(fml.sub(PosInExpr(0::0::Nil)))        // x>2;

 *   print(fml.sub(PosInExpr(0::1::Nil)))        // x+1<9
 *   print(fml.sub(PosInExpr(0::1::0::Nil)))     // x+1
 *   print(fml.sub(PosInExpr(0::1::0::0::Nil)))  // x
 *   print(fml.sub(PosInExpr(0::1::0::1::Nil)))  // 1
 *   print(fml.sub(PosInExpr(0::1::1::Nil)))     // 9
 *   print(fml.sub(PosInExpr(1::1::Nil)))        // x^2>=2
 *   print(fml.sub(PosInExpr(1::0::Nil)))        // x:=2*x+1; y:=0;
 *   print(fml.sub(PosInExpr(1::0::0::Nil)))     // x:=2*x+1;
 *   print(fml.sub(PosInExpr(1::0::1::Nil)))     // y:=0;
 *   print(fml.sub(PosInExpr(1::0::0::1::Nil)))  // 2*x+1
 * }}}
 * @see [[edu.cmu.cs.ls.keymaerax.btactics.Context.at()]]
 * @see [[edu.cmu.cs.ls.keymaerax.btactics.Context.replaceAt()]]
 * @see [[edu.cmu.cs.ls.keymaerax.btactics.Context.splitPos()]]
 * @see [[edu.cmu.cs.ls.keymaerax.btactics.Augmentors]]
 */
sealed case class PosInExpr(pos: List[Int] = Nil) {
  require(pos forall(_>=0), "all nonnegative positions")

  /** Append child to obtain position of given subexpression. */
  def +(child: Int): PosInExpr = new PosInExpr(pos :+ child)
  /** Append child to obtain position of given subexpression by concatenating `p2` to `this`. */
  def +(child : PosInExpr): PosInExpr = PosInExpr(this.pos ++ child.pos) ensuring(x => this.isPrefixOf(x))

  /** Head: The top-most position of this position */
  def head: Int = {require(pos!=Nil); pos.head}
  /** The child that this position refers to, i.e., the tail one level down */
  def child: PosInExpr = PosInExpr(pos.tail)
  /** The parent of this position, i.e., one level up */
  def parent: PosInExpr = PosInExpr(pos.dropRight(1))
  /** The sibling of this position (flip left to right and right to left) */
  def sibling: PosInExpr = PosInExpr(pos.dropRight(1) :+ (1-pos.last))

  /** Whether this position is a prefix of `p` */
  def isPrefixOf(p: PosInExpr): Boolean = p.pos.startsWith(pos)

  override def toString: String = "PosInExpr(" + pos.mkString(".") + ")"
  def prettyString: String = "." + pos.mkString(".")
}

object PosInExpr {
  /** Top position of an expression, i.e., the whole expression itself, not any subexpressions */
  val HereP: PosInExpr = new PosInExpr(Nil)
}

// @note observe that HereP and PosInExpr([]) will be equals, since PosInExpr is a case class
//object HereP extends PosInExpr

/**
  * @TODO this position class will be unnecessary after removal of deprecated rules. Or rather: the PosInExpr part is irrelevant for rules, merely for tactics.
  * Thus simplify into just a positive or negative integer type with some antecedent/succedent accessor sugar for isAnte etc around.
  * @todo use AntePos and SuccPos directly instead of index etc.
  * @todo Position should essentially become a nice name for a pair of a SeqPos and a PosInExpr.
  * @see [[SeqPos]]
  */
sealed trait Position {

  /** The position within formula */
  def inExpr: PosInExpr

//  require (getIndex >= 0, "nonnegative index " + getIndex)

  /** Whether this position is in the antecedent on the left of the sequent arrow */
  def isAnte: Boolean = top.isAnte
  /** Whether this position is in the succedent on the right of the sequent arrow */
  def isSucc: Boolean = !isAnte
  /**
    * Whether this position is a top-level position of a sequent instead of a subexpression.
    */
  def isTopLevel: Boolean = inExpr == HereP

  /** The top-level part of this position */
  def top: SeqPos

  //  def getIndex: Int = index

  /** Append child to obtain position of given subexpression by concatenating `p2` to `this`. */
  def +(child : PosInExpr): Position

  /** Advances the index by i on top-level positions. */
  @deprecated("Please compute top-level positions yourself")
  def advanceIndex(i: Int): Position

  /**
    * Check whether top-level index of this position is defined in given sequent (ignoring inExpr).
    */
  def isIndexDefined(s: Sequent): Boolean =
    if (isAnte)
      s.ante.length > top.getIndex
    else
      s.succ.length > top.getIndex


  /**
    * Top level position of this position
    * @return A position with the same index but on the top level (i.e., inExpr == HereP)
    */
  def topLevel: TopPosition

    //ensuring (r => r.isAnte==isAnte && r.index==index && r.inExpr == HereP)
//
//    /** Concatenate this with p2: Append p2 to this position */
//    def append(p2 : PosInExpr): Position = subPos(p2)
//
//    /**
//     * @param p The additional portion to append onto PosInExpr
//     * @return A subposition.
//     */
//    def subPos(p : PosInExpr): Position = {navigate(this.inExpr.append(p))
//    } ensuring (r => r.isAnte==isAnte && r.index==index && r.inExpr.pos.equals(this.inExpr.pos ++ p.pos) && this.inExpr.isPrefixOf(r.inExpr))
//
  /** Return a position with inExpr replaced by p */
  @deprecated("Unsure whether this will be kept")
  def navigate(instead : PosInExpr): Position

  // compatibility/convenience wrappers

  /** This position if it is an AntePosition, otherwise an error (convenience) */
  def checkAnte: AntePosition
  /** This position if it is a SuccPosition, otherwise an error (convenience) */
  def checkSucc: SuccPosition

  /** The top-level part of this position provided this position isTop (convenience) */
  def checkTop: SeqPos = if (isTopLevel) top else throw new IllegalArgumentException("Position was expected to be a top-level position: " + this)

  //@todo really?
  final def index: Int = top.getIndex

  override def toString: String = prettyString
  def prettyString: String = top.getPos + "." + inExpr.pos.mkString(".")
}

/** A position guaranteed to identify a top-level position */
//@todo not sure if this trait is sticky meaning all returned guys will be like that. Especially with weird navigation cases.
trait TopPosition extends Position {
  final override def isTopLevel: Boolean = true
}

/** A position guaranteed to identify an antecedent position
  * @see [[AntePos]]
  */
trait AntePosition extends Position {
  final override def isAnte: Boolean = true
  override def top: AntePos
  final def checkAnte: AntePosition = this
  final def checkSucc = throw new IllegalArgumentException("Antecedent position was expected to be a succedent position: " + this)
  override def topLevel: AntePosition with TopPosition
  override def advanceIndex(i: Int): AntePosition = {
    require(isTopLevel, "Advance index only at top level")
    require(index+i >= 0, "Cannot advance to negative index")
    AntePosition(index+i, inExpr)
  }
  def +(child : PosInExpr): AntePosition
}

/** A position guaranteed to identify a succedent position
  * @see [[SuccPos]]
  */
trait SuccPosition extends Position {
  final override def isAnte: Boolean = false
  override def top: SuccPos
  final def checkAnte = throw new IllegalArgumentException("Succedent position was expected to be an antecedent position: " + this)
  final def checkSucc: SuccPosition = this
  override def topLevel: SuccPosition with TopPosition
  override def advanceIndex(i: Int): SuccPosition = {
    require(isTopLevel, "Advance index only at top level")
    require(index+i >= 0, "Cannot advance to negative index")
    SuccPosition(index+i, inExpr)
  }
  def +(child : PosInExpr): SuccPosition
}

object AntePosition {
  def apply(top: AntePos): AntePosition with TopPosition = new AntePositionImpl(top, HereP) with TopPosition
  def apply(index: Int): AntePosition with TopPosition = apply(AntePos(index))
  def apply(index: Int, inExpr: PosInExpr): AntePosition = new AntePositionImpl(AntePos(index), inExpr)
  def apply(index: Int, inExpr: List[Int]): AntePosition = new AntePositionImpl(AntePos(index), PosInExpr(inExpr))
}

private case class AntePositionImpl (top: AntePos, inExpr: PosInExpr) extends AntePosition {
  def +(child : PosInExpr): AntePosition = new AntePositionImpl(top, inExpr+child)
  def topLevel = AntePosition.apply(top)
  //@note not TopLevel if HereP
  def navigate(instead : PosInExpr): Position = new AntePositionImpl(top, instead)
}

object SuccPosition {
  def apply(top: SuccPos): SuccPosition with TopPosition = new SuccPositionImpl(top, HereP) with TopPosition
  def apply(index: Int): SuccPosition with TopPosition = apply(SuccPos(index))
  def apply(index: Int, inExpr: PosInExpr): SuccPosition = new SuccPositionImpl(SuccPos(index), inExpr)
  def apply(index: Int, inExpr: List[Int]): SuccPosition = new SuccPositionImpl(SuccPos(index), PosInExpr(inExpr))
}

private case class SuccPositionImpl (top: SuccPos, inExpr: PosInExpr) extends SuccPosition {
  def +(child : PosInExpr): SuccPosition = new SuccPositionImpl(top, inExpr+child)
  def topLevel = SuccPosition.apply(top)
  //@note not TopLevel if HereP
  def navigate(instead : PosInExpr): Position = new SuccPositionImpl(top, instead)
}


@deprecated("Automated position converters should be removed.")
private[keymaerax] object Position {
  //@deprecated("Move as implicit definition to tactics and then ultimately remove")
  //@todo could also use p.top
  implicit def position2SeqPos[T <: SeqPos](p: Position): T = p.top.asInstanceOf[T]

  //implicit def antePosition2AntePos(p: AntePosition) : AntePos = assert(p.isAnte); new AntePos(p.index)
  //implicit def succPosition2AntePos(p: SuccPosition) : SuccPos = assert(!p.isAnte); new SuccPos(p.index)

  //implicit def position2AntePos(p: Position) : AntePos = if (p.isAnte) new AntePos(p.index) else throw new IllegalArgumentException("Wrong position side " + p)

  //implicit def position2SuccPos(p: Position) : SuccPos = if (!p.isAnte) new SuccPos(p.index) else throw new IllegalArgumentException("Wrong position side " + p)

  implicit def seqPos2Position(p: SeqPos) : Position = if (p.isAnte) AntePosition.apply(p.getIndex) else SuccPosition(p.getIndex)

  //  def antePos2Position(p: SeqPos) : AntePosition = if (p.isAnte) new AntePosition(p.getIndex, HereP) else throw new IllegalArgumentException("not ante")
//  def succPos2Position(p: SeqPos) : SuccPosition = if (p.isSucc) new SuccPosition(p.getIndex, HereP) else throw new IllegalArgumentException("not succ")
//  def seqPos2Position(p: SeqPos, posInExpr: List[Int]) : Position = if (p.isAnte) new AntePosition(p.getIndex, PosInExpr(posInExpr)) else new SuccPosition(p.getIndex, PosInExpr(posInExpr))
}

