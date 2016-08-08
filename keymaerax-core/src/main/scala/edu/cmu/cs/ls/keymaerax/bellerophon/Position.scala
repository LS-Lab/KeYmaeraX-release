/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.core._
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
  def +(appendChild: Int): PosInExpr = new PosInExpr(pos :+ appendChild) ensuring(r => this.isPrefixOf(r))
  /** Append child to obtain position of given subexpression by concatenating `appendChild` to `this`. */
  def +(appendChild : PosInExpr): PosInExpr = PosInExpr(this.pos ++ appendChild.pos) ensuring(r => this.isPrefixOf(r))

  /** Head: The top-most position of this position */
  def head: Int = {require(pos!=Nil); pos.head}
  /** The child that this position refers to, i.e., the tail one level down */
  def child: PosInExpr = PosInExpr(pos.tail)
  /** The parent of this position, i.e., one level up */
  def parent: PosInExpr = if (!pos.isEmpty) PosInExpr(pos.dropRight(1)) else throw new ProverException("ill-positioned: " + this + " has no parent")
  /** The sibling of this position (flip left to right and right to left) */
  def sibling: PosInExpr = parent + (1-pos.last)

  /** Whether this position is a prefix of `p` */
  def isPrefixOf(p: PosInExpr): Boolean = p.pos.startsWith(pos)

  override def toString: String = prettyString //"PosInExpr(" + pos.mkString(".") + ")"
  def prettyString: String = "." + pos.mkString(".")
}

object PosInExpr {
  /** Top position of an expression, i.e., the whole expression itself, not any subexpressions */
  val HereP: PosInExpr = new PosInExpr(Nil)
}

// @note observe that HereP and PosInExpr([]) will be equals, since PosInExpr is a case class
//object HereP extends PosInExpr

/** Position at which formula and subexpresion ofa a sequent to apply a tactic.
  * @TODO this position class will be unnecessary after removal of deprecated rules. Or rather: the PosInExpr part is irrelevant for rules, merely for tactics.
  * Thus simplify into just a positive or negative integer type with some antecedent/succedent accessor sugar for isAnte etc around.
  * @todo use AntePos and SuccPos directly instead of index etc.
  * @todo Position should essentially become a nice name for a pair of a SeqPos and a PosInExpr.
  * @see [[edu.cmu.cs.ls.keymaerax.core.SeqPos]]
  */
sealed trait Position {

  /** The subexpression position within the formula */
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
  //@todo this+0!=this is pretty confusing. 0,1 is worse than 1,2.
  def +(child: PosInExpr): Position

  /** Advances the index by i on top-level positions. */
  def advanceIndex(i: Int): Position

  /**
    * Check whether top-level index of this position is defined in given sequent (ignoring inExpr).
    */
  def isIndexDefined(s: Sequent): Boolean =
    if (isAnte)
      s.ante.length > index0
    else
      s.succ.length > index0


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

  private[keymaerax] final def index0: Int = top.getIndex
  //final def index1: Int = top.getIndex + 1

  override def toString: String = prettyString
  def prettyString: String = inExpr.pos match {
    case Nil => top.getPos.toString
    case _ => top.getPos + "." + inExpr.pos.mkString(".")
  }
}

object Position {
  /** Converts signed positions to position data structures.
    * -1 is the first antecedent position,
    * 1 the first succedent position
    * @see [[edu.cmu.cs.ls.keymaerax.bellerophon.PosInExpr]]
    */
  def apply(seqIdx: Int, inExpr: List[Int] = Nil): Position = SeqPos(seqIdx) match {
    case pos: AntePos => AntePosition(pos, PosInExpr(inExpr))
    case pos: SuccPos => SuccPosition(pos, PosInExpr(inExpr))
  }

  private[bellerophon] def apply(p: edu.cmu.cs.ls.keymaerax.core.SeqPos) : Position = p match {
    case pos: AntePos => AntePosition(pos)
    case pos: SuccPos => SuccPosition(pos)
  }

  /** Embedding SeqPos into Position at top level */
  implicit def seqPos2Position(p: SeqPos) : Position = apply(p)
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
  override def checkTop: AntePos = if (isTopLevel) top else throw new IllegalArgumentException("Position was expected to be a top-level position: " + this)
  override def topLevel: TopAntePosition
  override def advanceIndex(i: Int): AntePosition = {
    require(isTopLevel, "Advance index only at top level")
    require(index0+i >= 0, "Cannot advance to negative index")
    AntePosition.base0(index0+i, inExpr)
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
  override def checkTop: SuccPos = if (isTopLevel) top else throw new IllegalArgumentException("Position was expected to be a top-level position: " + this)
  override def topLevel: TopSuccPosition
  override def advanceIndex(i: Int): SuccPosition = {
    require(isTopLevel, "Advance index only at top level")
    require(index0+i >= 0, "Cannot advance to negative index")
    SuccPosition.base0(index0+i, inExpr)
  }
  def +(child : PosInExpr): SuccPosition
}

/** A top-level anteedent position */
trait TopAntePosition extends AntePosition with TopPosition {
  final override def checkTop: AntePos = top
}

/** A top-level succedent position */
trait TopSuccPosition extends SuccPosition with TopPosition {
  final override def checkTop: SuccPos = top
}

// Pseudo-Constructors

object AntePosition {
  def apply(top: AntePos): TopAntePosition = new AntePositionImpl(top, HereP) with TopAntePosition
  def apply(top: AntePos, inExpr: PosInExpr): AntePosition = new AntePositionImpl(top, inExpr)

  def base0(index: Int, inExpr: PosInExpr = HereP): AntePosition = AntePosition.apply(AntePos(index), inExpr)


  def apply(seqIdx: Int): TopAntePosition = apply(seqIdx2AntePos(seqIdx))
  def apply(seqIdx: Int, inExpr: List[Int]): AntePosition = new AntePositionImpl(seqIdx2AntePos(seqIdx), PosInExpr(inExpr))
  private def seqIdx2AntePos(base1: Int): AntePos = {
    require(base1>0, "positive indexing base 1: " + base1)
    AntePos(base1-1)
  } ensuring(r => r==SeqPos(-base1), "signed int conversion identical to core but faster")

}

object SuccPosition {
  def apply(top: SuccPos): TopSuccPosition = new SuccPositionImpl(top, HereP) with TopSuccPosition
  def apply(top: SuccPos, inExpr: PosInExpr): SuccPosition = new SuccPositionImpl(top,inExpr)
  def base0(index: Int, inExpr: PosInExpr = HereP): SuccPosition = SuccPosition.apply(SuccPos(index), inExpr)

  def apply(seqIdx: Int): TopSuccPosition = apply(seqIdx2SuccPos(seqIdx))
  def apply(seqIdx: Int, inExpr: List[Int]): SuccPosition = new SuccPositionImpl(seqIdx2SuccPos(seqIdx), PosInExpr(inExpr))

  private def seqIdx2SuccPos(base1: Int): SuccPos = {
    require(base1>0, "positive indexing base 1: " + base1)
    SuccPos(base1-1)
  } ensuring(r => r==SeqPos(base1), "signed int conversion identical to core but faster")
}

// Implementations

private case class AntePositionImpl (top: AntePos, inExpr: PosInExpr) extends AntePosition {
  def +(child : PosInExpr): AntePosition = new AntePositionImpl(top, inExpr+child)
  def topLevel = AntePosition.apply(top)
  //@note not TopLevel if HereP
  def navigate(instead : PosInExpr): AntePosition = new AntePositionImpl(top, instead)
}

private case class SuccPositionImpl (top: SuccPos, inExpr: PosInExpr) extends SuccPosition {
  def +(child : PosInExpr): SuccPosition = new SuccPositionImpl(top, inExpr+child)
  def topLevel = SuccPosition.apply(top)
  //@note not TopLevel if HereP
  def navigate(instead : PosInExpr): SuccPosition = new SuccPositionImpl(top, instead)
}


