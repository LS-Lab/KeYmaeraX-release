/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.tactics

import edu.cmu.cs.ls.keymaerax.core.{SeqPos, SuccPos, AntePos, Sequent}
import scala.language.implicitConversions

/**
 * Position within an expression as a list of subexpressions.
 * 0 is first child, 1 is second child, 2 is third child.
 */
case class PosInExpr(pos: List[Int] = Nil) {
  require(pos forall(_>=0), "all nonnegative positions")

  /** Head: The top-most position */
  def head: Int = {require(pos!=Nil); pos.head}
  /** The child that this position refers to */
  def child: PosInExpr = PosInExpr(pos.tail)
  /** The parent of this position, i.e., one level up */
  def parent: PosInExpr = PosInExpr(pos.dropRight(1))

  /** first child 0 */
  def first:  PosInExpr = new PosInExpr(pos :+ 0)
  /** second child 1 */
  def second: PosInExpr = new PosInExpr(pos :+ 1)
  /** third child 2 */
  def third:  PosInExpr = new PosInExpr(pos :+ 2)

  /** Concatenate this with p2: Append p2 to this position */
  def append(p2 : PosInExpr): PosInExpr = PosInExpr(this.pos ++ p2.pos) ensuring(x => this.isPrefixOf(x))

  /** Whether this position is a prefix of p */
  def isPrefixOf(p: PosInExpr): Boolean = p.pos.startsWith(pos)
}

// @note observe that HereP and PosInExpr([]) will be equals, since PosInExpr is a case class
/** Top position of an expression, i.e., the whole expression itself, not any subexpressions */
object HereP extends PosInExpr

  /**
   * @param index the number of the formula in the antecedent or succedent, respectively.
   * @param inExpr the position in said formula.
   * @TODO this position class will be unnecessary after removal of deprecated rules. Or rather: the PosInExpr part is irrelevant for rules, merely for tactics.
   * Thus simplify into just a positive or negative integer type with some antecedent/succedent accessor sugar for isAnte etc around.
   * @todo use AntePos and SuccPos directly instead of index etc.
   * @todo Position should essentially become a nice name for a pair of a SeqPos and a PosInExpr.
   */
  abstract class Position(val index: Int, val inExpr: PosInExpr = HereP) {
    require (index >= 0, "nonnegative index " + index)
    def isAnte: Boolean
    def getIndex: Int = index

    /**
     * Check whether index of this position is defined in given sequent (ignoring inExpr).
     */
    def isIndexDefined(s: Sequent): Boolean =
      if(isAnte)
        s.ante.length > getIndex
      else
        s.succ.length > getIndex

    /**
     * Top level position of this position
     * @return A position with the same index but on the top level (i.e., inExpr == HereP)
     */
    def topLevel: Position = {
      clone(index)
    } ensuring (r => r.isAnte==isAnte && r.index==index && r.inExpr == HereP)

    /**
     * @param p The additional portion to append onto PosInExpr
     * @return A subposition.
     */
    def subPos(p : PosInExpr) = {
      if(this.isAnte)
        AntePosition(this.index, this.inExpr.append(p))
      else
        SuccPosition(this.index, this.inExpr.append(p))
    } ensuring (r => r.isAnte==isAnte && r.index==index && r.inExpr.pos.equals(this.inExpr.pos ++ p.pos) && this.inExpr.isPrefixOf(r.inExpr))

    /**
     * Whether this position is a top-level position of a sequent.
     */
    def isTopLevel: Boolean = inExpr == HereP

    /** The top-level part of this position */
    def top: SeqPos

    def +(i: Int): Position

    def first: Position
    def second: Position
    def third: Position

    protected def clone(i: Int, e: PosInExpr = HereP): Position

    override def toString: String = "(" + (if (isAnte) "Ante" else "Succ") + ", " + getIndex + ", " + inExpr + ")"
  }

@deprecated("Automated position converters should be removed ultimately.")
object Position {
  //@deprecated("Move as implicit definition to tactics and then ultimately remove")
  //@todo could also use p.top
  implicit def position2SeqPos[T <: SeqPos](p: Position): T = if (p.isAnte) new AntePos(p.index).asInstanceOf[T] else new SuccPos(p.index).asInstanceOf[T]

  //implicit def antePosition2AntePos(p: AntePosition) : AntePos = assert(p.isAnte); new AntePos(p.index)
  //implicit def succPosition2AntePos(p: SuccPosition) : SuccPos = assert(!p.isAnte); new SuccPos(p.index)

  //implicit def position2AntePos(p: Position) : AntePos = if (p.isAnte) new AntePos(p.index) else throw new IllegalArgumentException("Wrong position side " + p)

  //implicit def position2SuccPos(p: Position) : SuccPos = if (!p.isAnte) new SuccPos(p.index) else throw new IllegalArgumentException("Wrong position side " + p)

  implicit def seqPos2Position(p: SeqPos) : Position = if (p.isAnte) new AntePosition(p.getIndex, HereP) else new SuccPosition(p.getIndex, HereP)
}

  class AntePosition(index: Int, inExpr: PosInExpr = HereP) extends Position(index, inExpr) {
    def isAnte = true
    protected def clone(i: Int, e: PosInExpr): Position = new AntePosition(i, e)
    def +(i: Int) = AntePosition(index + i, inExpr)
    def first: Position = AntePosition(index, inExpr.first)
    def second: Position = AntePosition(index, inExpr.second)
    def third: Position = AntePosition(index, inExpr.third)
    def top: AntePos = AntePos(index)
  }

  object AntePosition {
    def apply(index: Int, inExpr: PosInExpr = HereP): Position = new AntePosition(index, inExpr)
    def apply(index: Int, inExpr: List[Int]): Position = new AntePosition(index, PosInExpr(inExpr))
  }

  class SuccPosition(index: Int, inExpr: PosInExpr = HereP) extends Position(index, inExpr) {
    def isAnte = false
    protected def clone(i: Int, e: PosInExpr): Position = new SuccPosition(i, e)
    def +(i: Int) = SuccPosition(index + i, inExpr)
    def first: Position = SuccPosition(index, inExpr.first)
    def second: Position = SuccPosition(index, inExpr.second)
    def third: Position = SuccPosition(index, inExpr.third)
    def top: SuccPos = SuccPos(index)
  }

  object SuccPosition {
    def apply(index: Int, inExpr: PosInExpr = HereP): Position = new SuccPosition(index, inExpr)
    def apply(index: Int, inExpr: List[Int]): Position = new SuccPosition(index, PosInExpr(inExpr))
  }

