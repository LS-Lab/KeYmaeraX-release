package edu.cmu.cs.ls.keymaera.tactics

import edu.cmu.cs.ls.keymaera.core.{SeqPos, SuccPos, AntePos, Sequent}

/**
 */
  @deprecated("Remove from prover core")
  case class PosInExpr(pos: List[Int] = Nil) {
    require(pos forall(_>=0), "all nonnegative positions")
    def first:  PosInExpr = new PosInExpr(pos :+ 0)
    def second: PosInExpr = new PosInExpr(pos :+ 1)
    def third:  PosInExpr = new PosInExpr(pos :+ 2)

    def isPrefixOf(p: PosInExpr): Boolean = p.pos.startsWith(pos)
    def child: PosInExpr = PosInExpr(pos.tail)
  }

  // observe that HereP and PosInExpr([]) will be equals, since PosInExpr is a case class
  object HereP extends PosInExpr

  /**
   * @param index the number of the formula in the antecedent or succedent, respectively.
   * @param inExpr the position in said formula.
   * @TODO this position class will be unnecessary after removal of deprecated rules. Or rather: the PosInExpr part is irrelevant for rules, merely for tactics.
   * Thus simplify into just a positive or negative integer type with some antecedent/succedent accessor sugar for isAnte etc around.
   */
  @deprecated("Use SeqPos instead in prover core")
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
     * Whether this position is a top-level position of a sequent.
     */
    def isTopLevel: Boolean = inExpr == HereP

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
  implicit def position2SeqPos(p: Position) : SeqPos = if (p.isAnte) new AntePos(p.index) else new SuccPos(p.index)

  //implicit def position2AntePos(p: Position) : AntePos = if (p.isAnte) new AntePos(p.index) else throw new IllegalArgumentException("Wrong position side " + p)

  //implicit def position2SuccPos(p: Position) : SuccPos = if (!p.isAnte) new SuccPos(p.index) else throw new IllegalArgumentException("Wrong position side " + p)

  implicit def seqPos2Position(p: SeqPos) : Position = if (p.isAnte) new AntePosition(p.getIndex, HereP) else new SuccPosition(p.getIndex, HereP)
}

  @deprecated("Use AntePos or SeqPos(-...) instead")
  class AntePosition(index: Int, inExpr: PosInExpr = HereP) extends Position(index, inExpr) {
    def isAnte = true
    protected def clone(i: Int, e: PosInExpr): Position = new AntePosition(i, e)
    def +(i: Int) = AntePosition(index + i, inExpr)
    def first: Position = AntePosition(index, inExpr.first)
    def second: Position = AntePosition(index, inExpr.second)
    def third: Position = AntePosition(index, inExpr.third)
  }

  object AntePosition {
    def apply(index: Int, inExpr: PosInExpr = HereP): Position = new AntePosition(index, inExpr)
  }

  @deprecated("Use SuccPos or SeqPos instead")
  class SuccPosition(index: Int, inExpr: PosInExpr = HereP) extends Position(index, inExpr) {
    def isAnte = false
    protected def clone(i: Int, e: PosInExpr): Position = new SuccPosition(i, e)
    def +(i: Int) = SuccPosition(index + i, inExpr)
    def first: Position = SuccPosition(index, inExpr.first)
    def second: Position = SuccPosition(index, inExpr.second)
    def third: Position = SuccPosition(index, inExpr.third)
  }

  object SuccPosition {
    def apply(index: Int, inExpr: PosInExpr = HereP): Position = new SuccPosition(index, inExpr)
  }

