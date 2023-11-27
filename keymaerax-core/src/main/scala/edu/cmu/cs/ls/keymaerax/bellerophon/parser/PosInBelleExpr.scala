/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.bellerophon.parser

import edu.cmu.cs.ls.keymaerax.bellerophon._

/** Used to indicate the position in an expression. Usually for error reporting purposes. */
case class PosInBelleExpr(idxs: Seq[Int]) {
  def +(int:Int) = idxs :+ int
  def -()        = idxs.dropRight(1)

  def hd = idxs.head

  def apply(e: BelleExpr) = e match {
    case SeqTactic(l :: r :: Nil) => if(hd == 0) l else if(hd == 1) r else throw new PositionException(hd, e)
    case e: SeqTactic => if(hd == 0) e.seq.head else if(hd == 1) SeqTactic(e.seq.tail) else throw new PositionException(hd, e)
    case EitherTactic(l :: r :: Nil) => if(hd == 0) l else if(hd == 1) r else throw new PositionException(hd, e)
    case e: EitherTactic => if(hd == 0) e.alts.head else if(hd == 1) EitherTactic(e.alts.tail) else throw new PositionException(hd, e)
    case e: SaturateTactic => if(hd == 0) e.child else throw new PositionException(hd, e)
    case e: BranchTactic => if(hd < e.children.length) e.children(hd) else throw new PositionException(hd, e)
    case e: USubstPatternTactic => if(hd < e.options.length*2) {
      if(hd % 2 == 0) e.options(hd)._1
      else e.options(((hd-1)/2))._2
    } else throw new PositionException(hd, e)
    case e: BuiltInTactic => throw new PositionException(hd, e)
    case _ => ??? //@todo need the rest.
  }
}

class PositionException(head: Int, subExpr: BelleExpr) extends Exception(s"Position $head is not valid at $subExpr")
