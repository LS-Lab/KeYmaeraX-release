/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
/**
  * Check whether underlying strategy of Kaisar proof is a strategy for a given game
  * @author Brandon Bohrer
  */
package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.KaisarProof.{LocatedException, ProofCheckException}
import edu.cmu.cs.ls.keymaerax.core._

case class RefinementFailure(s: Statement, g: Program, node: ASTNode) extends LocatedException {
  override val msg: String = "Statement $s did not refine program $g"
  override def location: Option[Int] = node.location
}

object RefinementChecker {
  /** @throws RefinementFailure if s does not refine game */
  private def refine(s: Statement, game: Program): Unit = {
    // use "triv" and "?true" as terminators
    val (shd, stl) = s match {case Block(s :: ss) => (s, KaisarProof.block(ss)) case _ => (s, Triv())}
    val (ghd, gtl) = game match {case Compose(l, r) => (l ,r) case _ => (game, Test(True))}
    // compare head
    (shd, ghd) match {
        case (Modify(_ids, List((x, Some(f)))), Assign(xx, ff)) if x == xx && f == ff => ()
        case _ => throw RefinementFailure(shd, ghd, shd)
    }
    // recurse
    (stl, gtl) match {
      // end recursion
      case (Triv(), Test(True)) => ()
      // recurse
      case _ => refine(stl, gtl)
    }
  }

  def apply(s: Statement, game: Program): Unit = {
    try {
      refine(s, game)
    } catch {
        case rf: RefinementFailure =>
          throw ProofCheckException(s"Proof did not refine game $game", cause = rf)
    }
  }
}
