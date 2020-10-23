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
  override val msg: String = s"Statement $s did not refine program $g"
  override def toString: String = msg
  override def location: Option[Int] = node.location
}

object RefinementChecker {
  /** @throws RefinementFailure if s does not refine game */
  private def refine(s: Statement, game: Program): Unit = {
    // undo block constructors, drop ghosts
    val ss = KaisarProof.flatten(List(s)).dropWhile({case _: Ghost => true case _ => false})
    // use "triv" and "?true" as terminators
    (ss, game) match {
      case (Nil | Triv() :: Nil, Test(True)) => ()
      case (Nil, _) => throw RefinementFailure(Triv(), game, s)
      case (shd :: stl, _) =>
        val (ghd, gtl) = game match {case Compose(l, r) => (l ,r) case _ => (game, Test(True))}
        // compare head, which can be recursive
        (shd, ghd) match {
          case (Modify(_ids, List((x, Some(f)))), Assign(xx, ff)) if x == xx && f == ff => ()
          case (Assert(_id, p, _m), Dual(Test(q))) if p == q => ()
          case (BoxLoop(sbod, _), Loop(gbod)) =>
            refine(sbod, gbod)
          case _ => throw RefinementFailure(shd, ghd, shd)
        }
        // recurse
        refine (KaisarProof.block(stl), gtl)
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
