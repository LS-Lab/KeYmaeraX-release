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
import edu.cmu.cs.ls.keymaerax.btactics.helpers.DifferentialHelper._
import edu.cmu.cs.ls.keymaerax.infrastruct.FormulaTools
import edu.cmu.cs.ls.keymaerax.infrastruct.FormulaTools._

trait RefinementException extends LocatedException

case class RefinementFailure(s: Statement, g: Program, extraMsg: String = "", node: ASTNode = Triv()) extends RefinementException {
  override val msg: String = {
    val extra = if (extraMsg == "") "" else "\nadditional message: " + extraMsg
    s"Statement $s\n did not refine program $g" + extra
  }
  override def toString: String = msg
  override def location: Option[Int] = node.location
}

object RefinementChecker {
  /** @throws RefinementFailure if s does not refine game */
  private def refine(pode: ProveODE, ode: ODESystem, odeIsAngelic: Boolean): Unit = {
    val DiffCollection(cores, ghosts, invGhost) = pode.ds.collect
    val DomCollection(assume, assert, weak, modify) = pode.dc.collect
    if(pode.isAngelic != odeIsAngelic) {
      val msg =
        if(pode.isAngelic) "Proof has Angelic ODE but formula has Demonic ODE"
        else "Proof has Demonic ODE but formula has Angelic ODE"
      throw RefinementFailure(pode, ode, msg, pode)
    }
    val pfAtoms = cores.map(_.dp) ++ invGhost.map(_.dp)
    val gameAtoms = atomicOdes(ode).toSet
    if(pfAtoms != gameAtoms) {
      val proofOnly = pfAtoms -- gameAtoms
      val gameOnly = gameAtoms -- pfAtoms
      val proofMsg = if(proofOnly.isEmpty) "" else s"Proof contained extra ODEs ${proofOnly}. "
      val gameMsg = if(gameOnly.isEmpty) "" else s"Program contained extra ODEs ${gameOnly}. "
      throw RefinementFailure(pode, ode, proofMsg + gameMsg, pode)
    }
    val pfDcAtoms = (if (pode.isAngelic) assert else (assume ++ weak)).map(_.asFormula(pode.isAngelic))
    val pfDc = pfDcAtoms.flatMap(_.toList).fold[Formula](True)(And)
    val pfConjuncts = FormulaTools.conjuncts(pfDc).toSet.filter(_ != True)
    val gameConjuncts = FormulaTools.conjuncts(ode.constraint).toSet.filter(_ != True)
    if(pfConjuncts != gameConjuncts) {
      val proofOnly = pfConjuncts -- gameConjuncts
      val gameOnly = gameConjuncts -- pfConjuncts
      val proofMsg = if(proofOnly.isEmpty) "" else s"Proof contained extra conjuncts ${proofOnly}. "
      val gameMsg = if(gameOnly.isEmpty) "" else s"Program contained extra conjuncts ${gameOnly}. "
      throw RefinementFailure(pode, ode, proofMsg + gameMsg, pode)
    }
  }

  /** @throws RefinementFailure if s does not refine game */
  private def refine(s: Statement, game: Program): Unit = {
    // undo block constructors, drop ghosts
    val ss = KaisarProof.flatten(List(s)).dropWhile({case _: Ghost => true case _ => false})
    // use "triv" and "?true" as terminators
    (ss, game) match {
      case (Nil | Triv() :: Nil, Test(True)) => ()
      case (Nil, _) => throw RefinementFailure(Triv(), game, "Proof only proves fragment of game", s)
      case (shd :: stl, _) =>
        val (ghd, gtl) = game match {case Compose(l, r) => (l ,r) case _ => (game, Test(True))}
        // compare head, which can be recursive
        (shd, ghd) match {
            // @TODO:  ?,  x:=*, ++, switch, for, note, non-execution nodes,
          case (Modify(_ids, List((x, Some(f)))), Assign(xx, ff)) if x == xx && f == ff => ()
          case (Assert(_id, p, _m), Dual(Test(q))) if p == q => ()
          case (pode: ProveODE, osys: ODESystem) => refine(pode, osys, odeIsAngelic = false)
          case (pode: ProveODE, Dual(osys: ODESystem)) => refine(pode, osys, odeIsAngelic = true)
          case (BoxLoop(sbod, _), Loop(gbod)) =>
            refine(sbod, gbod)
          case _ => throw RefinementFailure(shd, ghd, s"Proof connective ${PrettyPrinter.short(shd)} does not match program $ghd", shd)
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
