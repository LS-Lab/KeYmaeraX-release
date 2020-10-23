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

  private def isIgnored(s: Statement): Boolean ={
    s match {
      case Triv() | _: Label | _: LetSym | _: Ghost | _: PrintGoal | _: Pragma | _: Was | _: Match => true
      case _ => false
    }
  }

  private def uncons(game: Program): (Program, Program) = {
    game match {
      case Compose(Compose(l, x), r) => uncons(Compose(l, Compose(x, r)))
      case Compose(l, r) => (l, r)
      case l => (l, Test(True))
    }
  }

  /** @throws RefinementFailure if s does not refine game */
  private def refine(s: Statement, game: Program): Unit = {
    // undo block constructors, drop ghosts and lets
    val ss = KaisarProof.flatten(List(s)).dropWhile(isIgnored)
    // use "triv" and "?true" as terminators
    (ss, game) match {
      case (Nil | Triv() :: Nil, Test(True)) => ()
      case (Nil, _) => throw RefinementFailure(Triv(), game, "Proof only proves fragment of game", s)
      case (shd :: stl, _) =>
        val (ghd, gtl) = uncons(game)
        // compare head, which can be recursive
        (shd, ghd) match {
          case (Modify(_ids, List((x, Some(f)))), Assign(xx, ff)) if x == xx && f == ff => ()
          case (Modify(_ids, List((x, Some(f)))), Dual(AssignAny(xx))) if x == xx => ()
          case (Modify(_ids, List((x, None))), AssignAny(xx)) if x == xx => ()
          case (Assert(_id, p, _m), Dual(Test(q))) if p == q => ()
          case (Assume(_id, p), Test(q)) if p == q => ()
          case (Note(x, pt, Some(fml)), Dual(Test(q))) if fml == q => ()
          // @TODO: SSA will fix this
          case (Note(x, pt, None), Dual(Test(q))) => throw RefinementFailure(shd, ghd, "Expected proved formula in note statement", s)
          case (pode: ProveODE, osys: ODESystem) => refine(pode, osys, odeIsAngelic = false)
          case (pode: ProveODE, Dual(osys: ODESystem)) => refine(pode, osys, odeIsAngelic = true)
          case (BoxLoop(sbod, _), Loop(gbod)) => refine(sbod, gbod)
          case (BoxChoice(sl, sr), Choice(gl, gr)) => refine(sl, gl); refine(sr, gr)
          case (Switch(_, pats), Dual(brGame: Choice)) =>
            val nBranches = pats.length
            StandardLibrary.unchoose(brGame, nBranches) match {
              case None => throw RefinementFailure(shd, ghd, "Program did not have enough branches for proof")
              case Some(gameBranches) =>
                val pairs = pats.zip(gameBranches)
                pairs.foreach({
                  case ((_pat, fml, s), Compose(Test(q), g)) if fml == q => refine(s, Dual(g))
                  case ((_pat, fml, s), g) => refine(s, g) // make guards optional
                })
            }
          // Box(Compose(Compose(Assign(metX, met0),Dual(Loop(Compose(Dual(a), Assign(metX,metIncr))))), Dual(Test(theConcl))), True)
          case (For(metX, met0, metIncr, conv, guard, body), assignMetZ) =>
            gtl match {
              // @TODO: More flexible pattern match
              case Compose(Dual(Loop(Compose(Dual(a), incr))), after) =>
                val (finalTest, gtl) = uncons(after)
                if (assignMetZ != Assign(metX, met0))
                  throw RefinementFailure(shd, ghd, "Game refined by for loop must start with initializer assignment")
                if (incr != Assign(metX, metIncr))
                  throw RefinementFailure(shd, ghd, "Game refined by for loop must have body ending in increment assignment")
                val metric = Metric(metX, metIncr, guard.f, Set()) // Note: assume taboos checked elsewhere
                val termCond = metric.guardPost(metX)
                val theConcl = conv.map(_.f) match {
                  case None => termCond
                  case Some(f) => And(f, termCond)
                }
                finalTest match {
                  case Dual(Test(concl)) if theConcl == concl => ()
                  case Dual(Test(concl)) => throw RefinementFailure(shd, ghd, s"For loop terminates with $theConcl but program had final condition $concl")
                  case fin => throw RefinementFailure(shd, ghd, s"For loop expects dual test at end of game, but got " + fin)
                }
                refine(body, a)
                refine(KaisarProof.block(stl), gtl)
              case _ => throw RefinementFailure(s, Compose(ghd, gtl), "For loop can only refine angelic loop containing increment, followed by assertion")
            }
          // @TODO: More specific error messages for tests etc
          case _ => throw RefinementFailure(shd, ghd, s"Proof connective ${PrettyPrinter.short(shd)} does not match program $ghd", shd)
        }
        // In lockstep cases, just recurse directly, else let the case handle recursion
        val oneToOne = shd match {case _: For  => false case _ => true}
        if (oneToOne)
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
