/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

/**
  * Check whether underlying strategy of Kaisar proof is a strategy for a given game
  * @author Brandon Bohrer
  */
package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.KaisarProof.{LocatedException, ProofCheckException}
import edu.cmu.cs.ls.keymaerax.core.{PrettyPrinter => _, _}
import edu.cmu.cs.ls.keymaerax.btactics.helpers.DifferentialHelper._
import edu.cmu.cs.ls.keymaerax.btactics.helpers.ProgramHelpers
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
      case Triv() | _: Label | _: LetSym | _: Ghost | _: PrintGoal | _: Pragma | _: Was | _: Match | _: Comment => true
      case _ => false
    }
  }

  // destructor for games which peels off the smallest head possible
  private def uncons(game: Program): (Program, Program) = {
    game match {
      // ; is self-dual
      case Dual(Compose(Compose(l, x), r)) => uncons(Dual(Compose(l, Compose(x, r))))
      case Dual(Compose(l, r)) => (Dual(l), Dual(r))
      case Compose(Compose(l, x), r) => uncons(Compose(l, Compose(x, r)))
      case Compose(l, r) => (l, r)
      case l => (l, Test(True))
    }
  }

  private def isPhiBlock(hp: Program): Boolean = {
    hp match {
      case Test(True) | Dual(Test(True)) => true
      case Assign(_, _ : Variable) | Dual(Assign(_, _: Variable)) => true
      case Compose(Assign(x, y : Variable), r) => isPhiBlock(r)
      case Compose(Dual(Assign(x, y : Variable)), r) => isPhiBlock(r)
      case _ => false
    }
  }

  private def asPhiBlock(hp: Program): List[Assign] = {
    hp match {
      case asgn: Assign => List(asgn)
      case Dual(asgn: Assign) => List(asgn)
      case Compose(asgn: Assign, r) => asgn :: asPhiBlock(r)
      case Compose(Dual(asgn: Assign), r) => asgn :: asPhiBlock(r)
      case Test(True) | Dual(Test(True)) => Nil
      case _ => throw new Exception("Bug: bad pattern match in RefinementChecker.asPhiBlock")
    }
  }

  /** Greedily split hybrid program into front and back, where "front" heuristically tries to find longest possible
    * sequence of SSA phi-assignments, if possible.
    *
    * @param game Hybrid program
    * @return (hd, tl) where hd is an initial block and tl is the remainder of the program, if any
    */
  private def unappend(game: Program): (Program, Program) = {
    def isAssign(hp: Program): Boolean = hp match {
      case Assign(_, _: Variable) | Dual(Assign(_, _: Variable)) | Dual(Dual(Assign(_, _: Variable))) => true
      case _ => false
    }
    def recombine(l: Program, x: Program, r: Program): (Program, Program) = {
      if (isPhiBlock(x)) (Compose(l, x), r)
      else (l, Compose(x, r))
    }
    game match {
      // ; is self-dual
      case Compose(Dual(Compose(l,x)), r) =>
        unappend(Compose(Dual(l), Compose(Dual(x), r)))
      case Compose(hd, r) if isAssign(hd) =>
        val (rl, rr) = unappend(r)
        recombine(hd, rl, rr)
      case Dual(Compose(hd, r)) if isAssign(hd)=>
        val (rl, rr) = unappend(Dual(r))
        recombine(hd, rl, rr)
      case Dual(Compose(Compose(l, x), r)) => uncons(Dual(Compose(l, Compose(x, r))))
      case Compose(l, r)  if isPhiBlock(l) => (l, r)
      case Compose(l, r) => (l, r)
      case Dual(Compose(l, r)) => (Dual(l), Dual(r))
      case l => (l, Test(True))
    }
  }

  /** @param s Statement
    * @return Statement s with any top-level [[Phi]] node stripped. Return value has same dynamics as [[s]]
    */
  private def unphi(s: Statement): Statement = {
    s match {
      case phi: Phi => phi.asgns
      case _ => s
    }
  }

  /** @return whether ss is a block of Modify statements which can be soundly reordered */
  private def commutativeMods(ss: List[Statement]): Boolean = {
    val mods = ss.flatMap({case mod: Modify => List(mod) case _ => Nil})
    if (mods.length < ss.length)
      return false // because some statement was not a Modify
    val fvs = mods.map(mod => mod.freeVars).reduce(_ ++ _)
    val bvs = mods.map(mod => mod.boundVars).reduce(_ ++ _)
    fvs.intersect(bvs).isEmpty
  }

  /** Attempts to soundly reorder statement list so that statement corresponding to a game appears first.
    * This is particularly useful when auto-generated proof statements are generated in some unknown arbitrary order.
    * @param ss List of Kaisar statements to be reordered
    * @param ghd Game by which to reorder ss. Is "head" in list traversal of games
    * @return Statement list equivalent to ss which, if possible, begins with statement corresponding to game ghd
    */
  private def sortBy(ss: List[Statement], ghd: Program): List[Statement] = {
    def sortBlock(ss: List[Statement], tail: List[Statement], as: Assign, isPhi: Boolean): List[Statement] = {
      val (same, diff) = ss.partition({
        case Modify(_, List((x, Some(f)))) if x == as.x && f == as.e => true
        case _ => false
      })
      same match {
        // maintain flattenedness
        case found :: Nil =>
          val diffBlock = if(diff.isEmpty) Nil else if (isPhi) List(Phi(Block(diff))) else List(Block(diff))
          (if(isPhi) Phi(found) else found) :: (diffBlock ++ tail)
        case _ => ss
      }
    }
    (ss, ghd) match {
      case (Block((_: Phi) :: (_: For) :: _) :: _, _) => ss
      // For now, only sort phis, but not for-loop phis
      case (Phi(Block(ss)) :: tail, as: Assign) if commutativeMods(ss)=>
        sortBlock(ss, tail, as, isPhi = true)
      case (Block(ss) :: tail, as: Assign) if commutativeMods(ss)=>
        sortBlock(ss, tail, as, isPhi = false)
      case _ => ss
    }
  }

  /** @param s Kaisar proof statement
    * @param gvs Set of variables mentioned in games (non-ghost variable set)
    * @return s with no-op statements stripped: explicit ghosts, implicit ghost phi assignments, meta nodes
    */
  // Ignore ghosts, phi-ghosts, meta nodes, etc
  private def beIgnorant(s: Statement, gvs: Set[Variable]): List[Statement] = {
    def ignorePhiGhost(maybePhi: Statement): List[Statement] = {
      maybePhi match {
        case phi: Phi =>
          val atoms =  KaisarProof.flatten(List(phi.asgns))
          // @TODO: Much better way: explicitly mention ghosts in SSA pass results
          // delete phi assignments of variables that don't appear in game because they're actually ghosts
          val kept = atoms.filter{
            case Modify(_, ((x, Some(f))) :: Nil) if !gvs.exists(y => y.name == x.name) => false
            case _ => true
          }
          kept match {
            case Nil => Nil
            case _ => List(Phi(KaisarProof.block(kept)))
          }
        case _ => List(maybePhi)
      }
    }
    KaisarProof.flatten(List(s)) match {
      // for-loops have phi-block headers which need manual special handling
      case lst@((phi : Phi) :: (fr: For) :: tl) => Block(phi :: fr :: Nil) :: tl
      case flat => val dropped = flat.dropWhile(isIgnored)
        dropped.flatMap(ignorePhiGhost)
    }
  }

  /** @return unit if phi block and program make same phi assignments possibly in different order and
    *  with possible duplicate assignments to the loop index due to silly artifacts of SSA pass
    *  @throws RefinementFailure if headers don't agree*/
  private def checkForHeaderAgrees(pf: Phi, game: Program, loopIndex: Variable): Unit = {
    val ss = KaisarProof.flatten(pf.asgns :: Nil)
    val fullS = Block(ss)
    val games = asPhiBlock(game)
    val ssAssigns = ss.map({case Modify(_, List((x, Some(f)))) => Assign(x, f) case _ => throw new Exception("Bad pattern match in RefinementChecker.forHeaderAgrees")})
    val lSet = ssAssigns.toSet
    val rSet = games.toSet
    val lDiff = lSet -- rSet
    val rDiff = rSet -- lSet
    val lAdmiss = lDiff.filter({case x if x.x == loopIndex => false case _ => true})
    if (rDiff.nonEmpty) {
      throw RefinementFailure(fullS, game, s"For-loop header or footer of game had extra assignments to: $rDiff")
    }
    if (lAdmiss.nonEmpty) {
      throw RefinementFailure(fullS, game, s"For-loop header or footer of proof had extra assignments to: $lAdmiss")
    }
  }

  /** @throws RefinementFailure if s does not refine game */
  private def refine(kc: Context, s: Statement, game: Program, gvs: Set[Variable]): Unit = {
    // undo block constructors, drop ghosts and lets
    val ss = beIgnorant(s, gvs)
    val (ghd, gtl) = uncons(game)
    // use "triv" and "?true" as terminators
    (sortBy(ss, ghd), game) match {
      case (Nil | Triv() :: Nil, Test(True) | Dual(Test(True))) => ()
      case (Nil, _) => throw RefinementFailure(Triv(), game, "Proof only proves fragment of game", s)
      case (shd :: stl, _) =>
        // compare head, which can be recursive
        (unphi(shd), ghd) match {
          case (Modify(_ids, List((x, Some(f)))), Assign(xx, ff)) if x == xx && f == ff => ()
          case (Modify(_ids, List((x, Some(f)))), Dual(AssignAny(xx))) if x == xx => ()
          case (Modify(_ids, List((x, None))), AssignAny(xx)) if x == xx => ()
          case (Assert(_id, p, _m), Dual(Test(q))) if p == q => ()
          case (Assume(_id, p), Test(q)) if p == q => ()
          case (Note(x, pt, Some(fml)), Dual(Test(q))) if fml == q => ()
          case (Note(x, pt, None), Dual(Test(q))) =>
            throw RefinementFailure(shd, ghd, "Expected proved formula in note statement", s)
          case (pode: ProveODE, osys: ODESystem) => refine(pode, osys, odeIsAngelic = false)
          case (pode: ProveODE, Dual(osys: ODESystem)) => refine(pode, osys, odeIsAngelic = true)
          case (bl@BoxLoop(sbod, _), Loop(gbod)) => {
            val con = kc.:+(BoxLoopProgress(bl, Triv()))
            refine(con, sbod, gbod, gvs)
          }
          case (bc@BoxChoice(sl, sr), Choice(gl, gr)) => {
            val conL = kc.:+(BoxChoiceProgress(bc, 0, Triv()))
            val conR = kc.:+(BoxChoiceProgress(bc, 1, Triv()))
            refine(conL, sl, gl, gvs)
            refine(conR, sr, gr, gvs)
          }
          case (sw@Switch(_, pats), Dual(brGame: Choice)) =>
            val nBranches = pats.length
            StandardLibrary.unchoose(brGame, nBranches) match {
              case None => throw RefinementFailure(shd, ghd, "Program did not have enough branches for proof")
              case Some(gameBranches) =>
                val pairs = pats.zip(gameBranches)
                var which = 0
                pairs.foreach( br => {
                  val con = kc.:+(SwitchProgress(sw, which, Triv()))
                  which = which + 1
                  br match {
                    case ((_pat, fml, s), Compose(Test(q), g)) if fml == q => refine(con, s, Dual(g), gvs)
                    case ((_pat, fml, s), g) => refine(con, s, g, gvs) // make guards optional
                  }})
            }
          case (Block((phi: Phi) :: (fr@For(metX, met0, metIncr, conv, guard, body, guardEps)) :: Nil), assignMetZ) =>
            def stripLoopFooter(s: Statement): (Statement, Phi) = {
              val ss = KaisarProof.flatten(List(s))
              if(!ss.last.isInstanceOf[Phi])
                throw RefinementFailure(shd, ghd, "Could not find phi nodes in footer of proof loop body")
              (KaisarProof.block(ss.dropRight(1)), ss.last.asInstanceOf[Phi])
            }
            val metXFooter = Variable(metX.name, metX.index.map(i => i + 1))
            val (gamePhi, loopAndCont) = unappend(gtl)
            val (loopGame, cont) = loopAndCont match {
              case (Compose(loop@Dual(Loop(_)), after)) => (loop, Some(after))
              case (Dual(Loop(_))) => (loopAndCont, None)
              case _ =>
                throw RefinementFailure(fr, loopAndCont, "Refining for-loop, expected game to have Angelic loop  {{body}*}^@ but couldn't find it")
            }
            val (gameBody, bodyAssigns) = loopGame match {
              case Dual(Loop(Compose(Dual(a), assigns))) => (a, assigns)
              case Dual(Loop(Dual(Compose(a, assigns)))) => (a, assigns)
              case _ => throw RefinementFailure(fr, loopGame, "Refining for-loop, loop body must have fixed format {body;^@; assigns}  or {body; assigns}^@")
            }
            val (incr: Assign, bodyPhi) = uncons(bodyAssigns)
            if (incr != Assign(metXFooter, metIncr)) {
              throw RefinementFailure(fr, loopGame, "Refining for-loop, loop body must have fixed format  {{body;}^@ incr;} where incr increments the loop index")
            }
            if(assignMetZ != Assign(metX, met0)) {
              val mod = Modify(Nil, List((metX, Some(met0))))
              throw RefinementFailure(mod, ghd, "Refining for-loop, game must start with assignment of index variable to initial value")
            }
            val (plainBody, Phi(proofBodyRawPhi)) = stripLoopFooter(body)
            val proofBodyPhi = Phi(KaisarProof.block(Modify(Nil, List((metX, Some(metXFooter)))) :: proofBodyRawPhi :: Nil))
            checkForHeaderAgrees(phi, gamePhi, metX)
            checkForHeaderAgrees(proofBodyPhi, bodyPhi, metX)
            val termCond = fr.guardDelta.map(gd => Metric.weakNegation(fr.guard.f, gd))
            val theConcl = (conv.map(_.f), termCond) match {
              case (None, Some(tc)) => tc
              case (Some(f), Some(tc)) => And(f, tc)
              case (Some(f), None) => f
            }
            // If tail starts with test of for loop termination condition, remove it before recursive call,
            // @TODO: Try to give helpful heuristic that looks for typos in final test condition
            val theTail =
              cont match {
                case None => Test(True)  // end of game reached
                case Some(Dual(Test(concl))) if theConcl == concl => Test(True) // erase the test, which is also the whole game
                case Some(Compose(Dual(Test(concl)), rest)) if theConcl == concl => rest // erase the test, leave the rest
                case Some(k)  => k // there was no test of termination condition, whole continuation should be treated as "after the loop"
              }
            // body ends in phi node, take everything but phi
            val kcp = kc.:+(phi)
            val bodCon = kcp.:+(ForProgress(fr, Triv()))
            val tailCon = kcp.:+(fr)
            refine(bodCon,plainBody, gameBody, gvs)
            refine(tailCon, KaisarProof.block(stl), theTail, gvs)
          // @TODO: More specific error messages for tests etc
          case _ => throw RefinementFailure(shd, ghd, s"Proof connective ${PrettyPrinter.short(shd)} does not match program $ghd", shd)
        }
        // In lockstep cases, just recurse directly, else let the case handle recursion
        val oneToOne = shd match {case (Block((_: Phi) :: (_: For) :: _))=> false case _ => true}
        if (oneToOne) {
          val con = kc.:+(shd)
          refine (con, KaisarProof.block(stl), gtl, gvs)
        }
    }
  }

  def apply(s: Statement, game: Program): Unit = {
    try {
      val vs = StaticSemantics(game)
      val gvs = vs.fv.toSet ++ vs.bv.toSet
      refine(Context.empty, s, game, gvs)
    } catch {
        case rf: RefinementFailure =>
          throw ProofCheckException(s"Proof did not refine game $game", cause = rf)
    }
  }
}
