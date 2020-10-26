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
      case Triv() | _: Label | _: LetSym | _: Ghost | _: PrintGoal | _: Pragma | _: Was | _: Match => true
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

  // destructor for games which peels off blocks of SSA assignments
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

  // Phi has no effect on dynamics of program, can delete in refinement comparisons
  private def unphi(s: Statement): Statement = {
    s match {
      case phi: Phi => phi.asgns
      case _ => s
    }
  }

  // Some statements, especially auto-generated ones, can be arranged in silly orders but are commutative anyway.
  // commute statements to agree with game when possible
  // @TODO: Support any dependency-free block assignment, not just free. Also check conditions even in phi case. Also change SSA pass not to do silly assignment orders
  // in phi blocks
  private def sortBy(ss: List[Statement], ghd: Program): List[Statement] = {
    (ss, ghd) match {
      case (Block((_: Phi) :: (_: For) :: _) :: _, _) => ss
      // For now, only sort phis, but not for-loop phis
      case (Phi(Block(ss)) :: tail, as: Assign) =>
        val (same, diff) = ss.partition({
          case Modify(_, List((x, Some(f)))) if x == as.x && f == as.e => true
          case _ => false
        })
        same match {
            // maintain flattenedness
          case found :: Nil =>
            val diffBlock = if(diff.nonEmpty) List(Phi(Block(diff))) else Nil
            Phi(found) :: (diffBlock ++ tail)
          case _ => ss
        }
      case _ => ss
    }
  }

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
    // @TODO: Need to be more exact and make sure rhs of each assignment is correct even though they're different for base case and main case
    val lSet = ssAssigns.toSet.map((asgn: Assign) => asgn.x)
    val rSet = games.toSet.map((asgn: Assign) => asgn.x)
    val lDiff = lSet -- rSet
    val rDiff = rSet -- lSet
    // @TODO: get exact SSA indices
    val lAdmiss = lDiff.filter({case x if x.name == loopIndex.name => false case _ => true})
    if (rDiff.nonEmpty) {
      throw RefinementFailure(fullS, game, s"For-loop header of game had extra assignments to: $rDiff")
    }
    if (lAdmiss.nonEmpty) {
      throw RefinementFailure(fullS, game, s"For-loop header of proof had extra assignments to: $lAdmiss")
    }
  }

  /** @throws RefinementFailure if s does not refine game */
  private def refine(s: Statement, game: Program, gvs: Set[Variable]): Unit = {
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
          // @TODO: SSA will fix this
          case (Note(x, pt, None), Dual(Test(q))) =>
            throw RefinementFailure(shd, ghd, "Expected proved formula in note statement", s)
          case (pode: ProveODE, osys: ODESystem) => refine(pode, osys, odeIsAngelic = false)
          case (pode: ProveODE, Dual(osys: ODESystem)) => refine(pode, osys, odeIsAngelic = true)
          case (BoxLoop(sbod, _), Loop(gbod)) => refine(sbod, gbod, gvs)
          case (BoxChoice(sl, sr), Choice(gl, gr)) => refine(sl, gl, gvs); refine(sr, gr, gvs)
          case (Switch(_, pats), Dual(brGame: Choice)) =>
            val nBranches = pats.length
            StandardLibrary.unchoose(brGame, nBranches) match {
              case None => throw RefinementFailure(shd, ghd, "Program did not have enough branches for proof")
              case Some(gameBranches) =>
                val pairs = pats.zip(gameBranches)
                pairs.foreach({
                  case ((_pat, fml, s), Compose(Test(q), g)) if fml == q => refine(s, Dual(g), gvs)
                  case ((_pat, fml, s), g) => refine(s, g, gvs) // make guards optional
                })
            }
          case (Block((phi: Phi) :: (fr@For(metX, met0, metIncr, conv, guard, body)) :: Nil), assignMetZ) =>
            def stripLoopFooter(s: Statement): Statement = {
              val ss = KaisarProof.flatten(List(s))
              if(!ss.last.isInstanceOf[Phi])
                throw RefinementFailure(shd, ghd, "Could not find phi nodes in footer of proof loop body")
              KaisarProof.block(ss.dropRight(1))
            }
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
            // @TODO: Stronger test which gets SSA renames exactly right but is also sonud
            if (incr.x.name != metX.name) {
              throw RefinementFailure(fr, loopGame, "Refining for-loop, loop body must have fixed format  {{body;}^@ incr;} where incr increments the loop index")
            }
            if(assignMetZ != Assign(metX, met0)) {
              val mod = Modify(Nil, List((metX, Some(met0))))
              throw RefinementFailure(mod, ghd, "Refining for-loop, game must start with assignment of index variable to initial value")
            }
            checkForHeaderAgrees(phi, gamePhi, metX)
            checkForHeaderAgrees(phi, bodyPhi, metX)
            val metric = Metric(metX, metIncr, guard.f, Set()) // Note: assume taboos checked elsewhere
            val termCond = metric.guardPost(metX)
            val theConcl = conv.map(_.f) match {
              case None => termCond
              case Some(f) => And(f, termCond)
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
            val plainBody = stripLoopFooter(body)
            refine(plainBody, gameBody, gvs)
            refine(KaisarProof.block(stl), theTail, gvs)

          // @TODO: More specific error messages for tests etc
          case _ => throw RefinementFailure(shd, ghd, s"Proof connective ${PrettyPrinter.short(shd)} does not match program $ghd", shd)
        }
        // In lockstep cases, just recurse directly, else let the case handle recursion
        val oneToOne = shd match {case (Block((_: Phi) :: (_: For) :: _))=> false case _ => true}
        if (oneToOne)
          refine (KaisarProof.block(stl), gtl, gvs)
    }
  }

  def apply(s: Statement, game: Program): Unit = {
    try {
      val vs = StaticSemantics(game)
      val gvs = vs.fv.toSet ++ vs.bv.toSet
      refine(s, game, gvs)
    } catch {
        case rf: RefinementFailure =>
          throw ProofCheckException(s"Proof did not refine game $game", cause = rf)
    }
  }
}