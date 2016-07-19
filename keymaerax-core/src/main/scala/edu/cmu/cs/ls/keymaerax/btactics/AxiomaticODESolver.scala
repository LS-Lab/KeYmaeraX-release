/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import DifferentialHelper._
import edu.cmu.cs.ls.keymaerax.lemma.LemmaDBFactory
import TacticFactory._
import Augmentors._
import com.sun.org.apache.xpath.internal.operations.Equals

import scala.collection.parallel.immutable

/**
  * An Axiomatic ODE solver (second attempt)
  *
  * @see Page 25 in http://arxiv.org/abs/1503.01981 for a high-level sketch.
  * @author Nathan Fulton
  */
object AxiomaticODESolver {
  /** The name of the explicit time variables. */
  private val TIMEVAR : String = "kyxtime"

  def tmpmsg(s:String) = println(s) //@todo before deployment, remove this method.

  //region The main tactic

  def apply(implicit qeTool: QETool) = axiomaticSolve(qeTool)

  def axiomaticSolve(implicit qeTool: QETool) = "axiomaticSolve" by ((pos:Position, s:Sequent) => {
    val odePos = subPosition(pos, 0::Nil)

    odeSolverPreconds(pos) &
    addTimeVarIfNecessary(odePos) &
    assertInitializedTimeVar(odePos) & //@note we leave t'=0*t+1 for now because it's easier to name the position after inverseDiffGhost steps.
    cutInSoln(qeTool)(pos).*@(TheType()) &
    HilbertCalculus.DW(pos) &
    simplifyPostCondition(qeTool)(pos) &
    inverseDiffCut(qeTool)(pos).*@(TheType()) &
    inverseDiffGhost(qeTool)(pos).*@(TheType()) &
    rewriteTime(pos) &
    HilbertCalculus.useAt("DS& differential equation solution")(pos)
    //    cutInTimeLB(qeTool)(pos) & @todo why is this done at all, let alone before performing the inverse idff cuts?
  })

  //endregion

  //region Preconditions

  val odeSolverPreconds =  "odeSolverPreconds" by ((pos: Position, s: Sequent) => {
    val modal = s(pos).asInstanceOf[Modal]
    val ODESystem(ode, constraint) = modal.program

    if(modal.isInstanceOf[Diamond])
      throw noDiamondsForNowExn
    else if(timeVar(ode).nonEmpty && atomicOdes(ode).last.xp.x != timeVar(ode).get)
      DebuggingTactics.error("Expected time var to occur at the end of the ODE.")
    else if(!isLinear(ode)) //@todo implement this check.
      DebuggingTactics.error("Expected ODE to be linear.")
    else
      Idioms.nil
  })

  //endregion

  //region Setup time variable

  /** Adds a time variable to the ODE if there isn't one already; otherwise, does nothing.
    *
    * @see [[addTimeVar]] */
  val addTimeVarIfNecessary = "addTimeVarIfNecessary" by ((pos: Position, s:Sequent) => s(pos) match {
      case x:DifferentialProgram if timeVar(x).isEmpty => addTimeVar(pos)
      case x:DifferentialProgram if timeVar(x).nonEmpty => Idioms.nil
      case x:ODESystem if timeVar(x).isEmpty => addTimeVar(pos)
      case x:ODESystem if timeVar(x).nonEmpty => Idioms.nil
      case _ => throw AxiomaticODESolverExn(s"Expected DifferentialProgram or ODESystem but found ${s(pos).getClass}")
  })

  val assertInitializedTimeVar = "assertInitializedTimeVar" by ((pos: Position, s: Sequent) => {
    val timer = (s(pos) match {
      case x: ODESystem => timeVar(x)
      case x: DifferentialProgram => timeVar(x)
      case _ => throw AxiomaticODESolverExn(s"Expected differential program or ode system but found ${s(pos).prettyString}")
    }) match {
      case Some(x) => x
      case None => throw new AxiomaticODESolverExn(s"Expected to have a time var by now in ${s(pos).prettyString}")
    }
    val initialConditions = conditionsToValues(s.ante.flatMap(extractInitialConditions(None)).toList)

    DebuggingTactics.assert(_ => initialConditions.keySet contains timer,
      s"There is no initialCondition for the time variable ${timer}") &
    DebuggingTactics.assert(_ => initialConditions(timer) == Number(0),
      s"The initial condition for ${timer} is non-zero (${initialConditions(timer)})")
  })

  /** Rewrites [{c}]p to [{c, t'=1}]p whenever the system c does not already contain a clock.
    * The positional argument should point to the location of c, NOT the location of the box.
    * This tactic should work at any top-level position and also in any context.
    *
    * @note If we want an initial value for time (kyxtime:=0) then this is the place to add that functionality.
    */
  val addTimeVar = "addTimeVar" by((pos: Position, s:Sequent) => {
    s(pos) match {
      case x:DifferentialProgram if timeVar(x).isEmpty => //ok
      case x:ODESystem if timeVar(x).isEmpty => //ok
      case _ => throw AxiomaticODESolverExn(s"setupTimeVar should only be called on differential programs without an existing time variable but found ${s(pos)} of type ${s(pos).getClass}.")
    }

    val modalityPos = parentPosition(pos)
    if(!s(modalityPos).isInstanceOf[Modal])
      throw AxiomaticODESolverExn("Parent position of setupTimeVar should be a modality.")

    val t = TacticHelper.freshNamedSymbol(Variable(TIMEVAR), s)

    s(modalityPos) match {
      case Box(_,_) => {
        HilbertCalculus.DG(t, Number(0), Number(1))(modalityPos) &
        DLBySubst.assignbExists(Number(0))(modalityPos) &
        DLBySubst.assignEquational(modalityPos)
      }
      case Diamond(_,_) => throw noDiamondsForNowExn
    }
  })

  //endregion

  //region Cut in solutions

  def cutInSoln(implicit qeTool: QETool) = "cutInSoln" by ((pos: Position, s: Sequent) => {
    assert(s(pos).isInstanceOf[Modal], s"Expected a modality but found ${s(pos).prettyString}")
    val system:ODESystem = s(pos).asInstanceOf[Modal].program match {
      case x:ODESystem => x
      case x:DifferentialProgram => ???
    }

    //@todo constrain to only true initial conditions by passing in Some(ode).
    //@todo I don't think that the extractInitialConditions code picks up a=0 as an initial condtion for x'=v,v'=a. Check this when changing None.
    val initialConditions = s.ante.flatMap(extractInitialConditions(None)).toList

    val nextEqn = sortAtomicOdes(atomicOdes(system))
      .filter(eqn => !isOne(eqn.e))
      .filter(eqn => isUnsolved(eqn.xp.x, system))
      .head

    tmpmsg(s"next equation to integrate and cut: ${nextEqn.prettyString}")

    //@todo switch completely to the new integrator, so that this is a single tactic instead of a saturated tactic.
    val solnToCut =
      Integrator(conditionsToValues(initialConditions), system).find(eq => eq.left == nextEqn.xp.x)
        .getOrElse(throw new Exception(s"Could not get integrated value for ${nextEqn.xp.x} using new integration logic."))

    tmpmsg(s"Solution for ${nextEqn.prettyString} is ${solnToCut}")

    //@note we have to cut one at a time instead of just constructing a single tactic because solutions need to be added
    //to the domain constraint for recurrences to work. IMO we should probably go for a different implementation of
    //integral and recurrence so that saturating this tactic isn't necessary, and we can just do it all in one shot.
    s(pos) match {
      case Box(ode, postcond) => {
        DifferentialTactics.diffCut(solnToCut)(pos) <(
          Idioms.nil,
          DebuggingTactics.debug("Doing diffInd on ", true) & DifferentialTactics.diffInd(qeTool)(pos) & DebuggingTactics.assertProved
        )
      }
      case Diamond(ode, postcond) => throw noDiamondsForNowExn
    }
  })

  /**
    * @param ode
    * @return The list of atomic differential equations occurring in the differential program.
    * @author Nathan Fulton
    */
  private def odeConstraints(ode : Program) : List[Formula] = ode match {
    case AtomicODE(x,e)                   => Nil
    case ODESystem(ode, constraint)       => constraint :: Nil
    case DifferentialProduct(left, right) => odeConstraints(left) ++ odeConstraints(right)
    case _                                => throw AxiomaticODESolverExn("Expected AtomicODE, ODESystem, or DifferentialProduct.") //@todo what about other differential programs?
  }

  /**
    *
    * @param v A variable occuring in the odes program.
    * @param system An ode system.
    * @return true if the program does not already contain an = constraint (a.k.a. sol'n) for v in the evolution domain.
    */
  def isUnsolved(v : Variable, system : ODESystem) = {
    val odes = atomicOdes(system.ode)
    if(odes.find(_.xp.x.equals(v)).isEmpty) false //Variables that don't occur in the ODE are trivially already solved.
    else if(timeVar(system.ode).equals(v)) false //Don't need to solve for the time var.
    //In non-special cases, check for a = evolution domain constraint in the ode.
    else {
      val vConstraints = odeConstraints(system).flatMap(decomposeAnds).find(_ match {
        case Equal(l, r) => l.equals(v)
        case _ => false
      })
      vConstraints.isEmpty
    }
  }

  //endregion

  //region diffCut lower bound on time

  /** Adds t>=0 to the differential equation's domain constraint.
    * @todo Why is this necessary? It's not included in the paper proof. */
  def cutInTimeLB(implicit qeTool: QETool) = "cutInTimeLB" by ((pos: Position, s: Sequent) => {
    assert(s(pos).isInstanceOf[Modal], s"Expected modality at position ${pos} of ${s.prettyString}")
    assert(s(pos).asInstanceOf[Modal].program.isInstanceOf[ODESystem], s"Expected modality to contain ODE System but it did not in ${s(pos)}")

    val system = s(pos).asInstanceOf[Modal].program.asInstanceOf[ODESystem]

    val lowerBound = Number(0) //@todo check that this is actually the lower bound. Lower bound could be symbolic.
    val timer = timeVar(system).getOrElse(throw AxiomaticODESolverExn("Expected ODE System to already have a time variable when cutInTimeLB is called."))

    //@todo this won't work in the case where we cut in our own time until Stefan's code for isntantiating exisentials is added in...
    s(pos).asInstanceOf[Modal] match {
      case Box(_,_) => TactixLibrary.diffCut(GreaterEqual(timer, lowerBound))(pos) <(Idioms.nil, TactixLibrary.diffInd(qeTool)(pos) & DebuggingTactics.assertProved)
      case Diamond(_,_) => throw noDiamondsForNowExn
    }
  })

  //endregion

  //region Simplify post-condition

  def simplifyPostCondition(implicit qetool: QETool) = "simplifyPostCondition" by ((pos: Position, s: Sequent) => {
    val modality = s(pos).asInstanceOf[Modal]
    val Box(ode, Imply(evolutionDomain, originalConclusion)) = modality

    val implication = Imply(simplifiedConclusion(evolutionDomain, originalConclusion), modality.child)

    tmpmsg(s"Implication is ${implication.prettyString}")
    tmpmsg(s"And modality is ${s(pos).prettyString}")
    /*
     * Explanation:
     * The tactic in the next four lines creates a new lemma that proves `implication`, then uses that lemma to perform useAt rewriting on the
     * conclusion of the box modality. This is IMO much cleaner than the old approach of cutting in an equivalence and proving by G,K,etc. manually.
     *
     * This tactic uses the name "_simplifyPostCondition" for the lemma.
     * This name must not exist must not exist prior to executing the tactic because the ProveAs tactic assumes the name is fresh.
     * Therefore, we clear out any lemma with this name from the database both before *and* after running the proveAs.
     * We clear out after for the obvious reason (the lemma's usage should be local). We clear out before as well in case
     * there was some exception in an early execution of this tactic that resulting in the tactic not running to completion
     * @todo ProveAs should do this be default at the end of each execution, and should implicitly use a namespace that lazuUseAt et al knows about.
     */
    clearProveAsScope("_simplifyPostCondition") &
    ProveAs("_simplifyPostCondition", implication, TactixLibrary.QE) &
    HilbertCalculus.lazyUseAt("_simplifyPostCondition", PosInExpr(1 :: Nil))(subPosition(pos, PosInExpr(1::Nil))) & //@todo weird positioning...
    clearProveAsScope("_simplifyPostCondition")
  })

  private def simplifiedConclusion(evolutionDomain: Formula, originalConclusion: Formula): Formula = {
    val fvs = StaticSemantics.freeVars(originalConclusion)
    val varsToReplace : Map[Variable, Term] = conditionsToValues(extractInitialConditions(None)(evolutionDomain)).filterKeys(fvs.contains)

    varsToReplace.foldLeft(originalConclusion)(
      (currentFormula, nextPair) => SubstitutionHelper.replaceFree(currentFormula)(nextPair._1, nextPair._2)
    )
  }

  @deprecated("Move this to a centralized location for ProveAs stuff", "4.2b2")
  def clearProveAsScope(lemmaName: String) = new DependentTactic("clearProveAsScope") {
    override def computeExpr(p:Provable) = {
      LemmaDBFactory.lemmaDB.remove(lemmaName)
      Idioms.nil
    }
  }

  //endregion

  //region Inverse diff cuts

  def inverseDiffCut(implicit qeTool: QETool) = "inverseDiffCut" by ((pos: Position, s: Sequent) => {
    val f: Modal = s(pos).asInstanceOf[Modal]
    val ODESystem(ode, constraint) = f.program
    val p = f.child

    constraint match {
      case And(leftConstriant, nextConstraint) if(isPartOfSoln(ode, nextConstraint)) => f match {
        case Box(_, _) => {
          HilbertCalculus.useExpansionAt("DC differential cut")(pos) <(
            Idioms.nil, /* Branch with no ev dom contraint */
            DifferentialTactics.diffInd(qeTool)(1) & DebuggingTactics.assertProved /* Show precond of diff cut */
            )
        }
        case Diamond(_,_) => throw noDiamondsForNowExn
      }
      case _ => Idioms.nil
    }
  })

  /** Returns true iff f is part of the cut-in solution for the ODE. */
  private def isPartOfSoln(ode: DifferentialProgram, f: Formula): Boolean = f match {
    case Equal(t1, t2) => atomicOdes(ode).exists(a => a.xp.x == t1 || a.xp.x == t2)
    case _ => false
  }

  //endregion

  //region Inverse diff ghosts

  def inverseDiffGhost(implicit qeTool: QETool) = "inverseDiffGhost" by ((pos: Position, s: Sequent) => {
    val f: Modal = s(pos).asInstanceOf[Modal]
    val ODESystem(ode, constraint) = f.program
    val p = f.child

    ode match {
      case ode:DifferentialProduct => {
        val y_ = firstODE(ode)
        val x_ = secondODE(ode)

        /* Note: Constructing our own substitution because the default substitution seems to get at least g(??) wrong. */
        def subst(r: RenUSubst) = {
          RenUSubst(USubst(
              "g(??)".asTerm ~> y_.e ::
              "f(??)".asTerm ~> x_.e ::
              "H(??)".asFormula ~> r("H(??)".asFormula) ::
              DifferentialProgramConst("c") ~> r(DifferentialProgramConst("c")) ::
              "p(??)".asFormula ~> r("p(??)".asFormula) ::
              Nil)) ++
          RenUSubst(URename("y_".asTerm.asInstanceOf[Variable], y_.xp.x)) ++
          RenUSubst(URename("x_".asTerm.asInstanceOf[Variable], x_.xp.x))
        }

        f match {
          case Box(_,_) => {
            val axiomName = if(atomicOdes(ode).length > 2) "DG++ System" else "DG++"
            TactixLibrary.cut(Forall(y_.xp.x::Nil, f)) <(
              HilbertCalculus.useAt("all eliminate")('Llast) & TactixLibrary.close & DebuggingTactics.assertProved,
              TactixLibrary.hide(pos) & HilbertCalculus.useExpansionAt(axiomName, ((s:RenUSubst) => subst(s)))(pos)
            )
          }
          case Diamond(_,_) => throw noDiamondsForNowExn
        }

      }
      case _ => Idioms.nil
    }
  })

  private def firstODE(ode: DifferentialProduct):AtomicODE = ode.left match {
    case pi:DifferentialProduct => firstODE(pi)
    case l:AtomicODE => l
    case _ => ???
  }

  private def secondODE(ode: DifferentialProduct):AtomicODE = ode.left match {
    case pi:DifferentialProduct => secondODE(pi)
    case l:AtomicODE => ode.right match {
      case pi:DifferentialProduct => firstODE(pi)
      case r:AtomicODE => r
      case _ => ???
    }
  }

  //endregion

  //region DS Diff Solve setup

  /** Rewrites t'=0*t+1 to t'=1
    * @todo this ought to be a post-processing stop for [[addTimeVar]] but isn't because locating the position could end up buggy too easily. */
  val rewriteTime = "rewriteTime" by ((pos: Position, s: Sequent) => {
    val f: Modal = s(pos).asInstanceOf[Modal]
    val ODESystem(AtomicODE(time, c), constraint) = f.program

//    val lemma = f match {
//      case Box(_,_) => Equiv(Box(ODESystem(AtomicODE(time, Number(1)), constraint), f.child), f)
//      case x:Diamond => throw noDiamondsForNowExn
//    }

    c match {
      case Plus(Times(zero, t), one) if(zero == Number(0) && one == Number(1)) => {
        DebuggingTactics.error("Don't know how to do this yet.")
//        clearProveAsScope("rewriteTimeLemma") &
//        ProveAs("rewriteTimeLemma", Equal(Number(1), c), TactixLibrary.QE) &
//        DebuggingTactics.debugAt("here1234", true)(subPosition(pos, PosInExpr(0 :: 0 :: 1 :: Nil))) &
//        HilbertCalculus.lazyUseAt("rewriteTimeLemma", PosInExpr(0 :: 0 :: 1 :: Nil))(pos) &
//        clearProveAsScope("rewriteTimeLemma")
      }
      case n:Number if(n == Number(1)) => Idioms.nil
      case _ => DebuggingTactics.error("Don't know how to handle this.")
    }
  })

  //endregion

  //region Misc.

  /** Exceptions thrown by the axiomatic ODE solver. */
  case class AxiomaticODESolverExn(msg: String) extends Exception(msg)
  val noDiamondsForNowExn = AxiomaticODESolverExn("No diamonds for now.")

  def parentPosition(pos: Position): Position =
    if(pos.isAnte) AntePosition(pos.checkAnte.top, pos.inExpr.parent)
    else SuccPosition(pos.checkSucc.top, pos.inExpr.parent)

  def subPosition(pos: Position, sub: PosInExpr): Position =
    if(pos.isAnte) AntePosition(pos.checkAnte.top, pos.inExpr + sub)
    else SuccPosition(pos.checkSucc.top, pos.inExpr + sub)
  def subPosition(pos: Position, sub: List[Int]): Position = subPosition(pos, PosInExpr(sub))

  //endregion
}