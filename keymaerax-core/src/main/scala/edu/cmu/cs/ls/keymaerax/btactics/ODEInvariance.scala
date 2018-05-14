package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.AnonymousLemmas._
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms._
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary.{useAt, _}
import edu.cmu.cs.ls.keymaerax.btactics.helpers.DifferentialHelper
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig

import scala.collection.immutable._

/**
  * Implements ODE tactics based on the axiomatization from
  * Differential equation axiomatization: The impressive power of differential ghosts [LICS'18].
  *
  * Created by yongkiat on 05/14/18.
  */

object ODEInvariance {

  private val namespace = "odeinvariance"

  lazy val geq = proveBy("f_()>=0 ==> f_()>0 | f_()=0".asSequent,QE)
  /* Teporary stash before moving into derived axioms */
  // TODO: maybe core's Cont axiom should be stated without DX?
  lazy val contAx =
    proveBy("f(||) > 0 -> <{t_'=1,c&f(||)>=0}>t_!=0".asFormula,
      implyR(1) &
      dR("f(||)>0".asFormula)(1) <(
        implyRi & byUS("Cont continuous existence"),
        DW(1) & G(1) & useAt("> flip")(1,0::Nil) & useAt(">= flip")(1,1::Nil) & useAt("<=")(1,1::Nil) & prop
      )
    )
  lazy val uniqAx =
    proveBy("<{c&q(||)}>p(||) & <{c&r(||)}>p(||) <-> <{c&q(||) & r(||)}>p(||)".asFormula,
      prop <(
        cut("<{c&q(||) & r(||)}>(p(||)|p(||))".asFormula) <(
          cohide2(-3,1) & mond & prop,
          hideR(1) & useAt("Uniq uniqueness",PosInExpr(1::Nil))(1) & prop),
        dR("q(||)&r(||)".asFormula)(1)<( closeId, DW(1) & G(1) & prop),
        dR("q(||)&r(||)".asFormula)(1)<( closeId, DW(1) & G(1) & prop)
      )
    )

  lazy val minLem =
    proveBy("min((f(),g()))>=0<->f()>=0&g()>=0".asFormula,QE)

  lazy val maxLemL =
    proveBy("f()>=0 -> max((f(),g()))>=0".asFormula,QE)

  lazy val maxLemR =
    proveBy("g()>=0 -> max((f(),g()))>=0".asFormula,QE)

  lazy val uniqMin =
    proveBy("<{c& min(f(||),g(||))>=0}>p(||) <-> <{c&f(||)>=0}>p(||) & <{c&g(||)>=0}>p(||)".asFormula,
      useAt(uniqAx)(1,1::Nil) & CE(PosInExpr(0::1::Nil)) & byUS(minLem)
    )

  //Refine left/right of max
  val refMaxL =
    proveBy("<{c&f(||)>=0}>p(||) -> <{c& max(f(||),g(||))>=0}>p(||)".asFormula,
      useAt("DR<> differential refine",PosInExpr(1::Nil))(1) & DW(1) & G(1) & byUS(maxLemL))

  val refMaxR =
    proveBy("<{c&g(||)>=0}>p(||) -> <{c& max(f(||),g(||))>=0}>p(||)".asFormula,
      useAt("DR<> differential refine",PosInExpr(1::Nil))(1) & DW(1) & G(1) & byUS(maxLemR))

  private val maxF = Function("max", None, Tuple(Real, Real), Real, interpreted=true)
  private val minF = Function("min", None, Tuple(Real, Real), Real, interpreted=true)

  //If given a bound i, generate the local progress formula up to that bound
  // i.e. the i-th Lie derivative is strict
  // p>=0 & (p=0 -> (p'>=0 & (p'=0 -> ...) & (p=0&... -> p'^i >0)
  def pStar(ode: DifferentialProgram,p:Term, bound: Int) : Formula ={
    if(bound <= 0) return Greater(p,Number(0))
    else{
      val lie = DifferentialSaturation.simplifiedLieDerivative(ode, p, None)
      val fml = pStar(ode,lie,bound-1)
      return And(GreaterEqual(p,Number(0)), Imply(Equal(p,Number(0)),fml))
    }
  }

  //Homomorphically extend pStar to max and min terms
  def pStarHom(ode: DifferentialProgram,p:Term, bound: Int) : Formula = {
    p match{
      case FuncOf(f,Pair(l,r)) =>
        if (f == maxF) Or(pStarHom(ode,l,bound),pStarHom(ode,r,bound))
        else if (f==minF) And(pStarHom(ode,l,bound),pStarHom(ode,r,bound))
        else ???
      case _ => pStar(ode,p,bound)
    }
  }


  /* G |- p>=0   G|- <x'=f(x)&p'>=0>o,D
   * -----
   * G |- <x'=f(x)&p>=0>o,D
   *
   * As a standalone tactic, this directly cuts p=0 | p>0 and leaves it open
   */
  def lpstep: DependentPositionTactic = "LPstep" by ((pos:Position,seq:Sequent) => {
    require(pos.isTopLevel && pos.isSucc, "LP step currently only in top-level succedent")

    val (p: Term, ode: DifferentialProgram) = seq.sub(pos) match {
      case Some(Diamond(ODESystem(o, GreaterEqual(p,_)), _)) => (p, o)
      case e => throw new BelleThrowable("Unknown shape: " + e)
    }
    //Maybe pass this as an argument to avoid recomputing
    val lie = DifferentialSaturation.simplifiedLieDerivative(ode, p, None)

    cutR(Or(Greater(p,Number(0)), Equal(p,Number(0))))(pos) <(
      //Left open for outer tactic (drops all other succedents)
      skip,
      implyR(pos) &
      orL('Llast) <(
        //Strict case
        useAt(contAx,PosInExpr(1::Nil))(pos) & closeId,
        //Integral case
        dR(GreaterEqual(lie,Number(0)),false)(pos) <(
          //left open for outer tactic
          skip,
          dI('full)(pos) //TODO: probably don't need full power dI here
        )
      ))
  })

  // The following LP helper orchestration tactics assume that the relevant "progress" condition
  // is in antecedent (-1), and the target progress condition is in succedent (1)
  // Currently, assume a uniform bound
  def lpgeq(bound:Int) : BelleExpr =
    if (bound <= 0)
      implyRi & byUS(contAx)
    else //Could also make this fallback to the continuity step for early termination
      DebuggingTactics.print("start") &
      andL(-1) & lpstep(1)< (
        hideL(-2) & byUS(geq),
        hideL(-1) & implyL(-1) & <(closeId, hideL(-2) & lpgeq(bound-1))
      )

  //p*>=0 & q*>=0
  def lpclosed(bound:Int, progressTerm:Term) : BelleExpr =
    progressTerm match{
      case FuncOf(f,Pair(l,r)) =>
        if (f == maxF) orL(-1) <(
          useAt(refMaxL,PosInExpr(1::Nil))(1) & lpclosed(bound,l),
          useAt(refMaxR,PosInExpr(1::Nil))(1) & lpclosed(bound,r))
        else if (f==minF) andL(-1) & useAt(uniqMin,PosInExpr(0::Nil))(1) & andR(1) <(
          hideL(-2) & lpclosed(bound,l),
          hideL(-1) & lpclosed(bound,r)
        )
        else ???
      case _ => lpgeq(bound)
    }

}
