package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.AnonymousLemmas._
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms._
import edu.cmu.cs.ls.keymaerax.btactics.SimplifierV3.context
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
  private def lieDer(ode:DifferentialProgram,p:Term) = DifferentialSaturation.simplifiedLieDerivative(ode, p, None)
  /* Temporary stash of derived axioms */
  lazy val geq = proveBy("f_()>=0 ==> f_()>0 | f_()=0".asSequent,QE)
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

  lazy val absLem =
    proveBy("-abs(f())>=0<->f()=0".asFormula,QE)

  lazy val uniqMin =
    proveBy("<{c& min(f(||),g(||))>=0}>p(||) <-> <{c&f(||)>=0}>p(||) & <{c&g(||)>=0}>p(||)".asFormula,
      useAt(uniqAx)(1,1::Nil) & CE(PosInExpr(0::1::Nil)) & byUS(minLem)
    )

  lazy val refAbs =
    proveBy("<{c& -abs(f(||))>=0}>p(||) <-> <{c&f(||)=0}>p(||)".asFormula,
      CE(PosInExpr(0::1::Nil)) & byUS(absLem)
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
  private val absF = Function("abs", None, Real, Real, interpreted=true)

  //Given a bound i, generate the local progress formula up to that bound
  // i.e. the i-th Lie derivative is strict
  // p>=0 & (p=0 -> (p'>=0 & (p'=0 -> ...) & (p=0&... -> p'^i >0)
  def pStar(ode: DifferentialProgram,p:Term, bound: Int) : Formula ={
    if(bound <= 0) return Greater(p,Number(0))
    else{
      val lie = lieDer(ode, p)
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
  def lpstep: DependentPositionTactic = "lpstep" by ((pos:Position,seq:Sequent) => {
    require(pos.isTopLevel && pos.isSucc, "LP step currently only in top-level succedent")

    val (p: Term, ode: DifferentialProgram) = seq.sub(pos) match {
      case Some(Diamond(ODESystem(o, GreaterEqual(p,_)), _)) => (p, o)
      case e => throw new BelleThrowable("Unknown shape: " + e)
    }
    //Maybe pass this as an argument to avoid recomputing
    val lie = lieDer(ode, p)

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
  // Currently, a uniform bound is assumed on all the progress conditions
  def lpgeq(bound:Int) : BelleExpr =
    if (bound <= 0)
      implyRi & byUS(contAx)
    else //Could also make this fallback to the continuity step for early termination
      //DebuggingTactics.print("start") &
      andL(-1) & lpstep(1)< (
        hideL(-2) & byUS(geq),
        hideL(-1) & implyL(-1) & <(closeId, hideL(-2) & lpgeq(bound-1))
      )

  //Homomorphically extend lpgeq to max and min terms
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

  //An ADT encoding the "instruction" for the ODE tactic is
  sealed trait Instruction
  //Disjunctive instruction
  case class Disj(left: Instruction, right:Instruction) extends Instruction
  case class Conj(left: Instruction, right:Instruction) extends Instruction
  //Prove atomic polynomial (in)equality with dI
  case class DiffInv(equational:Boolean) extends Instruction //TODO: maybe keep around provables for re-use
  //Prove atomic polynomial (in)equality with this cofactor
  case class Darboux(cofactor : Term, equational:Boolean) extends Instruction //TODO: maybe keep around provables for re-use
  //Prove atomic polynomial >= with this bound
  case class Strict(bound : Int) extends Instruction
  //Prove using closeF
  case class Triv() extends Instruction

  //Reduce polynomial a by b directly, returning (q,r) where b = qa+r
  private def polyReduce(a:Term, b:Term) : (Term,Term) ={
    //TODO: remove dependence on algebra tool
    if (ToolProvider.algebraTool().isEmpty) throw new BelleThrowable("reduction requires a AlgebraTool, but got None")
    val algTool = ToolProvider.algebraTool().get
    val quo = algTool.polynomialReduce(a,List(b))
    val cofactor = quo._1.head
    val rem = quo._2
    return (cofactor,rem)
  }
  // A more exhaustive implementation
  def pStarHomPlus(ode: DifferentialProgram, dom:Formula, p:Term, bound: Int) : (Formula,Instruction) = {
    p match{
      case FuncOf(f,Pair(l,r)) =>
        if (f == maxF) {
          val (lfml, linst) = pStarHomPlus(ode, dom, l, bound)
          val (rfml, rinst) = pStarHomPlus(ode, dom, r, bound)
          (Or(lfml, rfml), Disj(linst, rinst))
        }
        else if (f==minF) {
          val (lfml, linst) = pStarHomPlus(ode, dom, l, bound)
          val (rfml, rinst) = pStarHomPlus(ode, dom, r, bound)
          (And(lfml, rfml), Conj(linst, rinst))
        }
        else ???
      case Neg(FuncOf(a,p)) =>
        if (a==absF) {
          val lie = lieDer(ode, p)
          val (q,r) = polyReduce(lie,p)
          //Check if domain constraint implies r=0
          println("Equational Lie:"+lie+" "+q+" "+r)
          val pr = proveBy(Imply(dom,Equal(r,Number(0))),QE)
          if(pr.isProved)
            if(q == Number(0)) (Equal(p,Number(0)),DiffInv(true))
            else (Equal(p,Number(0)),Darboux(q,true))
          else
            (False, Triv())
        }
        else ???
      case _ => {
        val lie = lieDer(ode, p)
        val (q,r) = polyReduce(lie,p)
        println("Inequational Lie:"+lie+" "+q+" "+r)
        val pr = proveBy(Imply(dom,GreaterEqual(r,Number(0))),QE)
        if(pr.isProved)
          if(q == Number(0)) (GreaterEqual(p,Number(0)),DiffInv(false))
          else (GreaterEqual(p,Number(0)),Darboux(q,false))
        else
          (pStar(ode, p, bound),Strict(bound))
      }
    }
  }

  //Assume the Q progress condition is at -1
  def lpclosedPlus(inst:Instruction) : BelleExpr =
    inst match{
      case Darboux(t,eq) =>
        (if(eq) useAt(refAbs)(1) else skip) &
        DebuggingTactics.print("Darboux "+t+" "+eq) & implyRi & useAt("DR<> differential refine",PosInExpr(1::Nil))(1) & DifferentialTactics.dgDbx(t)(1)
      case Disj(l,r) =>
        DebuggingTactics.print("DISJ") &
        orL(-2) <(
          useAt(refMaxL,PosInExpr(1::Nil))(1) & lpclosedPlus(l),
          useAt(refMaxR,PosInExpr(1::Nil))(1) & lpclosedPlus(r))
      case Conj(l,r) =>
        DebuggingTactics.print("CONJ") &
        andL(-2) & useAt(uniqMin,PosInExpr(0::Nil))(1) & andR(1) <(
          hideL(-3) & lpclosedPlus(l),
          hideL(-2) & lpclosedPlus(r)
        )
      case DiffInv(eq) =>
        DebuggingTactics.print("DI "+eq) &
        (if(eq) useAt(refAbs)(1) else skip) & implyRi & useAt("DR<> differential refine",PosInExpr(1::Nil))(1) & dI('full)(1)
      case Strict(bound) =>
        DebuggingTactics.print("Strict"+bound) &
        hideL(-1) &
        lpgeq(bound)
      case Triv() =>
        DebuggingTactics.print("Triv") &
        closeF
    }

  // Prove closed semialgebraic invariants ++
  // Current assumptions (for completeness)
  // 1) domain constraint is open
  // 2) only -strict- cases occur for higher Lie derivatives, OR
  // 3) a Darboux inequality occurs
  def sAIclosedPlus(bound:Int=1) : DependentPositionTactic = "sAIc" byWithInput (bound,(pos:Position,seq:Sequent) => {
    require(pos.isTopLevel && pos.isSucc, "sAI only in top-level succedent")
    val (ode,dom,post) = seq.sub(pos) match {
      case Some(Box(sys:ODESystem,post)) => (sys.ode,sys.constraint,post)
      case _ => throw new BelleThrowable("sAI only at box ODE in succedent")
    }
    val (f2,propt)=SimplifierV3.simpWithDischarge(IndexedSeq[Formula](), post,
      DifferentialTactics.maxMinNormalize, SimplifierV3.emptyTaxs)
    val (p,(pf,inst)) = f2 match {
      case GreaterEqual(p,r) if r == Number(0) => (p,pStarHomPlus(ode,dom,p,bound))
      case _ => throw new BelleThrowable("Normalization failed to reach a normal form "+f2)
    }
    println("HOMPLUS:",p,pf,inst)

    //Rewrite postcondition to match real induction
    val (starter,imm) = propt match {
      case None => (skip,skip)
      case Some(pr) => (useAt(pr)(pos ++ PosInExpr(1::Nil)),useAt(pr,PosInExpr(1::Nil))(pos))
    }
    starter & useAt("RI& closed real induction >=")(pos) & andR(pos)<(
      implyR(pos) & imm & ?(closeId), //common case?
      cohideR(pos) & composeb(1) & dW(1) & implyR(1) & assignb(1) &
      implyR(1) & cutR(pf)(1)<(
          hideL(-3) & DebuggingTactics.print("QE step") & QE,
          cohide2(-3,1)& implyR(1) &
            //DebuggingTactics.print("STATE") &
            lpclosedPlus(inst)
        )
    )
  })
}
