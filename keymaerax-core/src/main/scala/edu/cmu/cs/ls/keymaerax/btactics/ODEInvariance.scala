package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.AnonymousLemmas._
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms._
import edu.cmu.cs.ls.keymaerax.btactics.SimplifierV3.{context, namespace}
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary.{useAt, _}
import edu.cmu.cs.ls.keymaerax.btactics.helpers.DifferentialHelper
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig

import scala.collection.immutable._
import scala.collection.mutable.ListBuffer

/**
  * Implements ODE tactics based on the axiomatization from
  * Differential equation axiomatization: The impressive power of differential ghosts [LICS'18].
  *
  * Created by yongkiat on 05/14/18.
  */

object ODEInvariance {

  private val namespace = "odeinvariance"
  private def lieDer(ode:DifferentialProgram,p:Term) =
      DifferentialHelper.simplifiedLieDerivative(ode, p, ToolProvider.simplifierTool())

  /* Stash of derived axioms */

  // Rewrite >=
  private lazy val geq = remember("f_()>=0 <-> f_()>0 | f_()=0".asFormula, QE, namespace)

  // Cont with the domain constraint already refined to >= instead of >
  private lazy val contAx =
    remember("f(||) > 0 -> <{t_'=1,c&f(||)>=0}>t_!=0".asFormula,
      implyR(1) &
      dR("f(||)>0".asFormula)(1) <(
        implyRi & byUS("Cont continuous existence"),
        DW(1) & G(1) & useAt("> flip")(1,0::Nil) & useAt(">= flip")(1,1::Nil) & useAt("<=")(1,1::Nil) & prop
      ), namespace)

  //iff version of uniqueness axiom
  private lazy val uniqAx =
    remember("<{c&q(||)}>p(||) & <{c&r(||)}>p(||) <-> <{c&q(||) & r(||)}>p(||)".asFormula,
      prop <(
        cut("<{c&q(||) & r(||)}>(p(||)|p(||))".asFormula) <(
          cohide2(-3,1) & mond & prop,
          hideR(1) & useAt("Uniq uniqueness",PosInExpr(1::Nil))(1) & prop),
        dR("q(||)&r(||)".asFormula)(1)<( closeId, DW(1) & G(1) & prop),
        dR("q(||)&r(||)".asFormula)(1)<( closeId, DW(1) & G(1) & prop)
      ),namespace)

  //Various conversion rewrites for CE in corresponding lemmas
  private lazy val minLem =
    remember("min((f(),g()))>=0<->f()>=0&g()>=0".asFormula,QE,namespace)

  private lazy val maxLemL =
    remember("f()>=0 -> max((f(),g()))>=0".asFormula,QE,namespace)

  private lazy val maxLemR =
    remember("g()>=0 -> max((f(),g()))>=0".asFormula,QE,namespace)

  private lazy val absLem =
    remember("-abs(f())>=0<->f()=0".asFormula,QE,namespace)

  private lazy val uniqMin =
    remember("<{c& min(f(||),g(||))>=0}>p(||) <-> <{c&f(||)>=0}>p(||) & <{c&g(||)>=0}>p(||)".asFormula,
      useAt(uniqAx)(1,1::Nil) & CE(PosInExpr(0::1::Nil)) & byUS(minLem),
      namespace)

  private lazy val refAbs =
    remember("<{c& -abs(f(||))>=0}>p(||) <-> <{c&f(||)=0}>p(||)".asFormula,
      CE(PosInExpr(0::1::Nil)) & byUS(absLem),
      namespace)

  //Refine left/right of max
  private lazy val refMaxL =
    remember("<{c&f(||)>=0}>p(||) -> <{c& max(f(||),g(||))>=0}>p(||)".asFormula,
      useAt("DR<> differential refine",PosInExpr(1::Nil))(1) & DW(1) & G(1) & byUS(maxLemL),
      namespace)

  private lazy val refMaxR =
    remember("<{c&g(||)>=0}>p(||) -> <{c& max(f(||),g(||))>=0}>p(||)".asFormula,
      useAt("DR<> differential refine",PosInExpr(1::Nil))(1) & DW(1) & G(1) & byUS(maxLemR),
      namespace)

  //Refine or under box
  private lazy val boxOrL =
    remember("[{c&q(||)}]p(||) -> [{c& q(||)}](p(||) | r(||))".asFormula,
      CMon(PosInExpr(1::Nil)) & prop,
      namespace)

  private lazy val boxOrR =
    remember("[{c&q(||)}]r(||) -> [{c& q(||)}](p(||) | r(||))".asFormula,
      CMon(PosInExpr(1::Nil)) & prop,
      namespace)

  private lazy val fastGeqCheck =
    remember("f_() = g_() -> (f_() >=0 -> g_()>=0)".asFormula,QE,
      namespace)

  private lazy val maxF = Function("max", None, Tuple(Real, Real), Real, interpreted=true)
  private lazy val minF = Function("min", None, Tuple(Real, Real), Real, interpreted=true)
  private lazy val absF = Function("abs", None, Real, Real, interpreted=true)

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

    //DebuggingTactics.print("LPSTEP"+p) &
    cutR(Or(Greater(p,Number(0)), Equal(p,Number(0))))(pos) <(
      //Left open for outer tactic (drops all other succedents)
      skip,
      implyR(pos) &
      //DebuggingTactics.print("OR STEP") &
        orL('Llast) <(
        //Strict case
        //DebuggingTactics.print("Cont STEP") &
          useAt(contAx,PosInExpr(1::Nil))(pos) & closeId,
        //Integral case
        //DebuggingTactics.print("DI STEP") &
        dR(GreaterEqual(lie,Number(0)),false)(pos) <(
          //left open for outer tactic
          skip,
          //TODO: this may fail on consts -- check
          cohideOnlyL('Llast) &
          //This is a special case where we don't want full DI, because we already have everything
          cohideOnlyR(pos) & dI('diffInd)(1) <(
            useAt(geq)(1) & orR(1) & closeId,
            cohideOnlyL('Llast) & (Dassignb(1)*) & implyRi &
            useAt(fastGeqCheck,PosInExpr(1::Nil))(1) & QE
          )
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
        hideL(-2) & useAt(geq)(-1) & closeId,
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

  /** Given a top-level succedent position corresponding to [x'=f(x)&Q]P
    * Tries to prove that P is a closed semialgebraic invariant, i.e. G|- [x'=f(x)&Q]P
    * P is assumed to be formed from conjunctions, disjunction, p<=q, p>=q, p=q
    * which are collectively normalized to f>=0 (f possibly involving max,min and abs)
    *
    * Current tactic limitations:
    * 1) Assumes that P is already in the antecedents, otherwise leaves that subgoal open
    * 2) It does not characterize local progress for domain constraint Q
    * 3) For polynomials p>=0 in the normalized form that are NOT rank 1, this tactic currently requires
    *    checks the progress formula (p*>0) up to a given bound, rather than p*>=0
    * @param bound (default 1): the bound on higher Lie derivatives to check for strict inequality, i.e. for p>=0,
    *              this is generated p>=0 & (p=0 -> (p'>=0 & (p'=0 -> ...p'^bound > 0 ...))
    *              (i.e. the bound-th Lie derivative is required to be strict)
    * @return Leaves the initial goal G |- P open if it does not prove by QE
    */
  def sAIclosedPlus(bound:Int=1) : DependentPositionTactic = "sAIc" byWithInput (bound,(pos:Position,seq:Sequent) => {
    require(pos.isTopLevel && pos.isSucc, "sAI only applicable in top-level succedent")
    val (ode,dom,post) = seq.sub(pos) match {
      case Some(Box(sys:ODESystem,post)) => (sys.ode,sys.constraint,post)
      case _ => throw new BelleThrowable("sAI only applicable to box ODE in succedent")
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
      case Some(pr) => (useAt(pr)(pos ++ PosInExpr(1::Nil)),useAt(pr,PosInExpr(1::Nil))('Rlast))
    }
    DebuggingTactics.print("PRE") & starter & useAt("RI& closed real induction >=")(pos) & andR(pos)<(
      implyR(pos) & imm & ?(closeId) & QE & done, //common case?
      cohideR(pos) & composeb(1) & dW(1) & implyR(1) & assignb(1) &
      implyR(1) & cutR(pf)(1)<(hideL(-3) & DebuggingTactics.print("QE step") & QE & done, skip) //Don't bother running the rest if QE fails
      & cohide2(-3,1)& implyR(1) & lpclosedPlus(inst)
    )
  })

  // Determines if a formula is of the special "recursive" rank one case
  // i.e. every p~0 is (trivially) Darboux
  // Additionally returns a list of formulas if so representing the diff cut order
  // TODO: can generalize p>=0, p>0 cases to check the barrier condition as well
  // TODO: this should be keeping track of co-factors
  def rankOneFml(ode: DifferentialProgram, dom:Formula, f:Formula) : Option[Formula] = {
    f match {
      case cf:ComparisonFormula =>
        val p = cf.left
        val lie = lieDer(ode, p)
        val (q,r) = polyReduce(lie,p)
        println("comparison fml: "+f+" Lie:"+lie+" "+q+" "+r)

        val zero = Number(0)
        val prf = cf match {
          case GreaterEqual(_, _) => GreaterEqual(r,zero)
          case Greater(_, _) => GreaterEqual(r,zero)
          case LessEqual(_, _) => LessEqual(r,zero) //Not needed
          case Less(_, _) => LessEqual(r,zero) //Not needed
          case Equal(_,_) => Equal(r,zero)
          case NotEqual(_,_) => Equal(r,zero)
        }
        val pr = proveBy(Imply(dom,prf),QE)
        println(pr)
        if(pr.isProved)
          Some(f)
        else {
          if(cf.isInstanceOf[Equal] || cf.isInstanceOf[NotEqual]) return None
          val pr2 = proveBy(Imply(And(dom, Equal(p, zero)), Greater(r, zero)), QE)
          println(pr2)
          if(pr2.isProved)
            Some(f)
          else None
        }

      case and:And =>
        var ls = DifferentialTactics.flattenConjunctions(and)
        var acc = ListBuffer[Formula]()
        var domC = dom
        while(true){
          println("Domain: ",domC)
          //Pull out the ones that are rank 1
          val checkls = ls.map(f =>
            rankOneFml(ode,domC,f) match { case None => Left(f) case Some(res) => Right(res)})
          val l = checkls.collect{case Left(v) => v}
          val r : List[Formula] = checkls.collect{case Right(v) => v}
          acc ++= r
          println("Acc: ",acc)
          if(l.length == checkls.length)
            return None
          else if(l.length == 0)
            return Some( acc.foldRight(True:Formula)((x,y) => And(x,y)))
          else {
            ls = l
            domC = r.foldRight(domC)((x, y) => And(x, y))
          }
        }
        return None
      case or:Or =>
        (rankOneFml(ode,dom,or.left),rankOneFml(ode,dom,or.right)) match
        {
          case (Some(l),Some(r)) => Some(Or(l,r))
          case _ => None
        }
      case _ => ???
    }
  }

  private def recRankOneTac(f:Formula) : BelleExpr = {
    //TODO:Currently Darbouxs all the time, but could just use dI in simple case
    //Perhaps delegate to Darboux tactic to check for simpler case
    DebuggingTactics.print(f.prettyString) & (f match {
      case True => G(1) & close
      case And(l,r) => andL(-1) & DebuggingTactics.print("state") & dC(l)(1)<(
        hideL(-1) & boxAnd(1) & andR(1) <(
          DW(1) & G(1) & prop,
          recRankOneTac(r)),
        hideL(-2) & recRankOneTac(l)
      )
      case Or(l,r) => orL(-1)<(
        useAt(boxOrL,PosInExpr(1::Nil))(1) & recRankOneTac(l),
        useAt(boxOrR,PosInExpr(1::Nil))(1) & recRankOneTac(r)
      )
      case _ => (DifferentialTactics.dgDbxAuto(1) & done) | DifferentialTactics.dgBarrier()(1)
    })
  }

  /** Given a top-level succedent position corresponding to [x'=f(x)&Q]P
    * Tries to prove that P is a semialgebraic invariant, i.e. G|- [x'=f(x)&Q]P
    * P is assumed to be formed from conjunctions, disjunctions and inequalities
    * This does not go via (closed) real induction, and so also applies for strict inequalities
    * However, all of the sub formulas need to be "recursively" rank 1, i.e. they are provable either:
    * 1) with darboux inequalities p'>=qp (for p>=0 , p>0)
    * 2) with a barrier certificate
    *
    * This tactic reorders conjunctions internally to try and find an order that works
    */
  def sAIRankOne : DependentPositionTactic = "sAIR1" by ((pos:Position,seq:Sequent) => {
    require(pos.isTopLevel && pos.isSucc, "sAI only in top-level succedent")
    val (ode,dom,post) = seq.sub(pos) match {
      case Some(Box(sys:ODESystem,post)) => (sys.ode,sys.constraint,post)
      case _ => throw new BelleThrowable("sAI only at box ODE in succedent")
    }
    val (f2,propt)=SimplifierV3.simpWithDischarge(IndexedSeq[Formula](), post,
      DifferentialTactics.atomNormalize2,SimplifierV3.emptyTaxs)
    val f3 = rankOneFml(ode,dom,f2) match {
      case None => throw new BelleThrowable("Not recursive rank 1: "+f2)
      case Some(f) => f
    }

    val reorder = proveBy(Equiv(f2,f3),QE)
    assert(reorder.isProved)

    println("Rank 1: "+f3)

    //Rewrite postcondition to match real induction
    val (starter,imm) = propt match {
      case None => (skip,skip)
      case Some(pr) => (useAt(pr)(pos ++ PosInExpr(1::Nil)),useAt(pr,PosInExpr(1::Nil))(pos))
    }
    starter & useAt(reorder)(pos ++ PosInExpr(1::Nil)) & cutR(f3)(pos)<(
      useAt(reorder,PosInExpr(1::Nil))(pos) & QE,
      cohideR(1) & implyR(1) & recRankOneTac(f3)
    )
  })
}
