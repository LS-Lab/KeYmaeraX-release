package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.AnonymousLemmas._
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms._
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.btactics.DifferentialTactics._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.helpers.DifferentialHelper
import edu.cmu.cs.ls.keymaerax.btactics.helpers.DifferentialHelper._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import org.apache.logging.log4j.scala.Logger

import scala.collection.immutable
import scala.collection.immutable._
import scala.collection.mutable.ListBuffer

/**
  * Implements ODE tactics based on the differential equation axiomatization.
  *
  * Created by yongkiat on 05/14/18.
  * @see Andre Platzer and Yong Kiam Tan. [[https://doi.org/10.1145/3209108.3209147 Differential equation axiomatization: The impressive power of differential ghosts]]. In Anuj Dawar and Erich Grädel, editors, Proceedings of the 33rd Annual ACM/IEEE Symposium on Logic in Computer Science, LICS'18, ACM 2018.
  */

object ODEInvariance {

  private val namespace = "odeinvariance"
  private val logger = Logger(getClass) //@note instead of "with Logging" to avoid cyclic dependencies
  private val debugTactic = false

  //Lie derivative
  private def lieDer(ode: DifferentialProgram,p: Term) : Term = simplifiedLieDerivative(ode, p, ToolProvider.simplifierTool())
  //First k Lie derivatives in increasing order
  private def lieDers(ode: DifferentialProgram,p: Term,k: Int) : List[Term] =
    if(k==0) List(p)
    else p::lieDers(ode,simplifiedLieDerivative(ode, p, ToolProvider.simplifierTool()),k-1)

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

  /** Given a bound i, generate the local progress formula up to that bound
    * i.e. the i-th Lie derivative is strict:
    * p>=0 & (p=0 -> (p'>=0 & (p'=0 -> ...) & (p=0&... -> p'^i >0)
    * Computes up to the rank if bound = None
    * @param ode   : the ODEs under consideration
    * @param p     : the polynomial p to generate p*>0
    * @param bound : number of higher Lie derivatives to generate
    * @param geq   : generate for >= (or <= if false)
    * @return ( p*>0 )
    */
  def pStar(ode: ODESystem,p:Term, bound: Option[Int], geq: Boolean = true) : Formula = {
    val trueBound = bound match {
      //todo: memoize the Lie derivatives along the way
      //todo: note that this can actually indicate the number of Lie derivatives we need
      // e.g. if the final groeber basis is generated by (1), then we will always hit a strict bound
      case None => rank(ode,List(p))._2
      case Some(b) => b
    }
    val lies = lieDers(ode.ode,p,trueBound)
    //This generates the last one STRICT
    val firsts = lies.take(trueBound)
    val last = lies.last
    val opGt = if(geq) Greater else Less
    val opGe = if(geq) GreaterEqual else LessEqual

    //todo: return p*=0 as well, but not needed for now
    firsts.foldRight(opGt(last,Number(0)):Formula)((p,f) => And(opGe(p,Number(0)),Imply(Equal(p,Number(0)),f)))
  }

  /** Homomorphically extend pStar to max and min terms
    *
    * @param ode   : the ODEs under consideration
    * @param p     : the term p>=0 (including max/min terms)
    * @param bound : number of higher Lie derivatives to generate
    * @return p*>0
    */
  def pStarHom(ode: DifferentialProgram,p:Term, bound: Int) : Formula = {
    p match{
      case FuncOf(f,Pair(l,r)) =>
        if (f == maxF) Or(pStarHom(ode,l,bound),pStarHom(ode,r,bound))
        else if (f==minF) And(pStarHom(ode,l,bound),pStarHom(ode,r,bound))
        else ???
      case _ => pStar(ODESystem(ode,True),p,Some(bound))
    }
  }

  /**
    * Computes the local progress formula f*
    * f* is assumed to consist of atomic comparisons normalized to have 0 on RHS (<=0,>=0,<0,>0,=0,!=0), And, Or
    * Sub-formulas outside this grammar are ignored if strict = false
    * @param ode    : the ODEs under consideration
    * @param f      : the formula f to compute f* for
    * @param bound  : optionally bounds the number of higher Lie derivatives that are considered
    * @return
    */
  def localProgressFml(ode: ODESystem,f: Formula,bound: Option[Int] = None) : Formula = {
    f match {
      case cf:ComparisonFormula => {
        pStar(ode,cf.left,bound, cf.isInstanceOf[Greater] || cf.isInstanceOf[GreaterEqual])
      }
      case And(l,r) => And(localProgressFml(ode,l,bound),localProgressFml(ode,r,bound))
      case Or(l,r) => Or(localProgressFml(ode,l,bound),localProgressFml(ode,r,bound))
      //todo: handle Equal, NotEqual and decide what to do with the rest
      case _ => False
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
            cohideOnlyL('Llast) & SaturateTactic(Dassignb(1)) & implyRi &
            useAt(fastGeqCheck,PosInExpr(1::Nil))(1) & QE
          )
        )
      ))
  })

  // The following LP helper orchestration tactics assume that the relevant "progress" condition
  // is in antecedent (-1), and the target progress condition is in succedent (1)
  // Currently, a uniform bound is assumed on all the progress conditions
  private def lpgeq(bound:Int) : BelleExpr =
    if (bound <= 0)
      useAt(contAx,PosInExpr(1::Nil))(1) & closeId
    else //Could also make this fallback to the continuity step for early termination
      //DebuggingTactics.print("start") &
      andL(-1) & lpstep(1)< (
        hideL(-2) & useAt(geq)(-1) & closeId,
        hideL(-1) & implyL(-1) & <(closeId, hideL(-2) & lpgeq(bound-1))
      )

  //todo: private
  //"unlocks" a strict inequality q > 0 | t = 0 by turning it into q - t^2*bound >= 0
  //as above, assumes local progress for q is in antecedent (-1) and the progress in succedent (1)
  //additionally, the domain is assumed to be exactly g>0 | t=0
  //Unfortunately, this tactic has to prove the power bounds on the fly but hopefully remember() can store them
  def lpgt(bound:Int): DependentTactic = "lpgt" by ((seq: Sequent) => {
    val boundPr = remember(("f_()-g_()^"+(2*bound).toString()+">=0 -> f_()>0 | g_()=0").asFormula, QE, namespace)
    val (p,t) = seq.succ(0).sub(PosInExpr(0::1::Nil)) match {
      case Some(Or(Greater(p,_),Equal(t,_))) => (p,t)
      case e => throw new BelleThrowable("lpgt called with incorrect result at expected position: " + e)
    }
    println(p,t)
    val unlocked = GreaterEqual(Minus(p,Power(t,Number(2*bound))),Number(0))
    dR(unlocked)(1)<(
      lpgeq(bound),
      diffWeakenG(1) & byUS(boundPr))
  })

  //Homomorphically extend lpgeq to max and min terms
  private def lpclosed(bound:Int, progressTerm:Term) : BelleExpr =
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
  //Prove atomic polynomial (in)equality with this cofactor
  case class Darboux(is_eq:Boolean, cofactor : Term, pr :ProvableSig) extends Instruction //TODO: maybe keep around provables for re-use
  //Prove atomic polynomial >= with this bound
  case class Strict(bound : Int) extends Instruction
  //Prove using closeF
  case class Triv() extends Instruction

  // A more exhaustive implementation
  private def pStarHomPlus(ode: DifferentialProgram, dom:Formula, p:Term, bound: Int) : (Formula,Instruction) = {
    p match {
      case FuncOf(f, Pair(l, r)) =>
        if (f == maxF) {
          val (lfml, linst) = pStarHomPlus(ode, dom, l, bound)
          val (rfml, rinst) = pStarHomPlus(ode, dom, r, bound)
          (Or(lfml, rfml), Disj(linst, rinst))
        }
        else if (f == minF) {
          val (lfml, linst) = pStarHomPlus(ode, dom, l, bound)
          val (rfml, rinst) = pStarHomPlus(ode, dom, r, bound)
          (And(lfml, rfml), Conj(linst, rinst))
        }
        else ???
      case Neg(FuncOf(a, p)) =>
        if (a == absF) {
          try {
            val prop = Equal(p, Number(0))
            val (pr, cofactor, rem) = findDbx(ode, dom, prop)
            (prop, Darboux(true, cofactor, pr))
          }
          catch {
            case e: BelleThrowable => (False, Triv())
          }
        }
        else ???
      case _ => {
        try {
          val prop = GreaterEqual(p, Number(0))
          val (pr, cofactor, rem) = findDbx(ode, dom, prop)
          (prop, Darboux(false, cofactor, pr))
        }
        catch {
          case e: BelleThrowable => (pStar(ODESystem(ode,True), p, Some(bound)), Strict(bound))
        }
      }
    }
  }

  //Assume the Q progress condition is at -1
  private def lpclosedPlus(inst:Instruction) : BelleExpr =
    SeqTactic(DebuggingTactics.debug(inst.toString(),doPrint = debugTactic),
      inst match{
      case Darboux(iseq,cofactor,pr) =>
        (if(iseq) useAt(refAbs)(1) else skip) &
        DebuggingTactics.debug("Darboux "+cofactor+" ",doPrint = debugTactic) &
        implyRi & useAt("DR<> differential refine",PosInExpr(1::Nil))(1) &
        dgDbx(cofactor)(1)
      case Disj(l,r) =>
        DebuggingTactics.debug("DISJ",doPrint = debugTactic) &
        orL(-2) <(
          useAt(refMaxL,PosInExpr(1::Nil))(1) & lpclosedPlus(l),
          useAt(refMaxR,PosInExpr(1::Nil))(1) & lpclosedPlus(r))
      case Conj(l,r) =>
        DebuggingTactics.debug("CONJ",doPrint = debugTactic) &
        andL(-2) & useAt(uniqMin,PosInExpr(0::Nil))(1) & andR(1) <(
          hideL(-3) & lpclosedPlus(l),
          hideL(-2) & lpclosedPlus(r)
        )
      case Strict(bound) =>
        DebuggingTactics.debug("Strict"+bound,doPrint = debugTactic) &
        hideL(-1) &
        lpgeq(bound)
      case Triv() =>
        DebuggingTactics.debug("Triv",doPrint = debugTactic) &
        closeF})

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
    * @return closes the subgoal if P is indeed invariant, fails if P fails to normalize to f>=0 form, or if
    *         one of tactic limitations is met
    * @see Andre Platzer and Yong Kiam Tan. [[https://doi.org/10.1145/3209108.3209147 Differential equation axiomatization: The impressive power of differential ghosts]]. In Anuj Dawar and Erich Grädel, editors, Proceedings of the 33rd Annual ACM/IEEE Symposium on Logic in Computer Science, LICS'18, ACM 2018.
    */
  def sAIclosedPlus(bound:Int=1) : DependentPositionTactic = "sAIc" byWithInput (bound,(pos:Position,seq:Sequent) => {
    require(pos.isTopLevel && pos.isSucc, "sAI only applicable in top-level succedent")
    require(ToolProvider.algebraTool().isDefined,"ODE invariance tactic needs an algebra tool (and Mathematica)")

    val (ode,dom,post) = seq.sub(pos) match {
      case Some(Box(sys:ODESystem,post)) => (sys.ode,sys.constraint,post)
      case _ => throw new BelleThrowable("sAI only applicable to box ODE in succedent")
    }

    val (fml,propt) = maxMinGeqNormalize(post)

    require(fml.isInstanceOf[GreaterEqual], "Normalization failed to reach normal form "+fml)
    val f2 = fml.asInstanceOf[GreaterEqual]

    //println("Rank reordering:",rankReorder(ODESystem(ode,dom),post))

    val (pf,inst) = pStarHomPlus(ode,dom,f2.left,bound)

    //println("HOMPLUS:"+pf+" "+inst)

    //Performs rewriting to and from the normal form
    //Isn't there a faster way to do this rewrite??
    val (starter,r1,r2,r3) = propt match {
      case None => (skip,skip,skip,skip)
      case Some(pr) => (
        useAt(pr)(pos ++ PosInExpr(1::Nil)),
        useAt(pr,PosInExpr(1::Nil))('Rlast),
        useAt(pr,PosInExpr(1::Nil))(-1,PosInExpr(1::Nil)),
        useAt(pr,PosInExpr(1::Nil))('Llast)
      )
    }

    DebuggingTactics.debug("PRE",doPrint = debugTactic) &
      starter & useAt("RI& closed real induction >=")(pos) & andR(pos)<(
      implyR(pos) & r1 & ?(closeId) & timeoutQE & done, //common case?
      cohideR(pos) & composeb(1) & dW(1) & implyR(1) & assignb(1) &
      implyR(1) & cutR(pf)(1)<(hideL(-3) & r2 & DebuggingTactics.debug("QE step",doPrint = debugTactic) & timeoutQE & done, skip) //Don't bother running the rest if QE fails
      & cohide2(-3,1)& DebuggingTactics.debug("Finish step",doPrint = debugTactic) & implyR(1) & lpclosedPlus(inst)
    )
  })

  // Determines if a formula is of the special "recursive" rank one case
  // i.e. every p~0 is (trivially) Darboux
  // returns a list of formulas internally re-arranged according to diff cut order
  def rankOneFml(ode: DifferentialProgram, dom:Formula, f:Formula) : Option[Formula] = {

    f match {
      case cf:ComparisonFormula =>
        //findDbx
        val (pr, cofactor, rem) = findDbx(ode, dom, cf,false)
        if (pr.isProved)// TODO: this should be keeping track of co-factors rather than throwing them away
          Some(f)
        else {
          if(cf.isInstanceOf[Equal] || cf.isInstanceOf[NotEqual]) return None
          //TODO: need to check cofactor well-defined as well?
          val pr2 = proveBy(Imply(And(dom, Equal(cf.left, Number(0))), Greater(rem, Number(0))), timeoutQE)
          logger.debug(pr2)
          if(pr2.isProved)
            Some(f)
          else None
        }

      case and:And =>
        var ls = flattenConjunctions(and)
        var acc = ListBuffer[Formula]()
        var domC = dom
        while(true){
          logger.debug("Domain: " + domC)
          //Pull out the ones that are rank 1
          val checkls = ls.map(f =>
            rankOneFml(ode,domC,f) match { case None => Left(f) case Some(res) => Right(res)})
          val l = checkls.collect{case Left(v) => v}
          val r : List[Formula] = checkls.collect{case Right(v) => v}
          acc ++= r
          logger.debug("Acc: " + acc)
          if(l.length == checkls.length)
            return None
          else if(l.length == 0)
            return Some(acc.foldRight(True:Formula)((x,y) => And(x,y)))
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
    DebuggingTactics.debug(f.prettyString,doPrint = debugTactic) & (f match {
      case True => G(1) & close
      case And(l,r) => andL(-1) &
        DebuggingTactics.debug("state",doPrint = debugTactic) & dC(l)(1)<(
        hideL(-1) & boxAnd(1) & andR(1) <(
          DW(1) & G(1) & prop,
          recRankOneTac(r)),
        hideL(-2) & recRankOneTac(l)
      )
      case Or(l,r) => orL(-1)<(
        useAt(boxOrL,PosInExpr(1::Nil))(1) & recRankOneTac(l),
        useAt(boxOrR,PosInExpr(1::Nil))(1) & recRankOneTac(r)
      )
      case _ => (dgDbxAuto(1) | dgBarrier()(1)) & done
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
    *
    * @param doReorder whether to reorder conjunctions
    * @param skipClosed whether to skip over closed invariants
    *                   (this should be used if the outer tactic already tried sAIclosedPlus, which is much faster
    *                   than this one anyway)
    *                   The option only applies if doReorder = true
    * @see Andre Platzer and Yong Kiam Tan. [[https://doi.org/10.1145/3209108.3209147 Differential equation axiomatization: The impressive power of differential ghosts]]. In Anuj Dawar and Erich Grädel, editors, Proceedings of the 33rd Annual ACM/IEEE Symposium on Logic in Computer Science, LICS'18, ACM 2018.
    */
  def sAIRankOne(doReorder:Boolean=true,skipClosed:Boolean =true) : DependentPositionTactic = "sAIR1" byWithInput (doReorder,(pos:Position,seq:Sequent) => {
    require(pos.isTopLevel && pos.isSucc, "sAI only in top-level succedent")
    require(ToolProvider.algebraTool().isDefined,"ODE invariance tactic needs an algebra tool (and Mathematica)")

    val (ode, dom, post) = seq.sub(pos) match {
      case Some(Box(sys: ODESystem, post)) => (sys.ode, sys.constraint, post)
      case _ => throw new BelleThrowable("sAI only at box ODE in succedent")
    }
    val (f2, propt) = semiAlgNormalize(post)

    val (starter, imm) = propt match {
      case None => (skip, skip)
      case Some(pr) => (useAt(pr)(pos ++ PosInExpr(1 :: Nil)), useAt(pr, PosInExpr(1 :: Nil))(pos))
    }

    if (!doReorder) {
      if (skipClosed & flattenConjunctions(f2).forall {
        case Equal(_, _) => true
        case GreaterEqual(_, _) => true
        case _ => false
      }) {
        fail
      }
      else {
        starter & cutR(f2)(pos) < (timeoutQE,
          cohideR(pos) & implyR(1) & recRankOneTac(f2)
        )
      }
    }
    else {
      val f3 =
        rankOneFml(ode, dom, f2) match {
          case None => throw new BelleThrowable("Unable to re-order to recursive rank 1 form: " + f2)
          case Some(f) => f
        }

      val reorder = proveBy(Equiv(f2, f3), timeoutQE)
      assert(reorder.isProved)

      logger.debug("Rank 1: " + f3)
      starter & useAt(reorder)(pos ++ PosInExpr(1 :: Nil)) & cutR(f3)(pos) < (
        useAt(reorder, PosInExpr(1 :: Nil))(pos) & timeoutQE,
        cohideR(pos) & implyR(1) & recRankOneTac(f3)
      )
    }
  })

  /**
    * Vectorial Darboux, currently just constructs and returns an appropriate provable
    * because we do not yet have vectorial dG
    *
    * @param odesys the ODE system
    * @param Gco the cofactor matrix
    * @param p the polynomial vector
    * @return provable with extra ghosts
    */
  def dgVdbx(odesys : ODESystem,Gco:List[List[Term]],p:List[Term]) : ProvableSig = {
    val dim = p.length
    assert(Gco.length == dim && Gco.forall(gs => gs.length == dim))
    val diffeqs = odesys.ode
    val dom = odesys.constraint

    val ghostPrefix = "vdbxy_"
    //Doubly indexed ghost variables
    val ghostVars = List.range(0,dim).map( i => List.range(0,dim).map( j => Variable(ghostPrefix,Some(i*dim+j))))
    //println("Ghost vars: "+ghostVars)

    val Gcotrans = Gco.transpose

    //Construct the system of equations
    val ghostRHS = List.range(0,dim).map( i => matvec_prod(Gcotrans,ghostVars(i)).map(t => Neg(t)))
    val ghostEqs = (ghostVars zip ghostRHS).map(p => p._1 zip p._2)
    //Each ghostEqs at this point is a separate vectorial diff ghost
    //We could also work directly with the flattened versions, but this is just for easier portability when we get vDG
    //println("Ghost eqs: "+ghostEqs)

    //For now, construct the differential equations obtained from ghosts
    val ghostDiffEqs = ghostEqs.flatten.map(p => AtomicODE(DifferentialSymbol(p._1),p._2)).reduce(DifferentialProduct.apply)
    val ghostSys = ODESystem(DifferentialProduct(diffeqs,ghostDiffEqs),dom)
    //println("Extended system: "+ghostSys)

    val zero = Number(0)
    val one = Number(1)
    //Constructing the p=0 invariant (using conjunctions)
    val inv = p.foldLeft[Formula](True)((fml,trm)=> And(Equal(trm,zero),fml))
    val boxfml = Box(ghostSys,inv)
    val fml = ghostVars.foldRight[Formula](boxfml)((vs,fml)=> (vs.foldRight[Formula](fml)((v,fml)=>Exists(v::Nil,fml))))
    //println("Formula: "+fml)

    //Finally, we can now prove the invariant property
    val seq = ProvableSig.startProof( Imply(inv,fml) )
    //println("Seq: "+seq)

    val determinant = sym_det(ghostVars)
    val trace = sym_trace(Gco)
    //println("Symbolic Det: "+determinant)
    //println("Symbolic Trace: "+trace)

    //Relevant tactics

    //Explicitly instantiate the sequence of ghost variables with the identity matrix
    val idExistsTac = List.range(0,dim).map( i => List.range(0,dim).map( j => existsR(Variable(ghostPrefix,Some(i*dim+j)),
      if(i==j) one else zero)))
    val idExistsTacPos = idExistsTac.foldRight(skip)( (exts,tac) => exts.foldRight(tac)( (ext,tac) => ext(1) & tac )  )

    //Cut in the symbolic dot products p.y = 0
    val dotprods = ghostVars.map( ls => Equal(dot_prod(ls,p),zero))
    val dITac = DifferentialTactics.diffInvariant(dotprods:_*)(1)

    val pr = proveBy(seq,
      implyR(1) & idExistsTacPos & dITac &
        diffCut(Greater(determinant,zero))(1) <(
          dW(1) & QE,
          //Prove Darboux invariance for the determinant
          dgDbx(Neg(trace))(1))
    )

    pr
  }

  /**
    * Event stuck tactics: roughly, [x'=f(x)&Q]P might be true in a state if:
    * 1) Q is false in the state (trivializing the box modality)
    * 2) Q,P are true in initial state, but the ODE cannot evolve for non-zero duration without leaving Q
    * 3) the "actual" interesting case, where P is true along all solutions (staying in Q)
    *
    * 1) is handled by diffUnpackEvolutionDomainInitially, this suite handles case 2)
    */

  /** Given a top-level succedent of the form [{t'=c,x'=f(x)& Q & t=d}]P
    * proves P invariant because the domain constraint prevents progress
    * This tactic is relatively flexible:
    * t'=c can be any time-like ODE (except c cannot be 0)
    * t=d requires d to be a constant number, which forces the whole ODE to be frozen
    * (of course, P should be true initially)
    */
  def timeBound : DependentPositionTactic = "timeBound" by ((pos:Position,seq:Sequent) => {
    require(pos.isTopLevel && pos.isSucc, "time bound only in top-level succedent")
    val (ode, dom, post) = seq.sub(pos) match {
      case Some(Box(sys: ODESystem, post)) => (sys.ode, sys.constraint, post)
      case _ => throw new BelleThrowable("time bound only at box ODE in succedent")
    }
    //Check that the domain at least freezes one of the coordinates
    val domConj = flattenConjunctions(dom)
    val atoms = atomicListify(ode)

    //Only need to freeze coordinates free in postcondition
    val fvs = StaticSemantics.freeVars(post)
    val freeAtoms = atoms.filter( p => fvs.contains(p.xp.x))

    val timeLike = atoms.flatMap(_ match {
      case AtomicODE(v ,n:Number) if n.value!=0 => Some(v.x)
      case _=> None
    })
    val constRHS = domConj.filter(_ match {
      //todo: this can be generalized
      case Equal(l,_:Number) if timeLike.contains(l) => true
      case _ => false})

    constRHS match {
      case Nil => throw new BelleThrowable("time bound requires at least one time-like coordinate to be frozen in domain, found none")
      case Equal(t,d)::_ =>
        //Construct the bounding polynomials sum_i (x_i-old(x_i))^2 <= (sum_i 2x_ix'_i)*t
        val left = freeAtoms.map(f =>
          Power(Minus(f.xp.x, FuncOf(Function("old", None, Real, Real, false), f.xp.x)),Number(2)):Term).reduce(Plus)
        val right = Times(freeAtoms.map(f => Times(Number(2),
          Times(Minus(f.xp.x, FuncOf(Function("old", None, Real, Real, false), f.xp.x)), f.e)):Term).reduce(Plus),Minus(t,d))
        dC(LessEqual(left,right))(pos)<(
          dW(pos) & QE & done,
          dI('full)(pos)
        )
    }
  })

  //@todo: copied from Expression.scala but slightly modified to always return atomic ODEs directly
  private def atomicListify(ode: DifferentialProgram): immutable.List[AtomicODE] =
  ode match {
    case p: DifferentialProduct => atomicListify(p.left) ++ atomicListify(p.right)
    case a: AtomicODE => a :: Nil
    case _ => throw new IllegalArgumentException("Unable to listify:"+ode)
  }

  /**
    * Given either a stuck diamond modality in the antecedent
    * G, P, <x'=f(x)&Q>~P |-
    * or dually a stuck box in the succedent:
    * G, P |- [x'=f(x)&Q]P
    *
    * reduces the goal to local progress into ~Q
    * G |- <t'=1,x'=f(x)& ~Q | t=0> t!=0
    *
    * todo: compose with local progress to further reduce to G |- ~Q*
    * todo: do not re-introduce t'=1 if it is already there
    */

  // main stuck argument
  private lazy val stuckRefine =
    remember("<{c&!q(||) | r(||)}>!r(||) -> ([{c&r(||)}]p(||) -> [{c&q(||)}]p(||))".asFormula,
      implyR(1) & implyR(1) &
        useAt("[] box",PosInExpr(1::Nil))(-2) & notL(-2) &
        useAt("[] box",PosInExpr(1::Nil))(1) & notR(1) &
        andLi & useAt("Uniq uniqueness")(-1) & DWd(-1) &
        cutL("<{c&(!q(||)|r(||))&q(||)}>!p(||)".asFormula)(-1) <(
          implyRi & useAt("DR<> differential refine",PosInExpr(1::Nil))(1) & DW(1) & G(1) & prop,
          cohideR(2) & implyR(1) & mond & prop), namespace)

  def domainStuck : DependentPositionTactic = "domainStuck" by ((pos:Position,seq:Sequent) => {
    require(pos.isTopLevel, "domain stuck only at top-level")
    val (ode, dom, post) = seq.sub(pos) match {
      //needs to be dualized
      case Some(Box(sys: ODESystem, post)) if pos.isSucc => (sys.ode, sys.constraint, post)
      //todo: case Some(Diamond(sys:ODESystem,post)) if pos.isAnte => (sys.ode, sys.constraint, post)
      case _ => throw new BelleThrowable("domain stuck for box ODE in succedent or diamond ODE in antecedent")
    }

    val tvName = "stuck_"
    val timeOde = (tvName+"'=1").asDifferentialProgram
    val stuckDom = (tvName+"=0").asFormula
    val odedim = getODEDim(seq,pos)

    val (negDom, propt) = semiAlgNormalize(Not(dom))
    //The negated domain is definitely normalizable if not something went wrong
    assert(propt.isDefined)

    // set up the time variable
    // commute it to the front to better match with realind/cont
    DifferentialTactics.dG(timeOde,None)(pos) & existsR(Number(0))(pos) & (useAt(", commute")(pos)) * odedim &
    cutR(Box(ODESystem(DifferentialProduct(timeOde,ode),stuckDom),post))(pos)<(
      timeBound(pos), //closes assuming P(init)
      useAt(stuckRefine,PosInExpr(1::Nil))(pos) &
      //Clean up the goal a little bit
      chase(pos.checkTop.getPos,PosInExpr(1::Nil)) & useAt(propt.get)(pos.checkTop.getPos,PosInExpr(0::1::0::Nil))
    )
  })

    /**
    * Explicitly calculate the conjunctive rank of a list of polynomials
    * (uses conjunctive optimization from SAS'14)
    * @param ode the ODESystem to use
    * @param polys the polynomials to compute rank for
    * @return the Groebner basis of the polynomials closed under Lie derivation + the rank (at which this occurs)
    */
  def rank(ode:ODESystem, polys:List[Term]) : (List[Term],Int) = {
    if (ToolProvider.algebraTool().isEmpty)
      throw new BelleThrowable(s"rank computation requires a AlgebraTool, but got None")

    val algTool = ToolProvider.algebraTool().get

    var gb = algTool.groebnerBasis(polys ++ domainEqualities(ode.constraint))
    var rank = 1
    //remainder after each round of polynomial reduction
    var remaining = polys

    while(true) {
      val lies = remaining.map(p => DifferentialHelper.simplifiedLieDerivative(ode.ode, p, ToolProvider.simplifierTool()))
      val quos = lies.map(p => algTool.polynomialReduce(p, gb))
      remaining = quos.map(_._2).filterNot(_ == Number(0))
      if(remaining.isEmpty) {
        //println(gb,rank)
        return (gb,rank)
      }
      gb = algTool.groebnerBasis(remaining ++ gb)
      rank+=1
    }
    (List(),0)
  }

  /** Experimenting with tricks for reordering the cofactor matrix
    * If we think of Gco as an adjacency matrix where:
    * Gco_{i,j} is non-zero iff there is an edge j -> i, ignoring self edges
    * Then "all" we need to do is topologically sort Gco
    * */
  private def rankReorder(ode:ODESystem, f:Formula) : Boolean = {
    val fml = semiAlgNormalize(f)
    rankReorderAux(ode,f)
  }

  private def rankReorderAux(ode:ODESystem, f:Formula) : Boolean = {
    val (atoms,rest) = flattenConjunctions(f).partition(
      _ match {
        case LessEqual(l,r) => true
        case GreaterEqual(l,r) => true
        case Equal(l,r) => true
        case _ => false
      }
    )
    val dorest = rest.forall ( _ match {
      case Or(l,r) => rankReorderAux(ode,l) && rankReorderAux(ode,r)
      case _ => false
    })
    val polys = atoms.map(f => f.asInstanceOf[ComparisonFormula].left)
    val (cof,gb,r) = rankCofactors(ode,polys)
    val reorder = reorderCofactors(cof)
    dorest && reorder.isDefined
  }

  private def reorderCofactors(Gco:List[List[Term]]) : Option[List[Int]] = {
    var adjacencies = Gco.zipWithIndex.map(pr =>
      (pr._2,pr._1.zipWithIndex.filterNot( p => p._1 == Number(0) || pr._2 == p._2).map(_._2))
    )
    var order = ListBuffer[Int]()
    while(adjacencies.nonEmpty) {
      //println("ADJ",adjacencies)
      val (l,r) = adjacencies.partition(pls => pls._2.isEmpty)
      val ls = l.map(_._1)
      if(l.isEmpty)
        return None
      order ++= ls
      adjacencies = r.map( pls => (pls._1,pls._2.filterNot(i => ls.contains(i))))
    }
    Some(order.toList)
  }

  //Cofactors at rank
  private def rankCofactors(ode:ODESystem, polys:List[Term]): (List[List[Term]],List[Term],Int) = {
    if (ToolProvider.algebraTool().isEmpty)
      throw new BelleThrowable(s"rank computation requires a AlgebraTool, but got None")

    val algTool = ToolProvider.algebraTool().get
    val (gb,r) = rank(ode,polys)
    val lies = gb.map(p => DifferentialHelper.simplifiedLieDerivative(ode.ode, p, ToolProvider.simplifierTool()))
    val quos = lies.map(p => algTool.polynomialReduce(p, gb))
    (quos.map(_._1),gb,r)
  }

  //Explicit symbolic expression for the determinant of a matrix
  //Currently just explicitly calculated, but can use Mathematica's det if available
  //Also, this probably doesn't actually need to be explicitly calculated everytime since we always apply it on ghost variables
  private def sym_det (m:List[List[Term]]) : Term = {
    val dim = m.length
    assert(m.forall(ls => ls.length == dim))
    if(dim==1) m(0)(0)
    else if(dim==2) //det ((a b)(c d)) = a d - b c
      Minus(Times(m(0)(0),m(1)(1)),Times(m(0)(1),m(1)(0)))
    else if(dim==3) //det ((a b c)(d e f)(g h i)) = -c e g + b f g + c d h - a f h - b d i + a e i
      ???
    else
      ???
  }

  //Symbolic trace
  private def sym_trace (m:List[List[Term]]) : Term = {
    val dim = m.length
    assert(m.forall(ls => ls.length == dim))
    List.range(0,dim).map(i=>m(i)(i)).foldLeft[Term](Number(0))(Plus.apply)
  }

  // Symbolic matrix and vector products, assuming that the dimensions all match up
  private def dot_prod (v1:List[Term],v2:List[Term]) : Term = {
    val zipped = (v1 zip v2).map({case (t1,t2)=>Times(t1,t2)})
    zipped.reduce(Plus.apply)
  }

  private def matvec_prod (m:List[List[Term]],v:List[Term]) : List[Term] ={
    m.map(ls => dot_prod(ls,v))
  }

}
