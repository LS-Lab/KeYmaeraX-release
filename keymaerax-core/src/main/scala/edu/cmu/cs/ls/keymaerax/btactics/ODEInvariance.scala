package edu.cmu.cs.ls.keymaerax.btactics


import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.AnonymousLemmas._
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms._
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.btactics.DifferentialTactics._
import edu.cmu.cs.ls.keymaerax.btactics.ODELiveness.vDG
import edu.cmu.cs.ls.keymaerax.btactics.SimplifierV3._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.helpers.DifferentialHelper._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.{DependencyAnalysis, PosInExpr, Position, RenUSubst, UnificationMatch}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.{ElidingProvable, ProvableSig}

import scala.collection.immutable
import scala.collection.immutable._
import scala.collection.mutable.ListBuffer
import edu.cmu.cs.ls.keymaerax.lemma._
import edu.cmu.cs.ls.keymaerax.btactics.macros.Tactic
import edu.cmu.cs.ls.keymaerax.tools.qe.BigDecimalQETool
import edu.cmu.cs.ls.keymaerax.tools.{SMTQeException, ToolEvidence}
import edu.cmu.cs.ls.keymaerax.parser.InterpretedSymbols._
import org.slf4j.LoggerFactory

/**
  * Implements ODE tactics based on the differential equation axiomatization.
  *
  * Created by yongkiat on 05/14/18.
  * @see Andre Platzer and Yong Kiam Tan. [[https://doi.org/10.1145/3209108.3209147 Differential equation axiomatization: The impressive power of differential ghosts]]. In Anuj Dawar and Erich Grädel, editors, Proceedings of the 33rd Annual ACM/IEEE Symposium on Logic in Computer Science, LICS'18, ACM 2018.
  */

object ODEInvariance {

  private val namespace = "odeinvariance"
  private val logger = LoggerFactory.getLogger(getClass) //@note instead of "with Logging" to avoid cyclic dependencies
  private val debugTactic = false

  //Lie derivative
  private def lieDer(ode: DifferentialProgram,p: Term) : Term = simplifiedLieDerivative(ode, p, ToolProvider.simplifierTool())

  //First k Lie derivatives in increasing order
  private def lieDers(ode: DifferentialProgram,p: Term,k: Int) : List[Term] =
    if(k==0) List(p)
    else p::lieDers(ode,simplifiedLieDerivative(ode, p, ToolProvider.simplifierTool()),k-1)

  /* Stash of derived axioms */
  // Rewrite >=
  private[btactics] lazy val geq = remember("f_()>=0 <-> f_()>0 | f_()=0".asFormula, QE, namespace)
  // Cont with the domain constraint already refined to >= instead of >
  // todo: uses c{|s_|} instead of c to work around USubstOne conservativity
  // around substituted differential program constants
  private[btactics] lazy val contAx =
    remember("f(||) > 0 -> <{t_'=1,c&f(||)>=0}>t_!=g()".asFormula,
      implyR(1) &
      dR("f(||)>0".asFormula)(1) <(
        cutL("1!=0 & f(||)>0".asFormula)(-1) <( implyRi & byUS(Ax.Cont), hideR(1) & implyR(1) & andR(1) <(hideL(-1) & QE,id) ),
        DW(1) & G(1) & useAt(Ax.flipGreater)(1,0::Nil) &
          useAt(Ax.flipGreaterEqual)(1,1::Nil) & useAt(Ax.lessEqual)(1,1::Nil) & prop
      ), namespace)

  private[btactics] lazy val contAxR =
    remember("f(||) > 0 -> <{t_'=-(1),c&f(||)>=0}>t_!=g()".asFormula,
      implyR(1) &
        dR("f(||)>0".asFormula)(1) <(
          cutL("-(1)!=0 & f(||)>0".asFormula)(-1) <( implyRi & byUS(Ax.Cont), hideR(1) & implyR(1) & andR(1) <(hideL(-1) & QE,id) ),
          DW(1) & G(1) & useAt(Ax.flipGreater)(1,0::Nil) &
            useAt(Ax.flipGreaterEqual)(1,1::Nil) & useAt(Ax.lessEqual)(1,1::Nil) & prop
        ), namespace)

  // unconditional cont with true in the domain constraint
  private lazy val contAxTrue =
    remember("<{t_'=1,c&1 > 0}>t_!=g()".asFormula,
          cutR("1!=0 & 1 > 0".asFormula)(1) <( QE,  byUS(Ax.Cont)), namespace)

  //Extra conversion rewrites for and/or
  //Refine left/right disjunct
  private lazy val refOrL =
    remember("<{c& p(||)}>r(||) -> <{c& p(||) | q(||)}>r(||)".asFormula,
      useAt(Ax.DRd,PosInExpr(1::Nil))(1) & DW(1) & G(1) & prop,
      namespace)

  private lazy val refOrR =
    remember("<{c& q(||)}>r(||) -> <{c& p(||) | q(||)}>r(||)".asFormula,
      useAt(Ax.DRd,PosInExpr(1::Nil))(1) & DW(1) & G(1) & prop,
      namespace)

  // The specific | distribution needed for LP
  private lazy val distOr =
    remember("<{c& (p(||) | s(||)) | (q(||) | s(||)) }>r(||) -> <{c& (p(||) | q(||)) | s(||)}>r(||)".asFormula,
      useAt(Ax.DRd,PosInExpr(1::Nil))(1) & DW(1) & G(1) & prop,
      namespace)

  // The specific & distribution needed for LP
  private lazy val distAnd =
    remember("<{c& (p(||) | s(||)) & (q(||) | s(||)) }>r(||) -> <{c& (p(||) & q(||)) | s(||)}>r(||)".asFormula,
      useAt(Ax.DRd,PosInExpr(1::Nil))(1) & DW(1) & G(1) & prop,
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

  private lazy val fastSOS = proveBy("g() >= 0 & (P() <-> g() <= 0) -> (P()&f()=0 <-> g()+f()*f()<=0)".asFormula,
    prop & OnAll(QE)
  )

  /** Given a polynomial p, and an ODE system, generates the formula
    * p*>0
    * along with additional information for
    * p*=0 (as provided by rank(ode,p)) -- this avoids recomputation of the cofactors
    * The rank r is reduced according to equalities already present in the domain constraint
    * In other words, the generated p* satisfies:
    * <x'=f(x)&Q>O & p*>=0 -> <x'=f(x)& p>=0 >O
    *
    * @param ode   : the ODE system
    * @param p     : the polynomial p
    * @return      : (p*>0, p*=0, rank)
    */
  def pStarGeq(ode: ODESystem,p:Term) : (Formula,(Int, List[Term], List[List[Term]])) = {
    val (r,g,cofactors) = rank(ode,List(p))
    val lies = lieDers(ode.ode,p,r-1)
    val firsts = lies.take(r-1)
    val last = lies.last
    (firsts.foldRight(Greater(last,Number(0)):Formula)((p,f) => And(GreaterEqual(p,Number(0)),Imply(Equal(p,Number(0)),f))),(r,g,cofactors))
  }

  //An ADT encoding "instructions" for the ODE tactic
  sealed trait Inst
  //Disjunctive step
  case class DisjFml(left: Inst, right:Inst) extends Inst
  //Conjunctive step
  case class ConjFml(left: Inst, right:Inst) extends Inst
  // Strict step:
  case class GtFml(rank : Int) extends Inst
  // Geq/Eq both keep cached information
  // In addition, if the groebner basis is List(1), then it is just discarded
  case class GeqFml(rank : Int, groebner: List[Term], cofactors: List[List[Term]]) extends Inst
  case class EqFml(rank : Int, groebner: List[Term], cofactors: List[List[Term]]) extends Inst
  
  /** Given a formula f in normal form (conjunction/disjunction of >=0, >0 or =0), generates the formula f*
    * This is accompanied by an extra data structure that caches additional information at each step
    *
    * @param ode   : the ODE system
    * @param f     : the formula in semialgebraic normal form
    * @return      : (f*, i)
    */
  def fStar(ode: ODESystem,f:Formula) : (Formula,Inst) = {
    f match {
      case Or(l, r) =>
        val (fl, il) = fStar(ode, l)
        val (fr, ir) = fStar(ode, r)
        (Or(fl, fr), DisjFml(il, ir))
      case And(l, r) =>
        val (fl, il) = fStar(ode, l)
        val (fr, ir) = fStar(ode, r)
        (And(fl, fr), ConjFml(il, ir))
      case Greater(l, r: Number) if r.value == 0 => {
        val (f, (r, gs, cofs)) = pStarGeq(ode, l)
        (f, GtFml(r))
      }
      case GreaterEqual(l, r: Number) if r.value == 0 => {
        val (f, (r, gs, cofs)) = pStarGeq(ode, l)
        //Special case where the ideal is empty (which seems to occur fairly often)
        if(gs == List(Number(1)))
          (f,GeqFml(r,List(),List()))
        else {
          val gf = gs.map(t => Equal(t, Number(0))).reduce(And)
          (Or(f, gf), GeqFml(r, gs, cofs))
        }
      }
      case Equal(l, r: Number) if r.value == 0 => {
        val (_, (r, gs, cofs)) = pStarGeq(ode, l)
        //Special case where the ideal is empty (which seems to occur fairly often)
        if(gs == List(Number(1)))
          (False,EqFml(r,List(),List()))
        else {
          val gf = gs.map(t => Equal(t, Number(0))).reduce(And)
          (gf, EqFml(r, gs, cofs))
        }
      }
      case _ => throw new IllegalArgumentException("Formula not in normal form: "+f)
    }
  }

  /* G |- p>=0   G|- <x'=f(x)&p'>=0>o,D
   * -----
   * G |- <x'=f(x)&p>=0>o,D
   *
   * As a standalone tactic, this directly cuts p=0 | p>0 and leaves it open
   *
   * @note uses Dconstify internally instead of an external wrapper because it leaves open goals afterwards
   */
  def lpstep: DependentPositionTactic = anon ((pos:Position,seq:Sequent) => {
    if(!(pos.isTopLevel && pos.isSucc))
      throw new IllFormedTacticApplicationException("lpstep: position " + pos + " must point to a top-level succedent position")

    val (p: Term, ode: DifferentialProgram) = seq.sub(pos) match {
      case Some(Diamond(ODESystem(o, GreaterEqual(p,_)), _)) => (p, o)
      case Some(e) => throw new TacticInapplicableFailure("lpstep only applicable to diamond ODEs, but got " + e.prettyString)
      case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + seq.prettyString)
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
          useAt(contAx,PosInExpr(1::Nil))(pos) & id |
            useAt(contAxR,PosInExpr(1::Nil))(1) & id,
          //Integral case
          //DebuggingTactics.print("DI STEP") &
          dR(GreaterEqual(lie,Number(0)),false)(pos) <(
            //left open for outer tactic
            skip,
            cohideOnlyL('Llast) &
              //This is a special case where we don't want full DI, because we already have everything
              cohideOnlyR(pos) &
              Dconstify(
                diffInd('diffInd)(1) <(
                  useAt(geq)(1) & orR(1) & id,
                  cohideOnlyL('Llast) & SaturateTactic(Dassignb(1)) & implyRi &
                  useAt(fastGeqCheck,PosInExpr(1::Nil))(1) & timeoutQE
              ))(1)
          )
        ))
  })

  // Helper tactic proving p*>0 -> <t'=1, x'=f(x)& p>=0> t!=0
  private def lpgeq(bound:Int) : BelleExpr =
    if (bound <= 0)
        useAt(contAx,PosInExpr(1::Nil))(1) & id |
        useAt(contAxR,PosInExpr(1::Nil))(1) & id
    else //Could also make this fallback to the continuity step for early termination
      // DebuggingTactics.print("start "+bound) &
      andL(-1) & lpstep(1)< (
        hideL(-2) & useAt(geq)(-1) & id,
        hideL(-1) & implyL(-1) & <(id, hideL(-2) & lpgeq(bound-1))
      )

  //Proves t_=0, <x'=f(x)&Q>t_!=0, P* |- <x'=f(x)&P>t_!=0
  // Note that the 2nd antecedent is only important when Q reduces the rank
  private def lpclosed(inst:Inst) : BelleExpr = {
    val tac =
    inst match {
      case DisjFml(l, r) =>
        DebuggingTactics.debug("DISJ", doPrint = debugTactic) &
          orL(-3) < (
            useAt(refOrL, PosInExpr(1 :: Nil))(1) & lpclosed(l),
            useAt(refOrR, PosInExpr(1 :: Nil))(1) & lpclosed(r))
      case ConjFml(l, r) =>
        DebuggingTactics.debug("CONJ", doPrint = debugTactic) &
          andL(-3) & useAt(Ax.UniqIff, PosInExpr(1 :: Nil))(1) & andR(1) < (
          hideL(-4) & lpclosed(l),
          hideL(-3) & lpclosed(r)
        )
      case GeqFml(r, gs, cofs) =>
        DebuggingTactics.debug(">= case, rank: "+r+" "+gs, doPrint = debugTactic) &
        (
          if(gs.isEmpty) {
            cohideOnlyL(-3) & lpgeq(r - 1)
          }
          else {
            orL(-3) < (
              cohideOnlyL(-3) & lpgeq(r - 1),
              implyRi()(-2, 1) & useAt(Ax.DRd, PosInExpr(1 :: Nil))(1) &
                dgVdbx(cofs, gs)(1) & DW(1) & G(1) & timeoutQE & done
            )
          }
        )
      case EqFml(r, gs, cofs) =>
        DebuggingTactics.debug("= case", doPrint = debugTactic) &
        (
          if(gs.isEmpty) {
            closeF
          }
          else {
            implyRi()(-2,1) & useAt(Ax.DRd,PosInExpr(1::Nil))(1) &
              dgVdbx(cofs,gs)(1) & DW(1) & G(1) & timeoutQE & done
          }
        )
      case GtFml(r) => ???
    }
    tac
  }

  // Proves t_=0, <t_'=1,x'=f(x)&Q>t_!=0, P* |- <t_'=1,x'=f(x)&P | t_=0>t_!=0
  // Note that the 2nd antecedent is only important when Q reduces the rank
  //todo: eventually, this should just replace lpclosed
  def lpgen(inst:Inst) : BelleExpr = {
    val tac =
      inst match {
        case DisjFml(l, r) =>
          DebuggingTactics.debug("DISJ", doPrint = debugTactic) &
            useAt(distOr, PosInExpr(1 :: Nil))(1) & // Distribute t_ = 0 disjunct in domain of progress fml
            orL(-3) < (
              useAt(refOrL, PosInExpr(1 :: Nil))(1) & lpgen(l),
              useAt(refOrR, PosInExpr(1 :: Nil))(1) & lpgen(r))
        case ConjFml(l, r) =>
          DebuggingTactics.debug("CONJ", doPrint = debugTactic) &
            useAt(distAnd, PosInExpr(1 :: Nil))(1) & // Distribute t_ = 0 disjunct in domain of progress fml
            andL(-3) & useAt(Ax.UniqIff, PosInExpr(1 :: Nil))(1) & andR(1) < (
            hideL(-4) & lpgen(l),
            hideL(-3) & lpgen(r)
          )
        case GeqFml(r, gs, cofs) =>
            useAt(refOrL, PosInExpr(1 :: Nil))(1) & // drop t_ = 0 disjunct in domain of progress fml
            DebuggingTactics.debug(">= case, rank: "+r+" "+gs, doPrint = debugTactic) &
            (
              if(gs.isEmpty) {
                cohideOnlyL(-3) & lpgeq(r - 1)
              }
              else {
                orL(-3) < (
                  cohideOnlyL(-3) & lpgeq(r - 1),
                  implyRi()(-2, 1) & useAt(Ax.DRd, PosInExpr(1 :: Nil))(1) &
                    dgVdbx(cofs, gs)(1) & DW(1) & G(1) & timeoutQE & done
                )
              }
            )
        case EqFml(r, gs, cofs) =>
          DebuggingTactics.debug("= case", doPrint = debugTactic) &
            useAt(refOrL, PosInExpr(1 :: Nil))(1) & // drop t_ = 0 disjunct in domain of progress fml
            (
              if(gs.isEmpty) {
                closeF
              }
              else {
                implyRi()(-2,1) & useAt(Ax.DRd,PosInExpr(1::Nil))(1) &
                  dgVdbx(cofs,gs)(1) & DW(1) & G(1) & timeoutQE & done
              }
            )
        case GtFml(r) =>
          DebuggingTactics.debug("> case, rank: "+r, doPrint = debugTactic) &
          hideL(-2) &
          lpgt(r)
      }
    tac
  }

  /** Given a top-level succedent position corresponding to [x'=f(x)&Q]P
    * Tries to prove that P is a closed semialgebraic invariant, i.e. G|- [x'=f(x)&Q]P
    *
    * G|-P  Q,P |- P*
    * --------------- (sAIc)
    * G |- [x'=f(x)&Q]P
    *
    * P is assumed to be formed from conjunctions, disjunction, p<=q, p>=q, p=q
    * which are collectively normalized to f>=0 (f possibly involving max,min and abs)
    *
    * TODO: Add Q* to the antecedents in the second premise
    * @return closes the subgoal if P is indeed invariant,
    *         This should only fail if either:
    *         1) P fails to normalize to f>=0 form (it isn't closed)
    *         2) it is not invariant
    * @see Andre Platzer and Yong Kiam Tan. [[https://doi.org/10.1145/3209108.3209147 Differential equation axiomatization: The impressive power of differential ghosts]]. In Anuj Dawar and Erich Grädel, editors, Proceedings of the 33rd Annual ACM/IEEE Symposium on Logic in Computer Science, LICS'18, ACM 2018.
    */
  // was "sAIc"
  def sAIclosed : DependentPositionTactic = anon ((pos:Position,seq:Sequent) => {
    if(!(pos.isTopLevel && pos.isSucc))
      throw new IllFormedTacticApplicationException("sAIclosed: position " + pos + " must point to a top-level succedent position")
    if (ToolProvider.algebraTool().isEmpty) throw new ProverSetupException("sAIclosed needs an algebra tool (and Mathematica)")

    val (sys,post) = seq.sub(pos) match {
      case Some(Box(sys:ODESystem,post)) => (sys,post)
      case Some(e) => throw new TacticInapplicableFailure("sAIc only applicable to box ODEs, but got " + e.prettyString)
      case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + seq.prettyString)
    }

    val (fml,propt1) = try {
      semiAlgNormalize(post)
    } catch {
      case ex: IllegalArgumentException => throw new TacticInapplicableFailure("Unable to normalize postcondition to semi-algebraic set", ex)
    }

    val (fmlMM,propt2) = try {
      maxMinGeqNormalize(fml)
    } catch {
      case ex: IllegalArgumentException => throw new TacticInapplicableFailure("Unable to normalize postcondition to max/min/>=", ex)
    }

    //This is a contract failure of maxMinGeqNormalize
    if (!fmlMM.isInstanceOf[GreaterEqual]) throw new UnsupportedTacticFeature("Normalization failed to reach max/min normal form "+fml)

    // For input formula f
    // tac1 rewrites with semialgebraic normalization
    val tac1 = propt1 match {
      case None => skip
      case Some(pr) => useAt(pr)(pos ++ PosInExpr(1::Nil))
    }

    // tac2 rewrites to maxmin normalization and vice-versa
    val (tac2,tac21,tac22,tac23) = propt2 match {
      case None => (skip,skip,skip,skip)
      case Some(pr) => (useAt(pr)(pos ++ PosInExpr(1::Nil)),
        useAt(pr,PosInExpr(1::Nil))('Rlast),
        useAt(pr,PosInExpr(1::Nil))(-1,PosInExpr(1::Nil)),
        useAt(pr,PosInExpr(1::Nil))(1,PosInExpr(0::1::Nil)))
    }

    val (pf,inst) = try {
      fStar(sys,fml)
    } catch {
      case ex: IllegalArgumentException => throw new TacticInapplicableFailure("Unable to generate formula f*", ex)
    }

    DebuggingTactics.debug("PRE",doPrint = debugTactic) &
      tac1 & tac2 &
      //@todo always check with doIfElse or TryCatch instead?
      Idioms.doIfElse(_.subgoals.forall(s => !StaticSemantics.symbols(s(pos.top)).contains("t_".asVariable)))(
        useAt(Ax.RIclosedgeq)(pos) &
        DebuggingTactics.debug("Real Induction",doPrint = debugTactic) &
        andR(pos) <(
          //G |- P
          implyR(pos) & tac21 & ?(id) & timeoutQE & done
          ,
          cohideR(pos) & composeb(1) & dW(1) & assignb(1) &
          implyR(1) &
          //Cut P*
          cutR(pf)(1) <(
            hideL(-3) & tac22 & DebuggingTactics.debug("QE step",doPrint = debugTactic) & timeoutQE & done,
            skip
          ) & //Don't bother running the rest if QE fails
          hideL(-1) & DebuggingTactics.debug("Finish step",doPrint = debugTactic) & implyR(1) &
          tac23 &
          //At this point, the sequent should be EXACTLY the following (where P is rewritten back to semialgebraic normal form):
          //t_=0, <x'=f(x)&Q>t_!=0, P* |- <x'=f(x)&P>t_!=0
          lpclosed(inst)
        )
        ,
        DebuggingTactics.error("Inapplicable: t_ occurs")
      )
  })

  // Similar to lpgeq but proves the unlocked version
  // t=0 , p*>0 -> <t'=1, x'=f(x)& p - t^(2k) >=0> t!=0
  private def lpgeqUnlock(bound:Int) : BelleExpr =
    if (bound <= 1)
      (useAt(contAx,PosInExpr(1::Nil))(1) | useAt(contAxR,PosInExpr(1::Nil))(1))  &
        exhaustiveEqL2R(-1) & hideL(-1) & QE
    else //Could also make this fallback to the continuity step for early termination
      andL(-2) & lpstep(1) &
      < (
        hideL(-3) & useAt(geq)(-2) & exhaustiveEqL2R(-1) & hideL(-1) & QE,
        hideL(-2) & implyL(-2) & <(
          exhaustiveEqL2R(-1) & hideL(-1) & hideR(1) & QE,
          hideL(-3) & lpgeqUnlock(bound-1))
      )

  //"unlocks" a strict inequality q > 0 | t = 0 by turning it into q - t^2*bound >= 0
  //as above, assumes local progress for q is in antecedent (-1) and the progress in succedent (1)
  //additionally, the domain is assumed to be exactly g>0 | t=0
  //Unfortunately, this tactic has to prove the power bounds on the fly but hopefully remember() can store them
  private def lpgt(bound:Int): DependentTactic = anon ((seq: Sequent) => {
    val boundPr = remember(("f_()-(g_()-h_())^"+(2*bound).toString()+">=0 -> f_()>0 | g_()=h_()").asFormula, QE, namespace)

    val (p,t,s) = seq.succ(0).sub(PosInExpr(0::1::Nil)) match {
      case Some(Or(Greater(p,_),Equal(t,s))) => (p,t,s)
      case Some(e) => throw new TacticInapplicableFailure("lpgt only applicable to disjunction of strict inequality and equality, but got " + e.prettyString)
      case None => throw new IllFormedTacticApplicationException("Position does not point to a valid position in sequent " + seq.prettyString)
    }
    //println(p,t)
    val unlocked = GreaterEqual(Minus(p,Power(Minus(t,s),Number(2*bound))),Number(0))
    dR(unlocked)(1)<(
      lpgeqUnlock(bound),
      diffWeakenG(1) & byUS(boundPr))
  })

  // Determines if a formula is of the special "recursive" rank one case
  // i.e. every p~0 is (trivially) Darboux
  // returns a list of formulas internally re-arranged according to diff cut order
  def rankOneFml(ode: DifferentialProgram, dom:Formula, f:Formula) : Option[Formula] = {

    f match {
      case cf:ComparisonFormula =>
        //findDbx
        val (pr, cofactor, rem) = try {
          findDbx(ode, dom, cf,false)
        } catch {
          case ex: ProofSearchFailure => return None
        }
        if (pr.isProved)// TODO: this should be keeping track of co-factors rather than throwing them away
          Some(f)
        else {
          if(cf.isInstanceOf[Equal] || cf.isInstanceOf[NotEqual]) return None
          //TODO: need to check cofactor well-defined as well?
          val pr2 = try {
            proveBy(Imply(And(dom, Equal(cf.left, Number(0))), Greater(rem, Number(0))), timeoutQE)
          }
          catch {
            //todo: Instead of eliminating quantifiers, Z3 will throw an exception that isn't caught by ?(timeoutQE)
            //This is a workaround
            case e : BelleThrowable if e.getCause.isInstanceOf[SMTQeException] =>  proveBy(False, skip)
          }
          logger.debug(pr2.toString)
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
        DebuggingTactics.debug("state",doPrint = debugTactic) & dC(l)(1) &
        Idioms.doIfElse(_.subgoals.size == 2)(<(
        hideL(-1) & boxAnd(1) & andR(1) <(
          DW(1) & G(1) & prop,
          recRankOneTac(r)),
        hideL(-2) & recRankOneTac(l)
        ),
        hideL(-1) & boxAnd(1) & andR(1) <(
          DW(1) & G(1) & prop,
          recRankOneTac(r))
      )
      case Or(l,r) => orL(-1)<(
        useAt(boxOrL,PosInExpr(1::Nil))(1) & recRankOneTac(l),
        useAt(boxOrR,PosInExpr(1::Nil))(1) & recRankOneTac(r)
      )
      case _ => (diffInd()(1) | dgDbxAuto(1) | dgBarrier(1)) & done
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
  // was "sAIR1"
  def sAIRankOne(doReorder:Boolean=true,skipClosed:Boolean =true) : DependentPositionTactic = anon {(pos:Position,seq:Sequent) => {
    if(!(pos.isTopLevel && pos.isSucc))
      throw new IllFormedTacticApplicationException("sAIRankOne: position " + pos + " must point to a top-level succedent position")

    if (ToolProvider.algebraTool().isEmpty) throw new ProverSetupException("ODE invariance tactic needs an algebra tool (and Mathematica)")

    val (ode, dom, post) = seq.sub(pos) match {
      case Some(Box(sys: ODESystem, post)) => (sys.ode, sys.constraint, post)
      case Some(e) => throw new TacticInapplicableFailure("sAIR1 only applicable to box ODEs, but got " + e.prettyString)
      case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + seq.prettyString)
    }
    val (f2, propt) = try {
      semiAlgNormalize(post)
    } catch {
      case ex: IllegalArgumentException => throw new TacticInapplicableFailure("Unable to normalize postcondition to semi-algebraic set", ex)
    }

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
          cohideR(pos) & implyR(1) &
          recRankOneTac(f2)
        )
      }
    }
    else {
      val f3 =
        try {
          rankOneFml(ode, dom, f2) match {
            case None => throw new TacticInapplicableFailure("Unable to re-order to recursive rank 1 form: " + f2)
            case Some(f) => f
          }
        } catch {
          case e: IllegalArgumentException =>
            throw new TacticInapplicableFailure("Unable to determine whether formula is rank 1 form", e)
        }

      val reorder = proveBy(Equiv(f2, f3), timeoutQE)
      if(!reorder.isProved)
        throw new TacticInapplicableFailure("Unable to automatically prove equivalence "+Equiv(f2,f3))

      starter & useAt(reorder)(pos ++ PosInExpr(1 :: Nil)) & cutR(f3)(pos) < (
        useAt(reorder, PosInExpr(1 :: Nil))(pos) & timeoutQE,
        cohideR(pos) & implyR(1) & recRankOneTac(f3)
      )
    }
  }}

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
  def timeBound : DependentPositionTactic = anon ((pos:Position,seq:Sequent) => {
    if(!(pos.isTopLevel && pos.isSucc))
      throw new IllFormedTacticApplicationException("timeBound: position " + pos + " must point to a top-level succedent position")

    val (ode, dom, post) = seq.sub(pos) match {
      case Some(Box(sys: ODESystem, post)) => (sys.ode, sys.constraint, post)
      case Some(e) => throw new TacticInapplicableFailure("timeBound only applicable to box ODEs, but got " + e.prettyString)
      case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + seq.prettyString)
    }
    //Check that the domain at least freezes one of the coordinates
    val domConj = flattenConjunctions(dom)
    val atoms = atomicListify(ode)

    //Only need to freeze coordinates free in postcondition
    val fvs = StaticSemantics.freeVars(post)
    val freeAtoms = atoms.filter( p => fvs.contains(p.xp.x))

    // Handle the special case where postcondition is constant
    if(freeAtoms.isEmpty)
      V(pos) & QE & done
    else {
      val timeLike = atoms.flatMap(_ match {
        case AtomicODE(v, n: Number) if n.value != 0 => Some(v.x)
        case _ => None
      })
      val constRHS = domConj.filter(_ match {
        //todo: this can be generalized
        case Equal(l, r) if StaticSemantics.freeVars(r).intersect(StaticSemantics.boundVars(ode)).isEmpty &&
          timeLike.contains(l) => true
        case _ => false
      })

      constRHS match {
        case Nil => throw new TacticInapplicableFailure("time bound requires at least one time-like coordinate to be frozen in domain, found none")
        case Equal(t, d) :: _ =>
          //Construct the bounding polynomials sum_i (x_i-old(x_i))^2 <= (sum_i 2x_ix'_i)*t
          val left = freeAtoms.map(f =>
            Power(Minus(f.xp.x, FuncOf(Function("old", None, Real, Real, false), f.xp.x)), Number(2)): Term).reduce(Plus)
          val right = Times(freeAtoms.map(f => Times(Number(2),
            Times(Minus(f.xp.x, FuncOf(Function("old", None, Real, Real, false), f.xp.x)), f.e)): Term).reduce(Plus), Minus(t, d))

          //dC with old(.) moves the formula to the last position
          dC(LessEqual(left, right))(pos) < (
            dW('Rlast) & QE & done,
            diffInd('full)('Rlast)
          )
      }
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
        useAt(Ax.box,PosInExpr(1::Nil))(-2) & notL(-2) &
        cutL("<{c&!q(||)|r(||)}>(!r(||) | !p(||))".asFormula)(-1) <( skip , cohideR(3) & implyR(1) & mond & prop) &
        useAt(Ax.box,PosInExpr(1::Nil))(1) & notR(1) &
        cutL("<{c&q(||)}>(!r(||) | !p(||))".asFormula)(-2) <( skip , cohideR(2) & implyR(1) & mond & prop) &
        andLi & useAt(Ax.Uniq, PosInExpr(0::Nil), (_: Option[Subst]) => {
          RenUSubst(("c".asDifferentialProgram, "c".asDifferentialProgram) ::
            ("p(||)".asFormula, "!r(||) | !p(||)".asFormula) ::
            ("q(||)".asFormula, "!q(||) | r(||)".asFormula) ::
            ("r(||)".asFormula, "q(||)".asFormula) :: Nil)
        })(-1) & DWd(-1) &
        cutL("<{c&(!q(||)|r(||))&q(||)}>!p(||)".asFormula)(-1) <(
          implyRi & useAt(Ax.DRd,PosInExpr(1::Nil))(1) & DW(1) & G(1) & prop,
          cohideR(2) & implyR(1) & mond & prop)
      , namespace)

  @Tactic(
    premises="Γ, t=0 |- ⟨t'=1,x'=f(x) & ~Q ∨ t=0⟩ t!=0, Δ",
    conclusion="Γ |- [x'=f(x) & Q}]P, Δ",
    displayLevel="browse")
  def domainStuck : DependentPositionTactic = anon ((pos:Position,seq:Sequent) => {
    if(!(pos.isTopLevel && pos.isSucc))
      throw new IllFormedTacticApplicationException("domainStuck: position " + pos + " must point to a top-level succedent position")

    val (ode, dom, post) = seq.sub(pos) match {
      //needs to be dualized
      case Some(Box(sys: ODESystem, post)) if pos.isSucc => (sys.ode, sys.constraint, post)
      //todo: case Some(Diamond(sys:ODESystem,post)) if pos.isAnte => (sys.ode, sys.constraint, post)
      case Some(e) => throw new TacticInapplicableFailure("domainStuck only applicable to box ODEs, but got " + e.prettyString)
      case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + seq.prettyString)
    }

    val timevar = TacticHelper.freshNamedSymbol("t_".asVariable, seq)
    val timer = AtomicODE(DifferentialSymbol(timevar),Number(1))

    val stuckDom = Equal(timevar,Number(0))
    val odedim = getODEDim(seq,pos)

    val (negDom, propt) = semiAlgNormalize(Not(dom))
    //The negated domain is definitely normalizable if not something went wrong
    if(propt.isEmpty)
      throw new UnsupportedTacticFeature("Unexpected failure in normalization of "+Not(dom))

    val (pf,inst) = try {
      fStar(ODESystem(ode,True),negDom)
    } catch {
      case ex: IllegalArgumentException => throw new TacticInapplicableFailure("Unable to generate formula f*", ex)
    }

    // Gross way of inserting time ODE in a stable way (copied from ODELiveness)
    val timetac =
      cut(Exists(List(timevar), Equal(timevar,Number(0)))) <( existsL('Llast), cohideR('Rlast) & QE) &
        vDG(timer)(pos)

    // set up the time variable
    // commute it to the front to better match with realind/cont
    timetac &
    cutR(Box(ODESystem(DifferentialProduct(timer,ode),stuckDom),post))(pos) <(
      timeBound(pos) & done //closes assuming P(init)
      ,
      useAt(stuckRefine,PosInExpr(1::Nil))(pos) &
      //Clean up the goal a little bit
      chase(pos.checkTop.getPos,PosInExpr(1::Nil)) & useAt(propt.get)(pos.checkTop.getPos,PosInExpr(0::1::0::Nil)) &
      cutR(pf)(pos) <(
        DebuggingTactics.debug("QE step",doPrint = debugTactic) & timeoutQE & done,
        cohideOnlyL('Llast) &
          cohideOnlyR(pos) &
          cutR(Diamond(ODESystem(DifferentialProduct(timer,ode),Greater(Number(1),Number(0))),NotEqual(timevar,Number(0))))(1) <(
            cohideR(1) & byUS(contAxTrue),
            implyR(1) & implyR(1) & lpgen(inst)
          )
      )
    )
  })

  /**
  * Explicitly calculate the conjunctive rank of a list of polynomials
  * (uses conjunctive optimization from SAS'14)
  * @param ode the ODESystem to use
  * @param polys the polynomials to compute rank for
  * @return the (conjunctive) rank, the Groebner basis closed under Lie derivation, and its cofactors (in that order)
  */
  def rank(ode:ODESystem, polys:List[Term]) : (Int, List[Term], List[List[Term]]) = {
    if (ToolProvider.algebraTool().isEmpty)
      throw new ProverSetupException("rank computation requires a AlgebraTool, but got None")

    val algTool = ToolProvider.algebraTool().get

    var gb = algTool.groebnerBasis(polys ++ domainEqualities(ode.constraint))
    var rank = 1
    //remainder after each round of polynomial reduction
    var remaining = polys

    while(true) {
      val lies = remaining.map(p => simplifiedLieDerivative(ode.ode, p, ToolProvider.simplifierTool()))
      val quos = lies.map(p => algTool.polynomialReduce(p, gb))
      remaining = quos.map(_._2).filterNot(_ == Number(0))
      if(remaining.isEmpty) {
        //println(gb,rank)
        val gblies = gb.map(p => simplifiedLieDerivative(ode.ode, p, ToolProvider.simplifierTool()))
        val cofactors = gblies.map(p => algTool.polynomialReduce(p, gb))
        return (rank,gb,cofactors.map(_._1))
      }
      gb = algTool.groebnerBasis(remaining ++ gb)
      rank+=1
    }
    (0,List(),List())
  }

  /**
    * Prove Vectorial Darboux (using a single differential ghost)
    * TODO: at the moment, it is unclear what the tactic interface should be
    * Currently, it expects an ODE, and cuts in the conjunction /\_i p_i=0 as follows:
    *
    * Gamma |- [x'=f(x)&Q&/\_i p_i=0]P    (it closes Gamma |- /\_i p_i=0 by QE)
    * --- vdbx(Gco,p,F)
    * Gamma |- [x'=f(x)&Q]P
    *
    * The optional flag switches this to vectorial darboux inequality instead:
    *
    * Gamma |- [x'=f(x)&Q& \/_i p_i != 0]P (it closes Gamma |- \/_i p_i !=0 by QE)
    * --- vdbx(Gco,p,T)
    * Gamma |- [x'=f(x)&Q]P
    *
    * @param Gco the cofactor matrix
    * @param ps the polynomial vector
    * @param negate implements vectorial darboux inequality instead
    * @return tactic implementing vdbx as described above
    * @see Andre Platzer and Yong Kiam Tan. [[https://doi.org/10.1145/3209108.3209147 Differential equation axiomatization: The impressive power of differential ghosts]]. In Anuj Dawar and Erich Grädel, editors, Proceedings of the 33rd Annual ACM/IEEE Symposium on Logic in Computer Science, LICS'18, ACM 2018.
    * @note uses Dconstify and handles other constification internally instead of an external wrapper
    */
  private lazy val dbxCond: ProvableSig = remember("((-g_())*y_()+0)*(z_())^2 + y_()*(2*z_()^(2-1)*(g_()/2*z_()+0))=0".asFormula,QE,namespace).fact

  private lazy val dbxEqOne: ProvableSig = ProvableSig.proveArithmetic(BigDecimalQETool, "1*1^2=1".asFormula)
  /** The ghost variables */
  private val gvy = Variable("dbxy_")
  private val gvz = Variable("dbxz_")
  private val zero = Number(0)
  private val one = Number(1)
  private val two = Number(2)

  def dgVdbx(Gco:List[List[Term]],ps:List[Term], negate:Boolean = false) : DependentPositionTactic = anon {(pos:Position,seq:Sequent) => {
    if(!(pos.isTopLevel && pos.isSucc))
      throw new IllFormedTacticApplicationException("dgVdbx: position " + pos + " must point to a top-level succedent position")

    val dim = ps.length
    if(! (Gco.length == dim && Gco.forall(gs => gs.length == dim) && dim >= 1))
      throw new IllFormedTacticApplicationException("dgVdbx: inputs have non-matching dimensions")

    val (ode,dom) = seq.sub(pos) match {
      case Some(Box(sys:ODESystem,_)) => (sys.ode,sys.constraint)
      case Some(e) => throw new TacticInapplicableFailure("dgVdbx only applicable to box ODEs, but got " + e.prettyString)
      case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + seq.prettyString)
    }

    // Turns the vector into sum_i p_i^2
    val sump = ps.map(p => Times(p,p)).reduce(Plus)

    //Convert between the conjunction /\_i p_i=0 and sum_i p_i^2 <=0
    val cutp =
      if(negate)
        ps.map(p => NotEqual(p,zero)).reduce(Or)
      else
        ps.map(p => Equal(p,zero)).reduce(And)

    //this can also be manually proved rather than using QE
    val pr =
      if(negate)
        proveBy(Equiv(cutp, Greater(sump,zero)), QE)
      else
        proveBy(Equiv(cutp,LessEqual(sump,zero)), SaturateTactic(useAt(fastSOS,PosInExpr(1::Nil))(1) & andR(1) <( prove_sos_positive, skip )) & QE )

    //Construct the term ||G||^2 + 1
    val cofactorPre = Plus(Gco.map(ts => ts.map(t=>Times(t,t):Term).reduceLeft(Plus)).reduceLeft(Plus),one)
    val qco = if (negate) Neg(cofactorPre) else cofactorPre

    //Construct the diff ghost y' = -qy
    val dey = AtomicODE(DifferentialSymbol(gvy), Times(Neg(qco), gvy))

    //Diff ghost z' = qz/2
    val dez = AtomicODE(DifferentialSymbol(gvz), Times(Divide(qco, two), gvz))

    val gtz = Greater(gvy, zero)
    val pcy = And(gtz,
      if(negate) Greater(Times(gvy, sump), zero)
      else LessEqual(Times(gvy, sump), zero)
    )
    val pcz = Equal(Times(gvy, Power(gvz, two)), one)

    val frobeniusLem = frobenius_subord_bound(dim)
    val frobenius = if(negate) frobeniusLem._2 else frobeniusLem._1

    //TODO: Is this the right place to handle constification??
    val sumpRepl = replaceODEfree(sump,sump,ode)
    val liePre = lieDerivative(ode,sumpRepl)
    val lie = replaceODEfree(sump,liePre,ode)
    val dpPre = dot_prod(matvec_prod(Gco,ps),ps)
    val dp = replaceODEfree(sump,dpPre,ode)
    if(lie == Number(0))
      dC(cutp)(pos) <( skip, diffInd('full)(pos))

    else
    //Cuts
    dC(cutp)(pos) <(
      skip,
      useAt(pr)(pos.checkTop.getPos,1::Nil) &
      DifferentialTactics.dG(dey, Some(pcy))(pos) & //Introduce the dbx ghost
        existsR(one)(pos) & //Anything works here, as long as it is > 0, 1 is convenient
        dC(gtz)(pos) < (
          // Do the vdbx case manually
          boxAnd(pos) & andR(pos) < (
            diffWeakenG(pos) & implyR(1) & andL('Llast) & id,
            //QE can't handle this alone: diffInd('full)(pos)
            Dconstify
            (
              diffInd('diffInd)(pos) <(
                //Cleanup the goal
                //Extra domain constraint from diffInd step
                hideL('Llast) &
                //Get rid of dbxy_=1 assumption
                exhaustiveEqL2R(hide=true)('Llast) &
                // TODO: The next 3 steps do not work with Dconstify
                //useAt(leftMultId)(pos++PosInExpr(0::Nil)) &
                //useAt(pr,PosInExpr(1::Nil))(pos) &
                //DebuggingTactics.debug("First Vdbx QE",true) &
                //p=0 must be true initially
                QE & DebuggingTactics.done("Vdbx condition must hold in the beginning")
                ,
                cohideOnlyR('Rlast) & SaturateTactic(Dassignb(1)) &
                  // At this point, we should get to (gy+0)p + y(p') <= 0
                  // or the negated version ((-g)y+0)p + y(p') >= 0
                  // Remove the y, turning the result into p' <= gp or gp <= p'
                  (if(negate) useAt(ghostLem2,PosInExpr(1::Nil))(1)
                  else useAt(ghostLem1,PosInExpr(1::Nil))(1)) &
                  andR(1) <(
                    andL('Llast) & close,
                  //Now we need a real rearrangement using Q |- p' = Gp
                  cut(Equal(lie,Times(two,dp))) <(
                    exhaustiveEqL2R('Llast) & hideL('Llast) &
                      //Finally apply the Frobenius bound
                      cohideR(1) & byUS(frobenius)
                    ,
                    // This is the only "real" use of QE.
                    DebuggingTactics.debug("Second Vdbx QE",debugTactic) &
                      hideR(1) & QE & DebuggingTactics.done("Vdbx condition must be preserved")
                  )
                )
              )
            )(pos)
          )
          ,
          DifferentialTactics.dG(dez, Some(pcz))(pos) & //Introduce the dbx ghost
            existsR(one)(pos) & //The sqrt inverse of y, 1 is convenient
            diffInd('diffInd)(pos) // Closes z > 0 invariant with another diff ghost
              <(
              hideL('Llast) & exhaustiveEqL2R(hide=true)('Llast)*2 & useAt(dbxEqOne)(pos) & closeT,
              cohideR('Rlast) & SaturateTactic(Dassignb(1)) & byUS(dbxCond)
            )
        )
    )
  }}

  /**
    * Implements (conjunctive) differential radical invariants
    *
    * G,Q |- /\_i p_i*=0
    * --- (dRI)
    * G |- [x'=f(x)&Q]/\_i p_i=0
    *
    * This proof rule is complete for open semialgebraic domain constraints Q
    * This requires a top-level postcondition which rearranges to be a conjunction of equalities
    * @see Khalil Ghorbal, Andrew Sogokon, and André Platzer. [[https://doi.org/10.1007/978-3-319-10936-7_10 Invariance of conjunctions of polynomial equalities for algebraic differential equations]].
    */
  @Tactic(names="(Conj.) Differential Radical Invariants",
    premises="Γ, Q |- p*=0",
    conclusion="Γ |- [x'=f(x) & Q}]p=0, Δ",
    displayLevel="browse")
  val dRI : DependentPositionTactic = anon ((pos:Position,seq:Sequent) => {
    if(!(pos.isTopLevel && pos.isSucc))
      throw new IllFormedTacticApplicationException("dRI: position " + pos + " must point to a top-level succedent position")

    val (sys, post) = seq.sub(pos) match {
      case Some(Box(sys: ODESystem, post)) => (sys, post)
      case Some(e) => throw new TacticInapplicableFailure("dRI only applicable to box ODEs, but got " + e.prettyString)
      case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + seq.prettyString)
    }

    val (f2, _) = try {
      semiAlgNormalize(post)
    } catch {
      case ex: IllegalArgumentException => throw new TacticInapplicableFailure("Unable to normalize postcondition to semi-algebraic set", ex)
    }

    val conjs = flattenConjunctions(f2)
    val polys = {
      if (conjs.forall(f => f.isInstanceOf[Equal]))
        conjs.map(f => f.asInstanceOf[Equal].left)
      else {
        //TODO: this is not the best way to go about proving this
        val (f2, _) = try {
          algNormalize(post)
        } catch {
          case ex: IllegalArgumentException => throw new TacticInapplicableFailure("Unable to normalize postcondition", ex)
        }

        //This is a contract failure of maxMinGeqNormalize
        if (!f2.isInstanceOf[Equal]) throw new UnsupportedTacticFeature("Normalization failed to reach an equation "+f2)
        List(f2.asInstanceOf[Equal].left)
      }
    }
    val (r,groebner,cofactors) = rank(sys,polys)

    //println(r,groebner,cofactors)

    diffUnpackEvolutionDomainInitially(pos) &
      DebuggingTactics.debug("dgVdbx",debugTactic) &
      dgVdbx(cofactors,groebner)(pos) &
      DebuggingTactics.debug("Final QE",debugTactic) &
      cohideR(pos) & DW(1) & G(1) & QE
  })

  private val cauchy_schwartz_lem = remember("b()>=0 & c()>=0 & a()*a() <= b()*c() -> (a()+u()*v())*(a()+u()*v()) <= (b()+u()*u())*(c()+v()*v())".asFormula,QE).fact
  /**
    * Pre-prove the symbolic lemmas for n-dimensional Cauchy Schwartz
    * Note: this lemma proves pretty quickly e.g. for n=10
    * @param n the dimension to use
    * @return the symbolic bound (u.v)^2 <= (||u||||v||)^2
    */
  def cauchy_schwartz_bound (n : Int) : ProvableSig = {

    require(n>=1, "Symbolic Cauchy-Schwartz inequality only applies for n >= 1")

    val pr1opt = getLemma("cauchy_schwartz_"+n.toString)

    if(pr1opt.isDefined)
      return pr1opt.get.fact

    val csuPrefix = "csiu"
    val csvPrefix = "csiv"
    val us = List.range(0,n).map(i => mkConst(csuPrefix,i))
    val vs = List.range(0,n).map(i => mkConst(csvPrefix,i))
    val dp = dot_prod(us,vs)
    val unorm = dot_prod(us,us)
    val vnorm = dot_prod(vs,vs)
    val fml1 = LessEqual(Times(dp,dp), Times(unorm,vnorm))
    val pr1 = proveBy(fml1,
      SaturateTactic(useAt(cauchy_schwartz_lem,PosInExpr(1::Nil))(1) & andR(1) <(prove_sos_positive, andR(1) <(prove_sos_positive,skip))) & QE)
    //val pr1 = proveBy(fml1 , QE)
    //println(pr1)
    val sgn = And(GreaterEqual(unorm,Number(0)),GreaterEqual(vnorm,Number(0)))

    val pr = proveBy(And(fml1,sgn),andR(1) <( by(pr1), prove_sos_positive))

    storeLemma(pr1, "cauchy_schwartz_"+n.toString)
    pr1
  }

  /**
    * Pre-prove the following double-sided bound:
    * -(||G||^2+1) ||p||^2 <= 2*((Gp).p) <= (||G||^2+1) ||p||^2
    *
    * The arithmetic is guided as follows:
    * For each row (G_i.p)^2 <= ||G_i||^2 ||p||^2 (Cauchy Schwartz)
    * Which implies ||Gp||^2 = sum_i (G_i.p)^2 <= sum_i ||G_i||^2 ||p||^2
    *
    * Then since
    * ((Gp).p)^2 <= ||Gp||^2 ||p||^2 (Cauchy Schwartz)
    * This yields
    * ((Gp).p)^2 <= (sum_i ||G_i||^2) ||p||^2 ||p||^2
    *
    * Then use a usubst lemma to get:
    * 2((Gp).p) <= (1+sum_i ||G_i||^2) ||p||^2
    * and also:
    * 2((Gp).p) >= -(1+sum_i ||G_i||^2) ||p||^2
    *
    * @param n the dimension to use
    * @return the symbolic bounds (||G||^2 + 1) ||p||^2 <= 2*((Gp).p) <= (||G||^2 + 1) ||p||^2
    */
  def frobenius_subord_bound (n : Int) : (ProvableSig,ProvableSig) = {

    require(n>=1, "Symbolic Frobenius norm inequality only applies for n >= 1")

    val finproptU = getLemma("frobenius_subord_U_"+n.toString)
    val finproptL = getLemma("frobenius_subord_L_"+n.toString)

    if(finproptU.isDefined && finproptL.isDefined)
      return (finproptU.get.fact,finproptL.get.fact)
    else if(finproptU.isDefined ^ finproptL.isDefined)
    {
      //If, for some reason, only one of them got added
      removeLemma("frobenius_subord_U_"+n.toString)
      removeLemma("frobenius_subord_L_"+n.toString)
    }

    val gPrefix = "gfrosub"
    val pPrefix = "pfrosub"

    val g = List.range(0,n).map(i => List.range(0,n).map(j => mkConst(gPrefix,i*n+j)))
    val p = List.range(0,n).map(i => mkConst(pPrefix,i))

    //This is done purely usubst style using Cauchy Schwartz
    val cs = cauchy_schwartz_bound(n)
    val csLhs = cs.conclusion.succ(0).sub(PosInExpr(0::0::Nil)).get

    // Use Cauchy-Schwartz on each sub-term (G_i.p)^2 <= ||G_i||^2||p||^2
    val gdot = g.map(
      gi => {
        val subst = UnificationMatch.unifiable(csLhs, dot_prod(gi, p)).get
        cs(subst.usubst)
      }
    )
    // println("Cauchy Schwartz: ",gdot)

    // Sum the sub-terms:
    // sum_i (G_i.p)^2 <= sum_i ||G_i||^2 ||p||^2
    val sum = gdot.tail.foldLeft(gdot.head)(
      (cur,pr) => {
        val subst1 = UnificationMatch.unifiable(lemDist.conclusion.succ(0).sub(PosInExpr(0::0::Nil)).get,cur.conclusion.succ(0)).get
        val subst2 = UnificationMatch.unifiable(lemDist.conclusion.succ(0).sub(PosInExpr(0::1::Nil)).get,pr.conclusion.succ(0)).get
        val subst = subst1++subst2
        val lemma = lemDist(subst.usubst)
        val uspr = proveBy(lemma.conclusion.succ(0).sub(PosInExpr(1::Nil)).get.asInstanceOf[Formula],
          useAt(lemma,PosInExpr(1::Nil))(1) & andR(1) <(by(cur),by(pr))
        )
        //println(uspr)
        uspr
      })
    //println("Sum: ",sum)

    // Multiply both sides by ||p||^2
    // sum_i (G_i.p)^2 ||p||^2 <= sum_i ||G_i||^2 ||p||^2 ||p||^2
    val pnorm = sum.conclusion.succ(0).sub(PosInExpr(1::1::Nil)).get.asInstanceOf[Term]
    val pnormpos = proveBy(GreaterEqual(pnorm,Number(0)),prove_sos_positive)

    val sump1 = useFor(lemPosMul,PosInExpr(0::Nil))(Position(1))(pnormpos)
    val sump = useFor(sump1,PosInExpr(0::Nil))(Position(1))(sum)

    // Transitivity
    // ((Gp).p)^2 <= sum_i (G_i.p)^2 ||p||^2 <= sum_i ||G_i||^2 ||p||^2 ||p||^2
    val trans1 = useFor(lemTrans,PosInExpr(0::Nil))(Position(1))(cs)
    val trans = useFor(trans1,PosInExpr(0::Nil))(Position(1))(sump)
    //println("Trans: ",trans)

    //Upper bound
    val ub1 = useFor(lemUb,PosInExpr(0::Nil))(Position(1))(pnormpos)
    val ub = useFor(ub1,PosInExpr(0::Nil))(Position(1))(trans)
    //Lower bound
    val lb1 = useFor(lemLb,PosInExpr(0::Nil))(Position(1))(pnormpos)
    val lb = useFor(lb1,PosInExpr(0::Nil))(Position(1))(trans)

    storeLemma(ub,"frobenius_subord_U_"+n.toString)
    storeLemma(lb,"frobenius_subord_L_"+n.toString)
    (ub,lb)
  }

  // Proves the following matrix-vector bound
  // 2(Ax.x) + 2b.x <= 2||A|| ||x||^2 + (1+(b.x)^2) <= 2(||A||^2+1)||x||^2 + ||b||^2||x||^2 + 1
  def affine_norm_bound (n : Int) : (ProvableSig) = {

    require(n>=1, "Symbolic affine norm inequality only applies for n >= 1")

    val affineOpt = getLemma("affine_norm_bound_"+n.toString)
    if(affineOpt.isDefined)
      return (affineOpt.get.fact)

    // The prefix for a just uses the same one as Frobenius subord
    val bPrefix = "baffine"
    val xPrefix = "xaffine"

    val b = List.range(0,n).map(i => mkConst(bPrefix,i))
    val x = List.range(0,n).map(i => mkConst(xPrefix,i))

    //This is done purely usubst style using Cauchy Schwartz
    val cs = cauchy_schwartz_bound(n)
    val csLhs = cs.conclusion.succ(0).sub(PosInExpr(0::0::Nil)).get

    //b.x * b.x <= ||b||^2||x||^2
    val blem0 = cs(UnificationMatch.unifiable(csLhs, dot_prod(b, x)).get.usubst)
    //b.x * b.x + 1 <= ||b||^2||x||^2 + 1
    val blem1 = useFor(lemAdd1,PosInExpr(0::Nil))(Position(1))(blem0)
    //2(b.x) <= b.x*b.x + 1
    val blem2 = lemSq(UnificationMatch.unifiable("a()".asTerm, dot_prod(b, x)).get.usubst)
    //2(b.x) <= ||b||^2||x||^2 + 1
    val blem = useFor(useFor(lemTrans,PosInExpr(0::Nil))(Position(1))(blem2),PosInExpr(0::Nil))(Position(1))(blem1)

    //2(Ax.x) <= (||A||^2+1)||x||^2
    val frosub = frobenius_subord_bound(n)._1

    val lem = useFor(useFor(lemAffinecomb,PosInExpr(0::Nil))(Position(1))(frosub),PosInExpr(0::Nil))(Position(1))(blem)
    storeLemma(lem,"affine_norm_bound_"+n.toString)
    lem
  }

  /**
    * Implements differential fixed point
    *
    * G, x=x0 |- [x'=f(x)& Q & x=x0]P    G|-f(x)=0
    * --- (dFP)
    * G |- [x'=f(x)&Q]P
    *
    */
  @Tactic(names="Differential Fixed Point",
    premises="Γ, x=x0 |-[x'=f(x) & Q &x=x0}]P, Δ ;; Γ |- f(x) = 0",
    conclusion="Γ |- [x'=f(x) & Q}]P, Δ",
    displayLevel="browse")
  val dFP : DependentPositionTactic = anon ((pos:Position,seq:Sequent) => {
    if(!(pos.isTopLevel && pos.isSucc))
      throw new IllFormedTacticApplicationException("dFP: position " + pos + " must point to a top-level succedent position")

    val (sys, post) = seq.sub(pos) match {
      case Some(Box(sys: ODESystem, post)) => (sys, post)
      case Some(e) => throw new TacticInapplicableFailure("dFP only applicable to box ODEs, but got " + e.prettyString)
      case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + seq.prettyString)
    }

    val vs = atomicListify(sys.ode).map( p => p.xp.x )
    val olds = vs.map(v => Equal(v,FuncOf(Function("old", None, Real, Real, false),v)))

    dC(olds.reduce(And.apply))(pos) <(
      skip,
      dRI(pos)
    )
  })

  /**
    * Helper and lemmas
    */
  private lazy val lemPosMul = remember("a() >= 0 -> b() <= c() -> b()*a() <= c()*a()".asFormula,QE).fact
  private lazy val lemTrans = remember("a() <= b() -> b() <= c() -> a() <= c()".asFormula,QE).fact
  private lazy val lemDist = remember("a() <= b()*e() & c () <= d()* e() -> a()+c() <= (b()+d())*e()".asFormula,QE).fact
  private lazy val lemUb = remember("c() >=0 -> a()*a() <= b()*c()*c() -> 2*a()<= (b()+1)*c()".asFormula,QE).fact
  private lazy val lemLb = remember("c() >=0 -> a()*a() <= b()*c()*c() -> 2*a() >= -(b()+1)*c()".asFormula,QE).fact

  private lazy val lemSq = remember("2*a() <= a()*a() + 1".asFormula,QE).fact
  private lazy val lemAdd1 = remember("a() <= b() -> a() +1 <= b() + 1".asFormula,QE).fact
  private lazy val lemAffinecomb = remember("a() <= d()*x() -> b() <= c()*x() + 1 -> a() + b() <= (d()+c()) * x() +1 ".asFormula,QE).fact

  // Specialized lemma to rearrange the ghosts
  private lazy val ghostLem1 = remember("y() > 0 & pp() <= (g()*p()) -> ((-g())*y()+0)*p() + y()*pp() <= 0".asFormula,QE)
  private lazy val ghostLem2 = remember("y() > 0 & pp() >= -(g()*p()) -> ((--g())*y()+0)*p() + y()*pp() >= 0".asFormula,QE)
  private lazy val leftMultId = remember("1*f() = f()".asFormula,QE)

  // Symbolic matrix and vector products, assuming that the dimensions all match up
  def dot_prod (v1:List[Term],v2:List[Term]) : Term = {
    val zipped = (v1 zip v2).map({case (t1,t2)=>Times(t1,t2)})
    zipped.reduce(Plus.apply)
  }

  def matvec_prod (m:List[List[Term]],v:List[Term]) : List[Term] = {
    m.map(ls => dot_prod(ls,v))
  }

  //computes m x n (assumes n transposed)
  private def matmat_prod (m:List[List[Term]],n:List[List[Term]]) : List[List[Term]] = {
    m.map(ls => matvec_prod(n,ls))
  }

  private def vecvec_sum (v1:List[Term],v2:List[Term]) : List[Term] = {
    (v1 zip v2).map({case (t1,t2)=>Plus(t1,t2)})
  }

  private def mkConst(name : String, index: Int) : Term ={
    FuncOf(Function(name,Some(index),Unit,Real),Nothing)
  }

  private def getLemma(name: String): Option[Lemma] = {
    val lemmaDB = LemmaDBFactory.lemmaDB
    lemmaDB.get(name)
  }

  private def removeLemma(name: String): Unit = {
    val lemmaDB = LemmaDBFactory.lemmaDB
    lemmaDB.remove(name)
  }

  private def storeLemma(pr:ProvableSig, name: String): Unit = {
    val lemmaDB = LemmaDBFactory.lemmaDB
    require(!lemmaDB.contains(name), "Lemma with name "+name+" already exists in DB")
    val evidence = ToolEvidence(immutable.List("input" -> pr.conclusion.prettyString, "output" -> "true")) :: Nil
    val id = lemmaDB.add(Lemma(pr, Lemma.requiredEvidence(pr, evidence),
      Some(name)))
    ()
  }

  private def replaceODEfree(post:Term, t:Term, ode: DifferentialProgram) : Term = {
    val consts = (StaticSemantics.freeVars(post) -- StaticSemantics.boundVars(ode)).toSet.filter(_.isInstanceOf[BaseVariable])
    consts.foldLeft(t)( (tt, c) => tt.replaceFree(c, FuncOf(Function(c.name, c.index, Unit, c.sort), Nothing)))
  }

  private def replaceODEfree(post:Term, f:Formula, ode: DifferentialProgram) : Formula = {
    val consts = (StaticSemantics.freeVars(post) -- StaticSemantics.boundVars(ode)).toSet.filter(_.isInstanceOf[BaseVariable])
    consts.foldLeft(f)( (tt, c) => tt.replaceFree(c, FuncOf(Function(c.name, c.index, Unit, c.sort), Nothing)))
  }

  // Proves SOS >= 0 by naive sum decomposition
  private val sqPos1 = remember("a_()^2 >= 0".asFormula,QE)
  private val sqPos2 = remember("a_()*a_() >= 0".asFormula,QE)
  private val plusPos = remember("a_()>=0 & b_() >=0 -> a_()+b_()>= 0".asFormula,QE)
  private def prove_sos_positive : BelleExpr = {
    SaturateTactic(OnAll(andR(1) |
    TryCatch(byUS(sqPos1), classOf[UnificationException], (ex: UnificationException) => throw new TacticInapplicableFailure("Un-unifiable with sqPos1", ex)) |
    TryCatch(byUS(sqPos2), classOf[UnificationException], (ex: UnificationException) => throw new TacticInapplicableFailure("Un-unifiable with sqPos2", ex)) |
    useAt(plusPos,PosInExpr(1::Nil))(1)))
  }

  /**
  * Old symbolic stuff that could be deleted
  */

  //Explicit symbolic expression for the determinant of a matrix
  //Currently just explicitly calculated, but can use Mathematica's det if available
  //Also, this probably doesn't actually need to be explicitly calculated everytime since we always apply it on ghost variables
  private def sym_det (m:List[List[Term]]) : Term = {
    val dim = m.length
    require(m.forall(ls => ls.length == dim), "sym_det called with non-matching dimensions.")
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
    require(m.forall(ls => ls.length == dim), "sym_trace called with non-matching dimensions.")
    List.range(0,dim).map(i=>m(i)(i)).foldLeft[Term](Number(0))(Plus.apply)
  }

  /**
    * Old implementation of sAIc -- should be deleted
    */

  //Various conversion rewrites for CE in corresponding max/min lemmas
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
      useAt(Ax.UniqIff, PosInExpr(0::Nil))(1,1::Nil) & CE(PosInExpr(0::1::Nil)) & byUS(minLem),
      namespace)

  private lazy val refAbs =
    remember("<{c& -abs(f(||))>=0}>p(||) <-> <{c&f(||)=0}>p(||)".asFormula,
      CE(PosInExpr(0::1::Nil)) & byUS(absLem),
      namespace)

  //Refine left/right of max
  private lazy val refMaxL =
    remember("<{c&f(||)>=0}>p(||) -> <{c& max(f(||),g(||))>=0}>p(||)".asFormula,
      useAt(Ax.DRd,PosInExpr(1::Nil))(1) & DW(1) & G(1) & byUS(maxLemL),
      namespace)

  private lazy val refMaxR =
    remember("<{c&g(||)>=0}>p(||) -> <{c& max(f(||),g(||))>=0}>p(||)".asFormula,
      useAt(Ax.DRd,PosInExpr(1::Nil))(1) & DW(1) & G(1) & byUS(maxLemR),
      namespace)

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
      case None => rank(ode,List(p))._1
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


  //An ADT encoding the "instruction" for the ODE tactic
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
  private def pStarHomPlus(ode: DifferentialProgram, dom:Formula, p:Term, bound: Int, context : Option[Formula]) : (Formula,Instruction,BelleExpr) = {
    p match {
      case FuncOf(f, Pair(l, r)) =>
        if (f == maxF) {
          //Encodes disjunctions
          val (lfml, linst, _) = pStarHomPlus(ode, dom, l, bound, None)
          val (rfml, rinst, _) = pStarHomPlus(ode, dom, r, bound, None)
          (Or(lfml, rfml), Disj(linst, rinst), QE)
        }
        else if (f == minF) {
          //Encodes conjunctions
          val (lfml, linst, ltac) = pStarHomPlus(ode, dom, l, bound, context)
          val (rfml, rinst, rtac) = pStarHomPlus(ode, dom, r, bound, context)
          (And(lfml, rfml), Conj(linst, rinst),
            if(context.isDefined) andR(1) <( ltac, rtac) else skip
          )
        }
        else ???
      case Neg(FuncOf(a, p)) =>
        if (a == absF) {
          //Encodes equalities
          val (prop,inst) =
            try {
              val prop = Equal(p, Number(0))
              val (pr, cofactor, rem) = findDbx(ode, dom, prop)
              (prop,Darboux(true, cofactor, pr))
            }
            catch {
              case e: ProofSearchFailure => (False, Triv())
            }

          if(context.isDefined)
          {
            val prf = proveBy(Sequent(IndexedSeq(context.get),IndexedSeq(prop)),timeoutQE)
            if(prf.isProved)
              (prop, inst, by(prf))
            else
              throw new TacticInapplicableFailure("QE failed")
          }
          else
            (prop, inst, timeoutQE)
        }
        else ???
      case _ => {
        //Encodes >=0
        val (prop,inst) =
          try {
            val prop = GreaterEqual(p, Number(0))
            val (pr, cofactor, rem) = findDbx(ode, dom, prop)
            (prop, Darboux(false, cofactor, pr))
          } catch {
            case _: ProofSearchFailure => (pStar(ODESystem(ode,True), p, Some(bound)), Strict(bound))
          }

        if(context.isDefined)
        {
          val prf = proveBy(Sequent(IndexedSeq(context.get),IndexedSeq(prop)),QE)
          if(prf.isProved)
            (prop, inst, by(prf))
          else
            throw new TacticInapplicableFailure("QE failed")
        }
        else
          (prop, inst, QE)
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
            implyRi & useAt(Ax.DRd,PosInExpr(1::Nil))(1) &
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

  //Temporary for compatibility
  //Given pr1 : a<->b , pr2 : b<->c returns provable for a<->c
  private def compose_equiv(pr1: Option[ProvableSig], pr2: Option[ProvableSig]) : Option[ProvableSig] = {
    (pr1,pr2) match {
      case (None,_) => pr2
      case (_,None) => pr1
      case (Some(pr1),Some(pr2)) => {
        val pr =useFor(pr2, PosInExpr(0 :: Nil))(Position(1, 1 :: Nil))(pr1)
        Some(pr)
      }
    }
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
    * @return closes the subgoal if P is indeed invariant, fails if P fails to normalize to f>=0 form, or if
    *         one of tactic limitations is met
    * @see Andre Platzer and Yong Kiam Tan. [[https://doi.org/10.1145/3209108.3209147 Differential equation axiomatization: The impressive power of differential ghosts]]. In Anuj Dawar and Erich Grädel, editors, Proceedings of the 33rd Annual ACM/IEEE Symposium on Logic in Computer Science, LICS'18, ACM 2018.
    */
  // was "sAIc"
  def sAIclosedPlus(bound:Int=1) : DependentPositionTactic = anon {(pos:Position,seq:Sequent) => {
    if(!(pos.isTopLevel && pos.isSucc))
      throw new IllFormedTacticApplicationException("sAIclosedPlus: position " + pos + " must point to a top-level succedent position")
    if (ToolProvider.algebraTool().isEmpty) throw new ProverSetupException("sAIclosedPlus needs an algebra tool (and Mathematica)")

    val (ode,dom,post) = seq.sub(pos) match {
      case Some(Box(sys:ODESystem,post)) => (sys.ode,sys.constraint,post)
      case Some(e) => throw new TacticInapplicableFailure("sAIc only applicable to ODEs, but got " + e.prettyString)
      case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + seq.prettyString)
    }

    val (fml1,propt1) = try {
      semiAlgNormalize(post)
    } catch {
      case ex: IllegalArgumentException => throw new TacticInapplicableFailure("sAI is unable to normalize postcondition to semi-algebraic set", ex)
    }

    val (fml,propt2) = try {
      maxMinGeqNormalize(fml1)
    } catch {
      case ex: IllegalArgumentException => throw new TacticInapplicableFailure("sAI is unable to normalize postcondition", ex)
    }

    val propt = compose_equiv(propt1,propt2)

    //This is a contract failure of maxMinGeqNormalize
    if (!fml.isInstanceOf[GreaterEqual]) throw new UnsupportedTacticFeature("Normalization failed to reach normal form "+fml)

    val f2 = fml.asInstanceOf[GreaterEqual]
    //println("Rank reordering:",rankReorder(ODESystem(ode,dom),post))

    val (pf,inst,qetac) = try {
      pStarHomPlus(ode,dom,f2.left,bound,Some(And(dom,post)))
    } catch {
      case ex: IllegalArgumentException => throw new TacticInapplicableFailure("sAI is unable to compute p*", ex)
    }

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
      //@todo always check with doIfElse vs. trycatch space compatible exception?
      starter & Idioms.doIfElse(_.subgoals.forall(s => !StaticSemantics.symbols(s(pos.top)).contains("t_".asVariable)))(
        useAt(Ax.RIclosedgeq)(pos) & andR(pos)<(
        implyR(pos) & r1 & ?(id) & timeoutQE & done, //common case?
        cohideR(pos) & composeb(1) & dW(1) & assignb(1) &
          implyR(1) & cutR(pf)(1)<(hideL(-3) & hideL(-2) & r2 & DebuggingTactics.debug("QE step",doPrint = debugTactic) & qetac & done, skip) //Don't bother running the rest if QE fails
          & cohide2(-3,1)& DebuggingTactics.debug("Finish step",doPrint = debugTactic) & implyR(1) & lpclosedPlus(inst)
      )
      ,
      DebuggingTactics.error("Inapplicable: t_ occurs")
    )
  }}

  private def simplify_mat(m:List[List[Term]]) :List[List[Term]] = {
    m.map(ls => ls.map (t => simpWithTool(ToolProvider.simplifierTool(),t)))
  }
  private def is_zero_mat(m:List[List[Term]]) : Boolean = {
    m.flatten.forall(p => p == Number(0))
  }

  //Computes and returns the sequence m, m^2, ... m^{k-1} if m^{k} = 0
  private def nilpotentIndex(m:List[List[Term]]) : Option[List[List[List[Term]]]] = {
    val dim = m.length
    require(m.forall(ls => ls.length == dim), "nilpotentIndex called with non-matching dimensions.")

    var ctr = 1
    //TODO: simplify here or later?
    var curmat = simplify_mat(m)
    val mt = curmat.transpose

    var mats = ListBuffer[List[List[Term]]]()

    while(ctr <= dim) { //k is bounded by the dimension of the matrix
      if(is_zero_mat(curmat))
        return Some(mats.toList)
      else if(ctr < dim) {
        mats += curmat
        val newmat = simplify_mat(matmat_prod(curmat, mt))
        curmat = newmat
      }
      ctr+=1
    }
    None
  }

  // Approximate coefficient of terms k in term t.
  private def coefficientOf(k:List[BaseVariable],t:Term) : (Map[BaseVariable,Term],Term,List[BaseVariable]) = {
    t match {
      // Numerical Constants
      case n:Number => (HashMap(),t,List())
      // Symbolic Constants
      case FuncOf(_,Nothing) =>  (HashMap(),t,List())
      case v:BaseVariable =>
        if(k.contains(v))
          (HashMap((v,Number(1))),Number(0),List())
        else
          (HashMap(),v,List())
      case Neg(t) =>
        val (m,tt,b) = coefficientOf(k,t)
        (m.mapValues(t => Neg(t)), Neg(tt),b)
      case Times(l,r) =>
        val (lm,lt,lb) = coefficientOf(k,l)
        val (rm,rt,rb) = coefficientOf(k,r)
        if(lm.isEmpty)
          (rm.mapValues(t => Times(lt,t)), Times(lt,rt), lb++rb)
        else if (rm.isEmpty)
          (lm.mapValues(t => Times(t,rt)), Times(lt,rt), lb++rb)
        else
          (HashMap(),Number(0), (lm.keys++rm.keys).toList++lb++rb)
      case Divide(l,r) =>
        val (lm,lt,lb) = coefficientOf(k,l)
        val (rm,rt,rb) = coefficientOf(k,r)
        if (rm.isEmpty)
          (lm.mapValues(t => Divide(t,rt)), Divide(lt,rt), lb++rb)
        else
          (HashMap(),Number(0), (lm.keys++rm.keys).toList++lb++rb)
      case Plus(l,r) =>
        val (lm,lt,lb) = coefficientOf(k,l)
        val (rm,rt,rb) = coefficientOf(k,r)
        ((lm.toList++rm.toList).groupBy(_._1).map( ff => ff._1 -> ff._2.map(_._2).reduceLeft(Plus)),Plus(lt,rt),lb++rb)
      case Minus(l,r) =>
        val (lm,lt,lb) = coefficientOf(k,l)
        val (rm,rt,rb) = coefficientOf(k,r)
        val rmneg = rm.mapValues(v => Neg(v))
        //This is fine since lm,rm keys at most intersect once
        ((lm.toList++rmneg.toList).groupBy(_._1).map( ff => ff._1 -> ff._2.map(_._2).reduceLeft(Plus)),Minus(lt,rt),lb++rb)
      /* give up for the rest of the cases:
       * Power, Differential, DifferentialSymbol, DotTerm, Nothing, Pair, UnitFunctional
       */
      case _ =>
        (HashMap(),Number(0), k)
    }
  }

  // Returns a representation in "linear" form x'=Ax+b for the given ODE if possible
  // A,b are not allowed to mention x
  def linFormODE(p:DifferentialProgram) : Option[(List[List[Term]],List[Term],List[BaseVariable])] = {
    // flattened ODE
    val flat = DependencyAnalysis.collapseODE(p)
    val kv = flat.mapValues( t => coefficientOf(flat.keys.toList,t) )

    //Turn kv into x'=Ax+b form
    //Canonize variable order
    val vars = kv.keys.toList.sortBy(f => f.toString)
    if (vars.exists( v => kv(v)._3.nonEmpty)) return None

    val A = vars.map( v => vars.map( vv =>  kv(v)._1 getOrElse (vv,Number(0))))
    val b = vars.map( v => kv(v)._2)
    Some(A,b,vars)
  }

  private def factorial(i:Int) : Int ={
    if (i <= 1) 1
    else i* factorial(i-1)
  }

  private def timeSeries(time:Term, ls:List[List[Term]]) : List[Term] = {
    ls.zipWithIndex.map(
      f =>
        f._1.map(t =>
          if (f._2==0) t
          else Times(t,Divide(Power(time,Number(f._2)),Number(factorial(f._2)))))
    ).reduce(vecvec_sum)
  }

  /** Given a top-level succedent position corresponding to [x'=f(x)&Q]P
    * with x'=f(x) a linear, nilpotent ODE
    *
    * Adds the (polynomial) solution x=Phi(x_0,t) of that ODE to the domain constraint
    *
    * --- QE
    * Q(Phi(x_0,t)), t>=0 |- P(Phi(x_0,t))
    * --- (only continues if solveEnd = true)
    * G,x=x_0, t=0 |-  [x'=f(x),t'=1& Q&t>=0& x=Phi(x_0,t)]P
    * --------------- (nilpotent solve)
    * G |- [x'=f(x)&Q]P
    *
    * @param solveEnd whether to continue with weaken and QE (see rule rendition above)
    * @return See the rule rendition above
    *         Special failure cases:
    *         1) Linearity heuristic checks fail e.g.: x'=1+x^2-x^2 will be treated as non-linear even though it is really linear
    *
    */
  // TODO: hacky communication of global time marker for nilpotentSolve
  val nilpotentSolveTimeVar = "time_".asVariable

  def nilpotentSolve(solveEnd : Boolean) : DependentPositionTactic = anon ((pos:Position,seq:Sequent) => {
    if(!(pos.isTopLevel && pos.isSucc))
      throw new IllFormedTacticApplicationException("nilpotent solve: position " + pos + " must point to a top-level succedent position")

    val (ode,dom,post) = seq.sub(pos) match {
      case Some(Box(sys:ODESystem,post)) => (sys.ode,sys.constraint,post)
      case Some(e) => throw new TacticInapplicableFailure("nilpotentSolve only applicable to box ODEs, but got " + e.prettyString)
      case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + seq.prettyString)
    }

    if (StaticSemantics.symbols(dom).exists(_.name == nilpotentSolveTimeVar.name))
      throw new IllFormedTacticApplicationException("nilpotent solve should not be called twice (solution already available from prior call)")

    val t = TacticHelper.freshNamedSymbol(nilpotentSolveTimeVar, seq)
    //Introduce a ghost variable

    val linForm = linFormODE(ode)
    if (linForm.isEmpty) throw new TacticInapplicableFailure("ODE " + ode + " could not be put into linear form x'=Ax")
    val (m, b, x) = linForm.get

    val npopt = nilpotentIndex(m)

    if (npopt.isEmpty) throw new TacticInapplicableFailure("Coefficient matrix for " + ode + " is not nilpotent.")
    val np = npopt.get

    val bsimp = b.map(t => simpWithTool(ToolProvider.simplifierTool(), t))

    val oldx = x.map(TacticHelper.freshNamedSymbol(_, seq))

    // Introduce the initial values x0
    val storeInitialVals =
      x.zip(oldx).map(v => discreteGhost(v._1, Some(v._2))('Rlast)).reduceOption[BelleExpr](_ & _).getOrElse(skip)

    // Partial solutions
    val sp = np.map(m => matvec_prod(m, oldx))

    //Forcing terms on partial solutions for x',x'',...
    val sb = bsimp :: np.map(m => matvec_prod(m, bsimp))

    // Actual solution
    val s = (oldx :: sb.zip(sp).map(f => vecvec_sum(f._1, f._2))) ++ List(sb.last)

    // LHS of partial solutions
    val sL =
      x :: np.map(m => matvec_prod(m, x)).zip(sb).map(f => vecvec_sum(f._1, f._2).map(t => simpWithTool(ToolProvider.simplifierTool(), t)))

    //The actual solution
    val sol = timeSeries(t, s).map(t => simpWithTool(ToolProvider.simplifierTool(), t))

    val cut = And(GreaterEqual(t, Number(0)), x.zip(sol).map(f => Equal(f._1, f._2)).reduceRight(And))

    val cutPrep = Range(0, s.length).map(i => timeSeries(t, s.drop(i)).map(t => simpWithTool(ToolProvider.simplifierTool(), t)))

    val cuts = sL.zip(cutPrep).tail.map(
      ff =>
        ff._1.zip(ff._2).collect({
          case f if f._1 != f._2 => Equal(f._1, f._2)
        }
        ).reduce(And)
    ) //.map( f => replaceODEfree(f,DifferentialProduct(AtomicODE(DifferentialSymbol(t),Number(1)),ode)))

    val start =
      if (solveEnd)
        diffUnpackEvolutionDomainInitially(pos)
      else
        skip

    val finish =
      if (solveEnd)
        ?(diffWeakenPlus('Rlast) & //todo: dW repeats storing of initial values which isn't very useful here
          andL('Llast) & andL('Llast) & //Last three assumptions should be Q, timevar>=0, solved ODE equations
          SaturateTactic(andL('Llast)) & //Splits conjunction of equations up
          SaturateTactic(exhaustiveEqL2R(true)('Llast)) & //rewrite
          timeoutQE & done)
      else
        skip

    start &
      HilbertCalculus.DGC(t, Number(1))(pos) &
      existsR(Number(0))(pos) &
      //NOTE: At this point, the box question is guaranteed to be 'Rlast because existR reorders succedents
      //If existsR is changed, all the 'Rlast should turn back into pos instead
      storeInitialVals &
      dC(cut)('Rlast) < (
      finish,
      // dRI directly is actually a lot slower than the dC chain even with naive dI
      // dRI('Rlast)
      cuts.foldLeft[BelleExpr](skip)((t, f) => dC(f)('Rlast) < (t, diffInd('full)('Rlast))) & diffInd('full)('Rlast)

      // this does the "let" once rather than on every dI -- doesn't help speed much
      //Dconstify(
      //  cuts.foldLeft(skip)( (t,f) => dC(f)('Rlast) < (t, dI('diffInd)('Rlast)
      //  <( QE , cohideOnlyR('Rlast) & SaturateTactic(Dassignb(1)) & QE )) ) &
      //    dI('diffInd)('Rlast)<( QE, cohideOnlyR('Rlast) & SaturateTactic(Dassignb(1)) & QE ))('Rlast)
    )
  })

  /** Implements the differential divide-and-conquer rule (with 3 premises)
    * The input is a polynomial p.
    * The branches marked (*) are closed automatically, assuming p is a Darboux polynomial
    * @see Andrew Sogokon, Khalil Ghorbal, Paul B. Jackson and André Platzer. [[https://doi.org/10.1007/978-3-662-49122-5_13]].
    *
    * G, p=0 -> [x'=f(x)&Q] p=0  (*)
    * G, p>0 -> [x'=f(x)&Q] p>0  (* - @todo: note redundancy, could just prove [x'=f(x)&Q]p!=0)
    * G, p<0 -> [x'=f(x)&Q] p<0  (* - see above )
    *
    * G, p=0 -> [x'=f(x)&Q & p=0] P
    * G, p>0 -> [x'=f(x)&Q & p>0] P
    * G, p<0 -> [x'=f(x)&Q & p<0] P
    * --------------- (DDC)
    * G |- [x'=f(x)&Q]P
    *
    * @param p the DDC polynomial
    * @return See the rule rendition above
    */

  private lazy val trichotomy = remember("f_()=0 | (f_() > 0 | f_() < 0)".asFormula, QE, namespace)

  def diffDivConquer(p : Term, cofactor : Option[Term] = None) : DependentPositionTactic = anon ((pos:Position,seq:Sequent) => {
    if(!(pos.isTopLevel && pos.isSucc))
      throw new IllFormedTacticApplicationException("diffDivConquer: position " + pos + " must point to a top-level succedent position")

    val (ode,dom,post) = seq.sub(pos) match {
      case Some(Box(sys:ODESystem,post)) => (sys.ode,sys.constraint,post)
      case Some(e) => throw new TacticInapplicableFailure("diffDivConquer only applicable to box ODEs, but got " + e.prettyString)
      case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + seq.prettyString)
    }

    val zero = Number(0)
    val dbx = cofactor match {
      case None => dgDbxAuto(pos)
      case Some(cof) => dgDbx(cof)(pos)
    }

    cutR(Or(Equal(p,zero),Or(Greater(p,zero),Less(p,zero))))(pos) <(
      cohideR(pos) &byUS(trichotomy),
      implyR(pos) & orL('Llast) <(
        /* p = 0*/
        dC(Equal(p,zero))(pos) <(skip, dbx),
        /* p > 0 | p < 0 */
        orL('Llast) <(
          dC(Greater(p,zero))(pos) <(skip, dbx),
          dC(Less(p,zero))(pos) <(skip, dbx)
        )
      )
    )
  })

  lazy val dCClosure = DifferentialTactics.dCClosure(true)

  /** Given a top-level succedent position corresponding to [x'=f(x)&Q]P
    *
    * G|-P  Q,Q*,P |- P*   Q,Q-*, !P |- (!P)-*
    * --------------- (sAI)
    * G |- [x'=f(x)&Q]P
    *
    * @return closes the subgoal if P is indeed invariant,
    * @see Andre Platzer and Yong Kiam Tan. [[https://doi.org/10.1145/3209108.3209147 Differential equation axiomatization: The impressive power of differential ghosts]]. In Anuj Dawar and Erich Grädel, editors, Proceedings of the 33rd Annual ACM/IEEE Symposium on Logic in Computer Science, LICS'18, ACM 2018.
    */
  def sAI : DependentPositionTactic = anon ((pos:Position,seq:Sequent) => {
    if(!(pos.isTopLevel && pos.isSucc))
      throw new IllFormedTacticApplicationException("sAI: position " + pos + " must point to a top-level succedent position")
    if (ToolProvider.algebraTool().isEmpty) throw new ProverSetupException("sAI needs an algebra tool (and Mathematica)")

    val (sys,post) = seq.sub(pos) match {
      case Some(Box(sys:ODESystem,post)) => (sys,post)
      case Some(e) => throw new TacticInapplicableFailure("sAI only applicable to box ODEs, but got " + e.prettyString)
      case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + seq.prettyString)
    }

    //todo: robustness against s_, t_, fv_* appearing in model
    val svar = BaseVariable("s_")
    val tvar = BaseVariable("t_")

    val atoms = AtomicODE(DifferentialSymbol(tvar),Number(1))::atomicListify(sys.ode)
    val oldnames = atoms.map(p => p.xp.x)
    val newnames = (1 to atoms.length).map( i => BaseVariable("fv_",Some(i)))
    val nameszip = oldnames zip newnames
    val ipost = Not(Imply(And(sys.constraint,Or(post,Equal(tvar,svar))) ,Imply(Equal(tvar,svar), post)))
    val renfvipost = nameszip.foldLeft(ipost : Formula)( (tt, c) => tt.replaceFree(c._1,c._2))

    val eqs = nameszip.map(c => Equal(c._1,c._2)).reduceRight(And)
//    val dfml = Diamond(
//      ODESystem(DifferentialProduct(AtomicODE(DifferentialSymbol(tvar),Number(1)),sys.ode),
//        And(sys.constraint,Or(post,Equal(tvar,svar)))
//      ),eqs)
    //val cutfml = newnames.foldLeft(And(renfvipost,dfml):Formula)( (f,c) => Exists(c::Nil,f))
    val dfml = Diamond(
          ODESystem(DifferentialProduct(AtomicODE(DifferentialSymbol(tvar),Number(1)),sys.ode),
            And(sys.constraint,Or(post,Equal(tvar,svar)))
          ),And(eqs,renfvipost))
    val cutfml = newnames.foldLeft(dfml:Formula)( (f,c) => Exists(c::Nil,f))

    val barcantac =
      (0 to atoms.length-1).map( List.fill(_)(0)).foldLeft(skip:BelleExpr)( (p,t) =>
        useAt(dBarcan)(1,t) & p
      )

    val existstac = oldnames.foldLeft(skip:BelleExpr) ( (p,t) =>
      existsR(t)(1) & p
    )

    val dadj = getDiffAdjInst(atoms)

    //P
    val (pfml,pfmlpropt) = try {
      semiAlgNormalize(post)
    } catch {
      case ex: IllegalArgumentException => throw new TacticInapplicableFailure("Unable to normalize postcondition to semi-algebraic set", ex)
    }

    //P*
    val (pstarpf, pstarinst) = try {
      fStar(sys,pfml)
    } catch {
      case ex: IllegalArgumentException => throw new TacticInapplicableFailure("Unable to generate formula f*", ex)
    }

    // Normalizes the postcondition appearing in local progress
    val ptac = pfmlpropt match {
      case None => skip
      case Some(pr) => useAt(pr)(1,0::1::0::Nil)
    }

    //!Q
    val (nqfml,nqfmlpropt) = try {
      semiAlgNormalize(Not(sys.constraint))
    } catch {
      case ex: IllegalArgumentException => throw new TacticInapplicableFailure("Unable to normalize postcondition to semi-algebraic set", ex)
    }

    //(!Q)*
    val (nqstarpf,nqstarinst) = try {
      fStar(sys,nqfml)
    } catch {
      case ex: IllegalArgumentException => throw new TacticInapplicableFailure("Unable to generate formula f* for f: "+nqfml, ex)
    }

    // Normalizes the postcondition appearing in local progress
    val nqtac = nqfmlpropt match {
      case None => skip
      case Some(pr) => useAt(pr,PosInExpr(1::Nil))(-2,0::1::0::Nil)
    }

    // <ODE & !Q> O
    val nqlp = Diamond(ODESystem(DifferentialProduct(AtomicODE(DifferentialSymbol(tvar),Number(1)),sys.ode),Or(nqfml,Equal(tvar,svar))),NotEqual(tvar,svar))
    // <ODE & Q>o
    val qlpi = Diamond(ODESystem(DifferentialProduct(AtomicODE(DifferentialSymbol(tvar),Number(1)),sys.ode),sys.constraint),NotEqual(tvar,svar))

    //Renamed
    val revodeList = atoms.map{ case AtomicODE(x,rhs) => AtomicODE(x, Neg(rhs))}
    val revode = revodeList.reduce(DifferentialProduct.apply)
    val revsys = nameszip.foldLeft(ODESystem(revode,sys.constraint):Program)( (tt, c) => tt.replaceAll(c._1,c._2)).asInstanceOf[ODESystem]

    val renpost = nameszip.foldLeft(post : Formula)( (tt, c) => tt.replaceFree(c._1,c._2))
    val rendom = revsys.constraint
    //Use to strengthen after dadj
    val revMon = Diamond(ODESystem(revsys.ode,And(revsys.constraint,Or(renpost,Equal(newnames.head,svar)))), NotEqual(newnames.head,svar))

    //!P
    val (npfml,npfmlpropt) = try {
      semiAlgNormalize(Not(renpost))
    } catch {
      case ex: IllegalArgumentException => throw new TacticInapplicableFailure("Unable to normalize postcondition to semi-algebraic set", ex)
    }

    //(!P)-*
    val (nprstarpf,nprstarinst) = try {
      fStar(revsys,npfml)
    } catch {
      case ex: IllegalArgumentException => throw new TacticInapplicableFailure("Unable to generate formula f*", ex)
    }

    // Normalizes the negated postcondition appearing in local progress
    val nptac = npfmlpropt match {
      case None => skip
      case Some(pr) => useAt(pr,PosInExpr(1::Nil))(-2,0::1::0::Nil)
    }

    //!Q
    val (rennqfml,rennqfmlpropt) = try {
      semiAlgNormalize(Not(rendom))
    } catch {
      case ex: IllegalArgumentException => throw new TacticInapplicableFailure("Unable to normalize postcondition to semi-algebraic set", ex)
    }

    //(!Q)-*
    val (rennqrstarpf,rennqrstarinst) = try {
      fStar(revsys,rennqfml)
    } catch {
      case ex: IllegalArgumentException => throw new TacticInapplicableFailure("Unable to generate formula f*", ex)
    }

    // Normalizes the postcondition appearing in local progress
    val rennqtac = rennqfmlpropt match {
      case None => skip
      case Some(pr) => useAt(pr,PosInExpr(1::Nil))(-2,0::1::0::Nil)
    }

    // <-ODE & !Q> O
    val rennqrlp = Diamond(ODESystem(revsys.ode,Or(rennqfml,Equal(newnames.head,svar))),NotEqual(newnames.head,svar))
    // <-ODE & !P> O
    val nprlp = Diamond(ODESystem(revsys.ode,Or(npfml,Equal(newnames.head,svar))),NotEqual(newnames.head,svar))

    // Can skip the O -> o step for forward branch if there are no equalities in domain
    val skipLock = domainEqualities(sys.constraint).isEmpty

    useAt(Ax.RI)(pos) & allR(pos) &
      useAt(and_imp,PosInExpr(0::Nil))(pos++PosInExpr(1::1::Nil)) &
      useAt(imp_and,PosInExpr(0::Nil))(pos++PosInExpr(1::Nil)) & boxAnd(pos) & andR(pos) <(
      cutR(Or(Equal(tvar,svar),NotEqual(svar,tvar)))(pos) <(
        cohideR(pos) & QE,
        //implyR moves succedent to 'Rlast
        implyR(pos) & orL('Llast) <(
          //initial branch
          useAt(Ax.DCC, PosInExpr(1::Nil))('Rlast) & andR('Rlast)<(
            timeBound('Rlast),
            cohideOnlyR('Rlast) & cohideOnlyL('Llast) &
            dC(GreaterEqual(tvar,svar))(1) <(
              DW(1) & G(1) & implyR(1) & implyR(1) &
              andL(-1) & hideL(-2) &
              dC(Greater(tvar,svar))(1) <(
                DW(1) & G(1) & implyR(1) & andL(-1) & hideL(-1) & QE,
                DifferentialTactics.dI(1)
              ),
              DifferentialTactics.dI(1)
            )
          ),
          //backwards branch
          DW('Rlast) & useAt(Ax.box,PosInExpr(1::Nil))('Rlast) & notR('Rlast) &
          cutL(cutfml)('Llast) <(
            (existsL('Llast) * newnames.length) &
              useAt(Ax.pVd)('Llast) & andL('Llast) &
              notL('Llast) & useAt(dadj)('Llast) &
              cutL(revMon)('Llast) <(
                implyR('Rlast) & andL('Llast) & hideL('Llast) &
                cut(Or(nprstarpf,rennqrstarpf)) <(
                  //Cleanup the sequent
                  (hideL(-1) * seq.ante.length) & // hide original antecedents
                  hideL(-1) & // hide s_!=t_
                  cohideOnlyR('Rlast) & //hide all succedents
                  hideL(-2) & // hide domain
                  useAt(Ax.UniqIff,PosInExpr(1::Nil))(-1) & andL(-1) &
                  implyR(1) & exchangeL(-1,-4) & exchangeL(-3,-4) & orL(-3) <(
                    //(!P)-* branch
                    cutR(nprlp)(1) <(
                      hideL(-4) & lpgen(nprstarinst),
                      hideL(-1) & hideL(-1) & hideL(-1) & implyR(1) & nptac &
                      andLi & useAt(Ax.UniqIff, PosInExpr(0 :: Nil))(-1) &
                      diamondd(-1) & hideR(1) & notL(-1) & DW(1) & G(1) & useAt(Ax.notNotEqual)(1,1::Nil) &
                        implyR(1) & andL(-1) & orL(-1) <(orL(-2) <(notL(-2) & id,id), id)
                    ),
                    //(!Q)-* branch
                    cutR(rennqrlp)(1) <(
                      hideL(-4) & lpgen(rennqrstarinst),
                      hideL(-1) & hideL('Llast) &  hideL('Llast) & implyR(1) & rennqtac &
                      andLi & useAt(Ax.UniqIff, PosInExpr(0 :: Nil))(-1) &
                      diamondd(-1) & hideR(1) & notL(-1) & DW(1) & G(1) & useAt(Ax.notNotEqual)(1,1::Nil) &
                      implyR(1) & andL(-1) & orL(-2) <( notL(-2) & id, id)
                    )
                  ),
                  ToolTactics.hideNonFOL & ?(QE & done)
                )
                ,
                //useAt(Ax.UniqIff,PosInExpr(1::Nil))('Llast),
                cohideOnlyL('Llast) & cohideOnlyR('Rlast) & useAt(Ax.Kd,PosInExpr(1::Nil))(1) &
                dW(1) & QE // todo: can do manually
              )

            ,
            cohideR('Rlast) & implyR(1) & barcantac &
            mond & existstac & andR(1) <(cohideR(1) & QE,id) // todo: maybe prove manually
          )
        )
      ),
      dW(pos) & andL(-1) & hideL(-2) & implyR(1) & implyR(1) & implyR(1) &
        ptac & cutR(Or(pstarpf,nqstarpf))(1) <(
        ToolTactics.hideNonFOL & ?(QE & done), //prove P* | (!Q)* from assumptions
        (if (skipLock) skip
        else {
        cutL(qlpi)('Llast) <(skip,
          cohideOnlyR('Rlast) &  useAt(Ax.DRd,PosInExpr(1::Nil))(1) &
          dC(Imply(Equal(tvar,svar),sys.constraint))(1) <(
            DW(1) & G(1) &
              implyR(1) & andL(-1) &
              orL(-1) <(id, implyL(-2) <(id,id)),
            useAt(Ax.DCC, PosInExpr(1::Nil))(1) & andR(1) <(cohideOnlyL(-1) & timeBound(1),
              dC(GreaterEqual(tvar,svar))(1) <(
                DW(1) & G(1) & implyR(1) & implyR(1) &
                andL(-1) & hideL(-2) &
                  dC(Greater(tvar,svar))(1) <(
                    DW(1) & G(1) & implyR(1) & andL(-1) & hideL(-1) & QE,
                    DifferentialTactics.dI(1)
                  ),
                cohideOnlyL(-2) & DifferentialTactics.dI(1)))
           )
        ) }) &
        implyR(1) & orL('Llast) <(
          // P* branch
          hideL(-3) & hideL(-1) & // set up into shape expected by lpgen
            lpgen(pstarinst),
          hideL(-3) & hideL(-1) & cutR(nqlp)(1) <(
            lpgen(nqstarinst),
            hideL(-1) & hideL('Llast) & implyR(1) & nqtac & andLi & useAt(Ax.UniqIff, PosInExpr(0 :: Nil))(-1) &
              diamondd(-1) & hideR(1) & notL(-1) & DW(1) & G(1) & useAt(Ax.notNotEqual)(1,1::Nil) &
              implyR(1) & andL(-1) &
              (if(skipLock) orL(-1) <( orL(-2) <(notL(-2) & id,id), id)
              else orL(-2) <( notL(-2) & id, id))
          )
        ))
    )
  })

  private val and_imp = remember("p() & q() <-> p() & (p() -> q())".asFormula,prop)
  private val imp_and = remember("(r() -> p() & q()) <-> ((r() -> p()) & (r() -> q()))".asFormula,prop)
  private val not_imp = remember("!(p() -> q()) <-> (p() & !q())".asFormula,prop)

  //todo: move to Ax.scala
  private lazy val dBarcan = proveBy("\\exists x_ <a{|^@x_|};>p(||) <-> <a{|^@x_|};>\\exists x_ p(||)".asFormula,
    diamondd(1,1::Nil) &
    diamondd(1,0::0::Nil) &
    useAt(Ax.existsDual,PosInExpr(1::Nil))(1,0::Nil) &
    useAt(Ax.doubleNegation)(1,0::0::0::Nil) &
    useAt(Ax.notExists)(1,1::0::1::Nil) & //@todo substitution clash
    useAt(Ax.barcan)(1,1::0::Nil) &
    byUS(Ax.equivReflexive)
  )

  private def getDiffAdjInst(odels:List[AtomicODE]) : ProvableSig = {

    val dim = odels.length
    val diffadj = Provable.diffAdjoint(dim)

    // @TODO: this very manually applies the uniform renaming part, since it's not automated elsewhere yet (?)
    // would also be much cleaner if one could access the renaming part more easily.
    val dadjlhs = (1 to dim).map( i => BaseVariable("x_", Some(i)))
    val lhs = odels.map(_.xp.x)  // variables in the ODE
    val diffadjren = (lhs zip dadjlhs).foldLeft(diffadj)( (acc,bv) => acc(URename(bv._1,bv._2,semantic=true)) )

    ElidingProvable(diffadjren)
  }


}
