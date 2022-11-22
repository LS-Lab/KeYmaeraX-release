package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.{InfiniteTacticLoopError, _}
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms._
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.AnonymousLemmas._
import edu.cmu.cs.ls.keymaerax.btactics.PropositionalTactics.prop
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.btactics.macros.DerivationInfoAugmentors._
import edu.cmu.cs.ls.keymaerax.lemma.Lemma
import edu.cmu.cs.ls.keymaerax.btactics.macros.{ProvableInfo, Tactic}

import scala.collection.immutable._

/**
  * Note: this is meant to be a watered down version of SimplifierV2
  * Goals: Faster, more predictable and customizable
  *
  * Given a list of rewriting axioms, this traverses a term/formula bottom up and exhaustively tries the list of axioms
  * at each step
  *
  * The rewriting axioms must have the form |- t = t' |- f -> t = t' or similarly for formulas and <->
  *
  * Created by yongkiat on 12/19/16.
  */

object SimplifierV3 {

  private val namespace = "simplifierv3"

  private val pA = PredOf(Function("A_", None, Unit, Bool), Nothing)
  private val pB = PredOf(Function("B_", None, Unit, Bool), Nothing)
  private val pP = PredOf(Function("P_", None, Unit, Bool), Nothing)
  private val pQ = PredOf(Function("Q_", None, Unit, Bool), Nothing)
  private val pF = PredOf(Function("F_", None, Unit, Bool), Nothing)
  private val pFF = PredOf(Function("FF_", None, Unit, Bool), Nothing)
  private val pFFF = PredOf(Function("FFF_", None, Unit, Bool), Nothing)
  private val pL = PredOf(Function("L_", None, Unit, Bool), Nothing)
  private val pLL = PredOf(Function("LL_", None, Unit, Bool), Nothing)
  private val pR = PredOf(Function("R_", None, Unit, Bool), Nothing)
  private val pRR = PredOf(Function("RR_", None, Unit, Bool), Nothing)
  private val fL = FuncOf(Function("L_", None, Unit, Real), Nothing)
  private val fLL = FuncOf(Function("LL_", None, Unit, Real), Nothing)
  private val fR = FuncOf(Function("R_", None, Unit, Real), Nothing)
  private val fRR = FuncOf(Function("RR_", None, Unit, Real), Nothing)
  private val fF = FuncOf(Function("F_", None, Unit, Real), Nothing)
  private val fFF = FuncOf(Function("FF_", None, Unit, Real), Nothing)
  private val fFFF = FuncOf(Function("FFF_", None, Unit, Real), Nothing)

  /** Term simplifier */

  /**
    * Lemmas used internally by term simplifier
    */
  private def termAx(ctor:(Term,Term)=>Term) : (ProvableSig,ProvableSig,ProvableSig) = {
    val limp = "A_() -> (L_() = LL_())".asFormula
    val rimp = "B_() -> (R_() = RR_())".asFormula
    val lhs = ctor("L_()".asTerm,"R_()".asTerm)
    val lAx = remember(Imply(limp,Imply( "A_()".asFormula ,Equal(lhs, ctor("LL_()".asTerm,"R_()".asTerm)))),
      prop & exhaustiveEqL2R(Find.FindLPlain("L_()=LL_()".asFormula)) & cohideR(1) & byUS(Ax.equalReflexive), namespace).fact
    val rAx = remember(Imply(rimp,Imply( "B_()".asFormula ,Equal(lhs, ctor("L_()".asTerm,"RR_()".asTerm)))),
      prop & exhaustiveEqL2R(Find.FindLPlain("R_()=RR_()".asFormula)) & cohideR(1) & byUS(Ax.equalReflexive), namespace).fact
    val lrAx = remember(Imply(And(limp,rimp),Imply( "A_() & B_()".asFormula ,Equal(lhs, ctor("LL_()".asTerm,"RR_()".asTerm)))),
      prop & exhaustiveEqL2R(Find.FindLPlain("L_()=LL_()".asFormula)) & exhaustiveEqL2R(Find.FindLPlain("R_()=RR_()".asFormula)) & cohideR(1) & byUS(Ax.equalReflexive), namespace).fact
    (lAx,rAx,lrAx)
  }

  /**
    *   Walks a pair and applies the given function everywhere, remembering where it applied that function
    *   Used for predicate arguments and formula arguments
    */
  private def pairWalk[A](t: Term, fn: Term => (Term,A), prefix :List[Int] = List[Int]()): (Term,List[(A,List[Int])]) = t match {
    case Pair(a,b) =>
      val (aa,l) = pairWalk(a,fn,0::prefix)
      val (bb,r) = pairWalk(b,fn,1::prefix)
      (Pair(aa,bb),l++r)
    case a =>
      val (aa,l) = fn(a)
      (aa,List((l,prefix.reverse)))
  }

  private lazy val plusAxs = termAx(Plus.apply)
  private lazy val minusAxs = termAx(Minus.apply)
  private lazy val timesAxs = termAx(Times.apply)
  private lazy val divAxs = termAx(Divide.apply)
  private lazy val powAxs = termAx(Power.apply)
  private lazy val negAx = remember( "(A_() -> (L_() = LL_())) -> A_() -> (-L_() = -LL_())".asFormula,
    prop & exhaustiveEqL2R(Find.FindLPlain("L_()=LL_()".asFormula)) & cohideR(1) & byUS(Ax.equalReflexive), namespace).fact

  private lazy val equalTrans = remember("(P_() -> (F_() = FF_())) & (Q_() -> (FF_() = FFF_())) -> (P_() & Q_() -> (F_() = FFF_())) ".asFormula,
    prop & exhaustiveEqL2R(Find.FindLPlain("F_()=FF_()".asFormula)) & exhaustiveEqL2R(Find.FindLPlain("FF_()=FFF_()".asFormula)) & cohideR(1) & byUS(Ax.equalReflexive), namespace).fact

  /**
    * An index is a function from a term/formula and the current formula context (i.e., assumptions)
    * to a list of simplification lemmas to try on that term/formula
    * TODO: think more about the type used to represent the current context
    */
  type context = Set[Formula]
  type termIndex = (Term,context) => List[ProvableSig]
  type formulaIndex = (Formula,context) => List[ProvableSig]

  lazy val emptyCtx = HashSet[Formula]()

  def composeIndex[A<:Expression] (is:((A,context) => List[ProvableSig])*)
                                 (f:A,ctx:context) : List[ProvableSig] = is.flatMap(axs => axs(f,ctx)).toList

  /**
    * Dependent term simplification workhorse
    * Given provable A -> (t = t') or (t = t'), a context, and a term x,
    * Checks if x unifies with t,
    * If applicable, checks for the A[unif] in the context
    * Then unifies the conclusion appropriately
    * Note: can avoid unifying again in the proof?
    */
  private def applyTermProvable(t:Term, ctx:context, pr:ProvableSig) : Option[(Term,Formula,ProvableSig)] = {
    //todo: Add some kind of unification search? (that precludes fast HashSet lookups though)
    pr.conclusion.succ(0) match {
      case Imply(prem,Equal(k,v)) => {
        val unif = try { UnificationMatch(k,t) } catch { case e:UnificationException => return None}
        val uprem = unif(prem)
        if(ctx.contains(uprem)){
          val concl = unif(v)
          //@todo construct substitution
          val proof = ProvableSig.startPlainProof(Imply(uprem,Equal(t,unif(v))))(byUS(pr), 0)
          //assert(proof.isProved)
          Some(concl,uprem,proof)
        }
        else None
      }
      case Equal(k,v) => {
        val unif = try { UnificationMatch(k,t) } catch { case _: UnificationException => return None}
        val concl = unif(v)
        //@todo construct substitution
        val proof = ProvableSig.startPlainProof(Imply(True, Equal(t, unif(v))))(ImplyRight(SuccPos(0)), 0)(CoHideRight(SuccPos(0)), 0)(byUS(pr), 0)
        //assert(proof.isProved)
        Some(concl,True,proof)
      }
      case _ => ??? //Illegal shape of rewrite
    }
  }

  /**
    * Term simplification of term t to term s
    * @param t term to simplify
    * @param ctx current context (assumptions)
    * @param taxs the term index
    * @return the simplified term s and an optional provable containing (premise,proof of premise->s=t) only if
    *         some simplification was applied.
    *         premise is an assumption in contained in ctx
    */
  def termSimp(t: Term, ctx: context, taxs: termIndex ): (Term, Option[(Formula,ProvableSig)]) = {
    val (rect,recpropt) =
      t match {
        case bop: BinaryCompositeTerm =>
          //todo: Doesn't work with pairs
          val (lf, lpropt) = termSimp(bop.left, ctx, taxs)
          val (rf, rpropt) = termSimp(bop.right, ctx, taxs)
          val concl = bop.reapply(lf, rf)
          val lem = bop match {
            case Plus(_, _) => plusAxs
            case Minus(_, _) => minusAxs
            case Times(_, _) => timesAxs
            case Divide(_, _) => divAxs
            case Power(_, _) => powAxs
          }

          (lpropt, rpropt) match {
            case (None, None) => (t, None)
            case (Some((lprem, lpr)), None) =>
              assert(rf==bop.right, "Missing proof: simplified r=" + bop.right.prettyString + " to " + rf.prettyString + ", but got no proof")
              val fml = Imply(lprem, Equal(t, concl))
              val subst = USubst(List(SubstitutionPair(pA, lprem), SubstitutionPair(fL, bop.left), SubstitutionPair(fLL, lf), SubstitutionPair(fR, bop.right)))
              val pr = ProvableSig.startPlainProof(fml)(CEat(lem._1(subst), PosInExpr(1 :: Nil))(SuccPos(0)), 0)(lpr, 0)
              (concl, Some((lprem, pr)))
            case (None, Some((rprem, rpr))) =>
              assert(lf==bop.left, "Missing proof: simplified l=" + bop.left.prettyString + " to " + lf.prettyString + ", but got no proof")
              val fml = Imply(rprem, Equal(t, concl))
              val subst = USubst(List(SubstitutionPair(pB, rprem), SubstitutionPair(fL, bop.left), SubstitutionPair(fR, bop.right), SubstitutionPair(fRR, rf)))
              val pr = ProvableSig.startPlainProof(fml)(CEat(lem._2(subst), PosInExpr(1 :: Nil))(SuccPos(0)), 0)(rpr, 0)
              (concl, Some((rprem, pr)))
            case (Some((lprem, lpr)), Some((rprem, rpr))) =>
              val premise = And(lprem, rprem)
              val fml = Imply(premise, Equal(t, concl))
              val subst = USubst(List(SubstitutionPair(pA, lprem), SubstitutionPair(pB, rprem), SubstitutionPair(fL, bop.left), SubstitutionPair(fLL, lf), SubstitutionPair(fR, bop.right), SubstitutionPair(fRR, rf)))
              val pr = ProvableSig.startPlainProof(fml)(CEat(lem._3(subst), PosInExpr(1 :: Nil))(SuccPos(0)), 0)(AndRight(SuccPos(0)), 0)(rpr, 1)(lpr, 0)
              (concl, Some((premise, pr)))
          }
        case Neg(u) =>
          //todo: It is not sound to go under a differential if there is context (x=0 |-/- x' = 0'
          //tactic needs to throw away the context if it wants to go under one
          val (ut,upropt) = termSimp(u,ctx,taxs)
          val nt = Neg(ut)
          upropt match {
            case None => (t,None)
            case Some((uprem,upr)) =>
              val fml = Imply(uprem,Equal(t,nt))
              val subst = USubst(List(SubstitutionPair(pA, uprem), SubstitutionPair(fL, u), SubstitutionPair(fLL, ut)))
              (nt,Some((uprem, ProvableSig.startPlainProof(fml)(CEat(negAx(subst), PosInExpr(1 :: Nil))(SuccPos(0)), 0)(upr, 0))))
          }

        case FuncOf(fn, c) if c != Nothing =>
          val (nArgs,proofs) = pairWalk(c,
            t=> termSimp(t,ctx,taxs))
          val nt = FuncOf(fn, nArgs)
          val premise = proofs.map({ case (None,_) => True case (Some(pr),_) => pr._1}).reduceRight(And)
          val cuts = proofs.zipWithIndex.map({
            case ((None,_),_) => ident
            case ((Some(prf),_),i) => CEat(prf._2, PosInExpr(1::Nil))(-(i+1)) andThen eqL2R(-(i+1))(1)
          }).foldLeft(_: ProvableSig)({ case (p, t) => p(t, 0) })
          val subst = USubst(List(SubstitutionPair(FuncOf(Function("s_", None, Unit, Real), Nothing), nt)))
          val pr = ProvableSig.startPlainProof(Imply(premise,Equal(t,nt)))(
            ImplyRight(SuccPos(0)), 0)(
            times(andL('Llast), proofs.length-1), 0)(
            cuts, 0)(
            cohideR(SuccPos(0)), 0)(
            Ax.equalReflexive.provable(subst), 0)
          (nt,Some(premise,pr))
        //todo: Function arguments
        case _ => (t, None)
      }

    //todo: Should this rewrite to saturation? Or is once enough?
    val rw = taxs(rect,ctx).toStream.flatMap( pr => applyTermProvable(rect,ctx,pr)).headOption
    rw match {
      case None => (rect,recpropt)
      case Some((tt,prem,pr)) =>
        //println("Simplified ",t," to ",tt)
        recpropt match {
          case None => (tt,Some(prem,pr))
          case Some((prem2,pr2)) =>
            val premise = And(prem2,prem)
            val fml = Imply(premise, Equal( t, tt ))
            val subst = USubst(List(SubstitutionPair(pP, prem2), SubstitutionPair(pQ, prem), SubstitutionPair(fF, t), SubstitutionPair(fFF, rect), SubstitutionPair(fFFF, tt)))
            val prr = (ProvableSig.startPlainProof(fml)
              (CEat(equalTrans(subst),PosInExpr(1::Nil))(SuccPos(0)), 0)
              (AndRight(SuccPos(0)), 0)
              (pr, 1)
              (pr2, 0)
            )
            (tt,Some(premise,prr))
        }
    }
  }


  /** Formula simplifier */

  /**
    * Lemmas used internally by formula simplifier
    */
  private def fmlAx(ctor:(Term,Term)=>Formula) : (ProvableSig,ProvableSig,ProvableSig) = {
    val limp = "A_() -> (L_() = LL_())".asFormula
    val rimp = "B_() -> (R_() = RR_())".asFormula
    val lhs = ctor("L_()".asTerm,"R_()".asTerm)
    val lAx = remember(Imply(limp,Imply( "A_()".asFormula ,Equiv(lhs, ctor("LL_()".asTerm,"R_()".asTerm)))),
      implyR(1) & implyR(1) & implyL(-1) <(id,exhaustiveEqL2R(-1) & cohideR(1) & byUS(Ax.equivReflexive)), namespace).fact
    val rAx = remember(Imply(rimp,Imply( "B_()".asFormula ,Equiv(lhs, ctor("L_()".asTerm,"RR_()".asTerm)))),
      implyR(1) & implyR(1)  & implyL(-1)<(id,exhaustiveEqL2R(-1) & cohideR(1) & byUS(Ax.equivReflexive)), namespace).fact
    val lrAx = remember(Imply(And(limp,rimp),Imply( "A_() & B_()".asFormula ,Equiv(lhs, ctor("LL_()".asTerm,"RR_()".asTerm)))),
      implyR(1) & implyR(1) & andL(-1) & implyL(-2) <(andL(-1) & id, implyL(-3) <(andL(-1) & id, exhaustiveEqL2R(-2) & exhaustiveEqL2R(-3) & cohideR(1) & byUS(Ax.equivReflexive)) ), namespace).fact
    (lAx,rAx,lrAx)
  }

  private lazy val eqAxs = fmlAx(Equal.apply)
  private lazy val geqAxs = fmlAx(GreaterEqual.apply)
  private lazy val gtAxs = fmlAx(Greater.apply)
  private lazy val leqAxs = fmlAx(LessEqual.apply)
  private lazy val ltAxs = fmlAx(Less.apply)
  private lazy val neAxs = fmlAx(NotEqual.apply)

  //Other customized internal lemmas
  //And
  //only L changes
  private lazy val andAxL =
    remember("(A_() -> (L_() <-> LL_())) -> (A_() -> (L_() & R_() <-> LL_() & R_()))".asFormula,prop & done, namespace).fact
  //only R changes
  private lazy val andAxR =
    remember("(B_() -> (R_() <-> RR_())) -> ((L_() -> B_()) -> (L_() & R_() <-> L_() & RR_()))".asFormula,prop & done, namespace).fact
  //both changed
  private lazy val andAxLR =
    remember(("(A_() -> (L_() <-> LL_())) & (B_() -> (R_() <-> RR_())) ->" +
      " ( (A_() & (LL_() -> B_())) -> (L_() & R_() <-> LL_() & RR_()) )").asFormula,prop & done, namespace).fact

  //Imply
  //only L changes
  private lazy val impAxL =
    remember("(A_() -> (L_() <-> LL_())) -> (A_() -> (L_() -> R_() <-> LL_() -> R_()))".asFormula,prop & done, namespace).fact
  //only R changes
  private lazy val impAxR =
    remember("(B_() -> (R_() <-> RR_())) -> ((L_() -> B_()) -> (L_() -> R_() <-> L_() -> RR_()))".asFormula,prop & done, namespace).fact
  //both changed
  private lazy val impAxLR =
    remember(("(A_() -> (L_() <-> LL_())) & (B_() -> (R_() <-> RR_())) ->" +
    " ( (A_() & (LL_() -> B_())) -> (L_() -> R_() <-> LL_() -> RR_()) )").asFormula,prop & done, namespace).fact

  //Or
  //only L changes
  private lazy val orAxL =
    remember("(A_() -> (L_() <-> LL_())) -> (A_() -> (L_() | R_() <-> LL_() | R_()))".asFormula,prop & done, namespace).fact
  //only R changes
  private lazy val orAxR =
    remember("(B_() -> (R_() <-> RR_())) -> ((!(L_()) -> B_()) -> (L_() | R_() <-> L_() | RR_()))".asFormula,prop & done, namespace).fact
  //both changed
  private lazy val orAxLR =
    remember(("(A_() -> (L_() <-> LL_())) & (B_() -> (R_() <-> RR_())) ->" +
    " ( (A_() & (!LL_() -> B_())) -> (L_() | R_() <-> LL_() | RR_()) )").asFormula,prop & done, namespace).fact

  //Negate
  private lazy val notAx =
    remember("(A_() -> (L_() <-> LL_())) -> (A_() -> (!L_() <-> !LL_()))".asFormula,prop & done, namespace).fact

  //Equiv
  //only L changes
  private lazy val equivAxL =
    remember("(A_() -> (L_() <-> LL_())) -> (A_() -> ( (L_() <-> R_()) <-> (LL_() <-> R_())))".asFormula,prop & done, namespace).fact
  //only R changes
  private lazy val equivAxR =
    remember("(B_() -> (R_() <-> RR_())) -> (B_() -> ( (L_() <-> R_()) <-> (L_() <-> RR_())))".asFormula,prop & done, namespace).fact
  //both changed
  private lazy val equivAxLR =
    remember(("(A_() -> (L_() <-> LL_())) & (B_() -> (R_() <-> RR_())) ->" +
    " ( (A_() & B_()) -> ((L_() <-> R_()) <-> (LL_() <-> RR_())) )").asFormula,prop & done, namespace).fact

  private lazy val equivTrans = remember("(P_() -> (F_() <-> FF_())) & (Q_() -> (FF_() <-> FFF_())) -> (P_() & Q_() -> (F_() <-> FFF_())) ".asFormula,prop & done, namespace).fact

  /**
    * Dependent formula simplification workhorse
    * Given provable A -> (P <-> P') or (P<->P'), a context, and a formula f,
    * Checks if P unifies with f,
    * If applicable, checks for the A[unif] in the context
    * Then unifies the conclusion appropriately
    * Note: can avoid unifying again in the proof?
    */
  private def applyFormulaProvable(f:Formula, ctx:context, pr:ProvableSig) : Option[(Formula,Formula,ProvableSig)] = {
    //todo: Add some kind of unification search? (that precludes fast HashSet lookups though)
    pr.conclusion.succ(0) match {
      case Imply(prem,Equiv(k,v)) =>
        val unif = try { UnificationMatch(k,f) } catch { case _: UnificationException => return None}
        val uprem = unif(prem)
        if (ctx.contains(uprem)) {
          val concl = unif(v)
          //@todo construct substitution
          val proof = ProvableSig.startPlainProof(Imply(uprem, Equiv(f, unif(v))))(byUS(pr), 0)
          //assert(proof.isProved)
          Some(concl,uprem,proof)
        } else None
      case Equiv(k,v) =>
        val unif = try { UnificationMatch(k,f) } catch { case _: UnificationException => return None }
        val Equiv(fsubst, _) = unif(Equiv(k,v))
        if (fsubst == f) {
          val concl = unif(v)
          //@todo construct substitution
          val proof = ProvableSig.startPlainProof(Imply(True, Equiv(f, unif(v))))(ImplyRight(SuccPos(0)), 0)(CoHideRight(SuccPos(0)), 0)(byUS(pr), 0)
          //assert(proof.isProved)
          Some(concl, True, proof)
        } else None
      case _ => ??? //Illegal shape of rewrite
    }
  }

  //todo: the number is not needed anymore
  private def addCtx(ctx:context,f:Formula,ctr:Int = 0) : (Int,context) =
  {
    if(ctx.contains(f) | f.equals(True) | f.equals(Not(False))){
      return (ctr,ctx)
    }
    f match {
      case And(l,r) =>
        val (nctr,nctx) = addCtx(ctx,l,ctr+1)
        addCtx(nctx,r,nctr)
      //todo: is it possible to make Nots smart here?
      case _ => (ctr,ctx+f)
    }
  }

  /**
    * Formula simplification of formula f to formula g
    * @param f formula to simplify
    * @param ctx current context (assumptions)
    * @param faxs the formula index
    * @param taxs the term index
    * @return the simplified formula g and an optional provable containing (premise,proof of premise -> (f<->g)) only if
    *         some simplification was applied
    *         premise is an assumption in contained in ctx
    */
  def formulaSimp(f: Formula,
                  ctx:context = HashSet.empty,
                  faxs: formulaIndex,
                  taxs: termIndex): (Formula,Option[(Formula,ProvableSig)]) = {
    //todo: enable flag to toggle left to right, right to left rewriting?
    val (recf,recpropt) =
    f match {
      case And(l,r) =>
        val (lf,lpropt) = formulaSimp(l,ctx,faxs,taxs)
        val (rf,rpropt) = formulaSimp(r,addCtx(ctx,lf)._2,faxs,taxs)
        val concl = And(lf,rf)
        (lpropt,rpropt) match {
          case (None,None) => (f,None)
          case (Some((lprem,lpr)),None) =>
            assert(rf==r, "Missing proof: simplified r=" + r.prettyString + " to " + rf.prettyString + ", but got no proof")
            val fml = Imply(lprem, Equiv(f, concl))
            val subst = USubst(List(SubstitutionPair(pA, lprem), SubstitutionPair(pL, l), SubstitutionPair(pLL, lf), SubstitutionPair(pR, r)))
            val pr = ProvableSig.startPlainProof(fml)(CEat(andAxL(subst),PosInExpr(1::Nil))(SuccPos(0)), 0)(lpr, 0)
            (concl,Some((lprem,pr)))
          case (None,Some((rprem,rpr))) =>
            assert(lf==l, "Missing proof: simplified l=" + l.prettyString + " to " + lf.prettyString + ", but got no proof")
            val premise = Imply(lf,rprem)
            val fml = Imply(premise , Equiv(f, concl))
            val subst = USubst(List(SubstitutionPair(pB, rprem), SubstitutionPair(pL, l), SubstitutionPair(pR, r), SubstitutionPair(pRR, rf)))
            val pr = ProvableSig.startPlainProof(fml)(CEat(andAxR(subst),PosInExpr(1::Nil))(SuccPos(0)), 0)(rpr, 0)
            (concl,Some((premise,pr)))
          case (Some((lprem,lpr)),Some((rprem,rpr))) =>
            val premise = And(lprem,Imply(lf,rprem))
            val fml = Imply(premise , Equiv(f, concl))
            val subst = USubst(List(SubstitutionPair(pA, lprem), SubstitutionPair(pB, rprem), SubstitutionPair(pL, l), SubstitutionPair(pLL, lf), SubstitutionPair(pR, r), SubstitutionPair(pRR, rf)))
            val pr = ProvableSig.startPlainProof(fml)(CEat(andAxLR(subst),PosInExpr(1::Nil))(SuccPos(0)), 0)(AndRight(SuccPos(0)), 0)(rpr, 1)(lpr, 0)
            (concl,Some((premise,pr)))
        }
      case Imply(l,r) =>
        val (lf,lpropt) = formulaSimp(l,ctx,faxs,taxs)
        val (rf,rpropt) = formulaSimp(r,addCtx(ctx,lf)._2,faxs,taxs)
        val concl = Imply(lf,rf)
        (lpropt,rpropt) match {
          case (None,None) => (f,None)
          case (Some((lprem,lpr)),None) =>
            assert(rf==r, "Missing proof: simplified r=" + r.prettyString + " to " + rf.prettyString + ", but got no proof")
            val fml = Imply(lprem, Equiv(f, concl))
            val subst = USubst(List(SubstitutionPair(pA, lprem), SubstitutionPair(pL, l), SubstitutionPair(pLL, lf), SubstitutionPair(pR, r)))
            val pr = ProvableSig.startPlainProof(fml)(CEat(impAxL(subst),PosInExpr(1::Nil))(SuccPos(0)), 0)(lpr, 0)
            (concl,Some((lprem,pr)))
          case (None,Some((rprem,rpr))) =>
            assert(lf==l, "Missing proof: simplified l=" + l.prettyString + " to " + lf.prettyString + ", but got no proof")
            val premise = Imply(lf,rprem)
            val fml = Imply(premise , Equiv(f, concl))
            val subst = USubst(List(SubstitutionPair(pB, rprem), SubstitutionPair(pL, l), SubstitutionPair(pR, r), SubstitutionPair(pRR, rf)))
            val pr = ProvableSig.startPlainProof(fml)(CEat(impAxR(subst),PosInExpr(1::Nil))(SuccPos(0)), 0)(rpr, 0)
            (concl,Some((premise,pr)))
          case (Some((lprem,lpr)),Some((rprem,rpr))) =>
            val premise = And(lprem,Imply(lf,rprem))
            val fml = Imply(premise , Equiv(f, concl))
            val subst = USubst(List(SubstitutionPair(pA, lprem), SubstitutionPair(pB, rprem), SubstitutionPair(pL, l), SubstitutionPair(pLL, lf), SubstitutionPair(pR, r), SubstitutionPair(pRR, rf)))
            val pr = ProvableSig.startPlainProof(fml)(CEat(impAxLR(subst),PosInExpr(1::Nil))(SuccPos(0)), 0)(AndRight(SuccPos(0)), 0)(rpr, 1)(lpr, 0)
            (concl,Some((premise,pr)))
        }
      case Or(l,r) =>
        //todo: Add some rewriting to handle the negation
        val (lf,lpropt) = formulaSimp(l,ctx,faxs,taxs)
        val (rf,rpropt) = formulaSimp(r,addCtx(ctx,Not(lf))._2,faxs,taxs)
        val concl = Or(lf,rf)
        (lpropt,rpropt) match {
          case (None,None) => (f,None)
          case (Some((lprem,lpr)),None) =>
            assert(rf==r, "Missing proof: simplified r=" + r.prettyString + " to " + rf.prettyString + ", but got no proof")
            val fml = Imply(lprem, Equiv(f, concl))
            val subst = USubst(List(SubstitutionPair(pA, lprem), SubstitutionPair(pL, l), SubstitutionPair(pLL, lf), SubstitutionPair(pR, r)))
            val pr = ProvableSig.startPlainProof(fml)(CEat(orAxL(subst),PosInExpr(1::Nil))(SuccPos(0)), 0)(lpr, 0)
            (concl,Some((lprem,pr)))
          case (None,Some((rprem,rpr))) =>
            assert(lf==l, "Missing proof: simplified l=" + l.prettyString + " to " + lf.prettyString + ", but got no proof")
            val premise = Imply(Not(lf),rprem)
            val fml = Imply(premise , Equiv(f, concl))
            val subst = USubst(List(SubstitutionPair(pB, rprem), SubstitutionPair(pL, l), SubstitutionPair(pR, r), SubstitutionPair(pRR, rf)))
            val pr = ProvableSig.startPlainProof(fml)(CEat(orAxR(subst),PosInExpr(1::Nil))(SuccPos(0)), 0)(rpr, 0)
            (concl,Some((premise,pr)))
          case (Some((lprem,lpr)),Some((rprem,rpr))) =>
            val premise = And(lprem,Imply(Not(lf),rprem))
            val fml = Imply(premise , Equiv(f, concl))
            val subst = USubst(List(SubstitutionPair(pA, lprem), SubstitutionPair(pB, rprem), SubstitutionPair(pL, l), SubstitutionPair(pLL, lf), SubstitutionPair(pR, r), SubstitutionPair(pRR, rf)))
            val pr = ProvableSig.startPlainProof(fml)(CEat(orAxLR(subst),PosInExpr(1::Nil))(SuccPos(0)), 0)(AndRight(SuccPos(0)), 0)(rpr, 1)(lpr, 0)
            (concl,Some((premise,pr)))
        }
      case Not(u) =>
        val (uf,upropt) = formulaSimp(u,ctx,faxs,taxs)
        val concl = Not(uf)
        upropt match {
          case None => (f,None)
          case Some((uprem,upr)) =>
            val fml = Imply(uprem, Equiv(f, concl))
            val subst = USubst(List(SubstitutionPair(pA, uprem), SubstitutionPair(pL, u), SubstitutionPair(pLL, uf)))
            val pr = ProvableSig.startPlainProof(fml)(CEat(notAx(subst),PosInExpr(1::Nil))(SuccPos(0)), 0)(upr, 0)
            (concl,Some((uprem,pr)))
        }
      case Equiv(l,r) =>
        val (lf,lpropt) = formulaSimp(l,ctx,faxs,taxs)
        val (rf,rpropt) = formulaSimp(r,ctx,faxs,taxs)
        val concl = Equiv(lf,rf)
        (lpropt,rpropt) match {
          case (None,None) => (f,None)
          case (Some((lprem,lpr)),None) =>
            assert(rf==r, "Missing proof: simplified r=" + r.prettyString + " to " + rf.prettyString + ", but got no proof")
            val fml = Imply(lprem, Equiv(f, concl))
            val subst = USubst(List(SubstitutionPair(pA, lprem), SubstitutionPair(pL, l), SubstitutionPair(pLL, lf), SubstitutionPair(pR, r)))
            val pr = ProvableSig.startPlainProof(fml)(CEat(equivAxL(subst),PosInExpr(1::Nil))(SuccPos(0)), 0)(lpr, 0)
            (concl,Some((lprem,pr)))
          case (None,Some((rprem,rpr))) =>
            assert(lf==l, "Missing proof: simplified l=" + l.prettyString + " to " + lf.prettyString + ", but got no proof")
            val fml = Imply(rprem , Equiv(f, concl))
            val subst = USubst(List(SubstitutionPair(pB, rprem), SubstitutionPair(pL, l), SubstitutionPair(pR, r), SubstitutionPair(pRR, rf)))
            val pr = ProvableSig.startPlainProof(fml)(CEat(equivAxR(subst),PosInExpr(1::Nil))(SuccPos(0)), 0)(rpr, 0)
            (concl,Some((rprem,pr)))
          case (Some((lprem,lpr)),Some((rprem,rpr))) =>
            val premise = And(lprem,rprem)
            val fml = Imply(premise , Equiv(f, concl))
            val subst = USubst(List(SubstitutionPair(pA, lprem), SubstitutionPair(pB, rprem), SubstitutionPair(pL, l), SubstitutionPair(pLL, lf), SubstitutionPair(pR, r), SubstitutionPair(pRR, rf)))
            val pr = ProvableSig.startPlainProof(fml)(CEat(equivAxLR(subst),PosInExpr(1::Nil))(SuccPos(0)), 0)(AndRight(SuccPos(0)), 0)(rpr, 1)(lpr, 0)
            (concl,Some((premise,pr)))
        }

      case cf:ComparisonFormula =>
        val l = cf.left
        val r = cf.right
        val (lt,lpropt) = termSimp(l,ctx,taxs)
        val (rt,rpropt) = termSimp(r,ctx,taxs)
        val concl = cf.reapply(lt,rt)

        val lem = cf match {
          case Equal(_,_) => eqAxs
          case GreaterEqual(_,_) => geqAxs
          case Greater(_,_) => gtAxs
          case LessEqual(_,_) => leqAxs
          case Less(_,_) => ltAxs
          case NotEqual(_,_) => neAxs
        }

        (lpropt,rpropt) match {
          case (None,None) => (f,None)
          case (Some((lprem,lpr)),None) =>
            assert(rt==r, "Missing proof: simplified r=" + r.prettyString + " to " + rt.prettyString + ", but got no proof")
            val fml = Imply(lprem, Equiv(f, concl))
            val subst = USubst(List(SubstitutionPair(pA, lprem), SubstitutionPair(fL, l), SubstitutionPair(fLL, lt), SubstitutionPair(fR, r)))
            val pr = ProvableSig.startPlainProof(fml)(CEat(lem._1(subst), PosInExpr(1 :: Nil))(SuccPos(0)), 0)(lpr, 0)
            (concl,Some((lprem,pr)))
          case (None,Some((rprem,rpr))) =>
            assert(lt==l, "Missing proof: simplified l=" + l.prettyString + " to " + lt.prettyString + ", but got no proof")
            val fml = Imply(rprem , Equiv(f, concl))
            val subst = USubst(List(SubstitutionPair(pB, rprem), SubstitutionPair(fL, l), SubstitutionPair(fR, r), SubstitutionPair(fRR, rt)))
            val pr = ProvableSig.startPlainProof(fml)(CEat(lem._2(subst), PosInExpr(1 :: Nil))(SuccPos(0)), 0)(rpr, 0)
            (concl,Some((rprem,pr)))
          case (Some((lprem,lpr)),Some((rprem,rpr))) =>
            val premise = And(lprem,rprem)
            val fml = Imply(premise , Equiv(f, concl))
            val subst = USubst(List(SubstitutionPair(pA, lprem), SubstitutionPair(pB, rprem), SubstitutionPair(fL, l), SubstitutionPair(fLL, lt), SubstitutionPair(fR, r), SubstitutionPair(fRR, rt)))
            val pr = ProvableSig.startPlainProof(fml)(CEat(lem._3(subst),PosInExpr(1::Nil))(SuccPos(0)), 0)(AndRight(SuccPos(0)), 0)(rpr, 1)(lpr, 0)
            (concl,Some((premise,pr)))
        }
      case q:Quantified =>
        val (remainingCtx, droppedCtx) = ctx.partition(f => StaticSemantics.freeVars(f).toSet.intersect(q.vars.toSet).isEmpty)
        val (uf,upropt) = formulaSimp(q.child,remainingCtx,faxs,taxs)
        val nf = q.reapply(q.vars, uf)

        upropt match {
          case None => (f,None)
          case Some((uprem,upr)) =>
            val premise = Forall(q.vars,uprem) //Implicitly, we are doing a forall quantification over the smaller simps
            val fml = Imply(premise, Equiv(f, nf))

            val seq = q match {
              case _: Forall => ((_: ProvableSig)
                (FOQuantifierTactics.allSkolemize(SuccPos(0)), 0)
                (FOQuantifierTactics.allInstantiate(None, None)(AntePos(0)), 0)
                (FOQuantifierTactics.allInstantiate(None, None)(AntePos(1)), 0)
                )
              case _: Exists => ((_: ProvableSig)
                (FOQuantifierTactics.existsSkolemize(AntePos(1)), 0)
                (FOQuantifierTactics.allInstantiate(None, None)(AntePos(0)), 0)
                (FOQuantifierTactics.existsInstantiate(None, None)(SuccPos(0)), 0)
                )
            }

            //This is nasty, there might be a better way to deal with the quantifiers
            val pr = (ProvableSig.startPlainProof(fml)
              (ImplyRight(SuccPos(0)), 0)
              (EquivRight(SuccPos(0)), 0)
              // right branch
              (seq, 1)
              (implyRi()(AntePos(1), SuccPos(0)), 1)
              (EquivifyRight(SuccPos(0)), 1)
              (CommuteEquivRight(SuccPos(0)), 1)
              (implyRi, 1)
              (upr, 1)
              // left branch
              (seq, 0)
              (implyRi()(AntePos(1), SuccPos(0)), 0)
              (EquivifyRight(SuccPos(0)), 0)
              (implyRi, 0)
              (upr, 0)
              )

            (nf,Some((premise,pr)))
        }

      case m: Modal =>
        //todo: This could keep some of the context around, maybe?
        //val (remainingCtx, droppedCtx) =
        //  ctx.partition(f => StaticSemantics.freeVars(f).toSet.intersect(StaticSemantics.boundVars(m).toSet).isEmpty)

        val (uf, upropt) = formulaSimp(m.child, HashSet.empty, faxs, taxs)

        upropt match {
          case None =>(f, None)
          case Some((uprem, upr)) =>
            //Simplification under modalities is tricky
            //The premises from the subprovable should be discharged first
            val concl = Equiv(m.child, uf)
            // |- p <-> q
            val upr2 = (ProvableSig.startPlainProof(concl)
              (CEat(upr,PosInExpr(1 :: Nil))(SuccPos(0)), 0)
              (fastCloser(HashSet.empty, uprem), 0))
            val res = m.reapply(m.program,uf)

            // |- [a]p <-> [a]p
            val init = Ax.equivReflexive.provable(
              USubst(SubstitutionPair(PredOf(Function("p_", None, Unit, Bool), Nothing), f) :: Nil))

            // |- [a]p <-> [a]q
            val pr1 = useFor(upr2, PosInExpr(0 :: Nil))(SuccPosition(1, 1:: 1 :: Nil))(init)

            val pr = (ProvableSig.startPlainProof(Imply(True,Equiv(f,res)))
              (ImplyRight(SuccPos(0)), 0)
              (CoHideRight(SuccPos(0)), 0)
              (pr1, 0))
            (res,Some(True,pr))

        }
      case PredOf(fn, c) if c != Nothing =>
        val (nArgs,proofs) = pairWalk(c, t=> termSimp(t,ctx,taxs))
        val nf = PredOf(fn, nArgs)
        val premise = proofs.map({ case (None,_) => True case (Some(pr),_) => pr._1}).reduceRight(And)
        val cuts = proofs.zipWithIndex.map({
          case ((None,_),_) => ident
          case ((Some(prf),_),i) => CEat(prf._2)(AntePos(i)) andThen eqL2R(AntePosition.base0(i))(SuccPosition.base0(0))
        }).foldLeft(_: ProvableSig)({ case (p, t) => p(t, 0) })
        val subst = USubst(List(SubstitutionPair(PredOf(Function("p_", None, Unit, Bool), Nothing), nf)))
        val pr = ProvableSig.startPlainProof(Imply(premise,Equiv(f,nf)))(
          ImplyRight(SuccPos(0)), 0)(
          times(andL('Llast), proofs.length-1), 0)(
          cuts, 0)(
          cohideR(1), 0)(
          Ax.equivReflexive.provable(subst), 0)
        (nf,Some(premise,pr))
      //Differentials
      case _ => (f,None)
    }

    //todo: Should this rewrite to saturation? Or is once enough?
    val rw = faxs(recf,ctx).toStream.flatMap( pr => applyFormulaProvable(recf,ctx,pr)).headOption

    rw match {
      case None => (recf,recpropt)
      case Some((ff,prem,pr)) =>
        recpropt match {
          case None => (ff,Some(prem,pr))
          case Some((prem2,pr2)) =>
            val premise = And(prem2,prem)
            val fml = Imply(premise, Equiv( f, ff ))
            //instantiate the middle ff to recf
            val subst = USubst(List(SubstitutionPair(pP, prem2), SubstitutionPair(pQ, prem), SubstitutionPair(pF, f), SubstitutionPair(pFF, recf), SubstitutionPair(pFFF, ff)))
            val prr = (ProvableSig.startPlainProof(fml)
              (CEat(equivTrans(subst), PosInExpr(1::Nil))(SuccPos(0)), 0)
              (AndRight(SuccPos(0)), 0)
              (pr, 1)
              (pr2, 0)
              )
            (ff,Some(premise,prr))
        }
    }
  }

  //Exhaustively split ONLY the last conjunct
  private val andSplit: ProvableSig=>ProvableSig = (provable: ProvableSig) => {
    var andStack = List(AntePos(provable.subgoals.head.ante.size-1))
    var pr = provable
    while (andStack.nonEmpty) {
      val p = andStack.head
      pr.subgoals.head(p) match {
        case _: And =>
          pr = pr(AndLeft(p), 0)
          andStack = AntePos(p.getIndex+1) +: andStack
        case _ =>
          andStack = andStack.tail
      }
    }
    pr
  }

  private def fastCloser(hs: context, f: Formula): ProvableSig=>ProvableSig = (pr: ProvableSig) => {
    //todo: auto close for NNF
    if (f == True) closeT.result(pr)
    else if (hs.contains(f)) id.result(pr)
    else {
      f match {
        case And(l, r) =>
          pr(AndRight(SuccPos(0)), 0)(fastCloser(hs, r), 1)(fastCloser(hs, l), 0)
        case Imply(l, r) =>
          val (_, newctx) = addCtx(hs, l)
          pr(ImplyRight(SuccPos(0)), 0)(andSplit, 0)(fastCloser(newctx, r), 0)
        case Forall(_, f) =>
          FOQuantifierTactics.allSkolemize(SuccPos(0)).computeResult(pr)(fastCloser(hs, f), 0)
        case _ => pr
      }
    }
  }

  private def termSimpWithDischarge(ctx:IndexedSeq[Formula],t:Term,taxs:termIndex) : (Term,Option[ProvableSig]) = {
    val hs = HashSet(ctx: _*) //todo: Apply simple decomposition that prop can handle here
    val (recf,recpropt) = termSimp(t,hs,taxs)
    (recf,
      recpropt match {
        case None => None
        case Some((prem, recpr)) =>
          Some(ProvableSig.startPlainProof(Sequent(ctx, IndexedSeq(Equal(t, recf))))
            (Cut(prem), 0)
            // show
            (HideRight(SuccPos(0)), 1)
            (fastCloser(hs, prem), 1)
            // use
            (CoHide2(AntePos(ctx.length), SuccPos(0)), 0)
            (implyRi, 0)
            (recpr, 0)
            )
      }
      )
  }


  /**
    * Almost identifcal to formulaSimp, but proves the rewrite directly with respect to ctx
    * @param f formula to simplify
    * @param ctx current context (assumptions)
    * @param faxs the formula index
    * @param taxs the term index
    * @return the simplified formula g and an optional provable containing proof of ctx -> (f<->g) only if
    *         some simplification was applied
    */
  def simpWithDischarge(ctx: IndexedSeq[Formula],
                        f: Formula,
                        faxs: formulaIndex,
                        taxs: termIndex): (Formula,Option[ProvableSig]) = {
    val hs = HashSet(ctx: _*) //todo: Apply simple decomposition that prop can handle here
    val (recf, recpropt) = formulaSimp(f,hs,faxs,taxs)
    (recf, recpropt match {
      case None => None
      case Some((prem,recpr)) =>
        Some(ProvableSig.startPlainProof(Sequent(ctx,IndexedSeq(Equiv(f,recf))))
          (Cut(prem), 0)
          // show
          (HideRight(SuccPos(0)), 1)
          (fastCloser(hs, prem), 1)
          // use
          (CoHide2(AntePos(ctx.length), SuccPos(0)), 0)
          (implyRi, 0)
          (recpr, 0)
          )
      }
    )
  }

  lazy val defaultFaxs: formulaIndex = composeIndex(baseIndex,boolIndex,cmpIndex)
  lazy val defaultTaxs: termIndex = composeIndex(composeIndex(arithGroundIndex,arithBaseIndex),arithSpecialIndex)

  //Allow the user to directly specify a list of theorems for rewriting
  private def thWrapper(ths: List[ProvableSig]) : (formulaIndex,termIndex) = {
    //Formula rewrites
    val fths = ths.filter(th =>
      th.conclusion.succ(0) match{
        case (Imply(_,Equiv(_,_))) => true
        case (Equiv(_,_)) => true
        case _=> false
      }
    )
    //Term rewrites
    val tths = ths.filter(th =>
      th.conclusion.succ(0) match{
        case (Imply(_,Equal(_,_))) => true
        case (Equal(_,_)) => true
        case _=> false
      }
    )
    ((f,ctx) => fths,(t,ctx)=>tths)
  }

  /**
   * Tactic that simplifies at the given position
   */
  def simpTac(ths: List[ProvableSig] = List.empty,
              faxs: formulaIndex = defaultFaxs,
              taxs: termIndex = defaultTaxs): BuiltInPositionTactic = anon { (provable: ProvableSig, pos: Position) =>
    val (fths, tths) = thWrapper(ths)
    val augmentFaxs: formulaIndex = composeIndex(fths,faxs)
    val augmentTaxs: termIndex = composeIndex(tths,taxs)

    val sequent = provable.subgoals.head

    sequent.sub(pos) match {
      case Some(f: Formula) =>
        //If simplification was at the top level, then we can use the existing context
        if (pos.isTopLevel) {
          val (ctx, cutPos, commute) =
            if (pos.isSucc) (sequent.ante, pos, commuteEquivR(1))
            else (sequent.ante.patch(pos.top.getIndex, Nil, 1), SuccPosition.base0(sequent.succ.length), skip)

          simpWithDischarge(ctx,f,augmentFaxs,augmentTaxs) match {
            case (_, None) => provable
            case (ff, Some(pr)) =>
              (provable(cutAtFw(ff)(pos), 0)
                (cohideOnlyR(cutPos), 1)
                (equivifyR(SuccPos(0)), 1)
                (commute, 1)
                (pr, 1)
                )
          }
        } else {
          //Otherwise we only do the simplification under empty context and CEat the result
          simpWithDischarge(IndexedSeq(),f,augmentFaxs,augmentTaxs) match {
            case (_, None) => provable
            case (_, Some(pr)) => provable(CEat(commuteEquivFR(SuccPosition(1))(pr))(pos), 0)
          }
        }
      case Some(t: Term) => termSimpWithDischarge(IndexedSeq(),t, augmentTaxs) match {
        case (_, None) => provable
        case (_, Some(pr)) => try {
          provable(CEat(useFor(Ax.equalCommute)(SuccPos(0))(pr))(pos), 0)
        } catch {
          case _: InfiniteTacticLoopError =>
            throw new UnsupportedTacticFeature("Unable to simplify term " + t +
              " because some of its variables appear in a maybe-bound context")
        }
      }
      case _ => provable
    }
  }

  @Tactic(names="Simplify",
    premises="Γ |- simplify(P), Δ",
    conclusion="Γ |- P, Δ",
    displayLevel="browse")
  val simplify: BuiltInPositionTactic = simpTac()

  /** Simplifies with full context (antecedent + negated succedent).  */
  val simplifyAllCtx: BuiltInPositionTactic = anon { (provable: ProvableSig, pos: Position) =>
    ProofRuleTactics.requireOneSubgoal(provable, "SimplifierV3.simplifyAllCtx")

    val alpha =
      if (pos.isSucc) {
        prop(
          { case (_: And, ap: AntePos) => List(AndLeft(ap)) case _ => List.empty },
          { (_, _) => List.empty })(List.empty, List.empty)
      } else {
        prop(
          { case (_: Or, sp: SuccPos) => List(OrRight(sp)) case _ => List.empty },
          { (_, _) => List.empty })(List.empty, List.empty)
      }

    val moveContext = (pr: ProvableSig) => {
      ProofRuleTactics.requireAtMostOneSubgoal(pr, "PropositionalTactics.moveContext")
      pr.subgoals.headOption.map(seq => {
        val indices = if (pos.isAnte) seq.succ.indices else seq.succ.indices.diff(List(pos.index0))
        indices.map(SuccPos).reverse.foldLeft(pr)({ case (p, i) =>
          val subst = USubst(List(SubstitutionPair(PredOf(Function("p_", None, Unit, Bool), Nothing), seq(i))))
          p(CEat(Ax.doubleNegation.provable(subst), PosInExpr(List(1)))(i), 0)(NotRight(i), 0) })
      }).getOrElse(pr)
    }

    provable(alpha andThen doIfFw(!_.isProved)(moveContext andThen SimplifierV3.simplify(pos)), 0)
  }

  /**
    * Full sequent simplification tactic
    */
  def fullSimpTac(ths: List[ProvableSig] = List.empty,
                  faxs: formulaIndex = defaultFaxs,
                  taxs: termIndex = defaultTaxs,
                  simpAntes: Boolean = true,
                  simpSuccs: Boolean = true): BuiltInTactic = anon { (provable: ProvableSig) =>

    val simps = simpTac(ths, faxs, taxs)

    val hideTrues = (pr: ProvableSig) => {
      pr.subgoals.head.ante.zipWithIndex.filter(_._1 == True).map(t => HideLeft(AntePos(t._2))).
        foldRight(pr)({ case (h, p) => p(h, 0) })
    }

    val hideFalses = (pr: ProvableSig) => {
      pr.subgoals.head.succ.zipWithIndex.filter(_._1 == False).map(t => HideRight(SuccPos(t._2))).
        foldRight(pr)({ case (h, p) => p(h, 0) })
    }

    val seq = provable.subgoals.head

    val antes =
      if (simpAntes) List.range(-1, -(seq.ante.length+1), -1).foldRight(provable)((i, pr) => pr(simps(i), 0))
      else provable

    val succ =
      if (simpSuccs) List.range(1, seq.succ.length+1, 1).foldRight(antes)((i, pr)=> pr(simps(i), 0))
      else antes

    succ(hideTrues, 0)(hideFalses, 0)
  }

  @Tactic(names="Full Simplify",
    premises="simplify(Γ |- P, Δ)",
    conclusion="Γ |- P, Δ",
    displayLevel="browse")
  val fullSimplify: BuiltInTactic = fullSimpTac()

  /** Term simplification indices */

//  private def qeTermProof(t:String,tt:String,pre:Option[String] = None): ProvableSig =
//  {
//    pre match{
//      case None => remember(Equal(t.asTerm,tt.asTerm),QE & done, namespace).fact
//      case Some(f) => remember(Imply(f.asFormula,Equal(t.asTerm,tt.asTerm)),QE & done, namespace).fact
//    }
//  }

  //These are mostly just the basic unit and identity rules
  private lazy val mulArith: List[ProvableSig] = List(
    Ax.zeroTimes.provable,
    Ax.timesZero.provable,
    Ax.timesIdentity.provable,
    useFor(Ax.timesCommute, PosInExpr(0 :: Nil))(SuccPosition(1,0::Nil))(Ax.timesIdentity.provable),
    Ax.timesIdentityNeg.provable,
    useFor(Ax.timesCommute, PosInExpr(0 :: Nil))(SuccPosition(1,0::Nil))(Ax.timesIdentityNeg.provable),
    Ax.negOneTimes.provable) ++
  //@note timesDivInverse not provable with Z3
  (if (ToolProvider.qeTool(Some("Mathematica")).isDefined) List(Ax.timesDivInverse.provable) else List.empty)

  private lazy val negArith: List[ProvableSig] = List(
    Ax.minusNeg.provable,
    Ax.negNeg.provable
  )

  private lazy val plusArith: List[ProvableSig] = List(
    Ax.plusZero.provable,
    Ax.zeroPlus.provable,
    Ax.plusNeg.provable,
    Ax.negPlus.provable
  )

  private lazy val minusArith: List[ProvableSig] = List(
    Ax.minusZero.provable,
    Ax.zeroMinus.provable)

  //TODO: move to DerivedAxioms?
  lazy val divArith: List[ProvableSig] = List(
    Ax.zeroDivNez.provable,
    useFor(Ax.gtzImpNez, PosInExpr(1 :: Nil))(SuccPosition(1,0::Nil))(Ax.zeroDivNez.provable),
    useFor(Ax.ltzImpNez, PosInExpr(1 :: Nil))(SuccPosition(1,0::Nil))(Ax.zeroDivNez.provable))

  lazy val powArith: List[ProvableSig] = List(
    Ax.powZero.provable,
    Ax.powOne.provable,
    Ax.powNegOne.provable)

  //These may also be useful:
  //qeTermProof("F_()*(F_()^-1)","1",Some("F_()>0")), qeTermProof("(F_()^-1)*F_()","1",Some("F_()>0")))
  //qeTermProof("F_()+(-F_())","0"),qeTermProof("(-F_())+F_()","0"),
  //  qeTermProof("x-x","0"),
  //  qeTermProof("F_()+G_()-F_()","G_()"),
  //  qeTermProof("F_()+G_()-G_()","F_()"),

  def arithBaseIndex (t:Term,ctx:context) : List[ProvableSig] = t match {
    case Neg(_)      => negArith
    case Plus(_,_)   => plusArith
    case Minus(_,_)  => minusArith
    case Times(_,_)  => mulArith
    case Divide(_,_) => divArith
    case Power(_,_)  => powArith
    case _           => List()
  }

  //This generates theorems on the fly to simplify ground arithmetic (only for integers)
  //Note: this skips over any arithmetic whose outputs are not integers
  def arithGroundIndex(t: Term, ctx: context = emptyCtx): List[ProvableSig] = {
    val res = t match {
      case n:Number if n.value.scale > 0 => Some(n.value)
      case Plus(n:Number,m:Number) => Some(n.value+m.value)
      case Minus(n:Number,m:Number) => Some(n.value-m.value)
      case Times(n:Number,m:Number) => Some(n.value*m.value)
      case Divide(n:Number,m:Number) if m.value!=0 => Some(n.value/m.value)
      case Power(n:Number,m:Number) => Some(n.value.pow(m.value.toInt))
      case Neg(n:Number) => Some(-n.value)
      case _ => None
    }
    res match {
      case None => List()
      case Some(v) if v.isExactDouble && v.isValidInt =>
        val num = Number(v.toIntExact)
        val pr = ProvableSig.startPlainProof(Equal(t, num))(opt(RCF), 0)
        if (pr.isProved) List(pr)
        else List()
      case _ => List()
    }
  }

  /** TODO: PURELY EXPERIMENTAL HACK. DO NOT MERGE.
    *
    * Map of (implicit) functions to simplification axiom(s) for their definition
    */
  def arithSpecialIndex(t:Term, ctx: context = emptyCtx) : List[ProvableSig] = {
    t match {
      case FuncOf(f,_) if f.interpreted =>
        ImplicitAx.getInitAx(f) match {
          case Some(ls) => ls.provable::Nil
          case None => Nil
        }
      case _ => Nil
    }
  }

  private lazy val impReflexive = remember("p_() -> p_()".asFormula, prop & done, namespace).fact
  private lazy val eqSymmetricImp = remember("F_() = G_() -> G_() = F_()".asFormula,
    prop & exhaustiveEqL2R(-1) & hideL(-1) & byUS(Ax.equalReflexive), namespace).fact

  //Constrained search for equalities of the form t = Num (or Num = t) in the context
  def groundEqualityIndex (t:Term,ctx:context) : List[ProvableSig] = {
    ctx.collectFirst(
      {
        case Equal(tt, n: Number) if !tt.isInstanceOf[Number] && tt == t =>
          impReflexive(
            USubst(SubstitutionPair(PredOf(Function("p_", None, Unit, Bool), Nothing), Equal(t, n: Number)) :: Nil))
        case Equal(n: Number, tt) if !tt.isInstanceOf[Number] && tt == t =>
          eqSymmetricImp(
            USubst(SubstitutionPair(FuncOf(Function("F_", None, Unit, Real), Nothing), n) ::
              SubstitutionPair(FuncOf(Function("G_", None, Unit, Real), Nothing), t) :: Nil))
      }).toList
  }

  //Unconstrained search for equalities of the form t = tt or tt = t in the context
  //It will always apply the first equality
  def fullEqualityIndex (t:Term,ctx:context) : List[ProvableSig] = {
    ctx.collectFirst(
      {
        case Equal(tt, ttt) if tt.equals(t) =>
          impReflexive(
            USubst(SubstitutionPair(PredOf(Function("p_", None, Unit, Bool), Nothing), Equal(t, ttt)) :: Nil))
        case Equal(ttt, tt) if tt.equals(t) =>
          eqSymmetricImp(
            USubst(SubstitutionPair(FuncOf(Function("F_", None, Unit, Real), Nothing), ttt) ::
              SubstitutionPair(FuncOf(Function("G_", None, Unit, Real), Nothing), t) :: Nil))
      }).toList
  }

  /** Formula simplification indices */
  private def propProof(f:String,ff:String,precond:Option[String] = None):ProvableSig =
  {
    precond match {
      case Some(pre) =>
        remember(Imply(pre.asFormula,Equiv(f.asFormula,ff.asFormula)), prop & done, namespace).fact
      case None =>
        remember(Equiv(f.asFormula,ff.asFormula), prop & done, namespace).fact
    }
  }

  //F_() -> (F_() <-> true)
  private lazy val tauto = propProof("F_()","true",Some("F_()"))
  //!(F_()) -> (F_() <-> false)
  private lazy val tauto2 = propProof("F_()","false",Some("!F_()"))
  //false -> (F_() <-> true)
  private lazy val tauto3 = propProof("F_()","true",Some("false"))

  //This is a critical index
  def baseIndex (f:Formula,ctx:context) : List[ProvableSig] = {
    f match {
      case True => List()
      case False => List(tauto3)
      case _ => List(tauto,tauto2,tauto3)
    }
  }

  /** Base index without F->(F<->true) dependent formula simplification. */
  def baseIndexWithoutDepFmlSimp(f:Formula,ctx:context) : List[ProvableSig] = {
    f match {
      case True => List()
      case False => List(tauto3)
      case _ => List(tauto2,tauto3)
    }
  }

  //TODO: These are annoying to add to the derived axioms database...
  private def qeSearch(cmp1:(Term,Term)=>Formula,cmps:List[(Term,Term)=>Formula]) : List[ProvableSig] = {
    //Use partial QE because I don't want to do everything by hand..
    val f = "F_()".asTerm
    val g = "G_()".asTerm
    val key = cmp1(f,g)
    cmps.flatMap(
      (cmp:(Term,Term) => Formula) => {
          List(
            remember(Imply(cmp(f, g), Equiv(key, True)), prop & onAll(?(QE)), namespace).fact,
            remember(Imply(cmp(f, g), Equiv(key, False)), prop & onAll(?(QE)), namespace).fact,
            remember(Imply(cmp(g, f), Equiv(key, True)), prop & onAll(?(QE)), namespace).fact,
            remember(Imply(cmp(g, f), Equiv(key, False)), prop & onAll(?(QE)), namespace).fact
          )
      }
    ).filter(_.isProved)
  }

  private lazy val eqs = Ax.equalSym.provable::qeSearch(Equal.apply,List(NotEqual.apply,Greater.apply,GreaterEqual.apply,Less.apply,LessEqual.apply))
  private lazy val neqs = Ax.notEqualSym.provable::qeSearch(NotEqual.apply,List(Equal.apply,Greater.apply,GreaterEqual.apply,Less.apply,LessEqual.apply))
  private lazy val gts = Ax.greaterNotSym.provable::qeSearch(Greater.apply,List(Equal.apply,NotEqual.apply,GreaterEqual.apply,Less.apply,LessEqual.apply))
  private lazy val ges = qeSearch(GreaterEqual.apply,List(Equal.apply,NotEqual.apply,Greater.apply,Less.apply,LessEqual.apply))
  private lazy val lts = Ax.lessNotSym.provable::qeSearch(Less.apply,List(Equal.apply,NotEqual.apply,Greater.apply,GreaterEqual.apply,LessEqual.apply))
  private lazy val les = qeSearch(LessEqual.apply,List(Equal.apply,NotEqual.apply,Greater.apply,GreaterEqual.apply,Less.apply))

  //This contains the basic heuristics for closing a comparison formula
  def cmpIndex (f:Formula,ctx:context) : List[ProvableSig] = {

    f match {
      // Not of a comparison formula
      case Not(bop:ComparisonFormula) =>
        List(Ax.notNotEqual,Ax.notEqual,
          Ax.notLess,Ax.notGreater,
          Ax.notLessEqual,Ax.notGreaterEqual).map(l=>l.provable)
      // Reflexive cases
      // This protects against unification errors using Scala to inspect the term directly
      case bop:ComparisonFormula if bop.left==bop.right =>
        bop match{
          case Less(_,_) => List(Ax.lessNotRefl.provable)
          case Greater(_,_) => List(Ax.greaterNotRefl.provable)
          case NotEqual(_,_) => List(Ax.notEqualNotRefl.provable)
          case Equal(_,_) => List(Ax.equalRefl.provable)
          case GreaterEqual(_,_) => List(Ax.greaterEqualRefl.provable)
          case LessEqual(_,_) => List(Ax.lessEqualRefl.provable)
        }
      //Closing by search
      case bop:ComparisonFormula =>
        bop match{
          case Less(_,_) => lts
          case Greater(_,_) => gts
          case NotEqual(_,_) => neqs
          case Equal(_,_) => eqs
          case GreaterEqual(_,_) => ges
          case LessEqual(_,_) => les
        }
      case _ => List()
    }

  }

  private lazy val andT = propProof("F_() & true","F_()")
  private lazy val Tand = propProof("true & F_()","F_()")
  private lazy val andF = propProof("F_() & false","false")
  private lazy val Fand = propProof("false & F_()","false")

  private lazy val implyT = propProof("F_() -> true","true")
  private lazy val Timply = propProof("true -> F_()","F_()")
  private lazy val implyF = propProof("F_() -> false","!F_()")
  private lazy val Fimply = propProof("false -> F_()","true")

  private lazy val orT = propProof("F_() | true","true")
  private lazy val Tor = propProof("true | F_()","true")
  private lazy val orF = propProof("F_() | false","F_()")
  private lazy val For = propProof("false | F_()","F_()")

  private lazy val equivT = propProof("F_() <-> true","F_()")
  private lazy val Tequiv = propProof("true <-> F_()","F_()")
  private lazy val equivF = propProof("F_() <-> false","!F_()")
  private lazy val Fequiv = propProof("false <-> F_()","!F_()")

  private lazy val notT = propProof("!true","false")
  private lazy val notF = propProof("!false","true")

  private lazy val forallTrue = remember("(\\forall x_ true)<->true".asFormula, autoClose, namespace).fact
  private lazy val forallFalse = remember("(\\forall x_ false)<->false".asFormula, autoClose, namespace).fact
  private lazy val existsTrue = remember("(\\exists x_ true)<->true".asFormula, autoClose, namespace).fact
  private lazy val existsFalse = remember("(\\exists x_ false)<->false".asFormula, autoClose, namespace).fact

  def boolIndex (f:Formula,ctx:context) : List[ProvableSig] ={
    f match {
      //Note: more pattern matching possible here
      case And(l,r) => List(andT,Tand,andF,Fand)
      case Imply(l,r) => List(implyT,Timply,implyF,Fimply)
      case Or(l,r) => List(orT,Tor,orF,For)
      case Equiv(l,r) =>  List(equivT,Tequiv,equivF,Fequiv)
      case Not(u) => List(notT,notF,Ax.doubleNegation.provable)
      case Forall(_,_) => List(forallTrue,forallFalse)
      case Exists(_,_) => List(existsTrue,existsFalse)
      case _ => List()
    }
  }

  def chaseIndex(f: Formula, ctx: context): List[ProvableSig] = {
    val id = ProvableSig.startPlainProof(Equiv(f,f))(byUS(Ax.equivReflexive.provable), 0)
    val cpr = chaseFor(3,3,e=>AxIndex.axiomsFor(e),(s,p)=>pr=>pr)(SuccPosition(1,1::Nil))(id)
    List(cpr)
  }

  def emptyTaxs(t:Term,ctx:context) : List[ProvableSig] = List()
  def emptyFaxs(f:Formula,ctx:context) : List[ProvableSig] = List()

  /**
    * A configurable normalizer using the simplifier
    */

  //Turns a formula into Negation Normal Form
  private def to_NNF(f:Formula) : Option[(Formula,ProvableSig)] = {
    def l2r(prv: ProvableSig, recursors: List[Int]*) : List[(ProvableSig, PosInExpr, List[PosInExpr])] =
      List((prv, PosInExpr(0::Nil), recursors.toList.map(PosInExpr(_))))
    def recurseFml(recursors: List[Int]*) : List[(ProvableSig, PosInExpr, List[PosInExpr])] = {
      l2r(Ax.equivReflexive.provable, recursors : _*)
    }
    val A = List()  // All / Whole subexpression
    val L = List(0) // Left
    val C = List(0) // Child
    val R = List(1) // Right
    def Left(xs: List[Int]) = 0::xs
    def Right(xs: List[Int]) = 1::xs
    val LL = Left(L)
    val LR = Left(R)
    val RL = Right(L)
    val RR = Right(R)
    val chaseNeg = chaseCustomFor({
      case formula: AtomicFormula => Nil
      case formula@Not(g:AtomicFormula) => g match {
        case Equal(a,b) => l2r(Ax.notEqual.provable)
        case NotEqual(a,b) => l2r(Ax.notNotEqual.provable)
        case Greater(a,b) => l2r(Ax.notGreater.provable)
        case GreaterEqual(a,b) => l2r(Ax.notGreaterEqual.provable)
        case Less(a,b) => l2r(Ax.notLess.provable)
        case LessEqual(a,b) => l2r(Ax.notLessEqual.provable)
        case True => l2r(notT)
        case False => l2r(notF)
        case _ => throw new IllegalArgumentException("to_NNF of formula " + formula + " not implemented")
      }
      case formula@Not(g:CompositeFormula) => g match {
        case Not(f) => l2r(Ax.doubleNegation.provable, A)
        case And(p,q) => l2r(Ax.notAnd.provable, L, R)
        case Or(p,q) => l2r(Ax.notOr.provable, L, R)
        case Imply(p,q) => l2r(Ax.notImply.provable, L, R)
        case Equiv(p,q) => l2r(Ax.notEquiv.provable, LL, RL, LR, RR)
        case Forall(vs, p) => l2r(Ax.notAll.provable, C)
        case Exists(vs, p) => l2r(Ax.notExists.provable, C)
        case Box(prg, p) => l2r(Ax.notBox.provable, C)
        case Diamond(prg, p) => l2r(Ax.notDiamond.provable, C)
        case _ => throw new IllegalArgumentException("to_NNF of formula " + formula + " not implemented")
      }
      case Imply(p,q) => l2r(Ax.implyExpand.provable, L, R)
      case Equiv(p,q) => l2r(Ax.equivExpandAnd.provable, LL, RL, LR, RR)
      case f:BinaryCompositeFormula => recurseFml(L, R)
      case f:Quantified             => recurseFml(C)
      case f:Modal                  => recurseFml(C)
      case expression => throw new IllegalArgumentException("to_NNF of expression " + expression + " not implemented")
    })
    val nnff = FormulaTools.negationNormalForm(f)
    if(nnff != f) {
      val prv = chaseNeg(Position(1, 1::Nil))(Ax.equivReflexive.provable(USubst(Seq(SubstitutionPair("p_()".asFormula, f)))))
      val pr = ProvableSig.startPlainProof(Equiv(f, nnff))(prv, 0)
      require(pr.isProved, "NNF normalization failed:"+f+" "+nnff)
      Some(nnff,pr)
    }
    else None
  }

  //Simplifier term index that throws an exception when it encounters terms that are not atomic
  private def atomicTermIndex(t:Term,ctx:context) : List[ProvableSig] = {
    t match {
      case v:BaseVariable => List()
      case n:Number => List()
      case FuncOf(f,Nothing) if !f.interp.isDefined => List()
      case FuncOf(f,_) if f.interp.isDefined => List()
      case Neg(_) => List()
      case Plus(_,_) => List()
      case Minus(_,_) => List()
      case Times(_,_) => List()
      case Divide(_,_) => List()
      case Power(_,_) => List()
      case _ =>
        throw new IllegalArgumentException("cannot normalize term:"+t+" rejecting immediately")
    }
  }

  /**
    * Normalize a formula
    * By default, this normalizer builds in:
    * 1) NNF conversion
    * 2) Term checking: no min, max, abs, functions (except consts) -- if checkTerms = true
    */
  private def doNormalize(fi:formulaIndex, checkTerms:Boolean = true)(f:Formula) : (Formula,Option[ProvableSig]) = {
    to_NNF(f) match {
      case Some((nnf,pr)) =>
        val (ff,propt) = SimplifierV3.simpWithDischarge (IndexedSeq[Formula] (), nnf, fi,
          if(checkTerms) atomicTermIndex else emptyTaxs)
        propt match {
          case None => (nnf,Some(pr))
          case Some(pr2) =>
            (ff, Some(useFor(pr2, PosInExpr(0 :: Nil))(SuccPosition(1, 1 :: Nil))(pr)) )
        }
      case None =>
        SimplifierV3.simpWithDischarge (IndexedSeq[Formula] (), f, fi,
          if(checkTerms) atomicTermIndex else emptyTaxs)
    }
  }

  //The basic semialgebraic normalizer turns all inequalities uniformly to have 0 on the RHS
  private lazy val leNorm: ProvableSig = remember("f_() <= g_() <-> g_() - f_() >= 0".asFormula,QE,namespace).fact
  private lazy val leFlip: ProvableSig = remember("0 <= g_() <-> g_() >= 0".asFormula,QE,namespace).fact
  private lazy val geNorm: ProvableSig = remember("f_() >= g_() <-> f_() - g_() >= 0".asFormula,QE,namespace).fact
  private lazy val ltNorm: ProvableSig = remember("f_() < g_() <-> g_() - f_() > 0".asFormula,QE,namespace).fact
  private lazy val ltFlip: ProvableSig = remember("0 < g_() <-> g_() > 0".asFormula,QE,namespace).fact
  private lazy val gtNorm: ProvableSig = remember("f_() > g_() <-> f_() - g_() > 0".asFormula,QE,namespace).fact
  private lazy val eqNorm: ProvableSig = remember(" f_() = g_() <-> f_() - g_() = 0 ".asFormula,QE,namespace).fact
  private lazy val neqNorm: ProvableSig = remember(" f_() != g_() <-> f_() - g_() > 0 | g_() - f_() > 0 ".asFormula,QE,namespace).fact
  private lazy val neqNorm2: ProvableSig = remember(" f_() != g_() <-> f_() - g_() != 0".asFormula,QE,namespace).fact

  // Additional formulas for specialized normalizers
  private lazy val trueGeqNorm:ProvableSig = remember("true<->1>=0".asFormula,QE,namespace).fact
  private lazy val falseGeqNorm:ProvableSig = remember("false<->-1>=0".asFormula,QE,namespace).fact
  private lazy val minGeqNorm:ProvableSig = remember("f_()>=0&g_()>=0<->min((f_(),g_()))>=0".asFormula,QE,namespace).fact
  private lazy val maxGeqNorm:ProvableSig = remember("f_()>=0|g_()>=0<->max((f_(),g_()))>=0".asFormula,QE,namespace).fact
  private lazy val eqNormAbs:ProvableSig = remember("f_() = 0 <-> -abs(f_())>=0".asFormula,QE,namespace).fact

  private lazy val trueGtNorm:ProvableSig = remember("true<->1>0".asFormula,QE,namespace).fact
  private lazy val falseGtNorm:ProvableSig = remember("false<->-1>0".asFormula,QE,namespace).fact
  private lazy val minGtNorm:ProvableSig = remember("f_()>0&g_()>0<->min((f_(),g_()))>0".asFormula,QE,namespace).fact
  private lazy val maxGtNorm:ProvableSig = remember("f_()>0|g_()>0<->max((f_(),g_()))>0".asFormula,QE,namespace).fact
  private lazy val neqNormAbs:ProvableSig = remember("f_() != g_()<-> abs(f_()-g_())>0".asFormula,QE,namespace).fact

  //Equational normalizers
  private lazy val andEqNorm:ProvableSig = remember("f_()=0 & g_()=0 <-> f_()^2 + g_()^2=0".asFormula,QE,namespace).fact
  private lazy val orEqNorm:ProvableSig = remember( "f_()=0 | g_()=0 <-> f_() * g_() = 0".asFormula,QE,namespace).fact
  private lazy val trueEqNorm:ProvableSig = remember("true <-> 0=0".asFormula,QE,namespace).fact
  private lazy val falseEqNorm:ProvableSig = remember( "false <-> 1=0".asFormula,QE,namespace).fact

  // Recursively normalize the formula to the form p=0, failing if that is not possible
  private def algNormalizeIndex(f:Formula,ctx:context) : List[ProvableSig] = {
    f match {
      case Equal(l, r) => if (r == Number(0)) List() else List(eqNorm)
      case And(l, r) => List(andEqNorm)
      case Or(l, r) => List(orEqNorm)
      case True => List(trueEqNorm)
      case False => List(falseEqNorm)
      case _ => throw new IllegalArgumentException("cannot normalize " + f + " to have 0 on RHS (must be a conjunction/disjunction of atomic equations)")
    }
  }

  // Recursively normalize the formula to have all (in)equalities with 0s on RHS, failing if that is not possible
  private def semiAlgNormalizeIndex(f:Formula,ctx:context) : List[ProvableSig] = {
    f match {
      case LessEqual(l,r) => List(leFlip,leNorm)
      case GreaterEqual(l,r) => if (r == Number(0)) List() else List(geNorm)
      case Less(l,r) => List(ltFlip,ltNorm)
      case Greater(l,r) => if (r == Number(0)) List() else List(gtNorm)
      case Equal(l,r) => if (r == Number(0)) List() else List(eqNorm)
      case NotEqual(l,r) => List(neqNorm) //if (r == Number(0)) List() else
      case And(l,r) =>  Nil
      case Or(l,r) =>  Nil
      case True => List(trueEqNorm)
      case False => List(falseEqNorm)
      case _ => throw new IllegalArgumentException("cannot normalize "+f+" to have 0 on RHS (must be a conjunction/disjunction of atomic comparisons)")
    }
  }
  // Recursively normalize =s and !=s
  private def disAlgNormalizeIndex(f:Formula,ctx:context) : List[ProvableSig] = {
    f match {
      case Equal(l,r) => if (r == Number(0)) List() else List(eqNorm)
      case NotEqual(l,r) => List(neqNorm2)
      case And(l,r) =>  Nil
      case Or(l,r) =>  Nil
      case _ => throw new IllegalArgumentException("cannot normalize "+f+" to have 0 on RHS (must be a conjunction/disjunction of =s or !=s comparisons)")
    }
  }

  // Simplifier index that normalizes only a single inequality to have 0 on the RHS
  private def ineqNormalizeIndex(f:Formula,ctx:context) : List[ProvableSig] = {
    f match {
      case LessEqual(l,r) => ()
      case GreaterEqual(l,r) => ()
      case Less(l,r) => ()
      case Greater(l,r) => ()
      case _ => throw new IllegalArgumentException("cannot normalize "+f+" to have 0 on RHS (must be inequality >=,>,<=,<)")
    }
    semiAlgNormalizeIndex(f,ctx)
  }

  // ineqNormalize + equality and disequalities (all atomic comparisons)
  private def atomNormalizeIndex(f:Formula,ctx:context) : List[ProvableSig] = {
    f match {
      case LessEqual(l,r) => ()
      case GreaterEqual(l,r) => ()
      case Less(l,r) => ()
      case Greater(l,r) => ()
      case Equal(l,r) => ()
      case NotEqual(l,r) => ()
      case _ => throw new IllegalArgumentException("cannot normalize "+f+" to have 0 on RHS (must be atomic comparison formula >=,>,<=,<,=,!=)")
    }
    semiAlgNormalizeIndex(f,ctx)
  }

  // Simplifier index that normalizes a formula into max/min >= normal form
  private def maxMinGeqNormalizeIndex(f:Formula,ctx:context) : List[ProvableSig] = {
    f match {
      case GreaterEqual(l,r:Number) if r.value.toInt == 0 => List()
      case Equal(l,r) => List(eqNormAbs) //Special normalization for equalities
      case And(l,r) =>  List(minGeqNorm)
      case Or(l,r) =>  List(maxGeqNorm)
      case True => List(trueGeqNorm)
      case False => List(falseGeqNorm)
      case _ => throw new IllegalArgumentException("cannot normalize "+f+" to max/min >=0 normal form (must be a conjunction/disjunction of >= 0s or =0s)")
    }
  }

  // Simplifier index that normalizes a formula into max/min > normal form
  private def maxMinGtNormalizeIndex(f:Formula,ctx:context) : List[ProvableSig] = {
    f match {
      case Greater(l,r:Number) if r.value.toInt == 0 => List()
      case And(l,r) =>  List(minGtNorm)
      case Or(l,r) =>  List(maxGtNorm)
      case True => List(trueGtNorm)
      case False => List(falseGtNorm)
      case _ => throw new IllegalArgumentException("cannot normalize "+f+" to max/min >0 normal form (must be a conjunction/disjunction of > 0s)")
    }
  }

  /**
    * Various normalization steps (the first thing each of them do is NNF normalize)
    * Note: This DOES NOT work with quantifiers!
    *
    * baseNormalize : the base normalizer
    * ineqNormalize : normalizes atomic inequalities only
    * atomNormalize : normalizes all (nested) atomic comparisons
    * semiAlgNormalize : semialgebraic to have 0 on RHS
    * maxMinGeqNormalize : max,min >=0 normal form
    *
    * All of these behave as follows:
    *
    * Input: f: formula
    * Output: (g:formula,pr:Option[ProvableSig]) where g is the normalized version of f
    * The (optional) pr contains a provable that proves their equivalence if f!=g
    * Additionally, if f is of the incorrect shape, then the normalizer will throw an IllegalArgumentException
    */
  val baseNormalize: Formula => (Formula,Option[ProvableSig]) = doNormalize(emptyFaxs)(_)
  val ineqNormalize: Formula => (Formula,Option[ProvableSig]) = doNormalize(ineqNormalizeIndex)(_)
  val atomNormalize: Formula => (Formula,Option[ProvableSig]) = doNormalize(atomNormalizeIndex)(_)
  val algNormalize: Formula => (Formula,Option[ProvableSig]) = doNormalize(algNormalizeIndex)(_)
  val semiAlgNormalize: Formula => (Formula,Option[ProvableSig]) = doNormalize(semiAlgNormalizeIndex)(_)
  val disAlgNormalize: Formula => (Formula,Option[ProvableSig]) = doNormalize(disAlgNormalizeIndex)(_)
  val semiAlgNormalizeUnchecked: Formula => (Formula,Option[ProvableSig]) = doNormalize(semiAlgNormalizeIndex, checkTerms= false)(_)
  val maxMinGeqNormalize: Formula => (Formula,Option[ProvableSig]) = doNormalize(maxMinGeqNormalizeIndex)(_)
  val maxMinGeqNormalizeUnchecked: Formula => (Formula,Option[ProvableSig]) = doNormalize(maxMinGeqNormalizeIndex, checkTerms= false)(_)
  val maxMinGtNormalize: Formula => (Formula,Option[ProvableSig]) = doNormalize(maxMinGtNormalizeIndex)(_)
  val maxMinGtNormalizeUnchecked: Formula => (Formula,Option[ProvableSig]) = doNormalize(maxMinGtNormalizeIndex, checkTerms= false)(_)
}
