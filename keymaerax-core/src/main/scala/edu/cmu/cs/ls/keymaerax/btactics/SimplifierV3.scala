package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig

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

  /** Term simplifier */
  //Internal lemmas for binary connectives
  private def termAx(ctor:(Term,Term)=>Term) : (ProvableSig,ProvableSig,ProvableSig) = {
    val limp = "A_() -> (L_() = LL_())".asFormula
    val rimp = "B_() -> (R_() = RR_())".asFormula
    val lhs = ctor("L_()".asTerm,"R_()".asTerm)
    val lAx = proveBy(Imply(limp,Imply( "A_()".asFormula ,Equal(lhs, ctor("LL_()".asTerm,"R_()".asTerm)))),prop & exhaustiveEqL2R(-1) & cohideR(1) & byUS("= reflexive"))
    val rAx = proveBy(Imply(rimp,Imply( "B_()".asFormula ,Equal(lhs, ctor("L_()".asTerm,"RR_()".asTerm)))),prop & exhaustiveEqL2R(-1) & cohideR(1) & byUS("= reflexive"))
    val lrAx = proveBy(Imply(And(limp,rimp),Imply( "A_() & B_()".asFormula ,Equal(lhs, ctor("LL_()".asTerm,"RR_()".asTerm)))),prop & exhaustiveEqL2R(-1) & exhaustiveEqL2R(-2) & cohideR(1) & byUS("= reflexive"))
    (lAx,rAx,lrAx)
  }

  //Walks a pair and applies the given function everywhere, remembering where it applied that function
  //Used for predicate arguments and formula arguments
  private def pairWalk[A](t: Term, fn: Term => (Term,A), prefix :List[Int] = List[Int]()): (Term,List[(A,List[Int])]) = t match {
    case Pair(a,b) =>
      val (aa,l) = pairWalk(a,fn,0::prefix)
      val (bb,r) = pairWalk(b,fn,1::prefix)
      (Pair(aa,bb),l++r)
    case a =>
      val (aa,l) = fn(a)
      (aa,List((l,prefix.reverse)))
  }

  private val plusAxs = termAx(Plus.apply)
  private val minusAxs = termAx(Minus.apply)
  private val timesAxs = termAx(Times.apply)
  private val divAxs = termAx(Divide.apply)
  private val powAxs = termAx(Power.apply)

  private val negAx = proveBy( "(A_() -> (L_() = LL_())) -> A_() -> (-L_() = -LL_())".asFormula,prop & exhaustiveEqL2R(-1) & cohideR(1) & byUS("= reflexive"))


  private val equalTrans = proveBy("(P_() -> (F_() = FF_())) & (Q_() -> (FF_() = FFF_())) -> (P_() & Q_() -> (F_() = FFF_())) ".asFormula,prop & QE)

  //Dependent term simplification workhorse
  //Given provable A -> (t = t') or (t = t'), a context, and a term x,
  // Checks if x unifies with t,
  // If applicable, checks for the A[unif] in the context
  // Then unifies the conclusion appropriately
  // Note: can avoid unifying again in the proof?
  def applyTermProvable(t:Term, ctx:HashSet[Formula], pr:ProvableSig) : Option[(Term,Formula,ProvableSig)] = {
    //todo: Add some kind of unification search? (that precludes fast HashSet lookups though)
    pr.conclusion.succ(0) match {
      case Imply(prem,Equal(k,v)) => {
        val unif = try { UnificationMatch(k,t) } catch { case e:UnificationException => return None}
        val uprem = unif(prem)
        if(ctx.contains(uprem)){
          val concl = unif(v)
          val proof = proveBy(Imply(uprem,Equal(t,unif(v))), byUS(pr))
          //assert(proof.isProved)
          Some(concl,uprem,proof)
        }
        else None
      }
      case Equal(k,v) => {
        val unif = try { UnificationMatch(k,t) } catch { case e:UnificationException => return None}
        val concl = unif(v)
        val proof = proveBy(Imply(True,Equal(t,unif(v))), implyR(1) & cohideR(1) & byUS(pr))
        //assert(proof.isProved)
        Some(concl,True,proof)
      }
      case _ => ??? //Illegal shape of rewrite
    }
  }

  //Given prem -> (left = right), returns left = right
  def completeDischarge(prem:Formula, left:Term, right:Term, pr:ProvableSig ) : ProvableSig = {
    proveBy(Equal(left,right), useAt(pr,PosInExpr(1 :: Nil))(1) & fastCloser(HashSet(),prem))
  }

  def termSimp(t:Term, ctx:HashSet[Formula], taxs:Term => List[ProvableSig]) : (Term, Option[(Formula,ProvableSig)]) =
  {
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
              val fml = Imply(lprem, Equal(t, concl))
              val pr = proveBy(fml, useAt(lem._1, PosInExpr(1 :: Nil))(1) & by(lpr))
              (concl, Some((lprem, pr)))
            case (None, Some((rprem, rpr))) =>
              val fml = Imply(rprem, Equal(t, concl))
              val pr = proveBy(fml, useAt(lem._2, PosInExpr(1 :: Nil))(1) & by(rpr))
              (concl, Some((rprem, pr)))
            case (Some((lprem, lpr)), Some((rprem, rpr))) =>
              val premise = And(lprem, rprem)
              val fml = Imply(premise, Equal(t, concl))
              val pr = proveBy(fml, useAt(lem._3, PosInExpr(1 :: Nil))(1) & andR(1) < (by(lpr), by(rpr)))
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
              (nt,Some((uprem,proveBy(fml, useAt(negAx, PosInExpr(1 :: Nil))(1) & by(upr)))))
          }

        //todo: this currently throws the context away, but I think it can probably be done better using eqL2R
        case FuncOf(fn, c) if c != Nothing =>
          val (nArgs,proofs) = pairWalk(c,
            t=>{
              val (tt,pr) = termSimp(t,ctx,taxs)
              (tt,pr match {
                case None => None
                case Some((f,pr)) => Some(completeDischarge(f,t,tt,pr))
              })
            }
          )
          val pref = 0::0::Nil
          val nt = FuncOf(fn, nArgs)
          val tactic = proofs.map({ case (None,_) => ident case (Some(eqPr), i) => useAt(eqPr)(1,pref++i) }).
            reduceRight(_&_) & byUS(DerivedAxioms.equalReflex)
          (nt,Some(True,proveBy(Imply(True,Equal(t, nt)), implyR(1) & cohideR(1) & tactic)))
        //todo: Function arguments
        case _ => (t, None)
      }

    //todo: Should this rewrite to saturation? Or is once enough?
    val rw = taxs(rect).toStream.flatMap( pr => applyTermProvable(rect,ctx,pr)).headOption
    rw match {
      case None => (rect,recpropt)
      case Some((tt,prem,pr)) =>
        //println("Simplified ",t," to ",tt)
        recpropt match {
          case None => (tt,Some(prem,pr))
          case Some((prem2,pr2)) =>
            val premise = And(prem2,prem)
            val fml = Imply(premise, Equal( t, tt ))
            //instantiate the middle ff to recf
            val prr = proveBy(fml,
              useAt("ANON",equalTrans,PosInExpr(1::Nil),
                (us:Option[Subst])=>us.get++RenUSubst(("FF_()".asTerm,rect)::Nil))(1) &
                andR(1) <(by(pr2),by(pr))
            )
            (tt,Some(premise,prr))
        }
    }
  }

  /** Formula simplifier */
  //Lemmas used internally by formula simplifier

  //The internal lemmas for comparison connectives
  private def fmlAx(ctor:(Term,Term)=>Formula) : (ProvableSig,ProvableSig,ProvableSig) = {
    val limp = "A_() -> (L_() = LL_())".asFormula
    val rimp = "B_() -> (R_() = RR_())".asFormula
    val lhs = ctor("L_()".asTerm,"R_()".asTerm)
    val lAx = proveBy(Imply(limp,Imply( "A_()".asFormula ,Equiv(lhs, ctor("LL_()".asTerm,"R_()".asTerm)))),
      implyR(1) & implyR(1) & implyL(-1) <(prop,exhaustiveEqL2R(-1) & cohideR(1) & byUS("<-> reflexive")))
    val rAx = proveBy(Imply(rimp,Imply( "B_()".asFormula ,Equiv(lhs, ctor("L_()".asTerm,"RR_()".asTerm)))),
      implyR(1) & implyR(1)  & implyL(-1) <(prop,exhaustiveEqL2R(-1) & cohideR(1) & byUS("<-> reflexive")))
    val lrAx = proveBy(Imply(And(limp,rimp),Imply( "A_() & B_()".asFormula ,Equiv(lhs, ctor("LL_()".asTerm,"RR_()".asTerm)))),
      implyR(1) & implyR(1) & andL(-1) & implyL(-2) <(prop, implyL(-3) <( prop, exhaustiveEqL2R(-2) & exhaustiveEqL2R(-3) & cohideR(1) & byUS("<-> reflexive")) ))
    (lAx,rAx,lrAx)
  }

  private val eqAxs = fmlAx(Equal.apply)
  private val geqAxs = fmlAx(GreaterEqual.apply)
  private val gtAxs = fmlAx(Greater.apply)
  private val leqAxs = fmlAx(LessEqual.apply)
  private val ltAxs = fmlAx(Less.apply)
  private val neAxs = fmlAx(NotEqual.apply)

  //Other customized internal lemmas
  //And
  //only L changes
  private val andAxL =
    proveBy("(A_() -> (L_() <-> LL_())) -> (A_() -> (L_() & R_() <-> LL_() & R_()))".asFormula,prop)
  //only R changes
  private val andAxR =
    proveBy("(B_() -> (R_() <-> RR_())) -> ((L_() -> B_()) -> (L_() & R_() <-> L_() & RR_()))".asFormula,prop)
  //both changed
  private val andAxLR =
    proveBy(("(A_() -> (L_() <-> LL_())) & (B_() -> (R_() <-> RR_())) ->" +
      " ( (A_() & (LL_() -> B_())) -> (L_() & R_() <-> LL_() & RR_()) )").asFormula,prop)

  //Imply
  //only L changes
  private val impAxL =
  proveBy("(A_() -> (L_() <-> LL_())) -> (A_() -> (L_() -> R_() <-> LL_() -> R_()))".asFormula,prop)
  //only R changes
  private val impAxR =
  proveBy("(B_() -> (R_() <-> RR_())) -> ((L_() -> B_()) -> (L_() -> R_() <-> L_() -> RR_()))".asFormula,prop)
  //both changed
  private val impAxLR =
  proveBy(("(A_() -> (L_() <-> LL_())) & (B_() -> (R_() <-> RR_())) ->" +
    " ( (A_() & (LL_() -> B_())) -> (L_() -> R_() <-> LL_() -> RR_()) )").asFormula,prop)

  //Or
  //only L changes
  private val orAxL =
  proveBy("(A_() -> (L_() <-> LL_())) -> (A_() -> (L_() | R_() <-> LL_() | R_()))".asFormula,prop)
  //only R changes
  private val orAxR =
  proveBy("(B_() -> (R_() <-> RR_())) -> ((!(L_()) -> B_()) -> (L_() | R_() <-> L_() | RR_()))".asFormula,prop)
  //both changed
  private val orAxLR =
  proveBy(("(A_() -> (L_() <-> LL_())) & (B_() -> (R_() <-> RR_())) ->" +
    " ( (A_() & (!LL_() -> B_())) -> (L_() | R_() <-> LL_() | RR_()) )").asFormula,prop)

  //Negate
  private val notAx =
  proveBy("(A_() -> (L_() <-> LL_())) -> (A_() -> (!L_() <-> !LL_()))".asFormula,prop)

  //Equiv
  //only L changes
  private val equivAxL =
  proveBy("(A_() -> (L_() <-> LL_())) -> (A_() -> ( (L_() <-> R_()) <-> (LL_() <-> R_())))".asFormula,prop)
  //only R changes
  private val equivAxR =
  proveBy("(B_() -> (R_() <-> RR_())) -> (B_() -> ( (L_() <-> R_()) <-> (L_() <-> RR_())))".asFormula,prop)
  //both changed
  private val equivAxLR =
  proveBy(("(A_() -> (L_() <-> LL_())) & (B_() -> (R_() <-> RR_())) ->" +
    " ( (A_() & B_()) -> ((L_() <-> R_()) <-> (LL_() <-> RR_())) )").asFormula,prop)

  private val equivTrans = proveBy("(P_() -> (F_() <-> FF_())) & (Q_() -> (FF_() <-> FFF_())) -> (P_() & Q_() -> (F_() <-> FFF_())) ".asFormula,prop)

  def composeIndex[A<:Expression]( is:(A => List[ProvableSig])*)
                  (f:A) : List[ProvableSig] = is.flatMap(axs => axs(f)).toList

  //Dependent formula simplification workhorse
  //Given provable A -> (P <-> P') or (P<->P'), a context, and a formula f,
  // Checks if P unifies with f,
  // If applicable, checks for the A[unif] in the context
  // Then unifies the conclusion appropriately
  // Note: can avoid unifying again in the proof?
  def applyFormulaProvable(f:Formula, ctx:HashSet[Formula], pr:ProvableSig) : Option[(Formula,Formula,ProvableSig)] = {
    //todo: Add some kind of unification search? (that precludes fast HashSet lookups though)
    pr.conclusion.succ(0) match {
      case Imply(prem,Equiv(k,v)) => {
        val unif = try { UnificationMatch(k,f) } catch { case e:UnificationException => return None}
        val uprem = unif(prem)
        if(ctx.contains(uprem)){
          val concl = unif(v)
          val proof = proveBy(Imply(uprem,Equiv(f,unif(v))), byUS(pr))
          //assert(proof.isProved)
          Some(concl,uprem,proof)
        }
        else None
      }
      case Equiv(k,v) => {
        val unif = try { UnificationMatch(k,f) } catch { case e:UnificationException => return None}
        val concl = unif(v)
        val proof = proveBy(Imply(True,Equiv(f,unif(v))), implyR(1) & cohideR(1) & byUS(pr))
        //assert(proof.isProved)
        Some(concl,True,proof)
      }
      case _ => ??? //Illegal shape of rewrite
    }
  }

  //Returns the number of conjuncts that got split up
  def addCtx(ctx:HashSet[Formula],f:Formula,ctr:Int = 0) : (Int,HashSet[Formula]) =
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

  def formulaSimp(f:Formula, ctx:HashSet[Formula] = HashSet(),
                  faxs: Formula => List[ProvableSig], taxs: Term => List[ProvableSig]) : (Formula,Option[(Formula,ProvableSig)]) =
  {
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
            val fml = Imply(lprem, Equiv(f, concl))
            val pr = proveBy(fml,useAt(andAxL,PosInExpr(1::Nil))(1) & by(lpr))
            (concl,Some((lprem,pr)))
          case (None,Some((rprem,rpr))) =>
            val premise = Imply(lf,rprem)
            val fml = Imply(premise , Equiv(f, concl))
            val pr = proveBy(fml, useAt(andAxR,PosInExpr(1::Nil))(1) & by(rpr))
            (concl,Some((premise,pr)))
          case (Some((lprem,lpr)),Some((rprem,rpr))) =>
            val premise = And(lprem,Imply(lf,rprem))
            val fml = Imply(premise , Equiv(f, concl))
            val pr = proveBy(fml,useAt(andAxLR,PosInExpr(1::Nil))(1) & andR(1) <(by(lpr),by(rpr)))
            (concl,Some((premise,pr)))
        }
      case Imply(l,r) =>
        val (lf,lpropt) = formulaSimp(l,ctx,faxs,taxs)
        val (rf,rpropt) = formulaSimp(r,addCtx(ctx,lf)._2,faxs,taxs)
        val concl = Imply(lf,rf)
        (lpropt,rpropt) match {
          case (None,None) => (f,None)
          case (Some((lprem,lpr)),None) =>
            val fml = Imply(lprem, Equiv(f, concl))
            val pr = proveBy(fml,useAt(impAxL,PosInExpr(1::Nil))(1) & by(lpr))
            (concl,Some((lprem,pr)))
          case (None,Some((rprem,rpr))) =>
            val premise = Imply(lf,rprem)
            val fml = Imply(premise , Equiv(f, concl))
            val pr = proveBy(fml, useAt(impAxR,PosInExpr(1::Nil))(1) & by(rpr))
            (concl,Some((premise,pr)))
          case (Some((lprem,lpr)),Some((rprem,rpr))) =>
            val premise = And(lprem,Imply(lf,rprem))
            val fml = Imply(premise , Equiv(f, concl))
            val pr = proveBy(fml,useAt(impAxLR,PosInExpr(1::Nil))(1) & andR(1) <(by(lpr),by(rpr)))
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
            val fml = Imply(lprem, Equiv(f, concl))
            val pr = proveBy(fml,useAt(orAxL,PosInExpr(1::Nil))(1) & by(lpr))
            (concl,Some((lprem,pr)))
          case (None,Some((rprem,rpr))) =>
            val premise = Imply(Not(lf),rprem)
            val fml = Imply(premise , Equiv(f, concl))
            val pr = proveBy(fml, useAt(orAxR,PosInExpr(1::Nil))(1) & by(rpr))
            (concl,Some((premise,pr)))
          case (Some((lprem,lpr)),Some((rprem,rpr))) =>
            val premise = And(lprem,Imply(Not(lf),rprem))
            val fml = Imply(premise , Equiv(f, concl))
            val pr = proveBy(fml,useAt(orAxLR,PosInExpr(1::Nil))(1) & andR(1) <(by(lpr),by(rpr)))
            (concl,Some((premise,pr)))
        }
      case Not(u) =>
        val (uf,upropt) = formulaSimp(u,ctx,faxs,taxs)
        val concl = Not(uf)
        upropt match {
          case None => (f,None)
          case Some((uprem,upr)) =>
            val fml = Imply(uprem, Equiv(f, concl))
            val pr = proveBy(fml,useAt(notAx,PosInExpr(1::Nil))(1) & by(upr))
            (concl,Some((uprem,pr)))
        }
      case Equiv(l,r) =>
        val (lf,lpropt) = formulaSimp(l,ctx,faxs,taxs)
        val (rf,rpropt) = formulaSimp(r,ctx,faxs,taxs)
        val concl = Equiv(lf,rf)
        (lpropt,rpropt) match {
          case (None,None) => (f,None)
          case (Some((lprem,lpr)),None) =>
            val fml = Imply(lprem, Equiv(f, concl))
            val pr = proveBy(fml,useAt(equivAxL,PosInExpr(1::Nil))(1) & by(lpr))
            (concl,Some((lprem,pr)))
          case (None,Some((rprem,rpr))) =>
            val fml = Imply(rprem , Equiv(f, concl))
            val pr = proveBy(fml, useAt(equivAxR,PosInExpr(1::Nil))(1) & by(rpr))
            (concl,Some((rprem,pr)))
          case (Some((lprem,lpr)),Some((rprem,rpr))) =>
            val premise = And(lprem,rprem)
            val fml = Imply(premise , Equiv(f, concl))
            val pr = proveBy(fml,useAt(equivAxLR,PosInExpr(1::Nil))(1) & andR(1) <(by(lpr),by(rpr)))
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
            val fml = Imply(lprem, Equiv(f, concl))
            val pr = proveBy(fml, useAt(lem._1, PosInExpr(1 :: Nil))(1) & by(lpr))
            (concl,Some((lprem,pr)))
          case (None,Some((rprem,rpr))) =>
            val fml = Imply(rprem , Equiv(f, concl))
            val pr = proveBy(fml, useAt(lem._2, PosInExpr(1 :: Nil))(1) & by(rpr))
            (concl,Some((rprem,pr)))
          case (Some((lprem,lpr)),Some((rprem,rpr))) =>
            val premise = And(lprem,rprem)
            val fml = Imply(premise , Equiv(f, concl))
            val pr = proveBy(fml,useAt(lem._3,PosInExpr(1::Nil))(1) & andR(1) <(by(lpr),by(rpr)))
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
              case Forall(_,_) => allR(1) & allL(-1) & allL(-2)
              case Exists(_,_) => existsL(-2) & allL(-1) & existsR(1)
            }

            //This is nasty, there might be a better way to deal with the quantifiers
            val pr = proveBy(fml, implyR(1) & equivR(1) &
              OnAll(seq & implyRi()(AntePos(1),SuccPos(0)) & equivifyR(1)) <(
                implyRi & by(upr),
                commuteEquivR(1) & implyRi & by(upr)
                )
            )

            (nf,Some((premise,pr)))
        }

      case m:Modal =>
        //todo: This could keep some of the context around, maybe?
        //val (remainingCtx, droppedCtx) =
        //  ctx.partition(f => StaticSemantics.freeVars(f).toSet.intersect(StaticSemantics.boundVars(m).toSet).isEmpty)

        val (uf,upropt) = formulaSimp(m.child,HashSet(),faxs,taxs)

        upropt match {
          case None =>(f,None)
          case Some((uprem,upr)) =>
            //Simplification under modalities is tricky
            //The premises from the subprovable should be discharged first
            val concl = Equiv(m.child,uf)
            // |- p <-> q
            val upr2 = proveBy(concl, useAt(upr,PosInExpr(1 :: Nil))(1) & fastCloser(HashSet(),uprem))
            val res = m.reapply(m.program,uf)

            // |- [a]p <-> [a]p
            val init = DerivedAxioms.equivReflexiveAxiom.fact(
              USubst(SubstitutionPair(PredOf(Function("p_", None, Unit, Bool), Nothing), f) :: Nil))

            // |- [a]p <-> [a]q
            val pr1 = useFor(upr2, PosInExpr(0 :: Nil))(SuccPosition(1, 1:: 1 :: Nil))(init)

            val pr = proveBy(Imply(True,Equiv(f,res)),implyR(1) & cohideR(1) & by(pr1))
            (res,Some(True,pr))

        }
      case PredOf(fn, c) if c != Nothing =>
        val (nArgs,proofs) = pairWalk(c,
          t=>{
            val (tt,pr) = termSimp(t,ctx,taxs)
            (tt,pr match {
              case None => None
              case Some((f,pr)) => Some(completeDischarge(f,t,tt,pr))
            })
          }
        )
        val pref = 0::0::Nil
        val nf = PredOf(fn, nArgs)
        val tactic = proofs.map({ case (None,_) => ident case (Some(eqPr), i) => useAt(eqPr)(1,pref++i) }).
        reduceRight(_&_) & byUS(DerivedAxioms.equivReflexiveAxiom)
        (nf,Some(True,proveBy(Imply(True,Equiv(f, nf)), implyR(1) & cohideR(1) & tactic)))

      //Differentials
      case _ => (f,None)
    }

    //todo: Should this rewrite to saturation? Or is once enough?
    val rw = faxs(recf).toStream.flatMap( pr => applyFormulaProvable(recf,ctx,pr)).headOption

    rw match {
      case None => (recf,recpropt)
      case Some((ff,prem,pr)) =>
        recpropt match {
          case None => (ff,Some(prem,pr))
          case Some((prem2,pr2)) =>
            val premise = And(prem2,prem)
            val fml = Imply(premise, Equiv( f, ff ))
            //instantiate the middle ff to recf
            val prr = proveBy(fml,
              useAt("ANON",equivTrans,PosInExpr(1::Nil),
                (us:Option[Subst])=>us.get++RenUSubst(("FF_()".asFormula,recf)::Nil))(1) &
              andR(1) <(by(pr2),by(pr))
            )
            (ff,Some(premise,prr))
        }
    }
  }

  def fastCloser(hs:HashSet[Formula],f:Formula): BelleExpr = {
    //todo: auto close for NNF
    if (f.equals(True)) closeT
    else if (hs.contains(f)) closeId
    else {
      f match {
        case And(l, r) =>
          andR(1) < (fastCloser(hs, l), fastCloser(hs, r))
        case Imply(l, r) =>
          val (ctr, newctx) = addCtx(hs, l)
          implyR(1) & (andL('Llast) * ctr) & fastCloser(newctx, r)
        case Forall(vars, f) =>
          allR(1) &
          fastCloser(hs, f)
        case _ => ident
      }
    }
  }

  def termSimpWithDischarge(ctx:IndexedSeq[Formula],t:Term,taxs:Term=>List[ProvableSig]) : (Term,Option[ProvableSig]) = {
    val hs = HashSet(ctx: _*) //todo: Apply simple decomposition that prop can handle here
    val (recf,recpropt) = termSimp(t,hs,taxs)

    (recf,
      recpropt match {
        case None => None
        case Some((prem,recpr)) =>
          val pr =
            Some(proveBy( Sequent(ctx,IndexedSeq(Equal(t,recf))),
              cut(prem) <( cohide2(-(ctx.length+1),1) & implyRi & by(recpr) , hideR(1) & fastCloser(hs,prem) )))
          pr
      }
      )
  }

  def simpWithDischarge(ctx:IndexedSeq[Formula],f:Formula,
                        faxs:Formula=>List[ProvableSig],taxs:Term=>List[ProvableSig]) : (Formula,Option[ProvableSig]) = {
    val hs = HashSet(ctx: _*) //todo: Apply simple decomposition that prop can handle here
    val (recf,recpropt) = formulaSimp(f,hs,faxs,taxs)

    (recf,
    recpropt match {
      case None => None
      case Some((prem,recpr)) =>
        val pr =
        Some(proveBy( Sequent(ctx,IndexedSeq(Equiv(f,recf))),
          cut(prem) <( cohide2(-(ctx.length+1),1) & implyRi & by(recpr) , hideR(1) & fastCloser(hs,prem) )))
        pr
      }
    )
  }

  val defaultFaxs:Formula=>List[ProvableSig] = composeIndex(baseIndex,boolIndex,cmpIndex)
  val defaultTaxs:Term=>List[ProvableSig] = composeIndex(arithGroundIndex,arithBaseIndex)

  //Allow the user to directly specify a list of theorems for rewriting
  private def thWrapper(ths: List[ProvableSig]) : (Formula=>List[ProvableSig],Term=>List[ProvableSig]) = {
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
    (f => fths,t=>tths)
  }

  //Simplifies a formula including sub-terms occuring in the formula
  def simpTac(ths:List[ProvableSig]=List(),
              faxs:Formula=>List[ProvableSig]=defaultFaxs,
              taxs:Term=>List[ProvableSig]=defaultTaxs):DependentPositionTactic = new DependentPositionTactic("simplify"){
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
      val (fths,tths) = thWrapper(ths)
      val augmentFaxs:Formula=>List[ProvableSig] = composeIndex(fths,faxs)
      val augmentTaxs:Term=>List[ProvableSig] = composeIndex(tths,taxs)

      override def computeExpr(sequent: Sequent): BelleExpr = {
        //println("Simplifying at",pos)
        sequent.sub(pos) match
        {
          case Some(f:Formula) =>
            //If simplification was at the top level, then we can use the existing context
            if (pos.isTopLevel)
            {
              val (ctx, cutPos, commute) =
                if (pos.isSucc) (sequent.ante, pos, commuteEquivR(1))
                else (sequent.ante.patch(pos.top.getIndex, Nil, 1), SuccPosition.base0(sequent.succ.length), skip)

              val (ff,pr) = simpWithDischarge(ctx,f,augmentFaxs,augmentTaxs)

              pr match {
                case None => ident
                case Some(pr) =>
                  cutAt (ff) (pos) < (
                  ident,
                  cohideOnlyR (cutPos) & equivifyR (1) & commute & by (pr)
                  )
              }
            }
            //Otherwise we only do the simplification under empty context and CEat the result
            else
            {
              val (ff,pr) = simpWithDischarge(IndexedSeq(),f,augmentFaxs,augmentTaxs)
              pr match {
                case None => ident
                case Some(pr) =>
                CEat(commuteEquivFR(SuccPosition(1))(pr))(pos)
              }
            }
          case Some(t:Term) =>
          {
            val (ff,pr) = termSimpWithDischarge(IndexedSeq(),t, augmentTaxs)
            pr match {
              case None => ident
              case Some(pr) =>
                CEat(useFor("= commute")(SuccPos(0))(pr))(pos)
            }
          }
          case _ => ident
        }
      }
    }
  }

  //Full sequent simplification tactic
  def fullSimpTac(ths:List[ProvableSig]=List(),
                  faxs:Formula=>List[ProvableSig]=defaultFaxs,
                  taxs:Term=>List[ProvableSig]=defaultTaxs):DependentTactic = new SingleGoalDependentTactic("fullSimplify") {

    val simps = simpTac(ths,faxs,taxs)

    override def computeExpr(seq: Sequent): BelleExpr = {
      val succ =
        (List.range(1,seq.succ.length+1,1).foldRight(ident)
        ((i:Int,tac:BelleExpr)=> simps(i) & tac))
      (List.range(-1,-(seq.ante.length+1),-1).foldRight(succ)
        ((i:Int,tac:BelleExpr)=> simps(i) & tac))
    }
  }

  /** Term simplification indices */

  private def qeTermProof(t:String,tt:String,pre:Option[String] = None): ProvableSig =
  {
    pre match{
      case None => proveBy(Equal(t.asTerm,tt.asTerm),QE)
      case Some(f) => proveBy(Imply(f.asFormula,Equal(t.asTerm,tt.asTerm)),QE)
    }
  }

  //These are mostly just the basic unit and identity rules
  private val mulArith = List(qeTermProof("0*F_()","0"), qeTermProof("F_()*0","0"), qeTermProof("1*F_()","F_()"),
    qeTermProof("F_()*1","F_()"), qeTermProof("-1*F_()","-F_()"), qeTermProof("F_()*-1","-F_()"))
  private val plusArith = List(qeTermProof("0+F_()","F_()"), qeTermProof("F_()+0","F_()"))
  private val minusArith = List( qeTermProof("F_()-0","F_()"),qeTermProof("0-F_()","-F_()"))
  //This is enabled by dependent rewriting
  private val divArith = List(qeTermProof("0/F_()","0",Some("F_()>0")), qeTermProof("0/F_()","0",Some("F_()<0")))
  private val powArith = List(qeTermProof("F_()^0","1",Some("F_()>0")), qeTermProof("F_()^0","1",Some("F_()<0")),
    qeTermProof("F_()^1","F_()"))

  //These may also be useful:
  //qeTermProof("F_()*(F_()^-1)","1",Some("F_()>0")), qeTermProof("(F_()^-1)*F_()","1",Some("F_()>0")))
  //qeTermProof("F_()+(-F_())","0"),qeTermProof("(-F_())+F_()","0"),
  //  qeTermProof("x-x","0"),
  //  qeTermProof("F_()+G_()-F_()","G_()"),
  //  qeTermProof("F_()+G_()-G_()","F_()"),

  def arithBaseIndex (t:Term) : List[ProvableSig] = {
    t match {
      case Plus(_,_) => plusArith
      case Minus(_,_) => minusArith
      case Times(_,_) => mulArith
      case Divide(_,_) => divArith
      case Power(_,_) => divArith
      case _ => List()
    }
  }

  //This generates theorems on the fly to simplify arithmetic
  def arithGroundIndex (t:Term) : List[ProvableSig] = {
    val res = t match {
      case Plus(n:Number,m:Number) => Some(n.value+m.value)
      case Minus(n:Number,m:Number) => Some(n.value-m.value)
      case Times(n:Number,m:Number) => Some(n.value*m.value)
      case Divide(n:Number,m:Number) => Some(n.value/m.value)
      case Power(n:Number,m:Number) if m.value.isValidInt => Some(n.value.pow(m.value.toInt))
      case Neg(n:Number) => Some(-n.value)
      case _ => None
    }
    res match {
      case None => List()
      case Some(v) =>
        val pr = proveBy(Equal(t,Number(v)),?(RCF))
        if(pr.isProved) List(pr)
        else List()
    }
  }

  def groundTermEval(t:Term) : Option[(Term,ProvableSig)] =
  {
    val res = t match {
      case Plus(n:Number,m:Number) => Some(n.value+m.value)
      case Minus(n:Number,m:Number) => Some(n.value-m.value)
      case Times(n:Number,m:Number) => Some(n.value*m.value)
      case Divide(n:Number,m:Number) => Some(n.value/m.value)
      case Power(n:Number,m:Number) => Some(n.value.pow(m.value.toInt))
      case Neg(n:Number) => Some(-n.value)
      case _ => None
    }

    res match {
      case None => None
      case Some(v) =>
        val pr = proveBy(Equal(t,Number(v)),?(RCF))
        if(pr.isProved) Some(Number(v),pr)
        else None
    }
  }

  /** Formula simplification indices */
  private def propProof(f:String,ff:String,precond:Option[String] = None):ProvableSig =
  {
    precond match {
      case Some(pre) =>
        proveBy(Imply(pre.asFormula,Equiv(f.asFormula,ff.asFormula)), prop)
      case None =>
        proveBy(Equiv(f.asFormula,ff.asFormula), prop)
    }
  }

  //F_() -> (F_() <-> true)
  val tauto = propProof("F_()","true",Some("F_()"))
  //!(F_()) -> (F_() <-> false)
  val tauto2 = propProof("F_()","false",Some("!F_()"))

  //This is a critical
  def baseIndex (f:Formula) : List[ProvableSig] = {
    f match {
      case True => List()
      case False => List()
      case _ => List(tauto,tauto2)
    }
  }

  private def qeFormulaProof(f:Option[String],t:String,tt:String):ProvableSig =
  {
    val ttt  = tt.asFormula
    f match{
      case None => proveBy(Equiv(t.asFormula,ttt),prop & QE)
      case Some(f) => proveBy(Imply(f.asFormula,Equiv(t.asFormula,ttt)),prop & QE)
    }
  }

  val ltNotReflex = qeFormulaProof(None,"F_()<F_()","false")
  val gtNotReflex = qeFormulaProof(None,"F_()>F_()","false")
  val neqNotReflex = qeFormulaProof(None,"F_()!=F_()","false")
  val equalReflex = qeFormulaProof(None,"F_() = F_()","true")
  val lessequalReflex = qeFormulaProof(None,"F_() <= F_()","true")
  val greaterequalReflex = qeFormulaProof(None,"F_() >= F_()","true")

  val eqSym = qeFormulaProof(Some("F_() = G_()"),"G_() = F_()","true")
  val neqSym = qeFormulaProof(Some("F_() != G_()"),"G_() != F_()","true")
  val gtNotSym = qeFormulaProof(Some("F_() > G_()"),"G_() > F_()","false")
  val ltNotSym = qeFormulaProof(Some("F_() < G_()"),"G_() < F_()","false")

  private def qeSearch(cmp1:(Term,Term)=>Formula,cmps:List[(Term,Term)=>Formula]) : List[ProvableSig] = {
    //Use partial QE because I don't want to do everything by hand..
    val f = "F_()".asTerm
    val g = "G_()".asTerm
    val key = cmp1(f,g)
    cmps.flatMap(
      (cmp:(Term,Term) => Formula) => {
          List(
            proveBy(Imply(cmp(f, g), Equiv(key, True)), prop & (QE*)),
            proveBy(Imply(cmp(f, g), Equiv(key, False)), prop & (QE*)),
            proveBy(Imply(cmp(g, f), Equiv(key, True)), prop & (QE*)),
            proveBy(Imply(cmp(g, f), Equiv(key, False)), prop & (QE*))
          )
      }
    ).filter(_.isProved)
  }

  val eqs = eqSym::qeSearch(Equal.apply,List(NotEqual.apply,Greater.apply,GreaterEqual.apply,Less.apply,LessEqual.apply))
  val neqs = neqSym::qeSearch(NotEqual.apply,List(Equal.apply,Greater.apply,GreaterEqual.apply,Less.apply,LessEqual.apply))
  val gts = gtNotSym::qeSearch(Greater.apply,List(Equal.apply,NotEqual.apply,GreaterEqual.apply,Less.apply,LessEqual.apply))
  val ges = qeSearch(GreaterEqual.apply,List(Equal.apply,NotEqual.apply,Greater.apply,Less.apply,LessEqual.apply))
  val lts = ltNotSym::qeSearch(Less.apply,List(Equal.apply,NotEqual.apply,Greater.apply,GreaterEqual.apply,LessEqual.apply))
  val les = qeSearch(LessEqual.apply,List(Equal.apply,NotEqual.apply,Greater.apply,GreaterEqual.apply,Less.apply))

  //This contains the basic heuristics for closing a comparison formula
  def cmpIndex (f:Formula) : List[ProvableSig] = {

    f match {
      // Reflexive cases
      // This protects against unification errors using Scala to inspect the term directly
      case bop:ComparisonFormula if bop.left==bop.right =>
        bop match{
          case Less(_,_) => List(ltNotReflex)
          case Greater(_,_) => List(gtNotReflex)
          case NotEqual(_,_) => List(neqNotReflex)
          case Equal(_,_) => List(equalReflex)
          case GreaterEqual(_,_) => List(greaterequalReflex)
          case LessEqual(_,_) => List(lessequalReflex)
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

  val andT = propProof("F_() & true","F_()")
  val Tand = propProof("true & F_()","F_()")
  val andF = propProof("F_() & false","false")
  val Fand = propProof("false & F_()","false")

  val implyT = propProof("F_() -> true","true")
  val Timply = propProof("true -> F_()","F_()")
  val implyF = propProof("F_() -> false","!F_()")
  val Fimply = propProof("false -> F_()","true")

  val orT = propProof("F_() | true","true")
  val Tor = propProof("true | F_()","true")
  val orF = propProof("F_() | false","F_()")
  val For = propProof("false | F_()","F_()")

  val equivT = propProof("F_() <-> true","F_()")
  val Tequiv = propProof("true <-> F_()","F_()")
  val equivF = propProof("F_() <-> false","!F_()")
  val Fequiv = propProof("false <-> F_()","!F_()")

  val notT = propProof("!true","false")
  val notF = propProof("!false","true")

  val forallTrue = proveBy("(\\forall x_ true)<->true".asFormula, auto )
  val forallFalse = proveBy("(\\forall x_ false)<->false".asFormula, auto)
  val existsTrue = proveBy("(\\exists x_ true)<->true".asFormula, auto )
  val existsFalse = proveBy("(\\exists x_ false)<->false".asFormula, auto )

  def boolIndex (f:Formula) : List[ProvableSig] ={
    f match {
      //Note: more pattern matching possible here
      case And(l,r) => List(andT,Tand,andF,Fand)
      case Imply(l,r) => List(implyT,Timply,implyF,Fimply)
      case Or(l,r) => List(orT,Tor,orF,For)
      case Equiv(l,r) =>  List(equivT,Tequiv,equivF,Fequiv)
      case Not(u) => List(notT,notF,DerivedAxioms.doubleNegationAxiom.fact)
      case Forall(_,_) => List(forallTrue,forallFalse)
      case Exists(_,_) => List(existsTrue,existsFalse)
      case _ => List()
    }
  }
}
