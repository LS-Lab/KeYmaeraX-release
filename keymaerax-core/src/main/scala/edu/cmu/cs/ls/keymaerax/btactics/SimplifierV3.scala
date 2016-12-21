package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig

import scala.collection.immutable.{Map, _}

/**
  * Note: this is meant to a watered down version of SimplifierV2
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

  //The internal lemmas for binary connectives
  private def termAx(ctor:(Term,Term)=>Term) : (ProvableSig,ProvableSig,ProvableSig) = {
    val limp = "A_() -> (L_() = LL_())".asFormula
    val rimp = "B_() -> (R_() = RR_())".asFormula
    val lhs = ctor("L_()".asTerm,"R_()".asTerm)
    val lAx = proveBy(Imply(limp,Imply( "A_()".asFormula ,Equal(lhs, ctor("LL_()".asTerm,"R_()".asTerm)))),prop & exhaustiveEqL2R(-1) & cohideR(1) & byUS("= reflexive"))
    val rAx = proveBy(Imply(rimp,Imply( "B_()".asFormula ,Equal(lhs, ctor("L_()".asTerm,"RR_()".asTerm)))),prop & exhaustiveEqL2R(-1) & cohideR(1) & byUS("= reflexive"))
    val lrAx = proveBy(Imply(And(limp,rimp),Imply( "A_() & B_()".asFormula ,Equal(lhs, ctor("LL_()".asTerm,"RR_()".asTerm)))),prop & exhaustiveEqL2R(-1) & exhaustiveEqL2R(-2) & cohideR(1) & byUS("= reflexive"))
    (lAx,rAx,lrAx)
  }

  private val plusAxs = termAx(Plus.apply)
  private val minusAxs = termAx(Minus.apply)
  private val timesAxs = termAx(Times.apply)
  private val divAxs = termAx(Divide.apply)
  private val powAxs = termAx(Power.apply)

  private val equalTrans = proveBy("(P_() -> (F_() = FF_())) & (Q_() -> (FF_() = FFF_())) -> (P_() & Q_() -> (F_() = FFF_())) ".asFormula,prop & QE)

  private def qeTermProof(t:String,tt:String,pre:Option[String] = None): ProvableSig =
  {
    pre match{
      case None => proveBy(Equal(t.asTerm,tt.asTerm),QE)
      case Some(f) => proveBy(Imply(f.asFormula,Equal(t.asTerm,tt.asTerm)),QE)
    }
  }

  //These may also be useful:
  //qeTermProof("F_()*(F_()^-1)","1",Some("F_()>0")), qeTermProof("(F_()^-1)*F_()","1",Some("F_()>0")))
  //qeTermProof("F_()+(-F_())","0"),qeTermProof("(-F_())+F_()","0"),
  //  qeTermProof("x-x","0"),
  //  qeTermProof("F_()+G_()-F_()","G_()"),
  //  qeTermProof("F_()+G_()-G_()","F_()"),

  //These are mostly just the basic unit and identity rules
  private val mulArith = List(qeTermProof("0*F_()","0"), qeTermProof("F_()*0","0"), qeTermProof("1*F_()","F_()"),
    qeTermProof("F_()*1","F_()"), qeTermProof("-1*F_()","-F_()"), qeTermProof("F_()*-1","-F_()"))
  private val plusArith = List(qeTermProof("0+F_()","F_()"), qeTermProof("F_()+0","F_()"))
  private val minusArith = List(qeTermProof("0-F_()","-F_()"), qeTermProof("F_()-0","F_()"))
  //This is enabled by dependent rewriting
  private val divArith = List(qeTermProof("0/F_()","0",Some("F_()>0")), qeTermProof("0/F_()","0",Some("F_()<0")))
  private val powArith = List(qeTermProof("F_()^0","1",Some("F_()>0")), qeTermProof("F_()^0","1",Some("F_()<0")),
    qeTermProof("F_()^1","F_()"))

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

  /** Term simplifier */
  def termSimp(t:Term, ctx:HashSet[Formula], taxs:Term => List[ProvableSig] = arithBaseIndex) : (Term, Option[(Formula,ProvableSig)]) =
  {
    val (rect,recpropt) =
      t match {
        case bop: BinaryCompositeTerm =>
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
        case _ => (t, None)
      }

    //todo: Should this rewrite to saturation? Or is once enough?
    val rw = taxs(rect).toStream.flatMap( pr => applyTermProvable(rect,ctx,pr)).headOption
    rw match {
      case None => (rect,recpropt)
      case Some((tt,prem,pr)) =>
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

  private val equivTrans = proveBy("(P_() -> (F_() <-> FF_())) & (Q_() -> (FF_() <-> FFF_())) -> (P_() & Q_() -> (F_() <-> FFF_())) ".asFormula,prop)

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
  //val andSym = propProof("P_() & Q_()","true","Q_() & P_()")

  def baseIndex (f:Formula) : List[ProvableSig] = {
    f match {
      case True => List()
      case False => List()
      case _ => List(tauto,tauto2)
    }
  }

  def boolIndex (f:Formula) : List[ProvableSig] ={
    f match {
      //Note: more pattern matching possible here
      case And(l,r) => List(andT,Tand,andF,Fand)
      case Imply(l,r) => List(implyT,Timply,implyF,Fimply)
      case Or(l,r) => List(orT,Tor,orF,For)
      case Equiv(l,r) =>  List(equivT,Tequiv,equivF,Fequiv)
      case Not(u) => List(notT,notF)
      case _ => List()
    }
  }

//  def deMorganIndex (f:Formula) : List[ProvableSig] = {
//  }

  def composeIndex( i1:Formula => List[ProvableSig], i2:Formula => List[ProvableSig] )
                  (f:Formula) : List[ProvableSig] = i1(f) ++ i2(f)

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

  def addCtx(ctx:HashSet[Formula],f:Formula) : HashSet[Formula] =
  {
    if(ctx.contains(f) | f.equals(True) | f.equals(Not(False))){
      return ctx
    }
    f match {
      case And(l,r) => addCtx(addCtx(ctx,l),r)
      //todo: is it possible to make Nots smart here?
      case _ => ctx+f
    }
  }

  def formulaSimp(f:Formula, ctx:HashSet[Formula] = HashSet(),
                  faxs: Formula => List[ProvableSig] = composeIndex(baseIndex,boolIndex),
                  taxs: Term => List[ProvableSig] = arithBaseIndex) : (Formula,Option[(Formula,ProvableSig)]) =
  {
    //todo: enable flag to toggle left to right, right to left rewriting?
    val (recf,recpropt) =
    f match {
      case And(l,r) =>
        val (lf,lpropt) = formulaSimp(l,ctx,faxs)
        val (rf,rpropt) = formulaSimp(r,addCtx(ctx,lf),faxs)
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
        val (lf,lpropt) = formulaSimp(l,ctx,faxs)
        val (rf,rpropt) = formulaSimp(r,addCtx(ctx,lf),faxs)
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
        val (lf,lpropt) = formulaSimp(l,ctx,faxs)
        val (rf,rpropt) = formulaSimp(r,addCtx(ctx,Not(lf)),faxs)
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

  def simpWithDischarge(ctx:IndexedSeq[Formula],f:Formula) : ProvableSig = {
    val hs = HashSet(ctx: _*) //todo: Apply simple decomposition that prop can handle here
    val (recf,recpropt) = formulaSimp(f,hs,composeIndex(baseIndex,boolIndex))

    proveBy( Sequent(ctx,IndexedSeq(Equiv(f,recf))),
      recpropt match {
        case None => cohideR(1) & byUS("= reflexive")
        case Some((prem,recpr)) =>
          cut(prem) <( implyRi & cohideR(1) & by(recpr) , hideR(1) & prop )
      }
    )

  }

  private def weaken(ctx:IndexedSeq[Formula]): ForwardTactic = pr => {
    val p = ProvableSig.startProof(pr.conclusion.glue(Sequent(ctx, IndexedSeq())))
    proveBy(p,
      cohideR(1) & //('Llast)*ctx.length &
        by(pr))
  }

  val divSimp = proveBy("t_()>0 -> 0 / t_() = 0".asFormula,QE)

  //make tail rec
  //Returns the list of premises, the key and the rewritten value
  def decomposeTermAx(f:Formula) : (List[Formula],Term,Term) = {
    f match {
      case Equal(l,r) => (List(),l,r)
      case Imply(l,r) =>
        val (ls,lrec,rrec) = decomposeTermAx(r)
        (l::ls,lrec,rrec)
      case _ => ??? //Invalid
    }
  }


}
