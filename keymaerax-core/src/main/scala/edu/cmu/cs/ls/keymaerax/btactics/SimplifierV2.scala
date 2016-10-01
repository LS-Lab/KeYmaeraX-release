package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

import scala.collection.immutable._

/**
  * Created by yongkiat on 9/29/16.
  */
object SimplifierV2 {

  /**
    * Returns the expression in expected position of |- t = t' or ctx |- f <-> f'
    * @param pr the provable from which to extract the expression
    * @return
    */
  private def extract(pr:Provable):Expression = {
    pr.conclusion.succ(0).sub(PosInExpr(1::Nil)).get
  }

  private def arithSimpAxioms(e:Expression): List[String] =
  {
    e match {
      case t:Term => t match{
        //todo: Need more simple arithmetic axioms in DerivedAxioms
        case Plus(_,_) => List("0+","+0","+ inverse")
        case Times(_,_) => List("0*","*0","* inverse")
        case _ => Nil
      }
      case _ => Nil
    }
  }

  private val plusLemma =
    proveBy(
      "(A() = B()) & (X() = Y()) -> (A()+X() = B()+Y())".asFormula,QE)
  private val minusLemma =
    proveBy(
      "(A() = B()) & (X() = Y()) -> (A()-X() = B()-Y())".asFormula,QE)
  private val timesLemma =
    proveBy(
      "(A() = B()) & (X() = Y()) -> (A()*X() = B()*Y())".asFormula,QE)
  //power and divide need side conditions

  /**
    * Takes a term t, with an equality context ctx and returns ctx |- t = t' using equalities in ctx
    * This is probably hopelessly slow...
    * @param t
    * @param ctx
    * @return
    */
  def equalityRewrites(t:Term,ctx:IndexedSeq[Formula]) :Provable = {
    t match {
      case a:AtomicTerm =>
        val pos = ctx.indexWhere( f => f match {
          case (Equal(l,_)) => if (a.equals(l)) true else false
          case _ => false})
        if (pos >= 0){
          proveBy(Sequent(ctx,IndexedSeq(ctx(pos))),close)
        }
        else {
          weaken(ctx)(DerivedAxioms.equalReflex.fact(
            USubst(SubstitutionPair(FuncOf(Function("s_",None,Unit,Real),Nothing), t)::Nil)))
        }
      case bop:BinaryCompositeTerm if (bop match {case Divide(_,_)=> false case Power(_,_) => false case _ => true})=>
        val l = bop.left
        val r = bop.right
        val lpr = equalityRewrites(l,ctx)
        val rpr = equalityRewrites(r,ctx)
        val lt = extract(lpr).asInstanceOf[Term]
        val rt = extract(rpr).asInstanceOf[Term]
        val lem = bop match{
          case Plus(_,_) => plusLemma
          case Minus(_,_) => minusLemma
          case Times(_,_) => timesLemma
        }
        proveBy(Sequent(ctx,IndexedSeq(Equal(bop.reapply(l,r),bop.reapply(lt,rt)))),
          cut(Equal(l,lt)) <(
            cut(Equal(r,rt)) <(
            useAt(lem,PosInExpr(1::Nil))(SuccPos(0)) & andR(1) <(
              closeId,closeId
              ),
            hideL('Llast) & hideR(SuccPos(0)) & by(rpr)),
          hideR(SuccPos(0))& by(lpr)
        ))
      case _ =>
        weaken(ctx)(DerivedAxioms.equalReflex.fact(
          USubst(SubstitutionPair(FuncOf(Function("s_",None,Unit,Real),Nothing), t)::Nil)))
    }

  }

  /**
    * Recursive term simplification using chase, proving |- t = t'
    * @param t The term to be simplifed
    */
  def termSimp(t:Term): Provable =
  {
    //todo: This may need to be generalized to do allow term simplification under a context
    val init = DerivedAxioms.equalReflex.fact(USubst(SubstitutionPair(FuncOf(Function("s_",None,Unit,Real),Nothing), t)::Nil))
    val pf = t match {
      case bop: BinaryCompositeTerm =>
        val l = bop.left
        val r = bop.right
        val lpr = termSimp(l)
        val lt = extract(lpr).asInstanceOf[Term]
        val rpr = termSimp(r)
        val rt = extract(rpr).asInstanceOf[Term]
        val nt = bop.reapply(lt,rt)
        proveBy(Sequent(IndexedSeq(), IndexedSeq(Equal(t, nt))),
          CEat(lpr)(SuccPosition(1,1::0::Nil))&
            CEat(rpr)(SuccPosition(1,1::1::Nil))& by(init))
      case _ => init
    }
    //println("Simplified: "+pf)
    val fin = chaseFor(3,3,e=>arithSimpAxioms(e),(s,p)=>pr=>pr)(SuccPosition(1,1::Nil))(pf)
    //println("Final: "+fin)
    fin
  }

  def termSimpWithRewrite(t:Term,ctx:IndexedSeq[Formula]): Provable =
  {
    //todo: filter context and keep only equalities around
    //todo: maybe do repeated equality rewriting
    val teq = equalityRewrites(t,ctx)
    val tt = extract(teq).asInstanceOf[Term]
    val tpr = termSimp(tt)
    val ttf = extract(tpr).asInstanceOf[Term]
    proveBy(Sequent(ctx,IndexedSeq(Equal(t,ttf))),
      CEat(tpr)(SuccPosition(1,1::Nil)) &
      cut(Equal(t,tt))<(close,
        hideR(SuccPos(0)) & by(teq)))

  }

  private def weaken(ctx:IndexedSeq[Formula]): ForwardTactic = pr => {
    val p = Provable.startProof(pr.conclusion.glue(Sequent(ctx, IndexedSeq())))
    proveBy(p,
      hideL('Llast)*ctx.length &
        by(pr))
  }

  //Justifications for adding things to the context
  private val andLemma =
  proveBy(
    "((P_() <-> F_()) & (F_() -> (Q_() <-> G_()))) ->(P_() & Q_() <-> F_() & G_())".asFormula,prop)

  private val implyLemma =
    proveBy(
      "((P_() <-> F_()) & (F_() -> (Q_() <-> G_()))) ->(P_() -> Q_() <-> F_() -> G_())".asFormula,prop)

  private val orLemma =
    proveBy(
      "((P_() <-> F_()) & (!(F_()) -> (Q_() <-> G_()))) ->(P_() | Q_() <-> F_() | G_())".asFormula,prop)

  private val equivLemma =
    proveBy(
      "((P_() <-> F_()) & (Q_() <-> G_())) ->((P_() <-> Q_()) <-> (F_() <-> G_()))".asFormula,prop)

  private val notLemma =
    proveBy(
      "(P_() <-> F_()) ->(!P_() <-> !F_())".asFormula,prop)

  private val equalLemma =
    proveBy(
      "(A() = B()) & (X() = Y()) -> (A() = X() <-> B() = Y())".asFormula,QE)

  private val notequalLemma =
    proveBy(
      "(A() = B()) & (X() = Y()) -> (A() != X() <-> B() != Y())".asFormula,QE)

  private val greaterequalLemma =
    proveBy(
      "(A() = B()) & (X() = Y()) -> (A() >= X() <-> B() >= Y())".asFormula,QE)

  private val greaterLemma =
    proveBy(
      "(A() = B()) & (X() = Y()) -> (A() > X() <-> B() > Y())".asFormula,QE)

  private val lessequalLemma =
    proveBy(
      "(A() = B()) & (X() = Y()) -> (A() <= X() <-> B() <= Y())".asFormula,QE)

  private val lessLemma =
    proveBy(
      "(A() = B()) & (X() = Y()) -> (A() < X() <-> B() < Y())".asFormula,QE)

  private val equivTrans =
    proveBy("(P() <-> Q()) -> (Q() <-> R()) -> (P() <-> R())".asFormula,prop)

  // Context management tactic generator for simplifier
  // Returns a new context ctx', and a tactic that turns
  // a goal of the form: ctx,f |- G into ctx' |- G
  // Currently only needed for And and Not, but can be generalized to work with other things too
  def addContext(f:Formula,ctx:IndexedSeq[Formula]) : (IndexedSeq[Formula],BelleExpr) =
  {
    //Don't add redundant things to context
    if(ctx.contains(f) | f.equals(True) | f.equals(Not(False))){
      return (ctx,hideL('Llast))
    }
    f match {
      //Ands are recursively decomposed into non-Ands and added to the left of the sequent
      case And(l,r) =>
        val (ctxL,tacL) = addContext(l,ctx)
        val (ctxR,tacR) = addContext(r,ctxL)
        (ctxR,andL('_) & implyRi(AntePos(ctx.length+1)) & tacL & implyR(SuccPos(0)) & tacR)
      //Both the de-morganed and originals are added to the context
      case Not(u) =>
        //Apply deMorgan things to Not
        val id = proveBy(Sequent(IndexedSeq(),IndexedSeq(Equiv(Not(u),Not(u)))),prop)
        val cpr = chaseFor(3,3,e=>AxiomIndex.axiomsFor(e),(s,p)=>pr=>pr)(SuccPosition(1,1::Nil))(id)
        val nu = extract(cpr).asInstanceOf[Formula]
        //No deMorgan applies, just add to context
        if (nu == f)
        {
          (ctx:+f,ident)
        }
        else
        {
          //Adds f to the context, but also all of its deMorganed things
          val(ctxU,tacU) = addContext(nu,ctx:+f)
          (ctxU,
            useAt(DerivedAxioms.andReflexive,PosInExpr(1::Nil))(AntePos(ctx.length)) & andL('_) &
            implyRi(AntePos(ctx.length)) & useAt(cpr,PosInExpr(0::Nil))(SuccPosition(1,0::Nil)) & implyR('_) & tacU)
        }
      case _ => (ctx:+f,ident)
    }

  }

  //Truth tables for propositional formulae
  //These should be in DerivedAxioms
  private def propProof(f:String,ff:String):Provable =
  {
    proveBy(Equiv(f.asFormula,ff.asFormula),prop)
  }

  val andT = propProof("F() & true","F()")
  val Tand = propProof("true & F()","F()")
  val andF = propProof("F() & false","false")
  val Fand = propProof("false & F()","false")

  val orT = propProof("F() | true","true")
  val Tor = propProof("true | F()","true")
  val orF = propProof("F() | false","F()")
  val For = propProof("false | F()","F()")

  val implyT = propProof("F() -> true","true")
  val Timply = propProof("true -> F()","F()")
  val implyF = propProof("F() -> false","!F()")
  val Fimply = propProof("false -> F()","true")

  val equivT = propProof("F() <-> true","F()")
  val Tequiv = propProof("true <-> F()","F()")
  val equivF = propProof("F() <-> false","!F()")
  val Fequiv = propProof("false <-> F()","!F()")

  val notT = propProof("!true","false")
  val notF = propProof("!false","true")

  private def propHeuristics(f:Formula) : Option[(Formula,Provable)] =
  {
    f match {
      case And(l,True) => Some(l,andT)
      case And(True,r) => Some(r,Tand)
      case And(_,False) => Some(False,andF)
      case And(False,_) => Some(False,Fand)

      case Or(l,True) => Some(True,orT)
      case Or(True,r) => Some(True,Tor)
      case Or(l,False) => Some(l,orF)
      case Or(False,r) => Some(r,For)

      case Imply(l,True) => Some(True,implyT)
      case Imply(True,r) => Some(r,Timply)
      case Imply(l,False) => Some(Not(l),implyF)
      case Imply(False,r) => Some(True,Fimply)

      case Equiv(l,True) => Some(l,equivT)
      case Equiv(True,r) => Some(r,Tequiv)
      case Equiv(l,False) => Some(Not(l),equivF)
      case Equiv(False,r) => Some(Not(r),Fequiv)

      case Not(True) => Some(False,notT)
      case Not(False) => Some(True,notF)

      case _ => None
    }
  }

  /**
    * Recursive formula simplification under a context using chase, proving ctx |- f = f'
    * The recursion always occurs left-to-right
    * @param f formula to simplify
    * @param ctx context in which to simplify
    * @return
    */
  def formulaSimp(f:Formula, ctx:IndexedSeq[Formula] = IndexedSeq()) : Provable =
  {
    //println("At: "+f+" Context: "+ctx)
    // todo: remove the use of prop from short circuit branches
    //Recursive simplification
    val recpr =
    f match {
      case And(l, r) =>
        val lpr = formulaSimp(l, ctx)
        val lf = extract(lpr).asInstanceOf[Formula]
        //short circuit
        if (lf.equals(False))
        {
          return proveBy(Sequent(ctx,IndexedSeq(Equiv(f,False))),
            cut(Equiv(l,lf))<(
              prop,
              hideR(SuccPos(0))& by(lpr)))
        }
        val (out,tac) = addContext(lf,ctx)
        //Use lf as part of context on the right
        val rpr = formulaSimp(r, out)
        val rf = extract(rpr).asInstanceOf[Formula]
        val nf = And(lf,rf)
        proveBy(Sequent(ctx, IndexedSeq(Equiv(f, nf))),
          cut(Equiv(l,lf)) <(
            cut(Imply(lf,Equiv(r,rf))) <(
              useAt(andLemma,PosInExpr(1::Nil))(SuccPos(0)) & andR(1) <(
                closeId,closeId
                ),
              hideL('Llast) & hideR(SuccPos(0)) & implyR(1) & tac & by(rpr)),
            hideR(SuccPos(0))& by(lpr)
            )
        )
      case Imply(l, r) =>
        val lpr = formulaSimp(l, ctx)
        val lf = extract(lpr).asInstanceOf[Formula]
        //short circuit
        if (lf.equals(False))
        {
          return proveBy(Sequent(ctx,IndexedSeq(Equiv(f,True))),
            cut(Equiv(l,lf))<(
              prop,
              hideR(SuccPos(0))& by(lpr)))
        }
        val (out,tac) = addContext(lf,ctx)
        //Use lf as part of context on the right
        val rpr = formulaSimp(r, out)
        val rf = extract(rpr).asInstanceOf[Formula]
        val nf = Imply(lf,rf)
        proveBy(Sequent(ctx, IndexedSeq(Equiv(f, nf))),
          cut(Equiv(l,lf)) <(
            cut(Imply(lf,Equiv(r,rf))) <(
              useAt(implyLemma,PosInExpr(1::Nil))(SuccPos(0)) & andR(1) <(
                closeId,closeId
                ),
              hideL('Llast) & hideR(SuccPos(0)) & implyR(1) & tac & by(rpr)),
            hideR(SuccPos(0))& by(lpr)
            )
        )
      case Or(l, r) =>
        val lpr = formulaSimp(l, ctx)
        val lf = extract(lpr).asInstanceOf[Formula]
        //short circuit
        if (lf.equals(True))
        {
          return proveBy(Sequent(ctx,IndexedSeq(Equiv(f,True))),
            cut(Equiv(l,lf))<(
              prop,
              hideR(SuccPos(0))& by(lpr)))
        }
        val (out,tac) = addContext(Not(lf),ctx)
        //Use lf as part of context on the right
        val rpr = formulaSimp(r, out)
        val rf = extract(rpr).asInstanceOf[Formula]
        val nf = Or(lf,rf)
        proveBy(Sequent(ctx, IndexedSeq(Equiv(f, nf))),
          cut(Equiv(l,lf)) <(
            cut(Imply(Not(lf),Equiv(r,rf))) <(
              useAt(orLemma,PosInExpr(1::Nil))(SuccPos(0)) & andR(1) <(
                closeId,closeId
                ),
              hideL('Llast) & hideR(SuccPos(0)) & implyR(1) & tac & by(rpr)),
            hideR(SuccPos(0))& by(lpr)
            )
        )
      case Equiv(l, r) =>
        val lpr = formulaSimp(l, ctx)
        val lf = extract(lpr).asInstanceOf[Formula]
        val rpr = formulaSimp(r, ctx)
        val rf = extract(rpr).asInstanceOf[Formula]
        val nf = Equiv(lf,rf)
        proveBy(Sequent(ctx, IndexedSeq(Equiv(f, nf))),
          cut(Equiv(l,lf)) <(
            cut(Equiv(r,rf)) <(
              useAt(equivLemma,PosInExpr(1::Nil))(SuccPos(0)) & andR(1) <(
                closeId,closeId
                ),
              hideL('Llast) & hideR(SuccPos(0)) & by(rpr)),
            hideR(SuccPos(0))& by(lpr)
            )
        )
      case Not(u) =>
        val upr = formulaSimp(u, ctx)
        val uf = upr.conclusion.succ(0).sub(PosInExpr(1 :: Nil)).get.asInstanceOf[Formula]
        val nf = Not(uf)
        proveBy(Sequent(ctx, IndexedSeq(Equiv(f, nf))),
          cut(Equiv(u,uf)) < (
            useAt(notLemma,PosInExpr(1::Nil))(SuccPos(0)) & closeId,
            hideR(SuccPos(0))&by(upr)))
      case cf:ComparisonFormula =>
        val l = cf.left
        val r = cf.right
        val lpr = termSimpWithRewrite(l,ctx)
        val rpr = termSimpWithRewrite(r,ctx)
        val lt = extract(lpr).asInstanceOf[Term]
        val rt = extract(rpr).asInstanceOf[Term]
        val nf = cf.reapply(lt,rt)
        val lem = cf match{
          case Equal(_,_) => equalLemma
          case NotEqual(_,_) => notequalLemma
          case GreaterEqual(_,_) => greaterequalLemma
          case Greater(_,_) => greaterLemma
          case LessEqual(_,_) => lessequalLemma
          case Less(_,_) => lessLemma
        }
        proveBy(Sequent(ctx, IndexedSeq(Equiv(cf, nf))),
          cut(Equal(l,lt))<(
            cut(Equal(r,rt))<(
              useAt(lem,PosInExpr(1::Nil))(SuccPos(0)) & andR(1) <(
                closeId,closeId
                ),
              hideL('Llast) & hideR(SuccPos(0)) & by(rpr)),
            hideR(SuccPos(0))& by(lpr)))
      case _ =>
        weaken(ctx)(DerivedAxioms.equivReflexiveAxiom.fact(
          USubst(SubstitutionPair(PredOf(Function("p_", None, Unit, Bool), Nothing), f) :: Nil)))
    }

    //Propositional simplification (these should be done by chase instead)
    val recf = extract(recpr).asInstanceOf[Formula]

    val proppr = propHeuristics(recf) match {
      case None => recpr
      case Some((ff,pr)) =>
        val pf = proveBy(Sequent(ctx,IndexedSeq(Equiv(recf,ff))),cohideR(SuccPos(0)) & byUS(pr))
        //This pattern proves transitivity of equivs
        proveBy(Sequent(ctx,IndexedSeq(Equiv(f,ff))),
          cut(Equiv(f,recf)) <(
            cut(Equiv(recf,ff)) <(
              implyRi(AntePos(ctx.length+1)) &
              implyRi(AntePos(ctx.length)) & cohideR(SuccPos(0)) & byUS(equivTrans),
              hideL('Llast) & hideR(SuccPos(0)) & by(pf)),
            hideR(SuccPos(0))& by(recpr)))
    }

    //Chase simplification
    val chasepr = chaseFor(3,3,e=>AxiomIndex.axiomsFor(e),(s,p)=>pr=>pr)(SuccPosition(1,1::Nil))(proppr)

    //Prove the formula if it occurs positively or negatively in the context
    val chasef = extract(chasepr).asInstanceOf[Formula]
    val tind = ctx.indexOf(chasef)
    if(tind>=0)
    {
      val prT = proveBy(Sequent(ctx,IndexedSeq(Equiv(chasef,True))),
        cohide2(AntePos(tind),SuccPos(0)) &
        useAt(equivT,PosInExpr(0::Nil))(SuccPos(0)) & close)
      proveBy(Sequent(ctx,IndexedSeq(Equiv(f,True))),
        cut(Equiv(f,chasef)) <(
          cut(Equiv(chasef,True)) <(
            implyRi(AntePos(ctx.length+1)) &
            implyRi(AntePos(ctx.length)) & cohideR(SuccPos(0)) & byUS(equivTrans),
            hideL('Llast) & hideR(SuccPos(0)) & by(prT)),
          hideR(SuccPos(0))& by(chasepr)))
    }
    else
    {
      val find = ctx.indexOf(Not(chasef))
      if(find>=0){
        val prF = proveBy(Sequent(ctx,IndexedSeq(Equiv(chasef,False))),
          cohide2(AntePos(find),SuccPos(0)) &
            useAt(equivF,PosInExpr(0::Nil))(SuccPos(0)) & close)
        proveBy(Sequent(ctx,IndexedSeq(Equiv(f,False))),
          cut(Equiv(f,chasef)) <(
            cut(Equiv(chasef,False)) <(
              implyRi(AntePos(ctx.length+1)) &
                implyRi(AntePos(ctx.length)) & cohideR(SuccPos(0)) & byUS(equivTrans),
              hideL('Llast) & hideR(SuccPos(0)) & by(prF)),
            hideR(SuccPos(0))& by(chasepr)))
      }
      else{
        chasepr
      }
    }
  }


}
