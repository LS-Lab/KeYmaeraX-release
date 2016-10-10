package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.core._
import scala.collection.immutable._

/**
  * Created by yongkiat on 9/29/16.
  */
object SimplifierV2 {

  /**
    * Returns the expression in expected position of ctx |- t = t' or ctx |- f <-> f'
    * @param pr the provable from which to extract the expression
    * @return
    */
  private def extract(pr:Provable):Expression = {
    pr.conclusion.succ(0).sub(PosInExpr(1::Nil)).get
  }

  //todo: All of these should be moved to derived axioms (some are already there, but missing the other side)
  //Proves |- f -> t = tt or just t = tt if f is given
  private def qeProof(f:Option[String],t:String,tt:String):(Term,Provable) =
  {
    val ttt  = tt.asTerm
    (ttt,
      f match{
        case None => proveBy(Equal(t.asTerm,ttt),QE)
        case Some(f) => proveBy(Imply(f.asFormula,Equal(t.asTerm,ttt)),QE)
      })
  }

  val arithProps = List(
    //Multiplication
    qeProof(None,"0*F_()","0"),
    qeProof(None,"F_()*0","0"),
    qeProof(None,"1*F_()","F_()"),
    qeProof(None,"F_()*1","F_()"),
    //qeProof(Some("F_()!=0"),"F_()*(F_()^-1)","1"),
    //qeProof(Some("F_()!=0"),"(F_()^-1)*F_()","1"),
    //Addition
    qeProof(None,"0+F_()","F_()"),
    qeProof(None,"F_()+0","F_()"),
    qeProof(None,"F_()+(-F_())","0"),
    qeProof(None,"(-F_())+F_()","0"),
    //Minus
    qeProof(None,"0-F_()","-F_()"),
    qeProof(None,"F_()-0","F_()"),
    qeProof(None,"F_()-F_()","0"),
    qeProof(None,"F_()+G_()-F_()","G_()"),
    //Division
    qeProof(None,"F_()/1","F_()"),
    //qeProof(Some("F_()!=0"),"F_()/F_()","1"),
    //qeProof(Some("F_()!=0"),"0/F_()","0"),
    //Negation
    qeProof(None,"-0","0"),
    qeProof(None,"-(-F_())","F_()")
  )

  def mksubst(s:Subst) :Subst = {
    //Force the substitution to not have variable renaming
    if(!s.renaming.isEmpty) {
      throw new ProverException("Substitution contains variable renaming: " + s)
    }
    return s
  }

  def qeHeuristics(eq:Provable): Option[Provable] = {
    //todo: filter the list, like what happens in chase
    for ((tt, pr) <- arithProps)
      try {
        return Some(useFor(pr, PosInExpr(0 :: Nil),s=>mksubst(s))(SuccPosition(1, 1 :: Nil))(eq))
      } catch {
        case _: ProverException =>
      }
    None
  }

  //Strips out constants and replaces them with 0 (+ unit)
  def flattenPlus(t:Term): (Term,BigDecimal) =
  {
    t match{
      case Plus(l,r) =>
        val (lt,lc) = flattenPlus(l)
        val (rt,rc) = flattenPlus(r)
        (Plus(lt,rt),(lc+rc))
      case n:Number =>
        (Number(0),n.value)
      case _ => (t,0)
    }
  }

  //Strips out constants and replaces them with 1 (* unit)
  def flattenTimes(t:Term): (Term,BigDecimal) =
  {
    t match{
      case Times(l,r) =>
        val (lt,lc) = flattenTimes(l)
        val (rt,rc) = flattenTimes(r)
        (Times(lt,rt),(lc*rc))
      case n:Number =>
        (Number(1),n.value)
      case _ => (t,1)
    }
  }

  //Fold constants
  def reassoc(t:Term): Provable =
  {
    val init = DerivedAxioms.equalReflex.fact(
      USubst(SubstitutionPair(FuncOf(Function("s_",None,Unit,Real),Nothing), t)::Nil))
    t match {
      case Plus(_,_) =>
        val (tt,c) = flattenPlus(t)
        if(c==0) init
        else proveBy(Equal(t,Plus(tt,Number(c))),QE)
      case Times(_,_) =>
        val (tt,c) = flattenTimes(t)
        if(c==1) init
        else proveBy(Equal(t,Times(tt,Number(c))),QE)
      case _ => init
    }
  }

  /**
    * Recursive term simplification using chase, proving |- t = t'
    * @param t The term to be simplifed
    */
  def termSimp(t:Term): (Term,Provable) =
  {
    //todo: This may need to be generalized to do allow term simplification under a context
    val init = DerivedAxioms.equalReflex.fact(
      USubst(SubstitutionPair(FuncOf(Function("s_",None,Unit,Real),Nothing), t)::Nil))
    val (rect,recpf) = t match {
      case bop: BinaryCompositeTerm =>
        val l = bop.left
        val r = bop.right
        val (lt,lpr) = termSimp(l)
        val (rt,rpr) = termSimp(r)
        val nt = bop.reapply(lt,rt)
        (nt,proveBy(Equal(t, nt),
          CEat(lpr)(SuccPosition(1,1::0::Nil))&
            CEat(rpr)(SuccPosition(1,1::1::Nil))& by(init)))
      case uop: UnaryCompositeTerm =>
        val u = uop.child
        val (ut,upr) = termSimp(u)
        val nt = uop.reapply(ut)
        (nt,proveBy(Equal(t,nt),
          CEat(upr)(SuccPosition(1,1::0::Nil)) & by (init)))
      case _ => (t,init)
    }

    //Apply arithmetic propositions
    val apf = qeHeuristics(recpf) match { case None => recpf case Some(pr) => pr}
    //println("Simplified: "+pf)
    //val fin = chaseFor(3,3,e=>AxiomIndex.axiomsFor(e),(s,p)=>pr=>pr)(SuccPosition(1,1::Nil))(apf)
    val ft = extract(apf).asInstanceOf[Term]
    //println("Final: "+fin)
    (ft,apf)
  }

  //Technically, we don't need QE for these (just use the proof for divideLemma)
  private val plusLemma = proveBy(
    "(A() = B()) & (X() = Y()) -> (A()+X() = B()+Y())".asFormula,QE)
  private val minusLemma =
    proveBy(
      "(A() = B()) & (X() = Y()) -> (A()-X() = B()-Y())".asFormula,QE)
  private val timesLemma =
    proveBy(
      "(A() = B()) & (X() = Y()) -> (A()*X() = B()*Y())".asFormula,QE)
  private val divideLemma =
    proveBy(
      "(A() = B()) & (X() = Y()) -> (A()/X() = B()/Y())".asFormula,
      implyR(1) & andL(-1) & exhaustiveEqL2R(-1) & exhaustiveEqL2R(-2) & cohideR(1) & byUS("= reflexive"))
  private val powerLemma =
    proveBy(
      "(A() = B()) & (X() = Y()) -> (A()^X() = B()^Y())".asFormula,
      implyR(1) & andL(-1) & exhaustiveEqL2R(-1) & exhaustiveEqL2R(-2) & cohideR(1) & byUS("= reflexive"))

  //Uses const congruence rule on a t and eq to generate |- eq -> t = t'
  def fwdeqL2R(eq:Formula,t:Term): Provable =
  {
    eq match
    {
      //Only rewrite equalities
      case Equal(l,r) =>
        val tdot = t.replaceFree(l,DotTerm())
        val tr = t.replaceFree(l,r)
        Provable.axioms("const congruence")(
          USubst(SubstitutionPair(FuncOf(Function("ctxT_", None, Real, Real), DotTerm()), tdot)::
            SubstitutionPair(FuncOf(Function("s", None, Unit, Real), Nothing), l) ::
            SubstitutionPair(FuncOf(Function("t", None, Unit, Real), Nothing), r) :: Nil))
      case _ => ???
    }
  }

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
      case bop:BinaryCompositeTerm =>
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
          case Divide(_,_) => divideLemma
          case Power(_,_) => powerLemma
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


  def termSimpWithRewrite(t:Term,ctx:IndexedSeq[Formula]): (Term,Provable) =
  {
    //todo: filter context and keep only equalities around
    //todo: maybe do repeated equality rewriting
    val teq = equalityRewrites(t,ctx)
    val tt = extract(teq).asInstanceOf[Term]
    val (ttf,tpr) = termSimp(tt)
    (ttf,proveBy(Sequent(ctx,IndexedSeq(Equal(t,ttf))),
      CEat(tpr)(SuccPosition(1,1::Nil)) &
        cut(Equal(t,tt))<(close,
          hideR(SuccPos(0)) & by(teq))))
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
  // (some already are)
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

      case Equal(l,r) if l.equals(r) => Some(True,equalReflex)
      case LessEqual(l,r) if l.equals(r) => Some(True,lessequalReflex)
      case GreaterEqual(l,r) if l.equals(r) => Some(True,greaterequalReflex)

      case _ => None
    }
  }

  //Reflexivity for comparison formulae
  //These should be in DerivedAxioms
  // (some already are)
  private def qeEquivProof(f:String,ff:String):Provable =
  {
    proveBy(Equiv(f.asFormula,ff.asFormula),QE)
  }

  val equalReflex = qeEquivProof("F() = F()","true")
  val lessequalReflex = qeEquivProof("F() <= F()","true")
  val greaterequalReflex = qeEquivProof("F() >= F()","true")

  /**
    * Recursive formula simplification under a context using chase, proving ctx |- f <-> f'
    * The recursion always occurs left-to-right
    * @param f formula to simplify
    * @param ctx context in which to simplify
    * @return f',pr where pr proves the equivalence
    */
  def formulaSimp(f:Formula, ctx:IndexedSeq[Formula] = IndexedSeq()) : (Formula,Provable) =
  {
    //println("At: "+f+" Context: "+ctx)
    // todo: remove the use of prop from short circuit branches
    //Recursive simplification
    val (recf:Formula,recpr:Provable) =
    f match {
      case And(l, r) =>
        val (lf,lpr) = formulaSimp(l, ctx)
        //short circuit
        if (lf.equals(False))
        {
          return (False,
            proveBy(Sequent(ctx,IndexedSeq(Equiv(f,False))),
              cut(Equiv(l,lf))<(
                prop,
                hideR(SuccPos(0))& by(lpr))))
        }
        //Update context with new formula
        val (out,tac) = addContext(lf,ctx)
        //Use lf as part of context on the right
        val (rf,rpr) = formulaSimp(r, out)
        val nf = And(lf,rf)
        (nf,proveBy(Sequent(ctx, IndexedSeq(Equiv(f, nf))),
          cut(Equiv(l,lf)) <(
            cut(Imply(lf,Equiv(r,rf))) <(
              useAt(andLemma,PosInExpr(1::Nil))(SuccPos(0)) & andR(1) <(
                closeId,closeId
                ),
              hideL('Llast) & hideR(SuccPos(0)) & implyR(1) & tac & by(rpr)),
            hideR(SuccPos(0))& by(lpr)
            )
        ))
      case Imply(l, r) =>
        val (lf,lpr) = formulaSimp(l, ctx)
        //short circuit
        if (lf.equals(False))
        {
          return (True,proveBy(Sequent(ctx,IndexedSeq(Equiv(f,True))),
            cut(Equiv(l,lf))<(
              prop,
              hideR(SuccPos(0))& by(lpr))))
        }
        val (out,tac) = addContext(lf,ctx)
        //Use lf as part of context on the right
        val (rf,rpr) = formulaSimp(r, out)
        val nf = Imply(lf,rf)
        (nf,proveBy(Sequent(ctx, IndexedSeq(Equiv(f, nf))),
          cut(Equiv(l,lf)) <(
            cut(Imply(lf,Equiv(r,rf))) <(
              useAt(implyLemma,PosInExpr(1::Nil))(SuccPos(0)) & andR(1) <(
                closeId,closeId
                ),
              hideL('Llast) & hideR(SuccPos(0)) & implyR(1) & tac & by(rpr)),
            hideR(SuccPos(0))& by(lpr)
            )
        ))
      case Or(l, r) =>
        val (lf,lpr) = formulaSimp(l, ctx)
        //short circuit
        if (lf.equals(True))
        {
          return (True,proveBy(Sequent(ctx,IndexedSeq(Equiv(f,True))),
            cut(Equiv(l,lf))<(
              prop,
              hideR(SuccPos(0))& by(lpr))))
        }
        val (out,tac) = addContext(Not(lf),ctx)
        //Use lf as part of context on the right
        val (rf,rpr) = formulaSimp(r, out)
        val nf = Or(lf,rf)
        (nf,proveBy(Sequent(ctx, IndexedSeq(Equiv(f, nf))),
          cut(Equiv(l,lf)) <(
            cut(Imply(Not(lf),Equiv(r,rf))) <(
              useAt(orLemma,PosInExpr(1::Nil))(SuccPos(0)) & andR(1) <(
                closeId,closeId
                ),
              hideL('Llast) & hideR(SuccPos(0)) & implyR(1) & tac & by(rpr)),
            hideR(SuccPos(0))& by(lpr)
            )
        ))
      case Equiv(l, r) =>
        val (lf,lpr) = formulaSimp(l, ctx)
        val (rf,rpr) = formulaSimp(r, ctx)
        val nf = Equiv(lf,rf)
        (nf,proveBy(Sequent(ctx, IndexedSeq(Equiv(f, nf))),
          cut(Equiv(l,lf)) <(
            cut(Equiv(r,rf)) <(
              useAt(equivLemma,PosInExpr(1::Nil))(SuccPos(0)) & andR(1) <(
                closeId,closeId
                ),
              hideL('Llast) & hideR(SuccPos(0)) & by(rpr)),
            hideR(SuccPos(0))& by(lpr)
            )
        ))
      case Not(u) =>
        val (uf,upr) = formulaSimp(u, ctx)
        val nf = Not(uf)
        (nf,proveBy(Sequent(ctx, IndexedSeq(Equiv(f, nf))),
          cut(Equiv(u,uf)) < (
            useAt(notLemma,PosInExpr(1::Nil))(SuccPos(0)) & closeId,
            hideR(SuccPos(0))&by(upr))))
      case cf:ComparisonFormula =>
        val l = cf.left
        val r = cf.right
        val (lt,lpr) = termSimpWithRewrite(l,ctx)
        val (rt,rpr) = termSimpWithRewrite(r,ctx)
        val nf = cf.reapply(lt,rt)
        val lem = cf match{
          case Equal(_,_) => equalLemma
          case NotEqual(_,_) => notequalLemma
          case GreaterEqual(_,_) => greaterequalLemma
          case Greater(_,_) => greaterLemma
          case LessEqual(_,_) => lessequalLemma
          case Less(_,_) => lessLemma
        }
        (nf,proveBy(Sequent(ctx, IndexedSeq(Equiv(cf, nf))),
          cut(Equal(l,lt))<(
            cut(Equal(r,rt))<(
              useAt(lem,PosInExpr(1::Nil))(SuccPos(0)) & andR(1) <(
                closeId,closeId
                ),
              hideL('Llast) & hideR(SuccPos(0)) & by(rpr)),
            hideR(SuccPos(0))& by(lpr))))
      case q:Quantified =>
        //Simplest thing to do is discard context completely
        //In this case upr has the form |- A <-> B so useFor
        val (uf,upr) = formulaSimp(q.child,IndexedSeq())
        val init = weaken(ctx)(DerivedAxioms.equivReflexiveAxiom.fact(
          USubst(SubstitutionPair(PredOf(Function("p_", None, Unit, Bool), Nothing), f) :: Nil)))
        val pr = useFor(upr, PosInExpr(0 :: Nil))(SuccPosition(1, 1:: 0 :: Nil))(init)
        (extract(pr).asInstanceOf[Formula],pr)
      case m:Modal =>
        val (uf,upr) = formulaSimp(m.child,IndexedSeq())
        val init = weaken(ctx)(DerivedAxioms.equivReflexiveAxiom.fact(
          USubst(SubstitutionPair(PredOf(Function("p_", None, Unit, Bool), Nothing), f) :: Nil)))
        val pr = useFor(upr, PosInExpr(0 :: Nil))(SuccPosition(1, 1:: 1 :: Nil))(init)
        (extract(pr).asInstanceOf[Formula],pr)
      case _ =>
        (f,weaken(ctx)(DerivedAxioms.equivReflexiveAxiom.fact(
          USubst(SubstitutionPair(PredOf(Function("p_", None, Unit, Bool), Nothing), f) :: Nil))))
    }

    //Propositional simplification (these should be done by chase instead)

    val (_,proppr:Provable) = propHeuristics(recf) match {
      case None => (recf,recpr)
      case Some((ff,pr)) =>
        val pf = proveBy(Sequent(ctx,IndexedSeq(Equiv(recf,ff))),cohideR(SuccPos(0)) & byUS(pr))
        //This pattern proves transitivity of equivs
        (ff,proveBy(Sequent(ctx,IndexedSeq(Equiv(f,ff))),
          cut(Equiv(f,recf)) <(
            cut(Equiv(recf,ff)) <(
              implyRi(AntePos(ctx.length+1)) &
                implyRi(AntePos(ctx.length)) & cohideR(SuccPos(0)) & byUS(equivTrans),
              hideL('Llast) & hideR(SuccPos(0)) & by(pf)),
            hideR(SuccPos(0))& by(recpr))))
    }

    //Chase simplification
    val chasepr = chaseFor(3,3,e=>AxiomIndex.axiomsFor(e),(s,p)=>pr=>pr)(SuccPosition(1,1::Nil))(proppr)
    val chasef = extract(chasepr).asInstanceOf[Formula]

    //Prove the formula if it occurs positively or negatively in the context
    //todo: Also check for negations of comparison formulae in context
    val tind = ctx.indexOf(chasef)
    if(tind>=0)
    {
      val prT = proveBy(Sequent(ctx,IndexedSeq(Equiv(chasef,True))),
        cohide2(AntePos(tind),SuccPos(0)) &
          useAt(equivT,PosInExpr(0::Nil))(SuccPos(0)) & close)
      (True,proveBy(Sequent(ctx,IndexedSeq(Equiv(f,True))),
        cut(Equiv(f,chasef)) <(
          cut(Equiv(chasef,True)) <(
            implyRi(AntePos(ctx.length+1)) &
              implyRi(AntePos(ctx.length)) & cohideR(SuccPos(0)) & byUS(equivTrans),
            hideL('Llast) & hideR(SuccPos(0)) & by(prT)),
          hideR(SuccPos(0))& by(chasepr))))
    }
    else
    {
      val find = ctx.indexOf(Not(chasef))
      if(find>=0){
        val prF = proveBy(Sequent(ctx,IndexedSeq(Equiv(chasef,False))),
          cohide2(AntePos(find),SuccPos(0)) &
            useAt(equivF,PosInExpr(0::Nil))(SuccPos(0)) & close)
        (False,proveBy(Sequent(ctx,IndexedSeq(Equiv(f,False))),
          cut(Equiv(f,chasef)) <(
            cut(Equiv(chasef,False)) <(
              implyRi(AntePos(ctx.length+1)) &
                implyRi(AntePos(ctx.length)) & cohideR(SuccPos(0)) & byUS(equivTrans),
              hideL('Llast) & hideR(SuccPos(0)) & by(prF)),
            hideR(SuccPos(0))& by(chasepr))))
      }
      else{
        (chasef,chasepr)
      }
    }
  }

  //Splits an equivalence in succedent of provable into left and right halves
  def splitEquiv(pr:Provable): (Provable,Provable) = {
    val seq = pr.conclusion
    assert(seq.succ.length == 1 && seq.succ(0).isInstanceOf[Equiv])
    seq.succ(0).fml match {
      case Equiv(l, r) =>
        val lpr = proveBy(Sequent(seq.ante, IndexedSeq(Imply(l, r))), equivifyR(1) & by(pr))
        val rpr = proveBy(Sequent(seq.ante, IndexedSeq(Imply(r, l))), equivifyR(1) & commuteEquivR(1) & by(pr))
        (lpr, rpr)
      case _ => ???
    }
  }

  //Commented out in ProofRuleTactics
  def exchangeR (posOne:SuccPos,posTwo:SuccPos) : BelleExpr = new BuiltInTactic("exchangeR") {
    override def result(provable: Provable) = {
      provable(ExchangeRightRule(posOne,posTwo), 0)
    }
  }

  //cohiding on one side of the sequent only
  def cohideRonly(pos:Position):BelleExpr ={
    assert(pos.isTopLevel & pos.isSucc)
    (exchangeR(SuccPos(0),pos.checkSucc.top)) & (hideR(2)*)
  }

  //Simplifies a formula including sub-terms occuring in the formula
  val simpTac:DependentPositionTactic = new DependentPositionTactic("formula simp"){
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
      override def computeExpr(sequent: Sequent): BelleExpr = {
        sequent.sub(pos) match
        {
          case Some(f:Formula) =>
            //If simplification was at the top level, then we can use the existing context
            if (pos.isTopLevel)
            {
              val (ff,pr) = formulaSimp(f,sequent.ante)
              cutAt(ff)(pos) < (
                ident,
                //todo: to remove the succ.length == 1 restriction, this needs to hide the other succ positions
                cohideRonly(pos)& equivifyR(1) & commuteEquivR(1) & by(pr)
                )
            }
            //Otherwise we only do the simplification under empty context and CEat the result
            else
            {
              val (ff,pr) = formulaSimp(f,IndexedSeq())
              CEat(commuteEquivFR(SuccPosition(1))(pr))(pos)
            }
          case Some(t:Term) =>
            val(tt,pr) = termSimp(t)
            CEat(useFor("= commute")(SuccPos(0))(pr))(pos)
          case _ => ident
        }
      }
    }
  }
}
