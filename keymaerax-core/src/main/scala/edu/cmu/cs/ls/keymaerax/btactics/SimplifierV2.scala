package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.core._

import scala.collection.immutable.{Map, _}
import edu.cmu.cs.ls.keymaerax.btactics.DebuggingTactics.print
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig

/**
  * Created by yongkiat on 9/29/16.
  */
object SimplifierV2 {

  /**
    * Returns the expression in expected position of ctx |- t = t' or ctx |- f <-> f'
    * @param pr the provable from which to extract the expression
    * @return
    */
  private def extract(pr:ProvableSig):Expression = {
    pr.conclusion.succ(0).sub(PosInExpr(1::Nil)).get
  }

  //todo: All of these should be moved to derived axioms (some are already there, but missing the other side)
  //Proves |- f -> t = tt or just t = tt
  private def qeTermProof(f:Option[String],t:String,tt:String):(Term,ProvableSig) =
  {
    val ttt  = tt.asTerm
    (ttt,
      f match{
        case None => proveBy(Equal(t.asTerm,ttt),QE & done)
        case Some(f) => proveBy(Imply(f.asFormula,Equal(t.asTerm,ttt)),QE & done)
      })
  }

  lazy val arithProps = List(
    //Multiplication
    qeTermProof(None,"0*F_()","0"),
    qeTermProof(None,"F_()*0","0"),
    qeTermProof(None,"1*F_()","F_()"),
    qeTermProof(None,"F_()*1","F_()"),
    qeTermProof(None,"-1*F_()","-F_()"),
    qeTermProof(None,"F_()*-1","-F_()"),
    //qeTermProof(Some("F_()!=0"),"F_()*(F_()^-1)","1"),
    //qeTermProof(Some("F_()!=0"),"(F_()^-1)*F_()","1"),
    //Addition
    qeTermProof(None,"0+F_()","F_()"),
    qeTermProof(None,"F_()+0","F_()"),
    qeTermProof(None,"F_()+(-F_())","0"),
    qeTermProof(None,"(-F_())+F_()","0"),
    //Minus
    qeTermProof(None,"0-F_()","-F_()"),
    qeTermProof(None,"F_()-0","F_()"),
    //todo: change to F_() - F_()
    qeTermProof(None,"x-x","0"),
    qeTermProof(None,"F_()+G_()-F_()","G_()"),
    qeTermProof(None,"F_()+G_()-G_()","F_()"),
    //Division
    qeTermProof(None,"F_()/1","F_()"),
    //qeTermProof(Some("F_()!=0"),"F_()/F_()","1"),
    //qeTermProof(Some("F_()!=0"),"0/F_()","0"),
    //Negation
    qeTermProof(None,"-(-F_())","F_()"),
    //Power
    qeTermProof(Some("F_()!=0"),"F_()^0","1"),
    qeTermProof(None,"F_()^1","F_()")
  )

  def mksubst(s:Subst) :Subst = {
    //Force the substitution to not have variable renaming
    if(!s.renaming.isEmpty) {
      throw new ProverException("Substitution contains variable renaming: " + s)
    }
    return s
  }

  def qeHeuristics(eq:ProvableSig): Option[ProvableSig] = {
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
  def reassoc(t:Term): ProvableSig =
  {
    val init = DerivedAxioms.equalReflex.fact(
      USubst(SubstitutionPair(FuncOf(Function("s_",None,Unit,Real),Nothing), t)::Nil))
    t match {
      case Plus(_,_) =>
        val (tt,c) = flattenPlus(t)
        if(c==0) init
        else proveBy(Equal(t,Plus(tt,Number(c))),QE & done)
      case Times(_,_) =>
        val (tt,c) = flattenTimes(t)
        if(c==1) init
        else proveBy(Equal(t,Times(tt,Number(c))),QE & done)
      case _ => init
    }
  }

  //If a term is purely arithmetic, then simplify it away (decided using RCF)
  //This doesn't work for things like: (1+ (x+2))
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

  /**
    * Recursive term simplification using chase, proving |- t = t'
    * @param t The term to be simplifed
    */
  def termSimp(t:Term): (Term,ProvableSig) =
  {
    //Recursive simplification in sub-terms
    val recpf = t match {
      case bop: BinaryCompositeTerm =>
        val l = bop.left
        val r = bop.right
        val (lt,lpr) = termSimp(l)
        val (rt,rpr) = termSimp(r)
        val nt = bop.reapply(lt,rt)
        proveBy(Equal(t, nt),
          CEat(lpr)(SuccPosition(1,1::0::Nil))&
            CEat(rpr)(SuccPosition(1,1::1::Nil))& byUS(DerivedAxioms.equalReflex))
      case uop: UnaryCompositeTerm =>
        val u = uop.child
        val (ut,upr) = termSimp(u)
        val nt = uop.reapply(ut)
        proveBy(Equal(t,nt),
          CEat(upr)(SuccPosition(1,1::0::Nil)) & byUS(DerivedAxioms.equalReflex))
      case FuncOf(fn, c) if c != Nothing =>
        val args = FormulaTools.argumentList(c)
        val simp = args.map(termSimp)
        val nArgs = simp.map(_._1).reduce[Term](Pair)
        val pref = if (args.size <= 1) 0::Nil else 0::0::Nil
        val tactic = simp.zipWithIndex.map({ case ((_, eqPr), i) => useAt(eqPr)(1, pref ++ PosInExpr.parseInt(i).pos) }).
          reduce[BelleExpr](_&_) & byUS(DerivedAxioms.equalReflex)
        proveBy(Equal(t, FuncOf(fn, nArgs)), tactic)
      case _ => DerivedAxioms.equalReflex.fact(
        USubst(SubstitutionPair(FuncOf(Function("s_",None,Unit,Real),Nothing), t)::Nil))
    }

    val rt = extract(recpf).asInstanceOf[Term]

    //Get rid of completely ground terms (that RCF can handle)
    val _ = groundTermEval(rt) match {
      case Some((t,eq)) =>
        return (t,useFor(eq, PosInExpr(0 :: Nil))(SuccPosition(1, 1 :: Nil))(recpf))
      case _ => ()
    }

    //Arithmetic propositions (non-ground rewrites like 0+x = x, x+0 = x , etc.)
    val apf = qeHeuristics(recpf) match { case None => recpf case Some(pr) => pr}

    //val fin = chaseFor(3,3,e=>AxiomIndex.axiomsFor(e),(s,p)=>pr=>pr)(SuccPosition(1,1::Nil))(apf)
    val ft = extract(apf).asInstanceOf[Term]
    //println("Final: "+fin)
    (ft,apf)
  }

  //Technically, we don't need QE for these (just use the proof for divideLemma)
  private lazy val plusLemma = proveBy(
    "(A_() = B_()) & (X_() = Y_()) -> (A_()+X_() = B_()+Y_())".asFormula,QE & done)
  private lazy val minusLemma =
    proveBy(
      "(A_() = B_()) & (X_() = Y_()) -> (A_()-X_() = B_()-Y_())".asFormula,QE & done)
  private lazy val timesLemma =
    proveBy(
      "(A_() = B_()) & (X_() = Y_()) -> (A_()*X_() = B_()*Y_())".asFormula,QE & done)
  private lazy val divideLemma =
    proveBy(
      "(A_() = B_()) & (X_() = Y_()) -> (A_()/X_() = B_()/Y_())".asFormula,
      implyR(1) & andL(-1) & exhaustiveEqL2R(-1) & exhaustiveEqL2R(-2) & cohideR(1) & byUS("= reflexive"))
  private lazy val powerLemma =
    proveBy(
      "(A_() = B_()) & (X_() = Y_()) -> (A_()^X_() = B_()^Y_())".asFormula,
      implyR(1) & andL(-1) & exhaustiveEqL2R(-1) & exhaustiveEqL2R(-2) & cohideR(1) & byUS("= reflexive"))

  /**
    * Takes a term t, with an equality context ctx and returns ctx |- t = t' using all equalities of the shape
    * t'' = n:Number
    * This is probably hopelessly slow...
    * @param t
    * @param ctx
    * @return
    */
  def equalityRewrites(t:Term,ctx:IndexedSeq[Formula]) :ProvableSig = {

    val rest = ctx.foldLeft(t)(
      (t: Term, f: Formula) =>
        f match {
          case Equal(l, n: Number) =>
            t.replaceFree(l, n)
          case _ => t
        }
    )
    proveBy(Sequent(ctx, IndexedSeq(Equal(t, rest))),
      ctx.zipWithIndex.foldRight(ident)(
        (f: (Formula, Int), tac: BelleExpr) =>
          f match {
            case (Equal(l, n: Number), i) =>
              eqL2R(-(i + 1))(1) & tac
            case _ => tac
          }
      ) & cohideR(1) & byUS("= reflexive"))
  }

  def termSimpWithRewrite(t:Term,ctx:IndexedSeq[Formula]): (Term,ProvableSig) =
  {
    //todo: filter context and keep only equalities around?
    val teq = equalityRewrites(t,ctx)
    val tt = extract(teq).asInstanceOf[Term]
    val (ttf,tpr) = termSimp(tt)
    (ttf,proveBy(Sequent(ctx,IndexedSeq(Equal(t,ttf))),
      CEat(tpr)(SuccPosition(1,1::Nil)) &
        cut(Equal(t,tt))<(close,
          hideR(SuccPos(0)) & by(teq))))
  }

  private def weaken(ctx:IndexedSeq[Formula]): ForwardTactic = pr => {
    val p = ProvableSig.startProof(pr.conclusion.glue(Sequent(ctx, IndexedSeq())))
    proveBy(p,
      cohideR(1) & //('Llast)*ctx.length &
        by(pr))
  }

  //Justifications for adding things to the context
  private lazy val andLemma =
  proveBy(
    "((P_() <-> F_()) & (F_() -> (Q_() <-> G_()))) ->(P_() & Q_() <-> F_() & G_())".asFormula,prop & done)

  private lazy val implyLemma =
    proveBy(
      "((P_() <-> F_()) & (F_() -> (Q_() <-> G_()))) ->(P_() -> Q_() <-> F_() -> G_())".asFormula,prop & done)

  private lazy val orLemma =
    proveBy(
      "((P_() <-> F_()) & (!(F_()) -> (Q_() <-> G_()))) ->(P_() | Q_() <-> F_() | G_())".asFormula,prop & done)

  private lazy val equivLemma =
    proveBy(
      "((P_() <-> F_()) & (Q_() <-> G_())) ->((P_() <-> Q_()) <-> (F_() <-> G_()))".asFormula,prop & done)

  private lazy val notLemma =
    proveBy(
      "(P_() <-> F_()) ->(!P_() <-> !F_())".asFormula,prop & done)

  private lazy val equalLemma =
    proveBy(
      "(A_() = B_()) & (X_() = Y_()) -> (A_() = X_() <-> B_() = Y_())".asFormula,QE & done)

  private lazy val notequalLemma =
    proveBy(
      "(A_() = B_()) & (X_() = Y_()) -> (A_() != X_() <-> B_() != Y_())".asFormula,QE & done)

  private lazy val greaterequalLemma =
    proveBy(
      "(A_() = B_()) & (X_() = Y_()) -> (A_() >= X_() <-> B_() >= Y_())".asFormula,QE & done)

  private lazy val greaterLemma =
    proveBy(
      "(A_() = B_()) & (X_() = Y_()) -> (A_() > X_() <-> B_() > Y_())".asFormula,QE & done)

  private lazy val lessequalLemma =
    proveBy(
      "(A_() = B_()) & (X_() = Y_()) -> (A_() <= X_() <-> B_() <= Y_())".asFormula,QE & done)

  private lazy val lessLemma =
    proveBy(
      "(A_() = B_()) & (X_() = Y_()) -> (A_() < X_() <-> B_() < Y_())".asFormula,QE & done)

  private lazy val equivTrans =
    proveBy("(P_() <-> Q_()) -> (Q_() <-> R_()) -> (P_() <-> R_())".asFormula,prop & done)

  private lazy val eqSym = proveBy("P_() = Q_() <-> Q_() = P_()".asFormula,QE & done)

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
        (ctxR, andL('Llast) & implyRi()(AntePos(ctx.length+1), SuccPos(0)) & tacL & implyR(SuccPos(0)) & tacR)
      //Both the de-morganed and originals are added to the context
      case Not(u) =>
        //Apply deMorgan things to Not
        val id = proveBy(Sequent(IndexedSeq(),IndexedSeq(Equiv(Not(u),Not(u)))),prop & done)
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
            useAt(DerivedAxioms.andReflexive,PosInExpr(1::Nil))(AntePos(ctx.length)) & andL('Llast) &
              implyRi()(AntePos(ctx.length), SuccPos(0)) & useAt(cpr,PosInExpr(0::Nil))(SuccPosition(1,0::Nil)) & implyR('_) & tacU)
        }
      case Equal(n:Number,r) =>
        //Add the flipped version of an equality so we always rewrite left-to-right
        (ctx:+Equal(r,n),implyRi()(AntePos(ctx.length), SuccPos(0)) & useAt(eqSym,PosInExpr(0::Nil))(SuccPosition(1,0::Nil)) &
          implyR('_))
      case _ => (ctx:+f,ident)
    }

  }

  //Truth tables for propositional formulae
  //These should be in DerivedAxioms
  // (some already are)
  private def propProof(f:String,ff:String):ProvableSig =
  {
    proveBy(Equiv(f.asFormula,ff.asFormula), prop & done)
  }

  lazy val andT = propProof("F_() & true","F_()")
  lazy val Tand = propProof("true & F_()","F_()")
  lazy val andF = propProof("F_() & false","false")
  lazy val Fand = propProof("false & F_()","false")

  lazy val orT = propProof("F_() | true","true")
  lazy val Tor = propProof("true | F_()","true")
  lazy val orF = propProof("F_() | false","F_()")
  lazy val For = propProof("false | F_()","F_()")

  lazy val implyT = propProof("F_() -> true","true")
  lazy val Timply = propProof("true -> F_()","F_()")
  lazy val implyF = propProof("F_() -> false","!F_()")
  lazy val Fimply = propProof("false -> F_()","true")

  lazy val equivT = propProof("F_() <-> true","F_()")
  lazy val Tequiv = propProof("true <-> F_()","F_()")
  lazy val equivF = propProof("F_() <-> false","!F_()")
  lazy val Fequiv = propProof("false <-> F_()","!F_()")

  lazy val notT = propProof("!true","false")
  lazy val notF = propProof("!false","true")

  lazy val forallTrue = proveBy("(\\forall x true)<->true".asFormula, auto )
  lazy val forallFalse = proveBy("(\\forall x false)<->false".asFormula, auto)
  lazy val existsTrue = proveBy("(\\exists x true)<->true".asFormula, auto )
  lazy val existsFalse = proveBy("(\\exists x false)<->false".asFormula, auto )


  //Proves |- f -> t = tt or just t = tt
  private def qeFormulaProof(f:Option[String],t:String,tt:String):ProvableSig =
  {
    val ttt  = tt.asFormula
    f match{
      case None => proveBy(Equiv(t.asFormula,ttt),prop & QE & done)
      case Some(f) => proveBy(Imply(f.asFormula,Equiv(t.asFormula,ttt)),prop & QE & done)
    }
  }

  lazy val ltNotReflex = qeFormulaProof(None,"F_()<F_()","false")
  lazy val gtNotReflex = qeFormulaProof(None,"F_()>F_()","false")
  lazy val neqNotReflex = qeFormulaProof(None,"F_()!=F_()","false")
  lazy val equalReflex = qeFormulaProof(None,"F_() = F_()","true")
  lazy val lessequalReflex = qeFormulaProof(None,"F_() <= F_()","true")
  lazy val greaterequalReflex = qeFormulaProof(None,"F_() >= F_()","true")

  private def propHeuristics(f:Formula) : Option[(Formula,ProvableSig)] = {
    f match {
      case And(l, True) => Some(l, andT)
      case And(True, r) => Some(r, Tand)
      case And(_, False) => Some(False, andF)
      case And(False, _) => Some(False, Fand)

      case Or(l, True) => Some(True, orT)
      case Or(True, r) => Some(True, Tor)
      case Or(l, False) => Some(l, orF)
      case Or(False, r) => Some(r, For)

      case Imply(l, True) => Some(True, implyT)
      case Imply(True, r) => Some(r, Timply)
      case Imply(l, False) => Some(Not(l), implyF)
      case Imply(False, r) => Some(True, Fimply)

      case Equiv(l, True) => Some(l, equivT)
      case Equiv(True, r) => Some(r, Tequiv)
      case Equiv(l, False) => Some(Not(l), equivF)
      case Equiv(False, r) => Some(Not(r), Fequiv)

      case Not(True) => Some(False, notT)
      case Not(False) => Some(True, notF)

      case Equal(l, r) if l == r => Some(True, equalReflex)
      case LessEqual(l, r) if l == r => Some(True, lessequalReflex)
      case GreaterEqual(l, r) if l == r => Some(True, greaterequalReflex)
      case Less(l, r) if l == r => Some(False, ltNotReflex)
      case Greater(l, r) if l == r => Some(False, gtNotReflex)
      case NotEqual(l, r) if l == r => Some(False, neqNotReflex)

      case Forall(l,True) => Some(True,forallTrue)
      case Forall(l,False) => Some(False,forallFalse)


      case Exists(l,True) => Some(True,existsTrue)
      case Exists(l,False) => Some(False,existsFalse)

      case _ => None
    }
  }

  // There are far too many cases to enumerate here
  // so we only handle the ones where the terms are in the same order
  // e.g. f()<g() -> f() <= g() but not g() > f() -> f() <= g()
  // The symmetric cases are obtained by searching in the opposite direction and applying the appropriate flipping lemma

  lazy val ltGeFalse = qeFormulaProof(Some("G_()>=F_()"),"G_()<F_()","false")
  lazy val ltGtFalse = qeFormulaProof(Some("G_()>F_()"),"G_()<F_()","false")
  lazy val ltEqFalse = qeFormulaProof(Some("G_()=F_()"),"G_()<F_()","false")

  lazy val leLtTrue = qeFormulaProof(Some("G_()<F_()"),"G_()<=F_()","true")
  lazy val leEqTrue = qeFormulaProof(Some("G_()=F_()"),"G_()<=F_()","true")
  lazy val leGtFalse = qeFormulaProof(Some("G_()>F_()"),"G_()<=F_()","false")

  lazy val gtLeFalse = qeFormulaProof(Some("G_()<=F_()"),"G_()>F_()","false")
  lazy val gtLtFalse = qeFormulaProof(Some("G_()<F_()"),"G_()>F_()","false")
  lazy val gtEqFalse = qeFormulaProof(Some("G_()=F_()"),"G_()>F_()","false")

  lazy val geGtTrue = qeFormulaProof(Some("G_()>F_()"),"G_()>=F_()","true")
  lazy val geEqTrue = qeFormulaProof(Some("G_()=F_()"),"G_()>=F_()","true")
  lazy val geLtFalse = qeFormulaProof(Some("G_()<F_()"),"G_()>=F_()","false")

  lazy val neLtTrue = qeFormulaProof(Some("G_()<F_()"),"G_()!=F_()","true")
  lazy val neGtTrue = qeFormulaProof(Some("G_()>F_()"),"G_()!=F_()","true")
  lazy val neEqFalse = qeFormulaProof(Some("G_()=F_()"),"G_()!=F_()","false")

  lazy val eqLtFalse = qeFormulaProof(Some("G_()<F_()"),"G_()=F_()","false")
  lazy val eqGtFalse = qeFormulaProof(Some("G_()>F_()"),"G_()=F_()","false")
  lazy val eqNeqFalse = qeFormulaProof(Some("G_()!=F_()"),"G_()=F_()","false")

  lazy val neqSym = proveBy("F_() != G_() <-> G_() != F_()".asFormula,QE & done)

  lazy val trueReflex = qeFormulaProof(Some("F_()"),"F_()","true")
  lazy val falseReflex = qeFormulaProof(Some("!F_()"),"F_()","false")

  //Finds a formula f in the antecedents to try and prove ctx |- g <-> h
  //If it exists, move it to get f -> (g <-> h)
  //Throws away the context and closes with the lemma provided
  def search(ctx:IndexedSeq[Formula],f:Formula,g:Formula,h:Formula,lem:ProvableSig) :Option[ProvableSig] ={
    val ind = ctx.indexOf(f)
    if(ind >= 0) {
      return Some(proveBy(Sequent(ctx, IndexedSeq(Equiv(g, h))),
        cohide2(AntePos(ind), SuccPos(0)) & implyRi & byUS(lem)))
    }
    else None
  }

  //  Proves ctx |- f <-> true or ctx |- f <-> false if possible
  // Flip prevents infinite loop when swapping between A < B <-> B > A
  def closeHeuristics(ctx:IndexedSeq[Formula],f:Formula,flip:Boolean = true) : Option[ProvableSig] = {
    //Closing heuristics
    //1. If formula appears in context, then close with true
    //2. If formula appears negated in context, close with false
    //3. Special cases for (in) equational reasoning

    val init:Option[ProvableSig] =
      f match {
        case Less(l,r) =>
          search(ctx,GreaterEqual(l,r),f,False,ltGeFalse) orElse
          search(ctx,Greater(l,r),f,False,ltGtFalse) orElse
          search(ctx,Equal(l,r),f,False,ltEqFalse) orElse(
            if(flip) {
              closeHeuristics(ctx, Greater(r, l), false) match{
                case None => None
                case Some(pr) => {
                  Some (useFor("> flip")(SuccPosition(1, 0 :: Nil))(pr))
                }
              }
            }
            else None
          )
        case LessEqual(l,r) =>
          search(ctx,Less(l,r),f,True,leLtTrue) orElse
          search(ctx,Equal(l,r),f,True,leEqTrue) orElse
          search(ctx,Greater(l,r),f,False,leGtFalse) orElse(
            if(flip) {
              closeHeuristics(ctx, GreaterEqual(r, l), false) match{
                case None => None
                case Some(pr) => {
                  Some (useFor(">= flip")(SuccPosition(1, 0 :: Nil))(pr))
                }
              }
            }
            else None
            )
        case Greater(l,r) =>
          search(ctx,LessEqual(l,r),f,False,gtLeFalse) orElse
          search(ctx,Less(l,r),f,False,gtLtFalse) orElse
          search(ctx,Equal(l,r),f,False,gtEqFalse) orElse(
            if(flip) {
              closeHeuristics(ctx, Less(r, l), false) match{
                case None => None
                case Some(pr) => {
                  Some (useFor("< flip")(SuccPosition(1, 0 :: Nil))(pr))
                }
              }
            }
            else None
            )
        case GreaterEqual(l,r) =>
          search(ctx,Greater(l,r),f,True,geGtTrue) orElse
          search(ctx,Equal(l,r),f,True,geEqTrue) orElse
          search(ctx,Less(l,r),f,False,geLtFalse) orElse(
            if(flip) {
              closeHeuristics(ctx, LessEqual(r, l), false) match{
                case None => None
                case Some(pr) => {
                  Some (useFor("<= flip")(SuccPosition(1, 0 :: Nil))(pr))
                }
              }
            }
            else None
            )
        case NotEqual(l,r) =>
          search(ctx,Less(l,r),f,True,neLtTrue) orElse
          search(ctx,Greater(l,r),f,True,neGtTrue) orElse
          search(ctx,Equal(l,r),f,False,neEqFalse) orElse(
            if(flip) {
              closeHeuristics(ctx, NotEqual(r, l), false) match{
                case None => None
                case Some(pr) => {
                  Some (useFor(neqSym,PosInExpr(0::Nil))(SuccPosition(1, 0 :: Nil))(pr))
                }
              }
            }
            else None
            )
        case Equal(l,r) =>
          search(ctx,Less(l,r),f,False,eqLtFalse) orElse
          search(ctx,Greater(l,r),f,False,eqGtFalse) orElse
          search(ctx,NotEqual(l,r),f,False,eqNeqFalse) orElse(
            if(flip) {
              closeHeuristics(ctx, Equal(r, l), false) match{
                case None => None
                case Some(pr) => {
                  Some (useFor(eqSym,PosInExpr(0::Nil))(SuccPosition(1, 0 :: Nil))(pr))
                }
              }
            }
            else None
            )
        case _ => None
      }

    init match {
      case Some(pr) => Some(pr)
      case None =>
        val trueReflex = qeFormulaProof(Some("F_()"), "F_()", "true")
        val falseReflex = qeFormulaProof(Some("!F_()"), "F_()", "false")

        //Case 1
        search(ctx, f, f, True, trueReflex) match {
          case Some(v) => Some(v)
          case None =>
            search(ctx, Not(f), f, False, falseReflex)
        }
    }

  }

  /**
    * Recursive formula simplification under a context using chase, proving ctx |- f <-> f'
    * The recursion always occurs left-to-right
    * @param f formula to simplify
    * @param ctx context in which to simplify
    * @return f',pr where pr proves the equivalence
    */
  def formulaSimp(f:Formula, ctx:IndexedSeq[Formula] = IndexedSeq()) : (Formula,ProvableSig) =
  {
    //println("At: "+f+" Context: "+ctx)
    // todo: remove the use of prop from short circuit branches
    //Recursive simplification
    val (recf:Formula,recpr:ProvableSig) =
    f match {
      case And(l, r) =>
        val (lf,lpr) = formulaSimp(l, ctx)
        //short circuit
        //        if (lf.equals(False))
        //        {
        //          return (False,
        //            proveBy(Sequent(ctx,IndexedSeq(Equiv(f,False))),
        //              cut(Equiv(l,lf))<(
        //                prop,
        //                hideR(SuccPos(0))& by(lpr))))
        //        }
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
              hideL('Llast) & hideR(SuccPos(0)) & implyR(1)  & tac & by(rpr)),
            hideR(SuccPos(0))& by(lpr)
            )
        ))
      case Imply(l, r) =>
        val (lf,lpr) = formulaSimp(l, ctx)
        //short circuit
        //        if (lf.equals(False))
        //        {
        //          return (True,proveBy(Sequent(ctx,IndexedSeq(Equiv(f,True))),
        //            cut(Equiv(l,lf))<(
        //              prop,
        //              hideR(SuccPos(0))& by(lpr))))
        //        }
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
        //        if (lf.equals(True))
        //        {
        //          return (True,proveBy(Sequent(ctx,IndexedSeq(Equiv(f,True))),
        //            cut(Equiv(l,lf))<(
        //              prop,
        //              hideR(SuccPos(0))& by(lpr))))
        //        }
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
        val (remainingCtx, droppedCtx) = ctx.partition(f => StaticSemantics.freeVars(f).toSet.intersect(q.vars.toSet).isEmpty)
        val (uf,upr) = formulaSimp(q.child,remainingCtx)
        val nf = q.reapply(q.vars, uf)

        val instantiate = q match {
          case Forall(_, _) => allR(1) & allL('Llast)
          case Exists(_, _) => existsL('Llast) & existsR(1)
        }

        (nf, proveBy(Sequent(ctx, IndexedSeq(Equiv(q, nf))),
          droppedCtx.map(f => hideL('L, f)).reduceOption[BelleExpr](_&_).getOrElse(skip) &
            equivR(1) & onAll(instantiate & implyRi()(AntePos(remainingCtx.length), SuccPos(0)) & equivifyR(1)) <(skip, commuteEquivR(1)) & onAll(by(upr))))
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

    val (_,proppr:ProvableSig) = propHeuristics(recf) match {
      case None => (recf,recpr)
      case Some((ff,pr)) =>
        val pf = proveBy(Sequent(ctx,IndexedSeq(Equiv(recf,ff))),cohideR(SuccPos(0)) & byUS(pr))
        //This pattern proves transitivity of equivs
        (ff,proveBy(Sequent(ctx,IndexedSeq(Equiv(f,ff))),
          cut(Equiv(f,recf)) <(
            cut(Equiv(recf,ff)) <(
              implyRi()(AntePos(ctx.length+1), SuccPos(0)) &
                implyRi()(AntePos(ctx.length), SuccPos(0)) & cohideR(SuccPos(0)) & byUS(equivTrans),
              hideL('Llast) & hideR(SuccPos(0)) & by(pf)),
            hideR(SuccPos(0))& by(recpr))))
    }

    //Chase simplification
    val chasepr = chaseFor(3,3,e=>AxiomIndex.axiomsFor(e),(s,p)=>pr=>pr)(SuccPosition(1,1::Nil))(proppr)
    val chasef = extract(chasepr).asInstanceOf[Formula]

    //Normalise > to <, >= to <=
    //    val (normpr,normf) = chasef match {
    //      case Greater(l, r) => (useFor("> flip")(SuccPosition(1, 1 :: Nil))(chasepr), Less(r, l))
    //      case GreaterEqual(l, r) => (useFor(">= flip")(SuccPosition(1, 1 :: Nil))(chasepr), LessEqual(r, l))
    //      case _ => (chasepr,chasef)
    //    }
    val (normpr,normf) = (chasepr,chasef)

    val closepr = closeHeuristics(ctx,normf)

    closepr match{
      case None => (normf,normpr)
      case Some(pr) =>
        val closef = extract(pr).asInstanceOf[Formula]
        (closef,proveBy(Sequent(ctx,IndexedSeq(Equiv(f,closef))),
          cut(Equiv(f,normf)) <(
            cut(Equiv(normf,closef)) <(
              implyRi()(AntePos(ctx.length+1), SuccPos(0)) &
                implyRi()(AntePos(ctx.length), SuccPos(0)) & cohideR(SuccPos(0)) & byUS(equivTrans),
              hideL('Llast) & hideR(SuccPos(0)) & by(pr)),
            hideR(SuccPos(0))& by(normpr))))

    }
  }

  //Splits an equivalence in succedent of provable into left and right halves
  def splitEquiv(pr:ProvableSig): (ProvableSig,ProvableSig) = {
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

  //Simplifies a formula including sub-terms occuring in the formula
  lazy val simpTac:DependentPositionTactic = "simplify" by ((pos: Position, sequent: Sequent) => {
    sequent.sub(pos) match
    {
      case Some(f:Formula) =>
        //If simplification was at the top level, then we can use the existing context
        if (pos.isTopLevel)
        {
          val (ctx, cutPos, commute) =
            if (pos.isSucc) (sequent.ante, pos, commuteEquivR(1))
            else (sequent.ante.patch(pos.top.getIndex, Nil, 1), SuccPosition.base0(sequent.succ.length), skip)

          val (ff,pr) = formulaSimp(f, ctx)

          cutAt(ff)(pos) < (
            ident,
            //todo: to remove the succ.length == 1 restriction, this needs to hide the other succ positions
            cohideOnlyR(cutPos) & equivifyR(1) & commute & by(pr)
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
  })

  //Simplifies at a (succ) position, restricting only to the requested part of the context and in the required order
  def rsimpTac(ipos:IndexedSeq[Integer]):DependentPositionTactic = new DependentPositionTactic("restricted simp"){
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
      override def computeExpr(sequent: Sequent): BelleExpr = {
        //todo: Change to raise the correct kind of error
        assert(pos.isTopLevel & pos.isSucc) //We can only do this at the top level because CE can't take antecedent contexts

        val positions = ipos.distinct.filter(i => i < sequent.ante.length) //Tactic doesn't work if the positions aren't distinct

        val ctx = positions.map(i => sequent.ante(i)) //todo: Check that these all exist in the sequent

        val f = sequent.sub(pos).get.asInstanceOf[Formula]

        val (ff,pr) = formulaSimp(f,ctx)

        cutAt(ff)(pos) < (
          ident,
          cohideOnlyR(pos) & equivifyR(1) & commuteEquivR(1) &
          positions.foldLeft(ident)(
              (tac: BelleExpr,i:Integer) =>
                implyRi(keep=true)(AntePos(i),SuccPos(0)) & tac) & cohideR(1) & implyR(1)*positions.length & by(pr)
          )
      }
    }
  }

  def flip[A1, A2, B](f: (A1,A2) => B): (A2,A1) => B = (x1, x2) => f(x2,x1)

  // Simplifies an entire sequent, throwing out unnecessary things in the context
  // 1) Moves all antecedents into implication |- (A_1 & ... & A_n) -> (S_1 \/ ... )
  // 2) Simplifies
  // 3) Moves the implications back

  // This might be slightly too unpredictable for some purposes, so use simpTac instead
  lazy val fullSimpTac:DependentTactic = "fullSimplify" by ((seq: Sequent) => {
    val succOr = seq.succ.reduceRightOption(Or).getOrElse(False)
    val anteAnd = seq.ante.reduceRightOption(And).getOrElse(True)
    val (ff,pr) = formulaSimp(Imply(anteAnd,succOr), IndexedSeq())
    ff match {
      case Imply(l,r) =>
        val (_, tac) = addContext (l, IndexedSeq () )
        PropositionalTactics.toSingleFormula & useAt (pr) (1) & implyR (1) & tac //(implyRi*) & useAt(pr)(1)
      case _ =>
        //This should only occur if the tactic managed to reduce the formula to false or the antecedents to true
        PropositionalTactics.toSingleFormula & useAt (pr) (1)
    }
  })

  lazy val swapImply = proveBy("(P_() -> Q_() -> R_()) <-> (Q_() -> P_() -> R_())".asFormula,prop & done)

  //Same as fullSimpTac, except the changes to the context get thrown out
  //todo: This doesn't work with antepositions
  lazy val safeFullSimpTac:DependentPositionTactic = new DependentPositionTactic("simp") {
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
      override def computeExpr(sequent: Sequent): BelleExpr = {
        assert(pos.isTopLevel && sequent.sub(pos).isDefined)
        val f = sequent.sub(pos).get.asInstanceOf[Formula]
        val (ctx, cutPos, commute) =
          if (pos.isSucc) (sequent.ante, pos, commuteEquivR(1))
          else (sequent.ante.patch(pos.top.getIndex, Nil, 1), SuccPosition.base0(sequent.succ.length), skip)
        val ctxAnd = ctx.reduceRightOption(And).getOrElse(True)
        val (ff, pr) = formulaSimp(Imply(ctxAnd, f), IndexedSeq())

        cutAt(ff)(pos) < (
          ident,
          cohideOnlyR(cutPos) &
          cut(ctxAnd) <(
            implyRi()(AntePos(sequent.ante.size),SuccPos(0)) & useAt(swapImply)(1) & cohideR(1) & equivifyR(1) & commute & by(pr)
            ,
            hideR(1) & (andR(1) <(close, (close | skip) partial))*(sequent.ante.size-1) & ?(close))
          )
      }
    }
  }

  //todo: Everything below is not part of the simplifier and should be moved elsewhere

  private lazy val nop = Assign(Variable("x_"),Variable("x_"))

  def isNop(p:Program) : Boolean = {
    p match {
      case Assign(x,y) => {
        y match { case v:Variable =>
          v.name.equals(x.name) case _ => false}
      }
      case _ => false
    }
  }
  def stripNoOp(p:Program) : Program = {
    p match {
      case Compose(p,pp) =>
        val sp = stripNoOp(p)
        val spp = stripNoOp(pp)
        if(isNop(sp)) spp
        else if(isNop(spp)) sp
        else Compose(sp,spp)
      case Choice(l,r) =>
        Choice(stripNoOp(l),stripNoOp(r))
      case _ => p
    }
  }

  //Attempt to rewrite the requested auxiliary variables in a program
  //The RHS of each rewrite is determined automatically if not already given
  def rewriteProgramAux(p:Program,targets:List[Variable],rewrites:Map[Variable,Term]=Map()):(Program,Map[Variable,Term]) = {
    p match {
      case Assign(v,e) =>
        val erw = rewrites.foldLeft(e) { (e,kv) => e.replaceFree(kv._1,kv._2) }
        if(targets.contains(v)){
          rewrites get v match{
            case None =>
              (nop,rewrites + (v -> erw))
            case Some(eorig) =>
              if(erw.equals(eorig)) (nop,rewrites)
              else throw new ProverException("Clashing rewrites for"+v+" : " + eorig+" "+erw)
          }
        }
        else {
          (Assign(v,erw),rewrites)
        }
      case Compose(l,r) =>
        val (lp,lrw) = rewriteProgramAux(l,targets,rewrites)
        val (rp,rrw) = rewriteProgramAux(r,targets,lrw)
        (Compose(lp,rp),rrw)
      case Choice(l,r) =>
        val (lp,lrw) = rewriteProgramAux(l,targets,rewrites)
        val (rp,rrw) = rewriteProgramAux(r,targets,rewrites)
        //None of the rewrites that occur inside a choice should matter outside
        (Choice(lp,rp),rewrites)
      case Test(f) =>
        val erw = rewrites.foldLeft(f) { (e,kv) => e.replaceFree(kv._1,kv._2) }
        (Test(erw),rewrites)
      //No other rewrites should be applied
      case p => (p,rewrites)
    }

  }

  private def hideBox(e:Expression) : List[String] =
  {
    e match {
      //Ignore nested loops and ODEs in chase
      case Box(ODESystem(_,_),_) => Nil
      case Box(Loop(_),_) => Nil
      case Box(_,_) => AxiomIndex.axiomsFor(e)
      case  _ => Nil //AxiomIndex.axiomsFor(e)
    }
  }

  // Given [a*]f, returns [b*]f and attempts a proof of [a*]f |- [b*]f
  // Also works if given p1 -> p2 -> ... p -> [a*]f , in which case the attempted proof is
  // p1 -> p2 -> ... -> [a*]f |- p1-> p2 -> ... -> [b*]f
  // where b has the requested auxiliaries rewritten away
  def rewriteLoopAux(f:Formula,targets:List[Variable]):(Formula,ProvableSig) = {
    f match {
      case (Imply(pre,rhs)) =>
        val (rf,pr) = rewriteLoopAux(rhs,targets)
        val tar = Imply(pre,rf)
        val seq = proveBy(Sequent(IndexedSeq(f),IndexedSeq(tar)),
          implyR(1) &
            modusPonens(AntePos(1),AntePos(0)) &
            hideL(-2) & ?(by(pr))
        )
        return (tar,seq)

      case (Box(Loop(prog),fml))=>
        val sprog = stripNoOp(rewriteProgramAux(prog,targets)._1)
        val tar = Box(Loop(sprog),fml)

        val seq = proveBy(Sequent(IndexedSeq(f),IndexedSeq(tar)),
          loop(f)(1) <
            (close,
              useAt("[*] iterate")(-1) & andL(-1) & close,
              //Crucial case, fails if the rewrite was bad:
              useAt("[*] iterate")(-1) & andL(-1) &
                chase(3,3, (e:Expression)=>hideBox(e))(SuccPosition(1,Nil)) &
                chase(3,3, (e:Expression)=>hideBox(e))(AntePosition(2,Nil)) &
                (? (close) )))
        (tar,seq)
      case _ => throw new ProverException("loop rewriting expects input shape [{a*}]f or p -> ")
    }
  }

}
