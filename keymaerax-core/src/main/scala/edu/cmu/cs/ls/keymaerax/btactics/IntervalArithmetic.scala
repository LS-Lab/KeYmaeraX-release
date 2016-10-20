/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.BelleExpr._
import edu.cmu.cs.ls.keymaerax.bellerophon.{OnAll, RenUSubst, _}
import edu.cmu.cs.ls.keymaerax.core.{Assign, Variable, _}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.Context._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms._
import edu.cmu.cs.ls.keymaerax.btactics.DebuggingTactics.print
import edu.cmu.cs.ls.keymaerax.btactics.SimplifierV2._
import edu.cmu.cs.ls.keymaerax.btactics.FOQuantifierTactics._

import scala.collection.immutable._

/**
  * Tactics for introducing interval arithmetic.
  *
  * @author Yong Kiam Tan
  */
object IntervalArithmetic {

  private val ubPrefix = "u"
  private val lbPrefix = "l"

  private def getVarName(t:Term) : String = {
    //todo: Ensure freshness?
    t match {
      case at:AtomicTerm  =>
        at.prettyString
      case f:FuncOf =>
        f.func.prettyString
      case Plus(l,r) =>
        "pL"+getVarName(l)+"C"+getVarName(r)+"R"
      case Times(l,r) =>
        "tL"+getVarName(l)+"C"+getVarName(r)+"R"
      case Minus(l,r) =>
        "tL"+getVarName(l)+"C"+getVarName(r)+"R"
      case Power(l,r) =>
        "powL"+getVarName(l)+"C"+getVarName(r)+"R"
      case _ => ???
    }
  }
  private def hideLeftBox(e:Expression) : List[String] =
  {
    e match {
      case Box(_,Box(_,_)) => AxiomIndex.axiomsFor(e)
      case  _ => Nil
    }
  }

  //Check if the context program already calculates the upper bound variable
  def contextContains(prog:Program,v:String) : Boolean = {
    prog match
    {
      case Assign(nvar,t) => nvar.name.equals(v)
      case Compose(lp,rp) =>
        contextContains(lp,v) | contextContains(rp,v)
      case _ => ???
    }

  }
  //Takes a program context ctxP, and term t
  //Returns a provable pr, program p, formula f and term t' such that:
  //pr = |- [ctxP;p] f
  //and f is an upper bound of the form t <= t'
  private val nop = Assign(Variable("x_"),Variable("x_"))

  private val composeAssoc = proveBy("[a_;{b_;c_;}] p_(||) <-> [{a_;b_;}c_;]p_(||)".asFormula,
    useAt("[;] compose")(SuccPosition(1,1::Nil)) &
      useAt("[;] compose")(SuccPosition(1,1::Nil)) &
      useAt("[;] compose")(SuccPosition(1,0::Nil)) &
      useAt("[;] compose")(SuccPosition(1,0::1::Nil)) &
      byUS("<-> reflexive"))

  private val testAddLem = proveBy("f() <= F() & g() <= G() -> f() + g() <= F() + G() ".asFormula, QE)

  //  val intervalAxiomContext = IndexedSeq(
  //    "\\forall x \\forall y (x + y <= uPlus(x,y))".asFormula,
  //    "\\forall x \\forall y (lPlus(x,y) <= x + y)".asFormula
  //  )

  val intervalAxiomContext = IndexedSeq(
    "\\forall x \\forall y (x + y <= uPlus(x,y))".asFormula,
    "\\forall x \\forall y (lPlus(x,y) <= x + y)".asFormula,
    "\\forall x \\forall y (x * y <= uTimes(x,y))".asFormula,
    "\\forall x \\forall y (lTimes(x,y) <= x * y)".asFormula
  )

  private val uPlus = Function("uPlus", None, Tuple(Real, Real), Real)
  private val lPlus = Function("lPlus", None, Tuple(Real, Real), Real)
  private val uTimes = Function("uTimes", None, Tuple(Real, Real), Real)
  private val lTimes = Function("lTimes", None, Tuple(Real, Real), Real)
  private val maxF = Function("max", None, Tuple(Real, Real), Real, interpreted=true)
  private val minF = Function("min", None, Tuple(Real, Real), Real, interpreted=true)

  //QE doesn't work well with uPlus(,)
  private val uPlusLem = proveBy(("((\\forall x \\forall y (x + y <= uPlus(x,y))) & f_() <= F_() & g_() <= G_()) ->" +
    "f_() + g_() <= uPlus(F_(),G_())").asFormula,
    useAt("all instantiate",(us:Subst)=>us++RenUSubst(("f()".asTerm,"F_()".asTerm )::Nil))(SuccPosition(1,0::0::Nil)) &
      useAt("all instantiate",(us:Subst)=>us++RenUSubst(("f()".asTerm,"G_()".asTerm )::Nil))(SuccPosition(1,0::0::Nil)) &
      useAt("+<= up",PosInExpr(1::Nil))(SuccPosition(1,1::Nil)) & prop)

  private val lPlusLem = proveBy(("((\\forall x \\forall y (lPlus(x,y) <= x + y)) & ff_() <= f_() & gg_() <= g_()) ->" +
    "lPlus(ff_(),gg_()) <= f_() + g_()").asFormula,
    useAt("all instantiate",(us:Subst)=>us++RenUSubst(("f()".asTerm,"ff_()".asTerm )::Nil))(SuccPosition(1,0::0::Nil)) &
      useAt("all instantiate",(us:Subst)=>us++RenUSubst(("f()".asTerm,"gg_()".asTerm )::Nil))(SuccPosition(1,0::0::Nil)) &
      useAt("<=+ down",PosInExpr(1::Nil))(SuccPosition(1,1::Nil)) & prop)

  val duplicateL:DependentPositionTactic = new DependentPositionTactic("duplicate L") {
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
      override def computeExpr(sequent: Sequent): BelleExpr = {
        assert(pos.isAnte && pos.isTopLevel)
        sequent.sub(pos) match {
          case Some(f: Formula) =>
            cut(f) < (ident, close)
          case _ => ident
        }
      }
    }
  }

  //Bad -- causes splitting
  private val maxLem = proveBy( "h_() <= f_() | h_() <= g_() -> h_() <= max(f_(),g_()) ".asFormula,QE)
  private val minLem = proveBy( "f_() <= H_() | g_() <= H_() -> min(f_(),g_()) <= H_()".asFormula,QE)

  //This is the exact shape of times generated
  private val uTimesLem = proveBy(
    ("((\\forall x \\forall y (x * y <= uTimes(x,y))) & f_() <= F_() & ff_() <= f_() & g_() <= G_() & gg_() <= g_() ->" +
      "f_() * g_() <= max((max((uTimes((F_(),G_())),uTimes((F_(),gg_())))),max((uTimes((ff_(),G_())),uTimes((ff_(),gg_())))))))").asFormula,
    implyR(1) &
      useAt("*<= up",PosInExpr(1::Nil))(1) & prop &
      (OnAll((useAt("maxLem",maxLem,PosInExpr(1::Nil))(1)) & prop)*)
        <(allL("ff_()".asTerm)(-1) & allL("gg_()".asTerm)(-1),
        allL("ff_()".asTerm)(-1) & allL("G_()".asTerm)(-1),
        allL("F_()".asTerm)(-1) & allL("gg_()".asTerm)(-1),
        allL("F_()".asTerm)(-1) & allL("G_()".asTerm)(-1)) &
      OnAll(close))

  private val lTimesLem = proveBy(
    ("((\\forall x \\forall y (lTimes(x,y) <= x * y)) & f_() <= F_() & ff_() <= f_() & g_() <= G_() & gg_() <= g_() ->" +
      "min((min((lTimes((F_(),G_())),lTimes((F_(),gg_())))),min((lTimes((ff_(),G_())),lTimes((ff_(),gg_())))))) <= f_() * g_())").asFormula,
    implyR(1) &
      useAt("<=* down",PosInExpr(1::Nil))(1) & prop &
      (OnAll((useAt("minLem",minLem,PosInExpr(1::Nil))(1)) & prop)*)
        <(allL("ff_()".asTerm)(-1) & allL("gg_()".asTerm)(-1),
        allL("ff_()".asTerm)(-1) & allL("G_()".asTerm)(-1),
        allL("F_()".asTerm)(-1) & allL("gg_()".asTerm)(-1),
        allL("F_()".asTerm)(-1) & allL("G_()".asTerm)(-1)) &
      OnAll(close))

  def fixSubst(subst:Subst,l:Term,r:Term):Subst ={
    subst ++ RenUSubst(
      ("F_()".asTerm, l) ::
        ("G_()".asTerm, r) ::
        Nil)
  }

  //Alternative approach: Just create the program directly, try the proof after and hope it works
  def deriveTermProgram(dir:Boolean,vars:List[String],t:Term) : (List[String],Program,Term) =
  {
    val varname = (if(dir) ubPrefix else lbPrefix) ++ getVarName(t)
    val nvar = Variable(varname)
    if (vars.contains(varname)) return (vars,nop,nvar)
    t match {
      case at:AtomicTerm =>
        return (vars,nop,at)
      case at:ApplicationOf =>
        return (vars,nop,at)
      //return (varname::vars,Assign(nvar,at),nvar)
      case Plus(l,r) =>
        val (lvars,lp,lbound) = deriveTermProgram(dir,vars,l)
        val (rvars,rp,rbound) = deriveTermProgram(dir,lvars,r)
        val func = if(dir) uPlus else lPlus
        return (rvars,Compose(Compose(lp,rp),Assign(nvar,FuncOf(func,Pair(lbound,rbound)))),nvar)
      case Times(l,r) =>
        //Upper bounds
        val (luvars,lup,lubound) = deriveTermProgram(true,vars,l)
        val (ruvars,rup,rubound) = deriveTermProgram(true,luvars,r)
        val (llvars,llp,llbound) = deriveTermProgram(false,ruvars,l)
        val (rlvars,rlp,rlbound) = deriveTermProgram(false,llvars,r)
        val func = if(dir) uTimes else lTimes
        val bound = if(dir) maxF else minF
        val boundstr = if(dir) "max" else "min"
        val uuasg = Assign(Variable(varname+"uu"),FuncOf(func,Pair(lubound,rubound)))
        val ulasg = Assign(Variable(varname+"ul"),FuncOf(func,Pair(lubound,rlbound)))
        val luasg = Assign(Variable(varname+"lu"),FuncOf(func,Pair(llbound,rubound)))
        val llasg = Assign(Variable(varname+"ll"),FuncOf(func,Pair(llbound,rlbound)))

        val ubvar = Variable(varname+"u"+boundstr)
        val lbvar = Variable(varname+"l"+boundstr)

        val umax = Assign(ubvar,FuncOf(bound,Pair(Variable(varname+"uu"),Variable(varname+"ul"))))
        val lmax = Assign(lbvar,FuncOf(bound,Pair(Variable(varname+"lu"),Variable(varname+"ll"))))
        //Existing progs
        val prog1 = Compose(Compose(lup,rup),Compose(llp,rlp))
        val prog2 = Compose(Compose(Compose(uuasg,ulasg),Compose(luasg,llasg)),Compose(umax,lmax))
        //Final program
        val prog = Compose(Compose(prog1,prog2),Assign(nvar,FuncOf(bound,Pair(ubvar,lbvar))))
        return (rlvars,prog,nvar)
      case _ => return(vars,nop,t)

    }
  }

  //Takes f and returns program a, formula f' such that
  // <a> f' -> f should be provable
  // Along with additional facts about the derivation that should be cut in
  // Variables threaded through
  //This commented version allows for shortcircuting, which is probably more useful, but the proof is hard(er)
  //  def deriveFormulaProgram(vars:List[String],f:Formula) : (List[String],Program,Formula,Formula) = {
  //    f match {
  //      case LessEqual(l,r) =>
  //      {
  //        val (luvars,lup,lubound) = deriveTermProgram(true,vars,l)
  //        val (rlvars,rlp,rlbound) = deriveTermProgram(false,luvars,r)
  //        return (rlvars, Compose(lup,rlp),LessEqual(lubound,rlbound),
  //          And(And(LessEqual(l,lubound),LessEqual(rlbound,r)),LessEqual(lubound,rlbound)))
  //      }
  //      case And(l,r) =>
  //      {
  //        val (lvars,lp,lf,lext) = deriveFormulaProgram(vars,l)
  //        val (rvars,rp,rf,rext) = deriveFormulaProgram(lvars,r)
  //        return (rvars, Compose(Compose(lp,Test(lf)),rp),rf, And(lext,rext))
  //      }
  //      case Or(l,r) =>
  //      {
  //        val (lvars,lp,lf,lext) = deriveFormulaProgram(vars,l)
  //        val (rvars,rp,rf,rext) = deriveFormulaProgram(lvars,r)
  //        return (rvars, Compose(lp,Choice(Test(lf),rp)),rf,Or(lext,rext))
  //      }
  //    }
  //  }

  def deriveFormulaProgram(vars:List[String],f:Formula) : (List[String],Program,Formula) = {
    f match {
      case LessEqual(l,r) =>
      {
        val (luvars,lup,lubound) = deriveTermProgram(true,vars,l)
        val (rlvars,rlp,rlbound) = deriveTermProgram(false,luvars,r)
        return (rlvars, Compose(lup,rlp),LessEqual(lubound,rlbound))
      }
      case Less(l,r) =>
      {
        val (luvars,lup,lubound) = deriveTermProgram(true,vars,l)
        val (rlvars,rlp,rlbound) = deriveTermProgram(false,luvars,r)
        return (rlvars, Compose(lup,rlp),Less(lubound,rlbound))
      }
      //Note that the r,l args are flipped for >= and >
      case GreaterEqual(r,l) =>
      {
        val (luvars,lup,lubound) = deriveTermProgram(true,vars,l)
        val (rlvars,rlp,rlbound) = deriveTermProgram(false,luvars,r)
        return (rlvars, Compose(lup,rlp),GreaterEqual(rlbound,lubound))
      }
      case Greater(r,l) =>
      {
        val (luvars,lup,lubound) = deriveTermProgram(true,vars,l)
        val (rlvars,rlp,rlbound) = deriveTermProgram(false,luvars,r)
        return (rlvars, Compose(lup,rlp),Greater(rlbound,lubound))
      }
      //Not sure what to do for equality, especially if it is on non-trivial sub-terms
      case Equal(l,r) =>
        return(vars,nop,Equal(l,r))
      //NotEqual can be translated to Greater or Less, but maybe it should have special meaning w.r.t. to Equal
      case NotEqual(l,r) =>
        return(vars,nop,NotEqual(l,r))
      case And(l,r) =>
      {
        val (lvars,lp,lf) = deriveFormulaProgram(vars,l)
        val (rvars,rp,rf) = deriveFormulaProgram(lvars,r)
        return (rvars, Compose(lp,rp),And(lf,rf))
      }
      case Or(l,r) =>
      {
        val (lvars,lp,lf) = deriveFormulaProgram(vars,l)
        val (rvars,rp,rf) = deriveFormulaProgram(lvars,r)
        return (rvars, Compose(lp,rp),Or(lf,rf))
      }
    }
  }

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
      case _ => p
    }
  }

  //Decompose across Imply
  //These are single sided implications
  private val decomposeAnd = proveBy("((P_() -> PP_()) & (Q_() -> QQ_())) -> (P_() & Q_() -> PP_() & QQ_())".asFormula,prop)
  private val decomposeOr = proveBy("((P_() -> PP_()) & (Q_() -> QQ_())) -> (P_() | Q_() -> PP_() | QQ_())".asFormula,prop)
  private val decomposeLE = proveBy("(f_() <= F_() & gg_() <= g_() ) -> (F_() <= gg_() -> f_() <= g_())".asFormula,QE)
  private val decomposeLT = proveBy("(f_() <= F_() & gg_() <= g_() ) -> (F_() < gg_() -> f_() < g_())".asFormula,QE)
  private val decomposeGE = proveBy("(f_() <= F_() & gg_() <= g_() ) -> (gg_() >= F_() -> g_() >= f_())".asFormula,QE)
  private val decomposeGT = proveBy("(f_() <= F_() & gg_() <= g_() ) -> (gg_() > F_() -> g_() > f_())".asFormula,QE)


  // These can be used to decompose the big formula generated at the end
  //private val decomposeDiamTestAnd = proveBy("<?p_() & q_();>r_() <-> <?p_();?q_();>r_()".asFormula,
  //  chase(SuccPosition(1,0::Nil)) & chase(SuccPosition(1,1::Nil)) & prop)
  //private val decomposeDiamTestOr = proveBy("<?p_() | q_();>r_() <-> <?p_(); ++ ?q_();>r_()".asFormula,
  //  chase(SuccPosition(1,0::Nil)) & chase(SuccPosition(1,1::Nil)) & prop)

  def deriveFormulaProof(f:Formula) : Provable =
  {
    val(_,pinit,ff) = deriveFormulaProgram(Nil,f)
    val prog = stripNoOp(Compose(pinit,Test(ff)))
    val pf = proveBy(Sequent(intervalAxiomContext,IndexedSeq(Imply(Diamond(prog,True),f))),
      //Turn the <> into a formula, preserving its shape
      chase(SuccPosition(1,0::Nil)) &
        //Repeatedly decompose w.r.t. shape of formula
        (OnAll(?(
          (useAt(decomposeAnd,PosInExpr(1::Nil))(1) & andR('_)) |
            (useAt(decomposeOr,PosInExpr(1::Nil))(1) & andR('_))))*) &
        //Decompose inequalities
        (OnAll(?(
          (useAt(decomposeLE,PosInExpr(1::Nil))(1) & andR('_)) |
          (useAt(decomposeLT,PosInExpr(1::Nil))(1) & andR('_)) |
          (useAt(decomposeGE,PosInExpr(1::Nil))(1) & andR('_)) |
          (useAt(decomposeGT,PosInExpr(1::Nil))(1) & andR('_))
        )) *) &
        //single step removal of the rounding arithmetic axioms
        (OnAll(?(
          (useAt(lPlusLem,PosInExpr(1::Nil))(1) & andR('_) < (close, andR('_))) |
            (useAt(uPlusLem,PosInExpr(1::Nil))(1) & andR('_) < (close, andR('_))) |
            (useAt(uTimesLem,PosInExpr(1::Nil))(1) & andR('_) < (close, (OnAll(?(andR('_)))*) )) |
            (useAt(lTimesLem,PosInExpr(1::Nil))(1) & andR('_) < (close, (OnAll(?(andR('_)))*)))
        ))*) &
        //reflexivity
        OnAll(simpTac(1) & closeT)
    )
    //Decompose the big formula here
    pf
  }

  def deriveProof(dir:Boolean,t:Term): Provable =
  {
    val (_,pinit,bound) = deriveTermProgram(dir:Boolean,Nil,t)
    val prog = stripNoOp(pinit)
    val f = if(dir) LessEqual(t,bound) else LessEqual(bound,t)
    //First prove the cut
    proveBy(Sequent(intervalAxiomContext,IndexedSeq(Box(prog,f))),
      //Removes the HP
      chase(1) &
        //single step removal of axs
        (OnAll(
          (useAt(lPlusLem,PosInExpr(1::Nil))(1) & andR('_) < (close, andR('_) & OnAll(simpTac(1) & ?(closeT)))) |
            (useAt(uPlusLem,PosInExpr(1::Nil))(1) & andR('_) < (close, andR('_) & OnAll(simpTac(1) & ?(closeT)))) |
            (useAt(uTimesLem,PosInExpr(1::Nil))(1) & andR('_) < (close, prop & OnAll(simpTac(1) & ?(closeT)))) |
            (useAt(lTimesLem,PosInExpr(1::Nil))(1) & andR('_) < (close, prop & OnAll(simpTac(1) & ?(closeT))))
        )*)
    )
  }

  /*
  //dir gives direction of bound, true = upper, false = lower
  def derive(dir:Boolean,ctxprog:Program,t:Term) : (Provable,Program,Formula,Term) = {
    //If the context program already calculates the required bound, then we do a no-op
    val varname = (if(dir) ubPrefix else lbPrefix) ++ getVarName(t)
    //Tricky -- may need to match against axioms for interval arith
    if(contextContains(ctxprog,varname))
    {
      val pr = proveBy(Sequent(intervalAxiomContext,IndexedSeq(Box(Compose(ctxprog,nop),conc))),
        chase(1) & (closeT partial)
      )
      return (pr,nop,conc,nvar)
    }
    t match {
      case at:AtomicTerm =>
        //Treat atomics as variable arguments i.e. already known
        val conc2 = LessEqual(at,at)
        return (proveBy(Sequent(intervalAxiomContext,IndexedSeq(Box(Compose(ctxprog,nop),conc2))),
          useAt("V vacuous")(1) & cohideR(1) & QE),nop,conc2,at)
//        val prog = Assign(nvar,at)
//        (proveBy(Box(Compose(ctxprog,prog),conc),
//          useAt("[;] compose")(1) &
//          useAt("[:=] assign")(SuccPosition(1,1::Nil)) &
//          useAt("V vacuous")(1) &
//          simpTac(1) &
//          closeT),
//        prog,conc,nvar)

      case at:ApplicationOf =>
        val prog = Assign(nvar,at)
        (proveBy(Sequent(intervalAxiomContext,IndexedSeq(Box(Compose(ctxprog,prog),conc))),
          useAt("[;] compose")(1) &
          useAt("[:=] assign")(SuccPosition(1,1::Nil)) &
          useAt("V vacuous")(1) &
          simpTac(1) &
          closeT),
        prog,conc,nvar)

      case Plus(l,r) =>
        val (lpf,lprog,lconc,lbound) = derive(dir,ctxprog,l)
        val (rpf,rprog,rconc,rbound) = derive(dir,Compose(ctxprog,lprog),r)
        val func = if(dir) uPlus else lPlus
        val asg = Assign(nvar,FuncOf(func,Pair(lbound,rbound)))
        val prog = Compose(Compose(lprog,rprog),asg)
        val plusLem = if(dir) uPlusLem else lPlusLem
        val antepos = if(dir) 0 else 1 //The position in the context axioms
        println(lpf)
        println(rpf)
        //[P;((a;b);c)]
        (proveBy(Sequent(intervalAxiomContext,IndexedSeq(Box(Compose(ctxprog,prog),conc))),
          useAt(composeAssoc)(1) &
          //[(P;(a;b));c)]
          useAt("[;] compose")(1) &
          useAt("[:=] assign")(SuccPosition(1,1::Nil)) &
          //[P;(a;b)]
          useAt(composeAssoc)(1) &
          useAt("plusLem",plusLem,PosInExpr(1::Nil), (us:Subst)=>fixSubst(us,lbound,rbound))(SuccPosition(1,1::Nil))&
          //[(P;a);b]
          useAt("[] split")(1) & andR(1)
          <(useAt("[;] compose")(1) & chase(SuccPosition(1,1::Nil)) & by(lpf),
          useAt("[] split")(1) & andR(1)
          <(by(rpf),
            useAt("V Vacuous",(us:Subst)=>us++RenUSubst(("a;".asProgram, Compose(Compose(ctxprog,lprog),rprog))::Nil))
              (AntePos(antepos)) &
            implyRi(AntePos(antepos),SuccPos(0)) &
//            //cohideR(1) &
            useAt("K modal modus ponens",PosInExpr(1::Nil))(1)&
            //Somehow, substituting x here breaks??
            useAt("all instantiate",(us:Subst)=>us++RenUSubst(("f()".asTerm, lbound)::Nil))(SuccPosition(1,1::0::Nil)) &
            useAt("all instantiate",(us:Subst)=>us++RenUSubst(("f()".asTerm, rbound)::Nil))(SuccPosition(1,1::0::Nil)) &
            simpTac(SuccPosition(1,1::Nil)) &
            useAt("V Vacuous",PosInExpr(1::Nil))(1) &
            closeT))),
          prog,conc,nvar)
    }


  }
  */


  def getBounds(f:Formula) =
    symbols(f).map(t => List(LessEqual(FuncOf(Function(lbPrefix,None,Real,Real),t),t),
      LessEqual(t,FuncOf(Function(ubPrefix,None,Real,Real),t)))).flatten

  //Same as symbols in TacticHelper, returns the set of vars and nullary function symbols
  //todo: Ensure that the upper and lower bound prefixes do not appear inside
  def symbols(f: Formula): Set[Term] = {
    var symbols = Set[Term]()
    ExpressionTraversal.traverse(new ExpressionTraversal.ExpressionTraversalFunction {
      override def preT(p: PosInExpr, e: Term): Either[Option[ExpressionTraversal.StopTraversal], Term] = e match {
        case v: Variable => symbols += v; Left(None)
        case FuncOf(fn: Function, u:AtomicTerm) => if(u==Nothing) symbols += e; Left(None)
        case _ => Left(None)
      }
    }, f)
    symbols
  }

  //Flips >= and >, and splits < and <= into two interval checks
  lazy val splitGreaterEqual: DependentPositionTactic = chaseI(5, 5, (exp: Expression) => exp match {
    case And(_,_) => "& recursor" :: Nil
    case Or(_,_) => "| recursor" :: Nil
    case GreaterEqual(_,_) => ">= flip" :: Nil
    case Greater(_,_) => "> flip" :: Nil
    case LessEqual(_,_) => "<= both" :: Nil
    case Less(_,_) => "< both" :: Nil
    case _ => Nil
  },
    (ax:String) => (us:Subst) => ax match {
      case "<= both" | "< both" => us ++ RenUSubst(
        ("F_()".asTerm, FuncOf(Function(ubPrefix,None,Real,Real), us("f_()".asTerm))) ::
          ("G_()".asTerm, FuncOf(Function(ubPrefix,None,Real,Real), us("g_()".asTerm))) ::
          ("ff_()".asTerm, FuncOf(Function(lbPrefix,None,Real,Real), us("f_()".asTerm))) ::
          ("gg_()".asTerm, FuncOf(Function(lbPrefix,None,Real,Real), us("g_()".asTerm))) ::
          Nil)
      case _ => us
    })

  //"NNF" by pushing negations into equations/inequations
  lazy val toNNF: DependentPositionTactic = chaseI(5, 5, (exp: Expression) => exp match {
    case And(_,_) => "& recursor" :: Nil
    case Or(_,_) => "| recursor" :: Nil
    case Imply(_,_) => "-> expand" :: Nil
    case Not(_) => AxiomIndex.axiomsFor(exp)
    case _ => Nil
  },
    ax => us => us
  )

  //Chases intervals inwards
  lazy val intervalify: DependentPositionTactic = chaseI(5, 5, (exp: Expression) => exp match {
    case And(_,_) => "& recursor" :: Nil
    case Or(_,_) => "| recursor" :: Nil
    case LessEqual(FuncOf(Function(lbPrefix,_,_,_,_),_),rhs) =>
      rhs match{
        case Plus(_,_) => "<=+ down" :: Nil
        case Minus(_,_) => "<=- down" :: Nil
        case Times(_,_) => "<=* down" :: Nil
        case Divide(_,_) => "<=Div down" :: Nil
        case Power(_,_) => "<=pow down" :: Nil
        case FuncOf(Function("abs",_,_,_,_),_) => "<=abs down" :: Nil
        case _ => Nil
      }
    case LessEqual(lhs,FuncOf(Function(ubPrefix,_,_,_,_),_)) =>
      lhs match{
        case Plus(_,_) => "+<= up" :: Nil
        case Minus(_,_) => "-<= up" :: Nil
        case Times(_,_) => "*<= up" :: Nil
        case Divide(_,_) => "Div<= up" :: Nil
        case Power(_,_) => "pow<= up" :: Nil
        case FuncOf(Function("abs",_,_,_,_),_) => "abs<= up" :: Nil
        case _ => Nil
      }
    case _ => Nil
  },
    (ax:String) => (us:Subst) => ax match {
      case "+<= up" | "-<= up" | "<=+ down" | "<=- down" | "<= both" | "*<= up" | "<=* down" | "Div<= up" | "<=Div down" | "pow<= up" | "<=pow down" | "abs<= up" | "<=abs down" => us ++ RenUSubst(
        ("F_()".asTerm, FuncOf(Function(ubPrefix,None,Real,Real), us("f_()".asTerm))) ::
          ("G_()".asTerm, FuncOf(Function(ubPrefix,None,Real,Real), us("g_()".asTerm))) ::
          ("ff_()".asTerm, FuncOf(Function(lbPrefix,None,Real,Real), us("f_()".asTerm))) ::
          ("gg_()".asTerm, FuncOf(Function(lbPrefix,None,Real,Real), us("g_()".asTerm))) ::
          Nil)
      case _ => us
    }
  )

}