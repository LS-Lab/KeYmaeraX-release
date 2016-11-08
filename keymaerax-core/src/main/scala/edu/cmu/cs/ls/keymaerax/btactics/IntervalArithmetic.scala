/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.{OnAll, RenUSubst, _}
import edu.cmu.cs.ls.keymaerax.core.{Assign, Variable, _}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms._
import edu.cmu.cs.ls.keymaerax.btactics.DebuggingTactics.print
import edu.cmu.cs.ls.keymaerax.btactics.SimplifierV2._
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._

import scala.collection.immutable._

/**
  * Tactics for introducing interval arithmetic.
  *
  * @author Yong Kiam Tan
  */
object IntervalArithmetic {

  private val ubPrefix = "u"
  private val lbPrefix = "l"
  private val DEBUG = false

  private val PlusU = Function("PlusU", None, Tuple(Real, Real), Real)
  private val PlusL = Function("PlusL", None, Tuple(Real, Real), Real)
  private val MinusU = Function("MinusU", None, Tuple(Real, Real), Real)
  private val MinusL = Function("MinusL", None, Tuple(Real, Real), Real)
  private val TimesU = Function("TimesU", None, Tuple(Real, Real), Real)
  private val TimesL = Function("TimesL", None, Tuple(Real, Real), Real)
  private val DivU = Function("DivU", None, Tuple(Real, Real), Real)
  private val DivL = Function("DivL", None, Tuple(Real, Real), Real)
  private val maxF = Function("max", None, Tuple(Real, Real), Real, interpreted=true)
  private val minF = Function("min", None, Tuple(Real, Real), Real, interpreted=true)
  private val absF = Function("min", None, Real, Real, interpreted=true)

  //Axiomatized functions
  private val axFuncs = List(PlusU,PlusL,TimesU,TimesL) //Ignored: MinusU,MinusL,DivU,DivL

  //Interpreted functions
  private val builtinFuncs = List(maxF,minF,absF)

  //Things that are considered variable inputs (no upper and lower bounds)
  //This is used to optimize calculation for times,power
  private def isVar(t:Term) : Boolean = {
    t match {
      case _ :AtomicTerm | FuncOf(_,Nothing) =>
        true
      case _ =>
        false
    }
  }

  private def getVarName(t:Term) : String = {
    //todo: Find some other neater way to generate these names
    t match {
      case at:AtomicTerm  =>
        at.prettyString
      case FuncOf(f,Nothing) => //Allows functions with unit args
        f.name
      case FuncOf(f,e) if (axFuncs.contains(f))=> //This allows interpreted functions
        f.name+getVarName(e)
      //case Pair(l,r)=>
      //  "L"+getVarName(l)+"C"+getVarName(r)+"R"
      case Plus(l,r) =>
        "pL"+getVarName(l)+"C"+getVarName(r)+"R"
      case Times(l,r) =>
        "tL"+getVarName(l)+"C"+getVarName(r)+"R"
      case Minus(l,r) =>
        "mL"+getVarName(l)+"C"+getVarName(r)+"R"
      case Power(l,r) =>
        "powL"+getVarName(l)+"C"+getVarName(r)+"R"
      case Divide(l,r) =>
        "dL"+getVarName(l)+"C"+getVarName(r)+"R"
      case Neg(l) =>
        "nL"+getVarName(l)+"R"
      case _ => {
        if (DEBUG) println("Unknown term: "+t);
        ???}
    }
  }

  //Check if the context program already calculates the bound variable
  private def contextContains(prog:Program,v:String) : Boolean = {
    prog match
    {
      case Assign(nvar,t) => nvar.name.equals(v)
      case Compose(lp,rp) =>
        contextContains(lp,v) | contextContains(rp,v)
      case Choice(lp,rp) =>
        contextContains(lp,v) & contextContains(rp,v)
      case _ => ???
    }
  }

  //Encoding of no-op
  private val nop = Assign(Variable("x_"),Variable("x_"))

  //Axiomatization of op-with-rounding functions
  val intervalAxiomContext = IndexedSeq(
    "\\forall x \\forall y (x + y <= PlusU(x,y))".asFormula,
    "\\forall x \\forall y (PlusL(x,y) <= x + y)".asFormula,

    "\\forall x \\forall y (x * y <= TimesU(x,y))".asFormula,
    "\\forall x \\forall y (TimesL(x,y) <= x * y)".asFormula,

    //todo: Remove these if we end up not using them
    "\\forall x \\forall y (x - y <= MinusU(x,y))".asFormula,
    "\\forall x \\forall y (MinusL(x,y) <= x - y)".asFormula,

    "\\forall x \\forall y (x / y <= DivU(x,y))".asFormula,
    "\\forall x \\forall y (DivL(x,y) <= x / y)".asFormula
  )

  //todo: negation lemma just strips the negation and flips the inequality
  private val NegLem = proveBy("g_()<=f_() -> -(f_()) <= -(g_())".asFormula,QE)

  private def liftSubst(s:Option[Subst]) : Subst =
    s match{
      case None => RenUSubst(Nil)
      case Some(_) => s.get
    }
  //Arithmetic lemmas involving the interval axioms
  private val PlusULem = proveBy(("((\\forall x \\forall y (x + y <= PlusU(x,y))) & f_() <= F_() & g_() <= G_()) ->" +
    "f_() + g_() <= PlusU(F_(),G_())").asFormula,
    useAt("all instantiate",(us:Option[Subst])=>liftSubst(us)++RenUSubst(("f()".asTerm,"F_()".asTerm)::Nil))(SuccPosition(1,0::0::Nil)) &
      useAt("all instantiate",(us:Option[Subst])=>liftSubst(us)++RenUSubst(("f()".asTerm,"G_()".asTerm)::Nil))(SuccPosition(1,0::0::Nil)) &
      useAt("+<= up",PosInExpr(1::Nil))(SuccPosition(1,1::Nil)) & prop)

  private val PlusLLem = proveBy(("((\\forall x \\forall y (PlusL(x,y) <= x + y)) & ff_() <= f_() & gg_() <= g_()) ->" +
    "PlusL(ff_(),gg_()) <= f_() + g_()").asFormula,
    useAt("all instantiate",(us:Option[Subst])=>liftSubst(us)++RenUSubst(("f()".asTerm,"ff_()".asTerm )::Nil))(SuccPosition(1,0::0::Nil)) &
      useAt("all instantiate",(us:Option[Subst])=>liftSubst(us)++RenUSubst(("f()".asTerm,"gg_()".asTerm )::Nil))(SuccPosition(1,0::0::Nil)) &
      useAt("<=+ down",PosInExpr(1::Nil))(SuccPosition(1,1::Nil)) & prop)

  private val MinusULem = proveBy(("((\\forall x \\forall y (x - y <= MinusU(x,y))) & f_() <= F_() & gg_() <= g_()) ->" +
    "f_() - g_() <= MinusU(F_(),gg_())").asFormula,
    useAt("all instantiate",(us:Option[Subst])=>liftSubst(us)++RenUSubst(("f()".asTerm,"F_()".asTerm )::Nil))(SuccPosition(1,0::0::Nil)) &
      useAt("all instantiate",(us:Option[Subst])=>liftSubst(us)++RenUSubst(("f()".asTerm,"gg_()".asTerm )::Nil))(SuccPosition(1,0::0::Nil)) &
      useAt("-<= up",PosInExpr(1::Nil))(SuccPosition(1,1::Nil)) & prop)

  private val MinusLLem = proveBy(("((\\forall x \\forall y (MinusL(x,y) <= x - y)) & ff_() <= f_() & g_() <= G_()) ->" +
    "MinusL(ff_(),G_()) <= f_() - g_()").asFormula,
    useAt("all instantiate",(us:Option[Subst])=>liftSubst(us)++RenUSubst(("f()".asTerm,"ff_()".asTerm )::Nil))(SuccPosition(1,0::0::Nil)) &
      useAt("all instantiate",(us:Option[Subst])=>liftSubst(us)++RenUSubst(("f()".asTerm,"G_()".asTerm )::Nil))(SuccPosition(1,0::0::Nil)) &
      useAt("<=- down",PosInExpr(1::Nil))(SuccPosition(1,1::Nil)) & prop)

  //Rewrites for max/min, not to be confused with the actual lemmas
  private val rwMax = proveBy( "h_() <= f_() | h_() <= g_() -> h_() <= max(f_(),g_()) ".asFormula,QE)
  private val rwMin = proveBy( "f_() <= H_() | g_() <= H_() -> min(f_(),g_()) <= H_()".asFormula,QE)

  //Specialization of both arguments
  private val TimesULemSpec = proveBy(("(\\forall x \\forall y (x * y <= TimesU(x,y))) ->" +
    "f_() * g_() <= TimesU(f_(),g_())").asFormula,
    implyR(1) & allL("f_()".asTerm)(-1) & allL("g_()".asTerm)(-1) & close)

  private val TimesLLemSpec = proveBy(("(\\forall x \\forall y (TimesL(x,y) <= x * y)) -> " +
    "TimesL(f_(),g_()) <= f_()*g_()").asFormula,
    implyR(1) & allL("f_()".asTerm)(-1) & allL("g_()".asTerm)(-1) & close)

  //todo: specialization of one or arg only (reduce the number of maxes to calculate to 1 instead of 3)

  private val TimesULem = proveBy(
    ("((\\forall x \\forall y (x * y <= TimesU(x,y))) & f_() <= F_() & ff_() <= f_() & g_() <= G_() & gg_() <= g_() ->" +
      "f_() * g_() <= max((max((TimesU((F_(),G_())),TimesU((F_(),gg_())))),max((TimesU((ff_(),G_())),TimesU((ff_(),gg_())))))))").asFormula,
    implyR(1) &
      useAt("*<= up",PosInExpr(1::Nil))(1) & prop &
      (OnAll((useAt("rwMax",rwMax,PosInExpr(1::Nil))(1)) & prop)*)
        <(allL("ff_()".asTerm)(-1) & allL("gg_()".asTerm)(-1),
        allL("ff_()".asTerm)(-1) & allL("G_()".asTerm)(-1),
        allL("F_()".asTerm)(-1) & allL("gg_()".asTerm)(-1),
        allL("F_()".asTerm)(-1) & allL("G_()".asTerm)(-1)) &
      OnAll(close))

  private val TimesLLem = proveBy(
    ("((\\forall x \\forall y (TimesL(x,y) <= x * y)) & f_() <= F_() & ff_() <= f_() & g_() <= G_() & gg_() <= g_() ->" +
      "min((min((TimesL((F_(),G_())),TimesL((F_(),gg_())))),min((TimesL((ff_(),G_())),TimesL((ff_(),gg_())))))) <= f_() * g_())").asFormula,
    implyR(1) &
      useAt("<=* down",PosInExpr(1::Nil))(1) & prop &
      (OnAll((useAt("rwMin",rwMin,PosInExpr(1::Nil))(1)) & prop)*)
        <(allL("ff_()".asTerm)(-1) & allL("gg_()".asTerm)(-1),
        allL("ff_()".asTerm)(-1) & allL("G_()".asTerm)(-1),
        allL("F_()".asTerm)(-1) & allL("gg_()".asTerm)(-1),
        allL("F_()".asTerm)(-1) & allL("G_()".asTerm)(-1)) &
      OnAll(close))

  private val rwPow2 = proveBy("f_()^2 = f_() * f_()".asFormula,QE)

  //specific bounds
  private val uPowLemSpec = proveBy(("(\\forall x \\forall y (x * y <= TimesU(x,y))) ->" +
    "f_()^2 <= TimesU(f_(),f_())").asFormula,
    implyR(1) & useAt(rwPow2,PosInExpr(0::Nil))(SuccPosition(1,0::Nil)) &
      allL("f_()".asTerm)(-1) & allL("f_()".asTerm)(-1) & close)

  private val lPowLemSpec = proveBy(("(\\forall x \\forall y (TimesL(x,y) <= x * y)) -> " +
    "TimesL(f_(),f_()) <= f_()^2").asFormula,
    implyR(1) & useAt(rwPow2,PosInExpr(0::Nil))(SuccPosition(1,1::Nil)) &
      allL("f_()".asTerm)(-1) & allL("f_()".asTerm)(-1) & close)

  //generic upper bound^2 lemmas
  private val uPowLem = proveBy(("((\\forall x \\forall y (x * y <= TimesU(x,y))) & ff_() <= f_() & f_() <= F_()) -> " +
    "f_()^2 <= max((TimesU(F_(),F_()),TimesU(ff_(),ff_())))").asFormula,
    implyR(1) & useAt("pow<= up",PosInExpr(1::Nil))(1) & prop &
      (OnAll(useAt(rwPow2,PosInExpr(0::Nil))(SuccPosition(1,0::Nil)))) &
      (OnAll((useAt("rwMax",rwMax,PosInExpr(1::Nil))(1)) & prop)*) &
      <(allL("ff_()".asTerm)(-1) & allL("ff_()".asTerm)(-1),
        allL("F_()".asTerm)(-1) & allL("F_()".asTerm)(-1)) &
      OnAll(close))

  //generic lower bound ^2 lemmas
  //When the interval is entirely positive
  private val lpowLem1 = proveBy("(0<=ff_() & ff_() <= f_() & h_() <= ff_()*ff_()) -> h_() <= f_()^2".asFormula,QE)
  private val poslPowLem = proveBy(
    ("((\\forall x \\forall y (TimesL(x,y) <= x * y)) & 0 <= ff_() & ff_() <= f_()) -> " +
      "TimesL(ff_(),ff_()) <= f_()^2").asFormula,
    implyR(1) &
      useAt(lpowLem1,PosInExpr(1::Nil))(1) & prop &
      allL("ff_()".asTerm)(-1) &
      allL("ff_()".asTerm)(-1) & close)
  //When the interval is entirely negative
  private val lpowLem2 = proveBy("(F_()<=0 & f_() <= F_() & h_() <= F_()*F_()) -> h_() <= f_()^2".asFormula,QE)
  private val neglPowLem = proveBy(
    ("((\\forall x \\forall y (TimesL(x,y) <= x * y)) & F_() <= 0 & f_() <= F_()) -> " +
      "TimesL(F_(),F_()) <= f_()^2").asFormula,
    implyR(1) &
      useAt(lpowLem2,PosInExpr(1::Nil))(1) & prop &
      allL("F_()".asTerm)(-1) &
      allL("F_()".asTerm)(-1) & close)
  //When it is inconclusive
  private val bothlPowLem = proveBy("0 <= F_()^2".asFormula,QE)

  //Optimized divison checking
  //Divisor >0 upper bound division
  //  private val udivLem1 = proveBy(("gg_() <= g_() & g_() <= G_() & f_() <= F_() & 0<gg_() &" +
  //    "F_()/G_() <= h_() & F_()/gg_() <= h_() -> f_()/g_() <= h_()").asFormula,QE)
  //  //Divisor >0 lower bound division
  //  private val udivLem2 = proveBy(("gg_() <= g_() & g_() <= G_() & ff_() <= f_() & 0<gg_() &" +
  //    "h_() <= ff_()/G_() & h_() <= ff_()/gg_() -> h_() <= f_()/g_()").asFormula,QE)
  //  //Divisor <0 upper bound division
  //  private val udivLem3 = proveBy(("gg_() <= g_() & g_() <= G_() & ff_() <= f_() & G_() < 0 &" +
  //    "ff_()/gg_() <= h_() & ff_()/G_() <= h_() -> f_()/g_() <= h_()").asFormula,QE)
  //  //Divisor <0 lower bound division
  //  private val udivLem4 = proveBy(("gg_() <= g_() & g_() <= G_() & f_() <= F_() & G_() < 0 &" +
  //    "h_() <= F_()/G_() & h_() <= F_()/gg_() -> h_() <= f_()/g_()").asFormula,QE)

  //todo: the specifications of DivU and DivL seem slightly off, because this doesn't require !(y=0),
  // but the full lemma does (because of appeal to QE)
  //Specialization of both arguments
  private val DivULemSpec = proveBy(("(\\forall x \\forall y (x / y <= DivU(x,y))) ->" +
    "f_() / g_() <= DivU(f_(),g_())").asFormula,
    implyR(1) & allL("f_()".asTerm)(-1) & allL("g_()".asTerm)(-1) & close)

  private val DivLLemSpec = proveBy(("(\\forall x \\forall y (DivL(x,y) <= x / y)) -> " +
    "DivL(f_(),g_()) <= f_() / g_()").asFormula,
    implyR(1) & allL("f_()".asTerm)(-1) & allL("g_()".asTerm)(-1) & close)

  private val DivULem = proveBy(("((\\forall x \\forall y (x / y <= DivU(x,y))) &" +
    "f_() <= F_() & ff_() <= f_() & g_() <= G_() & gg_() <= g_() & (G_()<0 | 0 < gg_()) -> " +
    "f_() / g_() <= max((max((DivU((F_(),G_())),DivU((F_(),gg_())))),max((DivU((ff_(),G_())),DivU((ff_(),gg_())))))))").asFormula,
    implyR(1) & (andL('Llast)*)&
      useAt("Div<= up",PosInExpr(1::Nil))(1) & simpTac(1) & hideL('Llast) & prop &
      (OnAll((useAt("rwMax",rwMax,PosInExpr(1::Nil))(1)) & prop)*) &
      <(allL("ff_()".asTerm)(-1) & allL("gg_()".asTerm)(-1),
        allL("ff_()".asTerm)(-1) & allL("G_()".asTerm)(-1),
        allL("F_()".asTerm)(-1) & allL("gg_()".asTerm)(-1),
        allL("F_()".asTerm)(-1) & allL("G_()".asTerm)(-1)) &
      OnAll(close))

  private val DivLLem = proveBy(("((\\forall x \\forall y (DivL(x,y) <= x / y)) &" +
    "f_() <= F_() & ff_() <= f_() & g_() <= G_() & gg_() <= g_() & (G_()<0 | 0<gg_()) -> " +
    "min((min((DivL((F_(),G_())),DivL((F_(),gg_())))),min((DivL((ff_(),G_())),DivL((ff_(),gg_())))))) <= f_() / g_() )").asFormula,
    implyR(1) & (andL('Llast)*)&
      useAt("<=Div down",PosInExpr(1::Nil))(1) & simpTac(1) & hideL('Llast) & prop &
      (OnAll((useAt("rwMin",rwMin,PosInExpr(1::Nil))(1)) & prop)*) &
      <(allL("ff_()".asTerm)(-1) & allL("gg_()".asTerm)(-1),
        allL("ff_()".asTerm)(-1) & allL("G_()".asTerm)(-1),
        allL("F_()".asTerm)(-1) & allL("gg_()".asTerm)(-1),
        allL("F_()".asTerm)(-1) & allL("G_()".asTerm)(-1)) &
      OnAll(close))

  //Upper bound for max, min
  private val MaxULem = proveBy("f_() <= F_() & g_() <= G_() -> max(f_(),g_()) <= max(F_(),G_())".asFormula,QE)
  private val MaxLLem = proveBy("ff_() <= f_() & gg_() <= g_() -> max(ff_(),gg_()) <= max(f_(),g_())".asFormula,QE)

  private val MinULem = proveBy("f_() <= F_() & g_() <= G_() -> min(f_(),g_()) <= min(F_(),G_())".asFormula,QE)
  private val MinLLem = proveBy("ff_() <= f_() & gg_() <= g_() -> min(ff_(),gg_()) <= min(f_(),g_())".asFormula,QE)

  //todo: abs is tricky because the interval can cross 0

  //encode if-then-else
  private def ifThenElse(f:Formula,p1:Program,p2:Program): Program =
  {
    Choice(Compose(Test(f),p1), Compose(Test(Not(f)),p2))
  }

  /**
    * @param dir direction of bound (true = upper, false = lower)
    * @param vars bounds already generated
    * @param t the term to bound
    * @return list of new vars bound, program and a bounding term calculated by that program
    */
  def deriveTermProgram(dir:Boolean,vars:List[String],t:Term) : (List[String],Program,Term) =
  {
    val varname = (if(dir) ubPrefix else lbPrefix) ++ getVarName(t)
    val nvar = Variable(varname)
    if (vars.contains(varname)) return (vars,nop,nvar)
    t match {
      case at:AtomicTerm =>
        return (vars,nop,t)
      case FuncOf(f,Nothing) =>
        return (vars,nop,t)
      case Neg(l) =>
        val (lvars,lp,lbound) = deriveTermProgram(!dir,vars,l)
        return(varname::lvars,Compose(lp,Assign(nvar,Neg(lbound))),nvar)
      case Plus(l,r) =>
        val (lvars,lp,lbound) = deriveTermProgram(dir,vars,l)
        val (rvars,rp,rbound) = deriveTermProgram(dir,lvars,r)
        val func = if(dir) PlusU else PlusL
        return (varname :: rvars,Compose(Compose(lp,rp),Assign(nvar,FuncOf(func,Pair(lbound,rbound)))),nvar)
      case Minus(l,r) =>
        val (lvars,lp,lbound) = deriveTermProgram(dir,vars,l)
        val (rvars,rp,rbound) = deriveTermProgram(!dir,lvars,r)
        val func = if(dir) MinusU else MinusL
        return (varname :: rvars,Compose(Compose(lp,rp),Assign(nvar,FuncOf(func,Pair(lbound,rbound)))),nvar)
      case Times(l,r) =>
        //Specific implementation if both l and r are known
        // (no need to calculate upper/lower bound)
        val func = if(dir) TimesU else TimesL
        if(isVar(l) & isVar(r)){
          val asg = Assign(nvar,FuncOf(func,Pair(l,r)))
          return (varname :: vars,asg,nvar)
        }

        //Upper bounds
        val (luvars,lup,lubound) = deriveTermProgram(true,vars,l)
        val (ruvars,rup,rubound) = deriveTermProgram(true,luvars,r)
        val (llvars,llp,llbound) = deriveTermProgram(false,ruvars,l)
        val (rlvars,rlp,rlbound) = deriveTermProgram(false,llvars,r)
        val bound = if(dir) maxF else minF
        val boundstr = if(dir) "max" else "min"
        //todo: all the variables used here can be skipped if they were already calculated elsewhere (e.g. by a divide)
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
        return (varname :: rlvars,prog,nvar)
      case Divide(l,r) =>
        val func = if(dir) DivU else DivL

        if(isVar(l) & isVar(r)){
          val asg = Assign(nvar,FuncOf(func,Pair(l,r)))
          return (varname :: vars,asg,nvar)
        }
        //Note: The interval must not cross 0
        val (luvars,lup,lubound) = deriveTermProgram(true,vars,l)
        val (ruvars,rup,rubound) = deriveTermProgram(true,luvars,r)
        val (llvars,llp,llbound) = deriveTermProgram(false,ruvars,l)
        val (rlvars,rlp,rlbound) = deriveTermProgram(false,llvars,r)
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
        //Bounds check
        //todo: we can avoid repeating this check
        val test = Test(Or(Less(rubound,Number(0)),Less(Number(0),rlbound)))
        //Final program
        val prog = Compose(Compose(Compose(prog1,test),prog2),Assign(nvar,FuncOf(bound,Pair(ubvar,lbvar))))
        return (varname :: rlvars,prog,nvar)
      case Power(l,n:Number) if n.value == 2 =>
        val func = if(dir) TimesU else TimesL
        val boundstr = if(dir) "max" else "min"

        //Specific implementation if the variable is already known
        // (no need to split the variable between upper/lower bound)
        if(isVar(l)){
          val asg = Assign(nvar,FuncOf(func,Pair(l,l)))
          return (varname :: vars,asg,nvar)
        }

        //Generic implementation for squaring to test out if-then-else
        val (luvars,lup,lubound) = deriveTermProgram(true,vars,l)
        val (llvars,llp,llbound) = deriveTermProgram(false,luvars,l)

        val prog1 = Compose(lup,llp)

        //Upper bound is standard
        if (dir){
          val uuasg = Assign(Variable(varname+"uu"),FuncOf(func,Pair(lubound,lubound)))
          val llasg = Assign(Variable(varname+"ll"),FuncOf(func,Pair(llbound,llbound)))
          val prog2 = Compose(uuasg,llasg)
          val lmax = Assign(nvar,FuncOf(maxF,Pair(Variable(varname+"uu"),Variable(varname+"ll"))))
          val prog = Compose(Compose(prog1,prog2),lmax)
          return(varname :: llvars,prog,nvar)
        }
        else
        {
          //If the U(x) <= 0 then U(x)^2 is a lower bound
          //else if the l(x) >= 0 then l(x)^2 is a lower bound
          //else 0 is the lower bound
          val luasg = Assign(nvar,FuncOf(func,Pair(lubound,lubound)))
          val llasg = Assign(nvar,FuncOf(func,Pair(llbound,llbound)))
          val zasg = Assign(nvar,Number(0))
          val innerTest = ifThenElse( LessEqual(Number(0),llbound), llasg, zasg )
          val outerTest = ifThenElse(LessEqual(lubound,Number(0)),luasg,innerTest)
          val prog = Compose(prog1,outerTest)
          return(varname :: llvars,prog,nvar)
        }
      case _ => return(vars,nop,t)
    }
  }

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

  private def hideDiamond(e:Expression) : List[String] =
  {
    e match {
      //This hides the final diamond
      case Diamond(Test(_),True) => Nil
      case Diamond(_,_) =>  AxiomIndex.axiomsFor(e)
      case  _ => Nil //AxiomIndex.axiomsFor(e)
    }
  }

  private val lastImplyRi: DependentTactic  = new SingleGoalDependentTactic("lastImplyRi") {
    override def computeExpr(sequent: Sequent): BelleExpr = {
      assert(sequent.ante.length > 0)
      implyRi(AntePos(sequent.ante.length-1),SuccPos(0))
    }
  }

  //Explicitly pattern match to apply the correct lemmas for each arithmetic goal shape
  val patmatchArith :DependentTactic = new SingleGoalDependentTactic("patmatchArith") {
    override def computeExpr(sequent:Sequent): BelleExpr = {
      sequent.succ(0) match {
        case LessEqual(a,b) => (a,b) match{
          case (Neg(_),Neg(_)) => useAt(NegLem,PosInExpr(1::Nil))(1)
          case (_,Plus(_,_)) => useAt(PlusLLem,PosInExpr(1::Nil))(1) & andR('_) < (close, andR('_))
          case (Plus(_,_),_) => useAt(PlusULem,PosInExpr(1::Nil))(1) & andR('_) < (close, andR('_))
          case (_,Minus(_,_)) => useAt(MinusLLem,PosInExpr(1::Nil))(1) & andR('_) < (close, andR('_))
          case (Minus(_,_),_) => useAt(MinusULem,PosInExpr(1::Nil))(1) & andR('_) < (close, andR('_))
          case (_,Times(l,r)) => {
            if(isVar(l) & isVar(r)){
              useAt(TimesLLemSpec,PosInExpr(1::Nil))(1)
            }
            else useAt(TimesLLem,PosInExpr(1::Nil))(1) & andR('_) < (close, (OnAll(?(andR('_)))*))
          }
          case (Times(l,r),_) => {
            if(isVar(l) & isVar(r)){
              useAt(TimesULemSpec,PosInExpr(1::Nil))(1)
            }
            else useAt(TimesULem,PosInExpr(1::Nil))(1) & andR('_) < (close, (OnAll(?(andR('_)))*))
          }
          case (_,Divide(l,r)) => {
            if(isVar(l) & isVar(r)){
              useAt(DivLLemSpec,PosInExpr(1::Nil))(1)
            }
            else {
              useAt(DivLLem,PosInExpr(1::Nil))(1) & andR('_)  < (close, (OnAll(?(andR('_)))*))
            }
          }
          case (Divide(l,r),_) => {
            if(isVar(l) & isVar(r)){
              useAt(DivULemSpec,PosInExpr(1::Nil))(1)
            }
            else {
              useAt(DivULem,PosInExpr(1::Nil))(1) & andR('_) < (close, (OnAll(?(andR('_)))*))
            }
          }
          case (_,Power(n,_)) =>
            if(isVar(n)) {
              useAt(lPowLemSpec,PosInExpr(1::Nil))(1)
            }
            else
              (useAt(poslPowLem,PosInExpr(1::Nil))(1) & andR('_) <(close, andR('_) <(close,ident))) |
                (useAt(neglPowLem,PosInExpr(1::Nil))(1) & andR('_) <(close, andR('_) <(close,ident))) |
                (cohideR(1) & byUS(bothlPowLem))
          case (Power(n,_),_) =>
            if(isVar(n)){
              useAt(uPowLemSpec,PosInExpr(1::Nil))(1)
            }
            else useAt(uPowLem,PosInExpr(1::Nil))(1) & andR('_) <(close, andR('_))
          case f => ident
        }
        case _ => ident
      }
    }
  }

  def debugPrint(str:String) : BelleExpr =
    if (DEBUG) print(str) else ident

  def deriveFormulaProof(f:Formula) : (Program,Provable) =
  {
    // f must be in NNF, with negations completely pushed into comparisons
    // Also, >, >= should be flipped to <, <=
    val(_,pinit,ff) = deriveFormulaProgram(Nil,f)
    val prog = Compose(stripNoOp(pinit),Test(ff))

    val pf = proveBy(Sequent(intervalAxiomContext,IndexedSeq(Imply(Diamond(prog,True),f))),
      //Turn the program part into a formula first, preserving the test part using hideDiamond
      debugPrint("Chasing away formula") &
        useAt("<;> compose")(SuccPosition(1,0::Nil)) &
        //        chase(3,3, (e:Expression)=>chaseAtomic(e))(SuccPosition(1,0::Nil)) & ident)
        chase(3,3, (e:Expression)=>hideDiamond(e))(SuccPosition(1,0::Nil)) &
        //Strip off all accumulated side conditions
        implyR(1) &
        //This is really slow if the goal splits a lot...
        debugPrint("splitting") &
        (OnAll(?(andL('Llast) | orL('Llast) ))*) &
        debugPrint("solve") &
        //Conditional bounds like those found in squares might lead to splitting
        OnAll(
          lastImplyRi &
            //Now clear up the diamond for the test part
            chase(SuccPosition(1,0::Nil)) &
            useAt("&true")(SuccPosition(1,0::Nil)) &
            //print("decompose f") &
            //Repeatedly decompose w.r.t. shape of formula
            (OnAll(?(
              (useAt(decomposeAnd,PosInExpr(1::Nil))(1) & andR('_)) |
                (useAt(decomposeOr,PosInExpr(1::Nil))(1) & andR('_))))*) &
            //Decompose inequalities
            debugPrint("decompose ineq") &
            (OnAll(?(
              (useAt(decomposeLE,PosInExpr(1::Nil))(1) & andR('_)) |
                (useAt(decomposeLT,PosInExpr(1::Nil))(1) & andR('_)) |
                (useAt(decomposeGE,PosInExpr(1::Nil))(1) & andR('_)) |
                (useAt(decomposeGT,PosInExpr(1::Nil))(1) & andR('_))
            )) *) &
            debugPrint("arith") &
            //single step removal of the rounding arithmetic axioms
            ((OnAll(debugPrint("arith step") &patmatchArith & debugPrint("done")))*) &
            //reflexivity
            OnAll(simpTac(1) & ?(closeT))
        )
    )
    //Decompose the big formula if desired here
    (prog,pf)
  }

  def prettyTerm(t:Term) : String = {
    t match {
      case n:Number => "Const "+n.value.toString()
      case FuncOf(f,Pair(l,r)) if (axFuncs.contains(f)) =>
        //If f is an arith function, then print the arguments
        f.name+" ("+prettyTerm(l) +") ("+ prettyTerm(r)+")"
      case FuncOf(f,Pair(l,r)) if (builtinFuncs.contains(f)) =>
        //For max,min (and later,abs, we need to capitalize...)
        if (f.equals(maxF)) "Max ("+prettyTerm(l) +") ("+ prettyTerm(r)+")"
        else if (f.equals(minF)) "Min "+prettyTerm(l) +") ("+ prettyTerm(r)+")"
        else ???
      case FuncOf(f,Nothing) => "func_"+f.name
      case v:Variable => v.name
      case Neg(l) => "Neg ("+prettyTerm(l)
      case _ => "Unsupported: "+t.toString
    }
  }

  def prettyFormula(f:Formula) : String = {
    f match {
      case And(l,r) => "And ("+prettyFormula(l)+") ("+prettyFormula(r)+")"
      case Or(l,r) => "Or ("+prettyFormula(l)+") ("+prettyFormula(r)+")"
      case LessEqual(l,r) => "LessEqual ("+prettyTerm(l)+") ("+prettyTerm(r)+")"
      case Less(l,r) => "Less ("+prettyTerm(l)+") ("+prettyTerm(r)+")"
      case Equal(l,r) => "Equal ("+prettyTerm(l)+") ("+prettyTerm(r)+")"
      case NotEqual(l,r) => "NotEqual ("+prettyTerm(l)+") ("+prettyTerm(r)+")"
      case _ => "Unsupported: "+f.prettyString
    }
  }

  def prettyProg(p:Program) : String = {
    p match {
      //If-then-else encoding
      case Choice(Compose(Test(f),e1),Compose(Test(Not(ff)),e2)) if ff.equals(f) =>
        "If ("+prettyFormula(f)+") ("+prettyProg(e1)+") ("+prettyProg(e2)+")"
      case Compose(a,b) =>
        "Seq ("+prettyProg(a)+") ("+prettyProg(b)+")"
      //prettyProg(a)+";\n"+prettyProg(b)
      case Assign(x,e) =>
        //Brackets around names not necessary
        "Assign "+x.name+" ("+prettyTerm(e)+")"
      case Test(f) =>
        "Test ("+prettyFormula(f)+")"
      case _ => "Unsupported: "+p.prettyString
    }
  }

  private val equivExpand = proveBy("(p_() <-> q_()) <-> ((p_() -> q_()) & (q_() -> p_()))".asFormula,prop)

  private val minusExpand = proveBy("f_()-g_() = f_() +(-g_())".asFormula,QE)

  private val plusRec = proveBy("f_() + g_() = f_() + g_()".asFormula,byUS("= reflexive"))
  private val timesRec = proveBy("f_() * g_() = f_() * g_()".asFormula,byUS("= reflexive"))
  //private val divRec = proveBy("f_() / g_() = f_() / g_()".asFormula,byUS("= reflexive"))
  private val powerRec = proveBy("f_() ^ g_() = f_() ^ g_()".asFormula,byUS("= reflexive"))

  private val lessEqualRec = proveBy("f_() <= g_() <-> f_() <= g_()".asFormula,byUS("<-> reflexive"))
  private val lessRec = proveBy("f_() < g_() <-> f_() < g_()".asFormula,byUS("<-> reflexive"))

  private def binaryDefault(ax:Provable) = (ax,PosInExpr(0::Nil), PosInExpr(0::Nil)::PosInExpr(1::Nil)::Nil)
  //Converts an input formula (FOL, no quantifiers) into a formula satisfying:
  //1) NNF (negations pushed into (in)equalities)
  //2) Flip inequalities
  //3) Rewrite arithmetic, e.g. push (a-b) to a + (-b), custom rewrites of powers to squares
  def normalise(f:Formula) : (Formula,Provable) = {
    val refl = proveBy(Equiv(f,f),byUS("<-> reflexive"))
    val nnf = chaseCustom((exp: Expression) => exp match {
      case And(_,_) => fromAxIndex("& recursor"):: Nil
      case Or(_,_) => fromAxIndex("| recursor") :: Nil
      case Imply(_,_) => fromAxIndex("-> expand") :: Nil
      case Equiv(_,_) => binaryDefault(equivExpand)::Nil
      case Not(_) => AxiomIndex.axiomsFor(exp).map(fromAxIndex)
      case _ => Nil
    })(SuccPosition(1,1::Nil))(refl)

    val flip = chaseCustom((exp: Expression) => exp match {
      case And(_,_) => fromAxIndex("& recursor"):: Nil
      case Or(_,_) => fromAxIndex("| recursor") :: Nil
      case Greater(_,_) => fromAxIndex("> flip")::Nil
      case GreaterEqual(_,_) => fromAxIndex(">= flip")::Nil
      case _ => Nil
    })(SuccPosition(1,1::Nil))(nnf)

    //Recurses into all sub terms
    val arith = chaseCustom((exp:Expression) => exp match {
      case And(_,_) => fromAxIndex("& recursor"):: Nil
      case Or(_,_) => fromAxIndex("| recursor") :: Nil
      case LessEqual(a,b) => binaryDefault(lessEqualRec)::Nil
      case Less(a,b) => binaryDefault(lessRec)::Nil

      case Plus(a,b) => binaryDefault(plusRec)::Nil
      case Times(a,b) => binaryDefault(timesRec)::Nil
      case Power(a,b) => binaryDefault(powerRec)::Nil
      case Minus(a,b) => binaryDefault(minusExpand)::Nil
      case _ => Nil
    })(SuccPosition(1,1::Nil))(flip)

    val fml = arith.conclusion.succ(0).sub(PosInExpr(1::Nil)).get.asInstanceOf[Formula]
    return (fml,arith)
  }

}