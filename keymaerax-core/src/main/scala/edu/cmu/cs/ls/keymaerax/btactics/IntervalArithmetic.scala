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

import scala.collection.immutable._

/**
  * Tactics for introducing interval arithmetic.
  *
  * @author Yong Kiam Tan
  */
object IntervalArithmetic {

  private val ubPrefix = "u"
  private val lbPrefix = "l"
  private val DEBUG = true

  //Things that are considered variable inputs (no upper and lower bounds)
  //This is used to optimize calculation for times,power
  private def isVar(t:Term) : Boolean = {
    t match {
      case _ :AtomicTerm | _ :FuncOf =>
        true
      case _ =>
        false
    }
  }

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
    "\\forall x \\forall y (x + y <= uPlus(x,y))".asFormula,
    "\\forall x \\forall y (lPlus(x,y) <= x + y)".asFormula,

    "\\forall x \\forall y (x - y <= uMinus(x,y))".asFormula,
    "\\forall x \\forall y (lMinus(x,y) <= x - y)".asFormula,

    "\\forall x \\forall y (x * y <= uTimes(x,y))".asFormula,
    "\\forall x \\forall y (lTimes(x,y) <= x * y)".asFormula,

    "\\forall x \\forall y (x / y <= uDiv(x,y))".asFormula,
    "\\forall x \\forall y (lDiv(x,y) <= x / y)".asFormula
  )

  private val uPlus = Function("uPlus", None, Tuple(Real, Real), Real)
  private val lPlus = Function("lPlus", None, Tuple(Real, Real), Real)
  private val uMinus = Function("uMinus", None, Tuple(Real, Real), Real)
  private val lMinus = Function("lMinus", None, Tuple(Real, Real), Real)
  private val uTimes = Function("uTimes", None, Tuple(Real, Real), Real)
  private val lTimes = Function("lTimes", None, Tuple(Real, Real), Real)
  private val uDiv = Function("uDiv", None, Tuple(Real, Real), Real)
  private val lDiv = Function("lDiv", None, Tuple(Real, Real), Real)
  private val maxF = Function("max", None, Tuple(Real, Real), Real, interpreted=true)
  private val minF = Function("min", None, Tuple(Real, Real), Real, interpreted=true)

  //Arithmetic lemmas involving the interval axioms
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

  private val uMinusLem = proveBy(("((\\forall x \\forall y (x - y <= uMinus(x,y))) & f_() <= F_() & gg_() <= g_()) ->" +
    "f_() - g_() <= uMinus(F_(),gg_())").asFormula,
    useAt("all instantiate",(us:Subst)=>us++RenUSubst(("f()".asTerm,"F_()".asTerm )::Nil))(SuccPosition(1,0::0::Nil)) &
      useAt("all instantiate",(us:Subst)=>us++RenUSubst(("f()".asTerm,"gg_()".asTerm )::Nil))(SuccPosition(1,0::0::Nil)) &
      useAt("-<= up",PosInExpr(1::Nil))(SuccPosition(1,1::Nil)) & prop)

  private val lMinusLem = proveBy(("((\\forall x \\forall y (lMinus(x,y) <= x - y)) & ff_() <= f_() & g_() <= G_()) ->" +
    "lMinus(ff_(),G_()) <= f_() - g_()").asFormula,
    useAt("all instantiate",(us:Subst)=>us++RenUSubst(("f()".asTerm,"ff_()".asTerm )::Nil))(SuccPosition(1,0::0::Nil)) &
      useAt("all instantiate",(us:Subst)=>us++RenUSubst(("f()".asTerm,"G_()".asTerm )::Nil))(SuccPosition(1,0::0::Nil)) &
      useAt("<=- down",PosInExpr(1::Nil))(SuccPosition(1,1::Nil)) & prop)

  //Bad -- causes splitting
  private val maxLem = proveBy( "h_() <= f_() | h_() <= g_() -> h_() <= max(f_(),g_()) ".asFormula,QE)
  private val minLem = proveBy( "f_() <= H_() | g_() <= H_() -> min(f_(),g_()) <= H_()".asFormula,QE)

  //This is the exact shape for times generated
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

  private val rwPow2 = proveBy("f_()^2 = f_() * f_()".asFormula,QE)

  //specific bounds

  private val uPowLemSpec = proveBy(("(\\forall x \\forall y (x * y <= uTimes(x,y))) ->" +
    "f_()^2 <= uTimes(f_(),f_())").asFormula,
    implyR(1) & useAt(rwPow2,PosInExpr(0::Nil))(SuccPosition(1,0::Nil)) &
      allL("f_()".asTerm)(-1) & allL("f_()".asTerm)(-1) & close)

  private val lPowLemSpec = proveBy(("(\\forall x \\forall y (lTimes(x,y) <= x * y)) -> " +
    "lTimes(f_(),f_()) <= f_()^2").asFormula,
    implyR(1) & useAt(rwPow2,PosInExpr(0::Nil))(SuccPosition(1,1::Nil)) &
      allL("f_()".asTerm)(-1) & allL("f_()".asTerm)(-1) & close)

  //generic upper bound^2 lemmas
  private val uPowLem = proveBy(("((\\forall x \\forall y (x * y <= uTimes(x,y))) & ff_() <= f_() & f_() <= F_()) -> " +
    "f_()^2 <= max((uTimes(F_(),F_()),uTimes(ff_(),ff_())))").asFormula,
    implyR(1) & useAt("pow<= up",PosInExpr(1::Nil))(1) & prop &
      (OnAll(useAt(rwPow2,PosInExpr(0::Nil))(SuccPosition(1,0::Nil)))) &
      (OnAll((useAt("maxLem",maxLem,PosInExpr(1::Nil))(1)) & prop)*) &
      <(allL("ff_()".asTerm)(-1) & allL("ff_()".asTerm)(-1),
        allL("F_()".asTerm)(-1) & allL("F_()".asTerm)(-1)) &
      OnAll(close))

  //generic lower bound ^2 lemmas
  //When the interval is entirely positive
  private val lpowLem1 = proveBy("(0<=ff_() & ff_() <= f_() & h_() <= ff_()*ff_()) -> h_() <= f_()^2".asFormula,QE)
  private val poslPowLem = proveBy(
    ("((\\forall x \\forall y (lTimes(x,y) <= x * y)) & 0 <= ff_() & ff_() <= f_()) -> " +
      "lTimes(ff_(),ff_()) <= f_()^2").asFormula,
    implyR(1) &
      useAt(lpowLem1,PosInExpr(1::Nil))(1) & prop &
      allL("ff_()".asTerm)(-1) &
      allL("ff_()".asTerm)(-1) & close)
  //When the interval is entirely negative
  private val lpowLem2 = proveBy("(F_()<=0 & f_() <= F_() & h_() <= F_()*F_()) -> h_() <= f_()^2".asFormula,QE)
  private val neglPowLem = proveBy(
    ("((\\forall x \\forall y (lTimes(x,y) <= x * y)) & F_() <= 0 & f_() <= F_()) -> " +
      "lTimes(F_(),F_()) <= f_()^2").asFormula,
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

  private val uDivLem = proveBy(("((\\forall x \\forall y (x / y <= uDiv(x,y))) &" +
    "f_() <= F_() & ff_() <= f_() & g_() <= G_() & gg_() <= g_() & (G_()<0 | gg_()>0) -> " +
    "f_() / g_() <= max((max((uDiv((F_(),G_())),uDiv((F_(),gg_())))),max((uDiv((ff_(),G_())),uDiv((ff_(),gg_())))))))").asFormula,
    implyR(1) & (andL('Llast)*)&
      useAt("div<= up",PosInExpr(1::Nil))(1) & simpTac(1) & hideL('Llast) & prop &
      (OnAll((useAt("maxLem",maxLem,PosInExpr(1::Nil))(1)) & prop)*) &
      <(allL("ff_()".asTerm)(-1) & allL("gg_()".asTerm)(-1),
        allL("ff_()".asTerm)(-1) & allL("G_()".asTerm)(-1),
        allL("F_()".asTerm)(-1) & allL("gg_()".asTerm)(-1),
        allL("F_()".asTerm)(-1) & allL("G_()".asTerm)(-1)) &
      OnAll(close))

  private val lDivLem = proveBy(("((\\forall x \\forall y (lDiv(x,y) <= x / y)) &" +
    "f_() <= F_() & ff_() <= f_() & g_() <= G_() & gg_() <= g_() & (G_()<0 | gg_()>0) -> " +
    "min((min((lDiv((F_(),G_())),lDiv((F_(),gg_())))),min((lDiv((ff_(),G_())),lDiv((ff_(),gg_())))))) <= f_() / g_() )").asFormula,
    implyR(1) & (andL('Llast)*)&
      useAt("<=div down",PosInExpr(1::Nil))(1) & simpTac(1) & hideL('Llast) & prop &
      (OnAll((useAt("minLem",minLem,PosInExpr(1::Nil))(1)) & prop)*) &
      <(allL("ff_()".asTerm)(-1) & allL("gg_()".asTerm)(-1),
        allL("ff_()".asTerm)(-1) & allL("G_()".asTerm)(-1),
        allL("F_()".asTerm)(-1) & allL("gg_()".asTerm)(-1),
        allL("F_()".asTerm)(-1) & allL("G_()".asTerm)(-1)) &
      OnAll(close))

  private def ifThenElse(f:Formula,p1:Program,p2:Program): Program =
  {
    Choice(Compose(Test(f),p1), Compose(Test(Not(f)),p2))
  }
  /**
    * @param dir direction of bound (true = upper, false = lower)
    * @param vars bounds already generated
    * @param t the term to bound (atomics,appOf, +, - , *)
    * @return list of new vars bound, program and a bounding term calculated by that program
    */
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
      case Minus(l,r) =>
        val (lvars,lp,lbound) = deriveTermProgram(dir,vars,l)
        val (rvars,rp,rbound) = deriveTermProgram(!dir,lvars,r)
        val func = if(dir) uMinus else lMinus
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
      case Divide(l,r) =>
        //Note: The interval must not cross 0
        val (luvars,lup,lubound) = deriveTermProgram(true,vars,l)
        val (ruvars,rup,rubound) = deriveTermProgram(true,luvars,r)
        val (llvars,llp,llbound) = deriveTermProgram(false,ruvars,l)
        val (rlvars,rlp,rlbound) = deriveTermProgram(false,llvars,r)
        val func = if(dir) uDiv else lDiv
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
        val test = Test(Or(Less(rubound,Number(0)),Greater(rlbound,Number(0))))
        //Final program
        val prog = Compose(Compose(Compose(prog1,test),prog2),Assign(nvar,FuncOf(bound,Pair(ubvar,lbvar))))
        return (rlvars,prog,nvar)
      case Power(l,n:Number) if n.value == 2 =>
        val func = if(dir) uTimes else lTimes
        val boundstr = if(dir) "max" else "min"

        //Specific implementation if the variable is already known
        // (no need to split the variable between upper/lower bound)
        if(isVar(l)){
          val asg = Assign(nvar,FuncOf(func,Pair(l,l)))
          return (vars,asg,nvar)
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
          return(llvars,prog,nvar)
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
          return(llvars,prog,nvar)
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

  private def hideDiamond(e:Expression) : List[String] =
  {
    e match {
      //This hides hte final diamond
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
        case LessEqual(l,r) => (l,r) match{
          case (_,Plus(_,_)) => useAt(lPlusLem,PosInExpr(1::Nil))(1) & andR('_) < (close, andR('_))
          case (Plus(_,_),_) => useAt(uPlusLem,PosInExpr(1::Nil))(1) & andR('_) < (close, andR('_))
          case (_,Minus(_,_)) => useAt(lMinusLem,PosInExpr(1::Nil))(1) & andR('_) < (close, andR('_))
          case (Minus(_,_),_) => useAt(uMinusLem,PosInExpr(1::Nil))(1) & andR('_) < (close, andR('_))
          case (_,Times(_,_)) => useAt(lTimesLem,PosInExpr(1::Nil))(1) & andR('_) < (close, (OnAll(?(andR('_)))*))
          case (Times(_,_),_) => useAt(uTimesLem,PosInExpr(1::Nil))(1) & andR('_) < (close, (OnAll(?(andR('_)))*))
          case (_,Divide(_,_)) => useAt(lDivLem,PosInExpr(1::Nil))(1) & andR('_)  < (close, (OnAll(?(andR('_)))*))
          case (Divide(_,_),_) => useAt(uDivLem,PosInExpr(1::Nil))(1) & andR('_) < (close, (OnAll(?(andR('_)))*))
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

  def deriveFormulaProof(f:Formula) : Provable =
  {
    //todo: f should be converted to nnf
    println(uDivLem)
    val(_,pinit,ff) = deriveFormulaProgram(Nil,f)
    val prog = Compose(stripNoOp(pinit),Test(ff))
    if(DEBUG) prettyPrint(prog)
    val pf = proveBy(Sequent(intervalAxiomContext,IndexedSeq(Imply(Diamond(prog,True),f))),
      //Turn the program part into a formula first, preserving the test part using hideDiamond
      debugPrint("Chasing away formula") &
        useAt("<;> compose")(SuccPosition(1,0::Nil)) &
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
            debugPrint("deompose ineq") &
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
    //Decompose the big formula here
    pf
  }

  def prettyPrint(p:Program) : Unit = {
    p match {
      case Compose(a,b) =>
        {
          prettyPrint(a)
          prettyPrint(b)
        }
      case _ => println(p.toString)
    }

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