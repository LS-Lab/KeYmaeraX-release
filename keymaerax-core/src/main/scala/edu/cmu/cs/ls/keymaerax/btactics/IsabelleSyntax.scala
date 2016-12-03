/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.{OnAll, RenUSubst, _}
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.DebuggingTactics.print
import edu.cmu.cs.ls.keymaerax.btactics.Idioms._
import edu.cmu.cs.ls.keymaerax.btactics.SimplifierV2._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core.{Assign, Variable, _}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig

import scala.collection.immutable._

/**
  * Tactics for converting a ModelPlex formula to Isabelle/HOL (no need for interval arithmetic)
  *
  * @author Yong Kiam Tan
  */
object IsabelleSyntax {

  private val DEBUG = true

  private val maxF = Function("max", None, Tuple(Real, Real), Real, interpreted=true)
  private val minF = Function("min", None, Tuple(Real, Real), Real, interpreted=true)
  private val absF = Function("min", None, Real, Real, interpreted=true)

  //axiomatized functions
  private val axFuncs = List(maxF,minF,absF)

  private val tempName = "temp"

  //Encoding of no-op
  private val nop = Assign(Variable("x_"),Variable("x_"))

  //Optimization from formula into a dL program that uses temporaries to minimize re-calculation
  /**
    * @param vars maps terms that have already been generated to the variable containing that term
    * @param tempctr counter for fresh temporaries
    * @param t the term to decompose
    * @return the accumulators for vars,tempctr, a program, and a term calculated by that program
    */
  def deriveTermProgram(t:Term,vars:Map[Term,Variable] = Map[Term,Variable](),tempctr:Integer = 0) : (Map[Term,Variable],Integer,Program,Term) = {
    vars.get(t) match {
      case Some(v) =>
        //Term already generated
        return (vars, tempctr, nop, v)
      case None => {
        val nvar = Variable(tempName + tempctr.toString)
        val ctr = tempctr + 1

        t match {
          //These don't use new the new temporary
          case at: AtomicTerm =>
            return (vars, tempctr, nop, t)
          case FuncOf(f, Nothing) =>
            return (vars, tempctr, nop, t)
          case Neg(l) =>
            val (nvars, nctr, lp, lv) = deriveTermProgram(l,vars, ctr)
            return (nvars + (t -> nvar), nctr, Compose(lp, Assign(nvar, Neg(lv))), nvar)
          case binop: BinaryCompositeTerm =>
            val (l, r) = (binop.left, binop.right)
            val (lvars, lctr, lp, lv) = deriveTermProgram(l,vars, ctr)
            val (rvars, rctr, rp, rv) = deriveTermProgram(r,lvars, lctr)
            return (rvars + (t -> nvar), rctr, Compose(Compose(lp, rp), Assign(nvar, binop.reapply(lv, rv))), nvar)
          case _ => return (vars, tempctr, nop, t)
        }
      }
    }
  }

  //Returns a program, and an equivalent formula to check after that program
  def deriveFormulaProgram(f:Formula,vars:Map[Term,Variable] = Map[Term,Variable](),tempctr:Integer = 0) : (Map[Term,Variable],Integer,Program,Formula) = {
    f match {
      case binop:ComparisonFormula =>
      {
        val (l,r) = (binop.left,binop.right)
        val (lvars,lctr,lp,lv) = deriveTermProgram(l,vars,tempctr)
        val (rvars,rctr,rp,rv) = deriveTermProgram(r,lvars,lctr)
        return (rvars, rctr, Compose(lp,rp),binop.reapply(lv,rv))
      }
      case binf: BinaryCompositeFormula =>
      {
        val (l,r) = (binf.left,binf.right)
        val (lvars,lctr,lp,lf) = deriveFormulaProgram(l,vars,tempctr)
        val (rvars,rctr,rp,rf) = deriveFormulaProgram(r,lvars,lctr)
        return (rvars, rctr, Compose(lp,rp),binf.reapply(lf,rf))
      }
      case Not(l) =>
      {
        val (lvars,lctr,lp,lf) = deriveFormulaProgram(l,vars,tempctr)
        return (lvars, lctr, lp,Not(lf))
      }
    }
  }

  def listConj(ls:List[Formula]) : Formula = {
    ls match {
      case Nil => True
      case (x::xs) => And(x,listConj(xs))//Compose(Test(x),listConj(xs))
    }
  }

  //Common formula elimination (reverse deMorgan/distributivity) for Or and And
  def commonFormula(f:Formula) : (Set[Formula],Formula) = {
    f match{
      case Or(l,r) =>
        val (lfs,lp) = commonFormula(l)
        val (rfs,rp) = commonFormula(r)
        val common = lfs.intersect(rfs)
        val ldiff = lfs.diff(common)
        val rdiff = rfs.diff(common)
        (common,Or(And(listConj(ldiff.toList),lp),And(listConj(rdiff.toList),rp) ))//Choice(Compose(listConj(ldiff.toList),lp),Compose(listConj(rdiff.toList),rp)))
      case And(l,r) =>
        val (lfs,lp) = commonFormula(l)
        val (rfs,rp) = commonFormula(r)
        val common = lfs.union(rfs)
        (common,And(lp,rp))
      case _ => (Set(f),True)
    }
  }

  private val decomposeAnd = proveBy("((P_() -> PP_()) & (Q_() -> QQ_())) -> (P_() & Q_() -> PP_() & QQ_())".asFormula,prop)
  private val decomposeOr = proveBy("((P_() -> PP_()) & (Q_() -> QQ_())) -> (P_() | Q_() -> PP_() | QQ_())".asFormula,prop)

  private val lastImplyRi: DependentTactic  = new SingleGoalDependentTactic("lastImplyRi") {
    override def computeExpr(sequent: Sequent): BelleExpr = {
      assert(sequent.ante.length > 0)
      implyRi(AntePos(sequent.ante.length-1),SuccPos(0))
    }
  }

  def commonFormulaProof(f:Formula) : (Formula,ProvableSig) = {
    val (fs,fu) = commonFormula(f)
    val ff = And(listConj(fs.toList),fu)

    (ff,proveBy(Imply(ff,f),
      (OnAll(?
      (implyR(1) & andL('Llast) & lastImplyRi & (andL('_)*) &
        ?((useAt(decomposeAnd,PosInExpr(1::Nil))(1) & andR('_)) |
          (useAt(decomposeOr,PosInExpr(1::Nil))(1) & andR('_)))))*) & prop))
  }


  def compileFormula(f:Formula) : Program = {
    f match {
      case Or(l,r) => Choice(compileFormula(l),compileFormula(r))
      case And(l,r) => Compose(compileFormula(l),compileFormula(r))
      case _ => Test(f)
    }
  }

  def compileFormulaProof(f:Formula) :ProvableSig = {
    val prog = compileFormula(f)
    proveBy(Imply(Diamond(prog,True),Diamond(Test(f),True)),
      chase(3,3)(SuccPosition(1,0::Nil)) &
        chase(3,3)(SuccPosition(1,1::Nil)) &
        //TODO: This is slow
        prop)
  }

  def debugPrint(str:String) : BelleExpr =
    if (DEBUG) print(str) else ident

  private def default(ax:ProvableSig) = (ax,PosInExpr(0::Nil), PosInExpr(0::Nil)::PosInExpr(1::Nil)::Nil)

  def deriveFormulaProof(f:Formula,decompose:Boolean=false) : (Program,ProvableSig) =
  {
    val(_,_,pinit,ff) = deriveFormulaProgram(f)
    //val prog = Compose(stripNoOp(pinit),Test(ff))
    val formula = if(decompose)compileFormula(ff) else Test(ff)
    val prog = Compose(stripNoOp(pinit),formula)

    val pf = proveBy(Imply(Diamond(prog,True),f),
      chase(3,3)(SuccPosition(1,0::Nil)) & prop)
    (prog,pf)

    //    chase(3,3)(SuccPosition(1,0::Nil)) & implyR(1) & close)

    //    if(decompose)
    //    {
    //
    //      val split = useFor("<;> compose")(SuccPosition(1,0::Nil))(pf)
    //      val compf = compileFormulaProof(ff)
    //      val change = useFor(compf,PosInExpr(1::Nil))(SuccPosition(1,0::1::Nil))(split)
    //      val reassm = useFor("<;> compose",PosInExpr(1::Nil))(SuccPosition(1,0::Nil))(change)
    ////      val retprog = reassm.conclusion.succ(0).sub(PosInExpr(1::Nil)).get
    //      println("exp",reassm)
    //      (prog,pf)
    //
    //    }
    //    else
    //      //No decomposition
    //      (prog,pf)
  }

  def prettyTerm(t:Term) : String = {
    t match {
      case n:Number =>
        if (n.value>=0) "Const (Abs_bword "+n.value.toString()+")"
        else "Neg (Const (Abs_bword "+(-n.value).toString()+"))"
      case FuncOf(f,Nothing) => "Var ''func_"+f.name+"''"
      case v:Variable => "Var ''"+v.name+"''"
      case Plus(l,r) => "Plus ("+prettyTerm(l)+")"+" ("+prettyTerm(r)+")"
      case Times(l,r) => "Times ("+prettyTerm(l)+")"+" ("+prettyTerm(r)+")"
      case FuncOf(f,Pair(l,r)) if (axFuncs.contains(f)) =>
        //For max,min
        if (f.equals(maxF)) "Max ("+prettyTerm(l) +") ("+ prettyTerm(r)+")"
        else if (f.equals(minF)) "Min ("+prettyTerm(l) +") ("+ prettyTerm(r)+")"
        else ???
      //case FuncOf(f,t) if (axFuncs.contains(f)) =>
      //  "Abs ("+prettyTerm(t)+")"
      case Neg(l) => "Neg ("+prettyTerm(l)+")"
      case _ => throw new IllegalArgumentException("Unsupported Term: "+t.toString)
    }
  }

  def prettyFormula(f:Formula) : String = {
    f match {
      case LessEqual(l,r) => "Leq ("+prettyTerm(l)+") ("+prettyTerm(r)+")"
      case And(l,r) => "And ("+prettyFormula(l)+") ("+prettyFormula(r)+")"

      case Or(l,r) => "Or ("+prettyFormula(l)+") ("+prettyFormula(r)+")"
      case Less(l,r) => "Le ("+prettyTerm(l)+") ("+prettyTerm(r)+")"
      case Equal(l,r) => "Equals ("+prettyTerm(l)+") ("+prettyTerm(r)+")"
      case NotEqual(l,r) => "Not( Equal ("+prettyTerm(l)+") ("+prettyTerm(r)+") )"
      case _ => throw new IllegalArgumentException("Unsupported formula: "+f.prettyString)
    }
  }

  def prettyProg(p:Program) : String = {
    p match {
      //If-then-else encoding
      case Choice(a,b) =>
        "Choice ("+prettyProg(a)+") ("+prettyProg(b)+")"
      case Compose(a,b) =>
        "Seq ("+prettyProg(a)+") ("+prettyProg(b)+")"
      //prettyProg(a)+";\n"+prettyProg(b)
      case Assign(x,e) =>
        //Brackets around names not necessary
        "Assign ''"+x.name+"'' ("+prettyTerm(e)+")"
      case Test(f) =>
        "Test ("+prettyFormula(f)+")"
      case _ => throw new IllegalArgumentException("Unsupported program: "+p.prettyString)
    }
  }

  private val equivExpand = proveBy("(p_() <-> q_()) <-> ((p_() -> q_()) & (q_() -> p_()))".asFormula,prop)
  private val notEqualExpand = proveBy("f_() != g_() <-> f_() > g_() | f_() < g_()".asFormula,QE)

  private val minusExpand = proveBy("f_()-g_() = f_() +(-g_())".asFormula,QE)
  private val powExpand = proveBy("f_()^2 = f_() * f_()".asFormula,QE)

  private val plusRec = proveBy("f_() + g_() = f_() + g_()".asFormula,byUS("= reflexive"))
  private val timesRec = proveBy("f_() * g_() = f_() * g_()".asFormula,byUS("= reflexive"))
  //private val divRec = proveBy("f_() / g_() = f_() / g_()".asFormula,byUS("= reflexive"))
  private val powerRec = proveBy("f_() ^ g_() = f_() ^ g_()".asFormula,byUS("= reflexive"))

  //Single arg functions
  private val fun1Rec = proveBy("f_(x_()) = f_(x_())".asFormula,byUS("= reflexive"))
  private val fun2Rec = proveBy("f_(x_(),y_()) = f_(x_(),y_())".asFormula,byUS("= reflexive"))

  private val equalRec = proveBy("f_() = g_() <-> f_() = g_()".asFormula,byUS("<-> reflexive"))
  private val notEqualRec = proveBy("f_() != g_() <-> f_() != g_()".asFormula,byUS("<-> reflexive"))
  private val lessEqualRec = proveBy("f_() <= g_() <-> f_() <= g_()".asFormula,byUS("<-> reflexive"))
  private val lessRec = proveBy("f_() < g_() <-> f_() < g_()".asFormula,byUS("<-> reflexive"))

  private def binaryDefault(ax:ProvableSig) = (ax,PosInExpr(0::Nil), PosInExpr(0::Nil)::PosInExpr(1::Nil)::Nil)

  //Converts an input formula (FOL, no quantifiers) into a formula satisfying:
  //1) NNF (negations pushed into (in)equalities)
  //2) Flip inequalities
  //3) Rewrite arithmetic, e.g. push (a-b) to a + (-b), p_()^2 -> p_() * p_()
  def normalise(f:Formula) : (Formula,ProvableSig) = {
    val refl = proveBy(Equiv(f,f),byUS("<-> reflexive"))
    val nnf = chaseCustomFor((exp: Expression) => exp match {
      case And(_,_) => fromAxIndex("& recursor"):: Nil
      case Or(_,_) => fromAxIndex("| recursor") :: Nil
      case Imply(_,_) => fromAxIndex("-> expand") :: Nil
      case Equiv(_,_) => binaryDefault(equivExpand)::Nil
      case NotEqual(_,_) => binaryDefault(notEqualExpand)::Nil
      case Not(_) => AxiomIndex.axiomsFor(exp).map(fromAxIndex)
      case _ => Nil
    })(SuccPosition(1,1::Nil))(refl)

    val flip = chaseCustomFor((exp: Expression) => exp match {
      case And(_,_) => fromAxIndex("& recursor"):: Nil
      case Or(_,_) => fromAxIndex("| recursor") :: Nil
      case Greater(_,_) => fromAxIndex("> flip")::Nil
      case GreaterEqual(_,_) => fromAxIndex(">= flip")::Nil
      case _ => Nil
    })(SuccPosition(1,1::Nil))(nnf)

    //Recurses into all sub terms
    val arith = chaseCustomFor((exp:Expression) => exp match {
      case And(_,_) => fromAxIndex("& recursor"):: Nil
      case Or(_,_) => fromAxIndex("| recursor") :: Nil
      case LessEqual(a,b) => binaryDefault(lessEqualRec)::Nil
      case Less(a,b) => binaryDefault(lessRec)::Nil
      case Equal(a,b) => binaryDefault(equalRec)::Nil
      case NotEqual(a,b) => binaryDefault(notEqualRec)::Nil

      case FuncOf(_,Pair(l,r)) => (fun2Rec,PosInExpr(0::Nil), PosInExpr(0::0::Nil)::PosInExpr(0::1::Nil)::Nil) :: Nil
      case FuncOf(_,_) => (fun1Rec,PosInExpr(0::Nil), PosInExpr(0::Nil)::Nil):: Nil
      case Plus(a,b) => binaryDefault(plusRec)::Nil
      case Times(a,b) => binaryDefault(timesRec)::Nil
      case Power(a,b) => binaryDefault(powExpand)::Nil
      case Minus(a,b) => (minusExpand,PosInExpr(0::Nil), PosInExpr(0::Nil)::PosInExpr(1::0::Nil)::Nil) :: Nil
      case _ => Nil
    })(SuccPosition(1,1::Nil))(flip)

    val fml = arith.conclusion.succ(0).sub(PosInExpr(1::Nil)).get.asInstanceOf[Formula]
    return (fml,arith)
  }

  //Merging everything together
  def isarSyntax(f:Formula) : (Program,ProvableSig) = {
    val (normf, normproof) = normalise(f) //normf <-> f
    val (commf, commproof) = commonFormulaProof(normf) //commf -> normf
    val (simpf, simpproof) = formulaSimp(commf) //simpf <-> commf
    val (prog, pff) = deriveFormulaProof(simpf,true)

    //todo: Something is wrong with useFor
    val compose = proveBy(Imply(Diamond(prog,True),f),
      implyR(1) & useAt(normproof)(1) & useAt(commproof,PosInExpr(1::Nil))(1) & useAt(simpproof,PosInExpr(0::Nil))(1) &
      lastImplyRi & by(pff)
    )

    (prog,compose)

  }

}
