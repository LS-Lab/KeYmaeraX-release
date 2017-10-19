package edu.cmu.cs.ls.keymaerax.pt

import edu.cmu.cs.ls.keymaerax.core._

/**
  * Convert proof terms to sublanguage + syntax used by Isabelle formalization
  * Created by bbohrer on 10/19/17.
  * @see [[ProofChecker]]
  * @author Brandon Bohrer
  */
class IsabelleConverter {
  type ID = String
  type Isequent = (List[Iformula],List[Iformula])
  type Irule = (List[Isequent],Isequent)

  // @TODO: more maps for more identifier types -> more efficient code
  // @TODO: automatically consider both arity and number of symbols for determining type size
  case class IDMap(varMap:Map[(String,Option[Int]),String],
                   funMap:Map[String,String],
                   conMap:Map[String,String],
                   fArity:Int,
                   pArity:Int)
  //case class IRat(num:Number,den:Number)

  case class ConversionException(msg:String) extends Exception {}

  sealed trait Itrm {}
  case class IVar(id:ID) extends Itrm {}
  case class IDiffVar(id:ID) extends Itrm {}
  case class IConst(int:Int) extends Itrm {}
  case class IFunction(f:ID, args:List[Itrm]) extends Itrm {}
  case class IPlus(left:Itrm, right:Itrm) extends Itrm {}
  case class ITimes(left:Itrm, right:Itrm) extends Itrm {}
  case class IDifferential(child:Itrm) extends Itrm {}

  sealed trait IODE {}
  case class IOVar(id:ID) extends IODE {}
  case class IOSing(x:ID, t:Itrm) extends IODE {}
  case class IOProd(left:IODE,right:IODE) extends IODE {}

  sealed trait Ihp {}
  case class IPvar(id:ID) extends Ihp {}
  case class IAssign(id:ID, t:Itrm) extends Ihp {}
  case class IDiffAssign(id:ID, t:Itrm) extends Ihp {}
  case class ITest(child:Iformula) extends Ihp {}
  case class IEvolveODE(ode:IODE, con:Iformula) extends Ihp {}
  case class IChoice(left:Ihp,right:Ihp) extends Ihp {}
  case class ISequence(left:Ihp,right:Ihp) extends Ihp {}
  case class ILoop(child:Ihp) extends Ihp {}

  sealed trait Iformula {}
  case class IGeq(left:Itrm, right:Itrm) extends Iformula {}
  case class IProp(id:ID, args:List[Itrm]) extends Iformula {}
  case class INot(child:Iformula) extends Iformula {}
  case class IAnd(left:Iformula,right:Iformula) extends Iformula {}
  case class IExists(x:ID, child:Iformula) extends Iformula {}
  case class IDiamond(prog:Ihp, post:Iformula) extends Iformula {}
  case class IInContext(id:ID, child:Iformula) extends Iformula {}

  sealed trait IaxRule {}
  case class ICT() extends IaxRule {}
  case class ICQ() extends IaxRule {}
  case class ICE() extends IaxRule {}
  case class IG() extends IaxRule {}

  sealed trait IruleApp {}
  case class IURename(what:ID,repl:ID) extends IruleApp {}
  case class IBRename(what:ID,repl:ID) extends IruleApp {}
  case class IRrule(r:Irrule, i:Int) extends IruleApp {}
  case class ILrule(r:Ilrule, i:Int) extends IruleApp {}
  case class ICloseId(i:Int,j:Int) extends IruleApp {}
  case class ICut(f:Iformula) extends IruleApp {}

  sealed trait Ilrule {}
  case class IImplyL() extends Ilrule {}
  case class IAndL() extends Ilrule {}
  //@TODO: These are different from the KyX rule
  case class IEquivForwardL() extends Ilrule{}
  case class IEquivBackwardL() extends Ilrule{}

  sealed trait Irrule {}
  case class IImplyR() extends Irrule {}
  case class IAndR() extends Irrule {}
  // @TODO: One of these is not in KyX rules
  case class ICohideR() extends Irrule {}
  case class ICohideRR() extends Irrule {}
  case class ITrueR() extends Irrule {}
  case class IEquivR() extends Irrule {}
  case class ISkolem() extends Irrule {}

  sealed trait Iaxiom {}
  case class IAloopIter() extends Iaxiom {}
  case class IAI() extends Iaxiom {}
  case class IAtest() extends Iaxiom {}
  case class IAbox() extends Iaxiom {}
  case class IAchoice() extends Iaxiom {}
  case class IAK() extends Iaxiom {}
  case class IAV() extends Iaxiom {}
  case class IAassign() extends Iaxiom {}
  case class IAdassign() extends Iaxiom {}
  case class IAdConst() extends Iaxiom {}
  case class IAdPlus() extends Iaxiom {}
  case class IAdMult() extends Iaxiom {}
  case class IADW() extends Iaxiom {}
  case class IADE() extends Iaxiom {}
  case class IADC() extends Iaxiom {}
  case class IADS() extends Iaxiom {}
  case class IADIGeq() extends Iaxiom {}
  case class IADIGr() extends Iaxiom {}
  case class IADG() extends Iaxiom {}

  /* @TODO: Represent this type magic in Scala or in generated code as necessary
    SFunctions       :: "'a ⇀ ('a + 'c, 'c) trm"
    SPredicates      :: "'c ⇀ ('a + 'c, 'b, 'c) formula"
    SContexts        :: "'b ⇀ ('a, 'b + unit, 'c) formula"
    SPrograms        :: "'c ⇀ ('a, 'b, 'c) hp"
    SODEs            :: "'c ⇀ ('a, 'c) ODE"
  */
  case class Isubst(SFunctions:List[Itrm], SPredicates:List[Iformula], SContexts:List[Iformula], SPrograms:List[Ihp], SODEs:List[IODE])

  sealed trait Ipt {}
  case class IFOLRConstant(f:Iformula) extends Ipt {}
  case class IRuleApp (child:Ipt, ra:IruleApp,branch:Int) extends Ipt {}
  case class IAxRule(ar:IaxRule) extends Ipt {}
  case class IPrUSubst(child:Ipt, sub:Isubst) extends Ipt {}
  case class IAx(ax:Iaxiom) extends Ipt {}
  case class IFNC(child:Ipt, seq:Isequent,ra:IruleApp) extends Ipt {}
  case class IPro(child:Ipt,pro:Ipt) extends Ipt {}
  case class IStart(seq:Sequent) extends Ipt {}
  case class ISub(child:Ipt, sub:Ipt, branch:Int) extends Ipt {}


  private def detuple(t:Term):List[Term] = {
    t match {
      case Pair(l,r) => detuple(l) ++ detuple(r)
      case _ => List(t)
    }
  }

  private def padArgs(terms: List[Term], n: Int):List[Term] = {
    val length = terms.length
    List.tabulate(n)(i => if(i < length) {terms(i)} else Number(0))
  }

  def apply(f:Formula,m:IDMap):Iformula = {
    f match {
      case GreaterEqual(l,r) => IGeq(apply(l,m), apply(r,m))
      case Greater(l,r) =>
        val (al,ar) = (apply(l,m), apply(r,m))
        IAnd(IGeq(al,ar), INot(IGeq(ar,al)))
      case LessEqual(l,r) => IGeq(apply(r,m), apply(l,m))
      case Less(l,r) =>
        val (al,ar) = (apply(l,m), apply(r,m))
        IAnd(IGeq(ar,al), INot(IGeq(al,ar)))
      case Equal(l,r) =>
        val (al,ar) = (apply(l,m), apply(r,m))
        IAnd(IGeq(al,ar),IGeq(ar,al))
      case NotEqual(l,r) =>
        val (al,ar) = (apply(l,m), apply(r,m))
        INot(IAnd(IGeq(al,ar),IGeq(ar,al)))
      case PredOf(Function(name,_,_,_,_), arg) =>
        val args = detuple(arg)
        val allArgs = padArgs(args, m.pArity)
        IProp(m.varMap(name), allArgs.map(apply(_, m)))
      case PredicationalOf(Function(name,_,_,_,_),child) =>
        IInContext(m.conMap(name), apply(child,m))
      case UnitPredicational(name,_) => IInContext(m.conMap(name),IGeq(IConst(0),IConst(0)))
      case Not(f) => INot(apply(f,m))
      case And(l,r) => IAnd(apply(l,m),apply(r,m))
      case Or(l,r) => INot(IAnd(INot(apply(l,m)),INot(apply(r,m))))
      // @TODO: Double-negation eliminate, but need to do that in isabelle land too
      case Imply(l,r) => INot(IAnd(INot(apply(r,m)),INot(INot(apply(l,m)))))
      // @TODO: Double-negation eliminate, but need to do that in isabelle land too
      case Equiv(l,r) =>
        val (al,ar) = (apply(l,m), apply(r,m))
        INot(IAnd(INot(IAnd(al,ar)),INot(IAnd(INot(al),INot(ar)))))
      case Exists(vars,child) =>
        val x = vars.head
        IExists(m.varMap(x),apply(child,m))
      case Forall(vars,child) =>
        val x = vars.head
        INot(IExists(m.varMap(x),INot(apply(child,m))))
      case Diamond(a,p) => IDiamond(apply(a,m),apply(p,m))
      case Box(a,p) => INot(IDiamond(apply(a,m),INot(apply(p,m))))
      case True => IGeq(IConst(0),IConst(0))
      case False => IGeq(IConst(0),IConst(1))
      case _ : UnitFunctional => throw ConversionException("Functionals not supported yet")
    }
  }

  def apply(t:Term, m:IDMap):Itrm = {
    t match {
      case BaseVariable(x,ind,_) => IVar(m.varMap((x,ind)))
      case DifferentialSymbol(BaseVariable(x,ind,_)) => IDiffVar(m.varMap((x,ind)))
      case Number(n) =>
        if(n.isValidInt) {
          IConst(n.intValue())
        } else {
          throw ConversionException("Can't convert non-integer literal: " + n)
        }
      case FuncOf(Function(name,_,_,_,_), arg) =>
        val args = detuple(arg)
        val allArgs = padArgs(args, m.fArity)
        IFunction(name, allArgs.map(apply(_, m)))
      case Plus(l,r) => IPlus(apply(l,m),apply(r,m))
      case Minus(l,r) => IPlus(apply(l,m),ITimes(IConst(-1),apply(r,m)))
      case Neg(t) => ITimes(IConst(-1),apply(t,m))
      case Times(l,r) => ITimes(apply(l,m),apply(r,m))
      case Differential(t) => IDifferential(apply(t,m))
      case Divide(l,r) => throw ConversionException("Converter currently does not support conversion of divisions")
      case Power(l,r) => throw ConversionException("Converter currently does not support conversion of powers")
    }
  }
  
  def apply(o:DifferentialProgram, m:IDMap):IODE = {
    o match {
      case AtomicODE(DifferentialSymbol(BaseVariable(x,ind,_)),e) =>
        IOSing(m.varMap(x,ind), apply(e,m))
      case DifferentialProduct(l,r) => IOProd(apply(l,m),apply(r,m))
      case DifferentialProgramConst(c,_) => IOVar(m.varMap(c))
    }
  }

  def apply(hp:Program, m:IDMap):Ihp = {
    hp match {
      case ProgramConst(name) => IPvar(m.varMap())
      case Assign(BaseVariable(x,ind,_),e) => IAssign(m.varMap((x,ind)),apply(e,m))
      case Assign(DifferentialSymbol(BaseVariable(x,ind,_)),e) => IDiffAssign(m.varMap((x,ind)),apply(e,m))
      case Test(p) => ITest(apply(p,m))
      case ODESystem(ode,con) => IEvolveODE(apply(ode,m),apply(con,m))
      case Choice(a,b) => IChoice(apply(a,m),apply(b,m))
      case Compose(a,b) => ISequence(apply(a,m),apply(b,m))
      case Loop(a) => ILoop(apply(a,m))
      case _ : AssignAny => throw ConversionException("Nondeterministic assignment not supported yet")
    }
  }

  def apply(seq:Sequent, m:IDMap):Isequent = {
    (seq.ante.map(apply(_,m)).toList,seq.succ.map(apply(_,m)).toList)
  }

  def apply(pr:Provable, m:IDMap):Irule = {
    (pr.subgoals.map(apply(_,m)).toList, apply(pr.conclusion,m))
  }
}
