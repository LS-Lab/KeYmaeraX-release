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

  val m:IDMap = ???

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

  object IaxRule {
    def apply(n:String):IaxRule = {
      n match {
        case "CT" => ICT()
        case "CQ" => ICQ()
        case "CE" => ICE()
        case "G" => IG()
        case _ =>
          throw ConversionException("Unrecognized axiomatic rule: " + n)
      }
    }
  }
  sealed trait IaxRule {}
  case class ICT() extends IaxRule {}
  case class ICQ() extends IaxRule {}
  case class ICE() extends IaxRule {}
  case class IG() extends IaxRule {}

  //object IruleApp {}
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

  object Iaxiom {
    def apply(n:String):Iaxiom = {
      n match {
          //@TODO: These names are all wrong; update them
        case "[*]" => IAloopIter()
        case "I induction" => IAI()
        case "[?] test" => IAtest()
        case "[] box" => IAbox()
        case "[++] choice" => IAchoice()
        case "K modal modus ponens" => IAK()
        case "V vacuous" => IAV()
        case "[:=] assign" => IAassign()
        //@TODO: These are probably collapsed on kyx side, need to re-split based on context
        case "[:='] assign" => IAdassign()
        case "(c())'" => IAdConst()
        case "(+)'" => IAdPlus()
        case "(*)'" => IAdMult()
        case "DW differential weakening" => IADW()
        case "DE differential effect" => IADE()
        case "DC differential cut" => IADC()
        case "DS differential solve" => IADS()
        //@TODO: specialize based on shape of differential formula
        case "DI differential invariant" => IADIGeq() // e.g. IADIGr()
        case "G goedel" => IADG()
      }
    }
  }

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
  case class IStart(seq:Isequent) extends Ipt {}
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

  def apply(name:String,seqPos:Seq[SeqPos],expArgs:Seq[Expression]):IruleApp = {
    (name, seqPos.toList, expArgs.toList) match {
      // @TODO: Get the names for everything
      case ("uniform renaming", _, BaseVariable(n1,ind1,_) :: BaseVariable(n2,ind2,_) :: Nil) =>
        IURename(m.varMap((n1,ind1)),m.varMap((n2,ind2)))
      case ("bound renaming", _, BaseVariable(n1,ind1,_) :: BaseVariable(n2,ind2,_) :: Nil) =>
        IBRename(m.varMap((n1,ind1)),m.varMap((n2,ind2)))
      case ("closeId", (a:AntePos)::(s:SeqPos)::Nil, _) => ICloseId(a.getIndex,s.getIndex)
      case ("cut", _, (f:Formula) :: Nil) => ICut(apply(f))
      case ("Imply Left", (a:AntePos)::Nil, _) => ILrule(IImplyL(),a.getIndex)
      case ("And Left", (a:AntePos)::Nil, _) => ILrule(IAndL(),a.getIndex)
      case ("Equiv Left1", (a:AntePos)::Nil, _) => ILrule(IEquivForwardL(),a.getIndex)
      case ("Equiv Left2", (a:AntePos)::Nil, _) => ILrule(IEquivBackwardL(),a.getIndex)

      case ("Imply Right", (s:SuccPos)::Nil, _) => IRrule(IImplyR(), s.getIndex)
      case ("Cohide Right", (s:SuccPos)::Nil, _) => IRrule(ICohideR(), s.getIndex)
      case ("Cohide Right 2", (s:SuccPos)::Nil, _) => IRrule(ICohideRR(), s.getIndex)
      case ("closeTrue", (s:SuccPos)::Nil, _) => IRrule(ITrueR(), s.getIndex)
      case ("Equiv Right", (s:SuccPos)::Nil, _) => IRrule(IEquivR(), s.getIndex)
      case ("All Right", (s:SuccPos)::Nil, _) => IRrule(ISkolem(), s.getIndex)
      case ("And Right", (s:SuccPos)::Nil, _) => IRrule(IAndR(), s.getIndex)
      case _ =>
        throw ConversionException("Unrecognized non-axiomatic rule: " + name)
    }
  }

  def apply(sub:USubst):Isubst = {
    ???
  }

  def apply(pt:ProofTerm):Ipt = {
    pt match {
      case FOLRConstant(f) => IFOLRConstant(apply(f))
      case RuleTerm(name) => IAxRule(IaxRule(name))
      case AxiomTerm(name) => IAx(Iaxiom(name))
      case RuleApplication(child, name, sub, seqPos, expArgs) =>
        IRuleApp(apply(child), apply(name,seqPos,expArgs),sub)
      case UsubstProvableTerm(child,subst) =>
        IPrUSubst(apply(child), apply(subst))
      case ForwardNewConsequenceTerm(child,con,r) =>
        IFNC(apply(child),apply(con),apply(r.name, Seq(AntePos(0)), Seq()))
      case ProlongationTerm(sub,pro) =>
        IPro(apply(sub),apply(pro))
      case Sub(child,sub,idx)=> ISub(apply(child),apply(sub),idx)
      case StartProof(seq) => IStart(apply(seq))
      case NoProof () => throw ConversionException("Encountered unproven subproof")
    }
  }

  def apply(f:Formula):Iformula = {
    f match {
      case GreaterEqual(l,r) => IGeq(apply(l), apply(r))
      case Greater(l,r) =>
        val (al,ar) = (apply(l), apply(r))
        IAnd(IGeq(al,ar), INot(IGeq(ar,al)))
      case LessEqual(l,r) => IGeq(apply(r), apply(l))
      case Less(l,r) =>
        val (al,ar) = (apply(l), apply(r))
        IAnd(IGeq(ar,al), INot(IGeq(al,ar)))
      case Equal(l,r) =>
        val (al,ar) = (apply(l), apply(r))
        IAnd(IGeq(al,ar),IGeq(ar,al))
      case NotEqual(l,r) =>
        val (al,ar) = (apply(l), apply(r))
        INot(IAnd(IGeq(al,ar),IGeq(ar,al)))
      case PredOf(Function(name,_,_,_,_), arg) =>
        val args = detuple(arg)
        val allArgs = padArgs(args, m.pArity)
        IProp(m.varMap((name,None)), allArgs.map(apply))
      case PredicationalOf(Function(name,_,_,_,_),child) =>
        IInContext(m.conMap(name), apply(child))
      case UnitPredicational(name,_) => IInContext(m.conMap(name),IGeq(IConst(0),IConst(0)))
      case Not(f) => INot(apply(f))
      case And(l,r) => IAnd(apply(l),apply(r))
      case Or(l,r) => INot(IAnd(INot(apply(l)),INot(apply(r))))
      // @TODO: Double-negation eliminate, but need to do that in isabelle land too
      case Imply(l,r) => INot(IAnd(INot(apply(r)),INot(INot(apply(l)))))
      // @TODO: Double-negation eliminate, but need to do that in isabelle land too
      case Equiv(l,r) =>
        val (al,ar) = (apply(l), apply(r))
        INot(IAnd(INot(IAnd(al,ar)),INot(IAnd(INot(al),INot(ar)))))
      case Exists(vars,child) =>
        val BaseVariable(x,ind,_) = vars.head
        IExists(m.varMap((x,ind)),apply(child))
      case Forall(vars,child) =>
        val BaseVariable(x,ind,_) = vars.head
        INot(IExists(m.varMap((x,ind)),INot(apply(child))))
      case Diamond(a,p) => IDiamond(apply(a),apply(p))
      case Box(a,p) => INot(IDiamond(apply(a),INot(apply(p))))
      case True => IGeq(IConst(0),IConst(0))
      case False => IGeq(IConst(0),IConst(1))
      case _ : UnitFunctional => throw ConversionException("Functionals not supported yet")
    }
  }

  def apply(t:Term):Itrm = {
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
        IFunction(name, allArgs.map(apply(_)))
      case Plus(l,r) => IPlus(apply(l),apply(r))
      case Minus(l,r) => IPlus(apply(l),ITimes(IConst(-1),apply(r)))
      case Neg(t) => ITimes(IConst(-1),apply(t))
      case Times(l,r) => ITimes(apply(l),apply(r))
      case Differential(t) => IDifferential(apply(t))
      case Divide(l,r) => throw ConversionException("Converter currently does not support conversion of divisions")
      case Power(l,r) => throw ConversionException("Converter currently does not support conversion of powers")
    }
  }

  def apply(o:DifferentialProgram):IODE = {
    o match {
      case AtomicODE(DifferentialSymbol(BaseVariable(x,ind,_)),e) =>
        IOSing(m.varMap(x,ind), apply(e))
      case DifferentialProduct(l,r) => IOProd(apply(l),apply(r))
      case DifferentialProgramConst(c,_) => IOVar(m.varMap((c,None)))
    }
  }

  def apply(hp:Program):Ihp = {
    hp match {
      case ProgramConst(name) => IPvar(m.varMap((name,None)))
      case Assign(BaseVariable(x,ind,_),e) => IAssign(m.varMap((x,ind)),apply(e))
      case Assign(DifferentialSymbol(BaseVariable(x,ind,_)),e) => IDiffAssign(m.varMap((x,ind)),apply(e))
      case Test(p) => ITest(apply(p))
      case ODESystem(ode,con) => IEvolveODE(apply(ode),apply(con))
      case Choice(a,b) => IChoice(apply(a),apply(b))
      case Compose(a,b) => ISequence(apply(a),apply(b))
      case Loop(a) => ILoop(apply(a))
      case _ : AssignAny => throw ConversionException("Nondeterministic assignment not supported yet")
    }
  }

  def apply(seq:Sequent):Isequent = {
    (seq.ante.map(apply(_)).toList,seq.succ.map(apply(_)).toList)
  }

  def apply(pr:Provable):Irule = {
    (pr.subgoals.map(apply(_)).toList, apply(pr.conclusion))
  }
}
