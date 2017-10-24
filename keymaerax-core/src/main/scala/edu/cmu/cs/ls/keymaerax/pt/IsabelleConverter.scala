package edu.cmu.cs.ls.keymaerax.pt

import java.io.{BufferedWriter, FileWriter, Writer}

import edu.cmu.cs.ls.keymaerax.bellerophon.PosInExpr
import edu.cmu.cs.ls.keymaerax.btactics.ExpressionTraversal.{ExpressionTraversalFunction, StopTraversal}
import edu.cmu.cs.ls.keymaerax.btactics.{AxiomInfo, DerivedRuleInfo, ExpressionTraversal}
import edu.cmu.cs.ls.keymaerax.core.{DotFormula, _}
import edu.cmu.cs.ls.keymaerax.pt.IsabelleConverter._

/**
  * Convert proof terms to sublanguage + syntax used by Isabelle formalization
  * Created by bbohrer on 10/19/17.
  * @see [[ProofChecker]]
  * @author Brandon Bohrer
  */
object IsabelleConverter {
  sealed abstract class ID {}
  case class IDEnum(x:String) extends ID
  case class IDUnit() extends ID
  case class IDLeft(child:ID) extends ID
  case class IDRight(child:ID) extends ID

  type Isequent = (List[Iformula],List[Iformula])
  type Irule = (List[Isequent],Isequent)

  // Keep this in sync with the code generation in Isabelle proof. If the number of IDs is too small then we can't export
  // the proof term, if it's too big then proof checking gets progressively slower
  val ISABELLE_IDS:Seq[String] = Seq("i1","i2","i3","i4","i5","i6","i7","i8","i9","i10")

  def detuple(t:Term):List[Term] = {
    t match {
      case Pair(l,r) => detuple(l) ++ detuple(r)
      case Nothing => List()
      case _ => List(t)
    }
  }
}

object IDMap {
  val axiomIds = IDMap(
    // next Id for vars
    Map((("x_",None), "i1"), (("y_",None), "i2"), (("v",None), "i1"), (("t_",None),"i2"), (("s_",None),"i3")),
    Map(("f","i1"), ("g","i2"),("s","i1"),("t","i2"),("ctxT","i3"), ("c","i1")),
    Map(("p","i1"),("q","i2"),("ctxF","i1")),
    //@TODO: Left is argumented, right is unit, double-check please
    Map((Left("p_"),"i1"),(Left("q_"),"i2"),(Right("P"),"i1"),(Left("J"),"i1")),
    Map(("a","i1"),("b","i2"),("a_","i1"),("b_","i2")),
    Map(("c","i1"),("d","i2"),("c","i3"),("a_","i1"), ("a","i1")),
    ISABELLE_IDS.length,
    ISABELLE_IDS.length,
    3, // next Id for var
    3,// next Id for fun
    2,// next Id for pred
    2,// next Id for con
    2,// next Id for prog
    3// next Id for ode
  )

  val empty:IDMap = axiomIds

  def ofSequent(seq:Sequent,acc:IDMap):IDMap = {
    seq.succ.foldLeft(seq.ante.foldLeft(acc)((acc,f) => ofFormula(f,acc)))((acc,f) => ofFormula(f,acc))
  }

  def ofProvable(pr:Provable,acc:IDMap):IDMap = {
    pr.subgoals.foldLeft(ofSequent(pr.conclusion,acc))((acc,seq) => ofSequent(seq,acc))
  }

  private class Trans(var pos:IDMap) extends ExpressionTraversalFunction() {

      override def preP(p: PosInExpr, e: Program): Either[Option[StopTraversal], Program] = {
        e match {
          case ProgramConst(name) => pos = pos.addProg(name)
          case DifferentialProgramConst(name,_) => pos = pos.addDiffProg(name)
          case _ =>
        }
        Left(None)
      }

      override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = {
        e match {
          case FuncOf(Function(name,_,_,_,_),arg) => pos = pos.addFunc(name,IsabelleConverter.detuple(arg).length)
          case BaseVariable(name,ind,_) => pos = pos.addVar(name,ind)
          case DifferentialSymbol(BaseVariable(name,ind,_)) => pos.addVar(name,ind)
          case _ =>
        }
        Left(None)
      }

      override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = {
        e match {
          case PredOf(Function(name, _, _, _, _), arg) => pos = pos.addPred(name,IsabelleConverter.detuple(arg).length)
          case PredicationalOf(Function(name, _, _, _, _), arg) => pos.addCon(name)
          case UnitPredicational(name, _) => pos.addUnitPred(name)
          case _ =>
        }
        Left(None)
      }
    }

  def ofFormula(f:Formula,acc:IDMap):IDMap = {
    val tr = new Trans(acc)
    ExpressionTraversal.traverse(tr, f)
    tr.pos
  }

  def ofTerm(f:Term,acc:IDMap):IDMap = {
    val tr = new Trans(acc)
    ExpressionTraversal.traverse(tr, f)
    tr.pos
  }

  def ofProgram(f:Program,acc:IDMap):IDMap = {
    val tr = new Trans(acc)
    ExpressionTraversal.traverse(tr, f)
    tr.pos
  }

  def ofExp(e:Expression,acc:IDMap):IDMap = {
    e match {
      case t:Term => ofTerm(t,acc)
      case p:Program => ofProgram(p,acc)
      case f:Formula => ofFormula(f,acc)
    }
  }

  def ofFunc(name:String, arg:Term, repl:Expression, acc:IDMap):IDMap = {
    val arity = IsabelleConverter.detuple(arg).length
    ofExp(repl,ofExp(arg,acc)).addFunc(name,arity)
  }

  def ofPred(name:String, arg:Term, repl:Expression, acc:IDMap):IDMap = {
    val arity = IsabelleConverter.detuple(arg).length
    ofExp(repl,ofExp(arg,acc)).addPred(name,arity)
  }

  def ofUnitPred(name:String,  repl:Expression, acc:IDMap):IDMap = {
    ofExp(repl,acc).addUnitPred(name)
  }

  def ofCon(name:String, arg:Formula, repl:Expression, acc:IDMap):IDMap = {
    ofExp(repl,ofExp(arg,acc)).addCon(name)
  }

  def ofProg(name:String, repl:Expression, acc:IDMap):IDMap = {
    ofExp(repl,acc).addProg(name)
  }

  def ofDiffConst(name:String, repl:Expression, acc:IDMap):IDMap = {
    ofExp(repl,acc).addDiffProg(name)
  }

  def ofSubst(us:USubst,acc:IDMap):IDMap = {
    us.subsDefsInput.map({case SubstitutionPair(what,repl) => (what,repl)}).foldLeft(acc){
      case (acc,(FuncOf(Function(name,_,_,_,_),arg),repl)) => ofFunc(name,arg,repl,acc)
      case (acc,(PredOf(Function(name,_,_,_,_),arg),repl)) => ofPred(name,arg,repl,acc)
      case (acc,(PredicationalOf(Function(name,_,_,_,_),arg),repl)) => ofCon(name,arg,repl,acc)
      case (acc,(UnitPredicational(name,arg),repl)) => ofUnitPred(name,repl,acc)
      case (acc,(ProgramConst(name),repl)) => ofProg(name,repl,acc)
      // Isabelle formalization doesn't have games, so collapse it all to systems anyway
      case (acc,(SystemConst(name),repl)) => ofProg(name,repl,acc)
      case (acc,(DifferentialProgramConst(name,_),repl)) => ofDiffConst(name,repl,acc)
        // TODO: Isabelle formalization needs unitfunctional support
      case (acc,(UnitFunctional(name,_,_),repl)) =>ofFunc(name,Number(0),repl,acc)
      case (x,y) => {
        println(x,y)
        val 2 = 1 + 1
        ???
      }
    }
  }

  def ofProofTerm(pt:ProofTerm, acc:IDMap):IDMap = {
    pt match {
      case FOLRConstant(f) => ofFormula(f,acc)
      case RuleApplication(child, ruleName, subgoal, sequentPositions, expArgs) =>
        expArgs.foldLeft(ofProofTerm(child,acc))((acc,exp) => ofExp(exp,acc))
      case RuleTerm(name: String) =>
        val r : Provable =
          try { Provable.rules(name) }
          catch {
            case _ : NoSuchElementException =>
              DerivedRuleInfo.allInfo.find(info => info.codeName == name).get.provable.underlyingProvable
          }
        ofProvable(r,acc)
      case UsubstProvableTerm(child: ProofTerm, substitution: USubst) =>
        ofSubst(substitution,ofProofTerm(child,acc))
      case AxiomTerm(name: String) => ofFormula(AxiomInfo(name).formula,acc)
      case ForwardNewConsequenceTerm(child: ProofTerm, newConsequence: Sequent, rule: Rule) =>
        ofSequent(newConsequence,ofProofTerm(child,acc))
      case ProlongationTerm(child: ProofTerm, prolongation: ProofTerm) =>
        ofProofTerm(child,ofProofTerm(prolongation,acc))
      case StartProof(phi:Sequent) => ofSequent(phi,acc)
      case Sub(child:ProofTerm, sub:ProofTerm, idx: Int) =>
        ofProofTerm(child,ofProofTerm(sub,acc))
      case NoProof() => throw ConversionException("Found subterm with NoProof()")
    }
  }
}

// @TODO: use detailed maps correctly throughout rest of ocode
// @TODO: Minimize size of types used
// @TODO: automatically consider both arity and number of symbols for determining type size
case class IDMap(varMap:Map[(String,Option[Int]),String],
                 funMap:Map[String,String],
                 predMap:Map[String,String],
                 conMap:Map[Either[String,String],String],
                 progMap:Map[String,String],
                 odeMap:Map[String,String],
                 fArity:Int,
                 pArity:Int,
                 maxVar:Int,
                 maxFun:Int,
                 maxPred:Int,
                 maxCon:Int,
                 maxProg:Int,
                 maxOde:Int) {
  def addVar(name:String, ind:Option[Int]):IDMap = {
    if(varMap.contains((name,ind))) { this }
    else if(varMap.size < ISABELLE_IDS.size) {
      IDMap(varMap.+(((name,ind),ISABELLE_IDS(maxVar))),funMap,predMap,conMap,progMap,odeMap,fArity,pArity,maxVar+1,maxFun,maxPred,maxCon,maxProg,maxOde)
    } else {
      throw ConversionException("Need more Isabelle identifiers, not enough to convert variable identifier: " + name)
    }
  }

  def addProg(name:String):IDMap = {
    if(progMap.contains(name)) { this }
    else if(progMap.size < ISABELLE_IDS.size) {
      IDMap(varMap,funMap,predMap,conMap,progMap.+((name,ISABELLE_IDS(maxProg))),odeMap,fArity,pArity,maxVar,maxFun,maxPred,maxCon,maxProg+1,maxOde)
    } else {
      throw ConversionException("Need more Isabelle identifiers, not enough to convert program identifier: " + name)
    }
  }

  def addDiffProg(name:String):IDMap = {
    if(odeMap.contains(name)) { this }
    else if(odeMap.size < ISABELLE_IDS.size) {
      IDMap(varMap,funMap,predMap,conMap,progMap,odeMap.+((name,ISABELLE_IDS(maxOde))),fArity,pArity,maxVar,maxFun,maxPred,maxCon,maxProg,maxOde+1)
    } else {
      throw ConversionException("Need more Isabelle identifiers, not enough to convert differential program identifier: " + name)
    }
  }

  def addUnitPred(name:String):IDMap = {
    if(conMap.contains(Right(name))) { this }
    else if(conMap.size < ISABELLE_IDS.size) {
      IDMap(varMap,funMap,predMap,conMap.+((Right(name),ISABELLE_IDS(maxCon))),progMap,odeMap,fArity,pArity,maxVar,maxFun,maxPred,maxCon+1,maxProg,maxOde)
    } else {
      throw ConversionException("Need more Isabelle identifiers, not enough to convert nullary predicational identifier: " + name)
    }
  }

  def addCon(name:String):IDMap = {
    if(conMap.contains(Left(name))) { this }
    else if(conMap.size < ISABELLE_IDS.size) {
      IDMap(varMap,funMap,predMap,conMap.+((Left(name),ISABELLE_IDS(maxCon))),progMap,odeMap,fArity,pArity,maxVar,maxFun,maxPred,maxCon+1,maxProg,maxOde)
    } else {
      throw ConversionException("Need more Isabelle identifiers, not enough to convert unary predicational identifier: " + name)
    }
  }

  def addFunc(name:String, arity:Int):IDMap = {
    if(funMap.contains(name)) {
      this
    } else if(funMap.size < ISABELLE_IDS.size) {
      IDMap(varMap,funMap.+((name,ISABELLE_IDS(maxFun))),predMap,conMap,progMap,odeMap,fArity.max(arity),pArity,maxVar,maxFun+1,maxPred,maxCon,maxProg,maxOde)
    } else {
      throw ConversionException("Need more Isabelle identifiers, not enough to convert function identifier: " + name)
    }
  }

  def addPred(name:String, arity:Int):IDMap = {
    if(predMap.contains(name)) {
      this
    } else if(predMap.size < ISABELLE_IDS.size) {
      IDMap(varMap,funMap,predMap.+((name,ISABELLE_IDS(maxPred))),conMap,progMap,odeMap,fArity,pArity.max(arity),maxVar,maxFun,maxPred+1,maxCon,maxProg,maxOde)
    } else {
      throw ConversionException("Need more Isabelle identifiers, not enough to convert predicate identifier: " + name)
    }
  }
}
//case class IRat(num:Number,den:Number)

case class ConversionException(msg:String) extends Exception {
  override def toString:String = {"ConversionException: " + msg}
}

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
      case "CQ equation congruence" => ICQ()
      case "CE congruence" => ICE()
      case "G" => IG()
      case "monb" => Imonb()
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
case class Imonb() extends IaxRule {}

//object IruleApp {}
sealed trait IruleApp {}
case class IURename(what:ID,repl:ID) extends IruleApp {}
case class IBRename(what:ID,repl:ID) extends IruleApp {}
case class IRrule(r:Irrule, i:Int) extends IruleApp {}
case class ILrule(r:Ilrule, i:Int) extends IruleApp {}
case class ICloseId(i:Int,j:Int) extends IruleApp {}
case class ICohide2(i:Int,j:Int) extends IruleApp {}
case class ICut(f:Iformula) extends IruleApp {}

sealed trait Ilrule {}
case class IHideL() extends Ilrule {}
case class IImplyL() extends Ilrule {}
case class IAndL() extends Ilrule {}
//@TODO: These are different from the KyX rule
case class IEquivForwardL() extends Ilrule{}
case class IEquivBackwardL() extends Ilrule{}

sealed trait Irrule {}
case class ICutRight(f:Iformula)   extends Irrule {}
case class IImplyR() extends Irrule {}
case class IAndR() extends Irrule {}
case class IHideR() extends Irrule {}
// @TODO: CohideRR
case class ICohideR() extends Irrule {}
case class ICohideRR() extends Irrule {}
case class ITrueR() extends Irrule {}
case class IEquivR() extends Irrule {}
case class IEquivifyR() extends Irrule {}
case class ICommuteEquivR() extends Irrule {}
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
      case "[':=] differential assign" => IAdassign()
      case "x' derive var" => IAdvar()
      case "c()' derive constant fn" => IAdConst()
      case "(+)'" => IAdPlus()
      case "(*)'" => IAdMult()
      case "DW differential weakening" => IADW()
      case "DE differential effect" => IADE()
      case "DC differential cut" => IADC()
      case "DS differential solve" => IADS()
      //@TODO: specialize based on shape of differential formula
      case "DI differential invariant" => IADIGeq() // e.g. IADIGr()
      case "G goedel" => IADG()
      case "<-> reflexive" => IAEquivReflexive()
      case "DE differential effect (system)" => IADiffEffectSys()
      case ">=' derive >=" => {
        val 2 = 1 + 1
        throw ConversionException("Needed to convert proof using DifferentialFormula to one that doesn't, but didn't")
      }
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
case class IAdvar() extends Iaxiom {}

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
case class IAEquivReflexive() extends Iaxiom {}
case class IADiffEffectSys() extends Iaxiom {}


/* @TODO: Represent this type magic in Scala or in generated code as necessary
  SFunctions       :: "'a ⇀ ('a + 'c, 'c) trm"
  SPredicates      :: "'c ⇀ ('a + 'c, 'b, 'c) formula"
  SContexts        :: "'b ⇀ ('a, 'b + unit, 'c) formula"
  SPrograms        :: "'c ⇀ ('a, 'b, 'c) hp"
  SODEs            :: "'c ⇀ ('a, 'c) ODE"
*/
case class Isubst(SFunctions:List[Option[Itrm]], SPredicates:List[Option[Iformula]], SContexts:List[Option[Iformula]], SPrograms:List[Option[Ihp]], SODEs:List[Option[IODE]])

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

class IsabelleConverter(pt:ProofTerm) {


  val m:IDMap = IDMap.ofProofTerm(pt, IDMap.empty)



  private def padArgs(terms: List[Term], n: Int):List[Term] = {
    val length = terms.length
    List.tabulate(n)(i => if(i < length) {terms(i)} else Number(0))
  }

  def apply(name:String,seqPos:Seq[SeqPos],expArgs:Seq[Expression]):IruleApp = {
    (name, seqPos.toList, expArgs.toList) match {
      // @TODO: Get the names for everything
      case ("Uniform Renaming", _, BaseVariable(n1,ind1,_) :: BaseVariable(n2,ind2,_) :: Nil) =>
        IURename(IDEnum(m.varMap((n1,ind1))),IDEnum(m.varMap((n2,ind2))))
      case ("Bound Renaming", _, BaseVariable(n1,ind1,_) :: BaseVariable(n2,ind2,_) :: Nil) =>
        IBRename(IDEnum(m.varMap((n1,ind1))),IDEnum(m.varMap((n2,ind2))))
      case ("Close", (a:AntePos)::(s:SeqPos)::Nil, _) => ICloseId(a.getIndex,s.getIndex)
      case ("cut", _, (f:Formula) :: Nil) => ICut(apply(f))
      case ("CoHide2", (a:AntePos) :: (s:SuccPos) :: Nil, _) => ICohide2(a.getIndex,s.getIndex)


      case ("Imply Left", (a:AntePos)::Nil, _) => ILrule(IImplyL(),a.getIndex)
      case ("And Left", (a:AntePos)::Nil, _) => ILrule(IAndL(),a.getIndex)
      case ("Equiv Left1", (a:AntePos)::Nil, _) => ILrule(IEquivForwardL(),a.getIndex)
      case ("Equiv Left2", (a:AntePos)::Nil, _) => ILrule(IEquivBackwardL(),a.getIndex)
      case ("HideLeft", (a:AntePos)::Nil, _) => ILrule(IHideL(),a.getIndex)

      case ("cut Right", (s:SuccPos) :: Nil, (f:Formula) :: Nil) => IRrule(ICutRight(apply(f)), s.getIndex)
      case ("Imply Right", (s:SuccPos)::Nil, _) => IRrule(IImplyR(), s.getIndex)
      case ("CoHideRight", (s:SuccPos)::Nil, _) => IRrule(ICohideR(), s.getIndex)
      case ("Cohide Right 2", (s:SuccPos)::Nil, _) => IRrule(ICohideRR(), s.getIndex)
      case ("closeTrue", (s:SuccPos)::Nil, _) => IRrule(ITrueR(), s.getIndex)
      case ("Equiv Right", (s:SuccPos)::Nil, _) => IRrule(IEquivR(), s.getIndex)
      case ("EquivifyRight", (s:SuccPos)::Nil, _) => IRrule(IEquivifyR(), s.getIndex)
      case ("CommuteEquivRight", (s:SuccPos)::Nil, _) => IRrule(ICommuteEquivR(), s.getIndex)
      case ("All Right", (s:SuccPos)::Nil, _) => IRrule(ISkolem(), s.getIndex)
      case ("And Right", (s:SuccPos)::Nil, _) => IRrule(IAndR(), s.getIndex)
      case ("HideRight", (s:SuccPos)::Nil, _) => IRrule(IHideR(), s.getIndex)
      case _ =>
        throw ConversionException("Unrecognized non-axiomatic rule: " + name + ","  + seqPos.toList +", " + expArgs.toList)
    }
  }

  private def sortSubs[T](seq:Seq[(Expression,Expression)], f:(Expression => String), g:(Expression => T)):List[T] = {
    val withKeys = seq.map({case (ns,e) => (ns,e,f(ns))})
    withKeys.sortBy({case (ns,e,key) => key}).map{case (_,e,_) => e}.map(g).toList
  }

  // @TODO: Surely has type issues
  // @TODO: Have to ensure identifier renaming preserves choice of reserved identifiers in axioms/axiomatic rules
  def apply(sub:USubst):Isubst = {
    def extendSub[T](l:List[T]):List[Option[T]] = {
      val somes = l.map(Some(_))
      val numSomes = somes.length
      List.tabulate(ISABELLE_IDS.length)({case i => if(i < numSomes) {somes(i)} else None})
    }
    val pairs = sub.subsDefsInput.map({case SubstitutionPair(what,repl) => (what,repl)})
    val (fun, t1) = pairs.partition({case (_: FuncOf, _) => true case _ => false})
    val (pred, t2) = t1.partition({case (_: PredOf, _) => true case _ => false})
    val (con, t3) = t2.partition({case (_: PredicationalOf, _) => true case (_: UnitPredicational, _) => true case _ => false})
    val (prog, t4) = t3.partition({case (_: ProgramConst, _) => true case (_:SystemConst, _) => true case _ => false})
    val (ode, t5) = t4.partition({case (_: DifferentialProgramConst, _) => true case _ => false})
    //@TODO: Need unitfuns in isabelles
    val (unitFun, t6) = t5.partition({case (_: UnitFunctional, _) => true case _ => false})
    assert(t6.isEmpty, "Forgot to handle symbols in substitution: " + t6)
    // @TODO: Need to insert lefts/rights in ids on RHS
    Isubst(
      extendSub(sortSubs(fun, {case FuncOf(Function(name,_,_,_,_),_) => m.funMap(name)}, {case e:Term => apply(e)})),
      extendSub(sortSubs(pred, {case PredOf(Function(name,_,_,_,_),_) => m.predMap(name)}, {case e:Formula => apply(e)})),
      extendSub(sortSubs(con, {case PredicationalOf(Function(name,_,_,_,_),_) => m.conMap(Left(name)) case UnitPredicational(name, _) => m.conMap(Right(name))}, {case e:Formula => apply(e)})),
      //@todo: need program map and stuff
      extendSub(sortSubs(prog, {case ProgramConst(name) =>  m.progMap(name) case SystemConst(name) =>  m.progMap(name)}, {case e:Program => apply(e)})),
      extendSub(sortSubs(ode, {case DifferentialProgramConst(name,_) =>  m.odeMap(name)}, {case e:DifferentialProgram => apply(e)})))
  }

  private def rulePoses(r:Rule):List[SeqPos] = {
   r match {
     case pr:PositionRule => List(pr.pos)
     case Close(a,s) => List(a,s)
     case CoHide2(a,s) => List(a,s)
     case CutLeft(f,a) => List(a)
     case CutRight(f,s) => List(s)
     case ExchangeRightRule(s1,s2) => List(s1,s2)
     case ExchangeLeftRule(a1,a2) => List(a1,a2)
     case _ => List()
   }
  }

  private def ruleExps(r:Rule):List[Expression] = {
    r match {
      case Cut(f) => List(f)
      case CutLeft(f,a) => List(f)
      case CutRight(f,s) => List(f)
      case UniformRenaming(what,repl) => List(what,repl)
      case BoundRenaming(what,repl,pos) => List(what,repl)
      case _ => List()
    }
  }

  private def isDiffFormulaChase(pt:ProofTerm):Boolean = {
    pt match {
      case Sub(Sub(RuleApplication(StartProof(reflFml),cutRightName/*"cut Right"*/,_,_,_),
           ForwardNewConsequenceTerm(
           ForwardNewConsequenceTerm(ProlongationTerm(UsubstProvableTerm(AxiomTerm(geqPrimeName/*">=' derive >="*/),_),
                                                      UsubstProvableTerm(RuleTerm(ceName/*"CE Equiv"*/),_)),_,_:EquivifyRight),_,_:CoHideRight),_),
      UsubstProvableTerm(AxiomTerm(equivReflName),_),_)
      =>
        val 2 = 1 + 1
        true
      case Sub(Sub(RuleApplication(StartProof(reflFml), cutRightName /*"cut Right"*/ , _, _, _),
      ForwardNewConsequenceTerm(
      ForwardNewConsequenceTerm(ProlongationTerm(UsubstProvableTerm(AxiomTerm(geqPrimeName /*">=' derive >="*/), _),
      UsubstProvableTerm(RuleTerm(ceName /*"CE Equiv"*/), _)), _, _), _, _), _),
      UsubstProvableTerm(AxiomTerm(equivReflName), equivReflSubst), where) =>
        println("Did we find a new case for diff formula chase?"+ pt)
        false
      case _ => false
    }
  }


  // @TODO: Add translation for the DI part itself too
  // case IADIGeq() => b0("ADIGeq")
  private def translateDiffFormulaChase(pt:ProofTerm):Ipt = {
    pt match {
      case Sub(Sub(RuleApplication(StartProof(reflFml), "cut Right", _, _, _),
      ForwardNewConsequenceTerm(
      ForwardNewConsequenceTerm(ProlongationTerm(UsubstProvableTerm(AxiomTerm(">=' derive >="), _),
      UsubstProvableTerm(RuleTerm("CE congruence"), _)), _, _: EquivifyRight), _, _: CoHideRight), _),
      UsubstProvableTerm(AxiomTerm("<-> reflexive"), equivReflSubst), where) =>
        //reflFml = {Sequent@3669} "  ==>  (v)'>=(0)'<->(v>=0)'"
        //equivReflSubst = {USubst@3670} "USubst{(p_()~>(v>=0)')}"
        /*
        cut Right
        CoHideRight
        EquivifyRight
        >=' derive >=
        CE congruence
        <-> reflexive
         */
        println(reflFml+"\n\n\n"+equivReflSubst)
        ISub(IStart(apply(reflFml)),IPrUSubst(IAx(Iaxiom("<-> reflexive")),apply(equivReflSubst)), where)
    }
  }

  def apply(pt:ProofTerm):Ipt = {
    if(isDiffFormulaChase(pt)) {
      translateDiffFormulaChase(pt)
    } else {
      pt match {
        case FOLRConstant(f) => IFOLRConstant(apply(f))
        case RuleTerm(name) => IAxRule(IaxRule(name))
        case AxiomTerm(name) => IAx(Iaxiom(name))
        case RuleApplication(child, name, sub, seqPos, expArgs) =>
          IRuleApp(apply(child), apply(name, seqPos, expArgs), sub)
        case UsubstProvableTerm(child, subst) =>
          IPrUSubst(apply(child), apply(subst))
        case ForwardNewConsequenceTerm(child, con, r) =>
          IFNC(apply(child), apply(con), apply(r.name, rulePoses(r), ruleExps(r)))
        case ProlongationTerm(sub, pro) =>
          IPro(apply(sub), apply(pro))
        case Sub(child, sub, idx) => ISub(apply(child), apply(sub), idx)
        case StartProof(seq) => IStart(apply(seq))
        case NoProof() => throw ConversionException("Encountered unproven subproof")
      }
    }
  }

  def apply(f:Formula):Iformula = {
    f match {
      case DotFormula => IInContext(IDRight(IDUnit()), IGeq(IConst(0),IConst(0)))
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
        IAnd(IGeq(al,ar),IGeq(ar,al))
      case PredOf(Function(name,_,_,_,_), arg) =>
        val args = IsabelleConverter.detuple(arg)
        val allArgs = padArgs(args, m.pArity)
        IProp(IDEnum(m.predMap(name)), allArgs.map(apply))
      case PredicationalOf(Function(name,_,_,_,_),child) =>
        IInContext(IDEnum(m.conMap(Left(name))), apply(child))
      case UnitPredicational(name,_) => {
        val 2 = 1 + 1
        IInContext(IDEnum(m.conMap(Right(name))), IGeq(IConst(0), IConst(0)))

      }
      case Not(f) => INot(apply(f))
        //INot(IAnd(IGeq(al,ar),IGeq(ar
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
        IExists(IDEnum(m.varMap((x,ind))),apply(child))
      case Forall(vars,child) =>
        val BaseVariable(x,ind,_) = vars.head
        INot(IExists(IDEnum(m.varMap((x,ind))),INot(apply(child))))
      case Diamond(a,p) => IDiamond(apply(a),apply(p))
      case Box(a,p) => INot(IDiamond(apply(a),INot(apply(p))))
      case True => IGeq(IConst(0),IConst(0))
      case False => IGeq(IConst(0),IConst(1))
      case DifferentialFormula(GreaterEqual(t1,t2)) =>
        IGeq(IDifferential(apply(t1)),IDifferential(apply(t2)))
      case DifferentialFormula(Greater(t1,t2)) =>
        IGeq(IDifferential(apply(t1)),IDifferential(apply(t2)))
      case DifferentialFormula(LessEqual(l,r)) => IGeq(IDifferential(apply(r)), IDifferential(apply(l)))
      case DifferentialFormula(Less(l,r)) => IGeq(IDifferential(apply(r)), IDifferential(apply(l)))
      case DifferentialFormula(Equal(l,r)) =>
        val (al,ar) = (IDifferential(apply(l)), IDifferential(apply(r)))
        IAnd(IGeq(al,ar),IGeq(ar,al))
      case DifferentialFormula(NotEqual(l,r)) =>
        val (al,ar) = (IDifferential(apply(l)), IDifferential(apply(r)))
        IAnd(IGeq(al,ar),IGeq(ar,al))
      case DifferentialFormula(And(p,q)) =>
        val (al,ar) = (apply(DifferentialFormula(p)), apply(DifferentialFormula(q)))
        IAnd(al,ar)
      case DifferentialFormula(Or(p,q)) =>
        val (al,ar) = (apply(DifferentialFormula(p)), apply(DifferentialFormula(q)))
        IAnd(al,ar)
      case _ : UnitFunctional => throw ConversionException("Functionals not supported yet")
    }
  }

  val emptyArgs:List[Itrm] = List.tabulate(m.fArity)(_ =>IConst(0))

  def apply(t:Term):Itrm = {
    t match {
      case Nothing =>
        val 2 = 1 + 1
        ???
        //@TODO Please add unit functionals, this is just bogus so I can see what else is out there
      case UnitFunctional(name, _space, _sort) => IFunction(IDEnum("i5"), emptyArgs)
      case DotTerm(s,None) => IFunction(IDRight(IDEnum("i1")), emptyArgs)
      case DotTerm(s,Some(n)) => IFunction(IDRight(IDEnum("i"+n)), emptyArgs)
      case BaseVariable(x,ind,_) => IVar(IDEnum(m.varMap((x,ind))))
      case DifferentialSymbol(BaseVariable(x,ind,_)) => IDiffVar(IDEnum(m.varMap((x,ind))))
      case Number(n) =>
        if(n.isValidInt) {
          IConst(n.intValue())
        } else {
          throw ConversionException("Can't convert non-integer literal: " + n)
        }
      case FuncOf(Function(name,_,_,_,_), arg) =>
        val args = IsabelleConverter.detuple(arg)
        val allArgs = padArgs(args, m.fArity)
        IFunction(IDEnum(m.funMap(name)), allArgs.map(apply(_)))
      case Plus(l,r) => IPlus(apply(l),apply(r))
      case Minus(l,r) => IPlus(apply(l),ITimes(IConst(-1),apply(r)))
      case Neg(t) => ITimes(IConst(-1),apply(t))
      case Differential(t) => IDifferential(apply(t))
      case Divide(l,r) => throw ConversionException("Converter currently does not support conversion of divisions")
      case Power(l,r) => throw ConversionException("Converter currently does not support conversion of powers")
    }
  }

  def apply(o:DifferentialProgram):IODE = {
    o match {
      case AtomicODE(DifferentialSymbol(BaseVariable(x,ind,_)),e) =>
        IOSing(IDEnum(m.varMap(x,ind)), apply(e))
      case DifferentialProduct(l,r) => IOProd(apply(l),apply(r))
      case DifferentialProgramConst(c,_) => IOVar(IDEnum(m.odeMap(c)))
    }
  }

  def apply(hp:Program):Ihp = {
    hp match {
      case ProgramConst(name) => IPvar(IDEnum(m.varMap((name,None))))
      case Assign(BaseVariable(x,ind,_),e) => IAssign(IDEnum(m.varMap((x,ind))),apply(e))
      case Assign(DifferentialSymbol(BaseVariable(x,ind,_)),e) => IDiffAssign(IDEnum(m.varMap((x,ind))),apply(e))
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

  val INIT_CAPACITY = 1000000

  def scalaExpr:String = {
    val sb = new StringBuilder(INIT_CAPACITY)
    new ScalaBuilder(sb)(apply(pt))
    sb.toString()
  }

  private def writeObjects(sb:StringBuilder,objName:String, fieldName:String,mainName:String):Unit = {
    val imports = List("Real","Rat","Int","Proof_Checker","Syntax", "Nat", "USubst","Scratch")
    // Writing everything out in full detail is quite verbose. Let's give the Scala parser (and anyone debugging) a break by using some abbreviations
    val defs = List(
      "val z:trm[myvars,myvars] = Const(Ratreal(Frct((int_of_integer(0),int_of_integer(1)))))",
      s"val e:(myvars => trm[myvars,myvars]) = {${ISABELLE_IDS.map(i => s"case $i() => z").mkString(" ")}}",
      s"def ns[T]:(myvars => Option[T]) =   {${ISABELLE_IDS.map(i => s"case $i() => None").mkString(" ")}}",
      s"def s(t:trm[myvars,myvars]):(myvars =>trm[myvars,myvars]) = {case ${ISABELLE_IDS.head}() => t ${ISABELLE_IDS.tail.map(i => s"case $i() => z").mkString(" ")}}"
    )
    sb.++=("object "); sb.++=(objName);sb.++=(" {\n")
    imports.foreach({case s => sb.++=("  import ");sb.++=(s);sb.++=("._\n")})
    defs.foreach({case d => sb.++=("  ");sb++=(d);sb.++=("\n")})
    sb.++=("  val ");sb.++=(fieldName);sb.++=(":pt[myvars,myvars,myvars] = \n");
    new ScalaBuilder(sb)(apply(pt))
    sb.++=("\n}\n\n")
    sb.++=("object "); sb.++=(mainName);sb.++=(" {\n")
    imports.foreach({case s => sb.++=("  import ");sb.++=(s);sb.++=("._\n")})
    sb.++=("  def main(input : Array[String]) = {\n    val pred = ddl_pt_ok_i("+objName+"."+fieldName+")\n    val res = Predicate.eval(pred)\n    println(res())\n  }}")
  }

  def scalaObjects(objName:String, fieldName:String,mainName:String):String = {
    val sb = new StringBuilder(INIT_CAPACITY)
    writeObjects(sb,objName,fieldName,mainName)
    sb.toString()
  }

  def exportScalaObjects(fileName:String,objName:String, fieldName:String,mainName:String):Unit = {
    val writer = new BufferedWriter(new FileWriter(fileName))
    val sb = new StringBuilder(INIT_CAPACITY)
    writeObjects(sb,objName,fieldName,mainName)
    writer.append(sb)
    writer.close()
  }
}

class ScalaBuilder(sb:StringBuilder) {
  private def b0(name:String):Unit = {
    sb.++=(name)
    sb.++=("()")
  }

  def b1(name:String,f:(() => Unit)):Unit = {
    sb.++=(name)
    sb.++=("(")
    f()
    sb.++=(")")
  }

  private def b2(name:String,f:(()=> Unit),g:(()=> Unit)):Unit = {
    sb.++=(name)
    sb.++=("(")
    f()
    sb.++=(",")
    g()
    sb.++=(")")
  }

  private def b3(name:String,f:(()=> Unit),g:(()=> Unit),h:(()=> Unit)):Unit = {
    sb.++=(name);sb.++=("(");f();sb.++=(",");g();sb.++=(",");h();sb.++=(")")
  }

  private def b6(name:String,f1:(()=> Unit),f2:(()=> Unit),f3:(()=> Unit),f4:(()=> Unit),f5:(()=> Unit),f6:(()=> Unit)):Unit = {
    sb.++=(name);sb.++=("(");f1();sb.++=(",");f2();sb.++=(",");f3();sb.++=(",");f4();sb.++=(",");f5();sb.++=(",");f6();sb.++=(")")
  }

  private def btup(f:(()=>Unit),g:(()=>Unit)):Unit = {
    sb.++=("(");f();sb.++=(",");g();sb.++=(")")
  }

  private def blist[T](l:List[T],f:(T=>Unit)):Unit = {
    sb.++=("List(")
    l match {
      case Nil => ()
      case x::xs =>
        f(x)
        xs.foreach({case y => sb.++=(","); f(y)})
    }
    sb.++=(")")
  }

  private def brat(n:Int):Unit = {
    b1("Ratreal",{()=>b1("Frct",{()=>btup({()=>apply(n)},{()=>apply(1)})})})
  }

  // finite functions over identifiers
  private def bff[T](l:List[T],f:(T=>Unit)):Unit = {
    val cases = l.zip(ISABELLE_IDS)
    sb.++=("{")
    cases.foreach({case(v,id) =>
      sb.++=("case "); sb.++=(id); sb.++=("() => ");f(v);sb.++=(" ")
    })
    sb.++=("}")
  }

  private def emptyElse(args:List[Itrm], f:(() => Unit)):Unit = {
    if(args.forall({case IConst(0) => true case _ => false})) {
      sb.++=("e")
    } else if (args.length >= 1 && args.tail.forall({case IConst(0) => true case _ => false})) {
      b1("s", ()=> apply(args.head))
    } else {
      f()
    }
  }

  private def noneElse[T](args:List[Option[T]], f:(() => Unit)):Unit = {
    if(args.forall({case None => true case _ => false})) {
      sb.++=("ns")
    } else {
      f()
    }
  }

  def apply(id:ID):Unit = {
    id match {
      case IDEnum(n) => b0(n)
      case IDLeft(id) => b1("Left", ()=>apply(id))
      case IDRight(id) => b1("Right", ()=>apply(id))
      case IDUnit() => b0("")
    }
  }

  def apply(t:Itrm):Unit = {
    t match {
      case IVar(x) => b1("Var", () => apply(x))
      case IConst(n) if n == 0 => sb.++=("z")
      case IConst(n) =>  b1("Const",()=>brat(n))
      case IFunction(n,args) => b2("Function",()=>apply(n),()=> emptyElse(args,()=>bff(args,apply(_:Itrm))))
      case IPlus(a,b) => b2("Plus",()=>apply(a),()=>apply(b))
      case ITimes(a,b) => b2("Times",()=>apply(a),()=>apply(b))
      case IDiffVar(x) => b1("DiffVar", ()=>apply(x))
      case IDifferential(t) => b1("Differential",()=>apply(t))
    }
  }

  def apply(p:Ihp):Unit = {
    p match {
      case IPvar(a) => b1("Pvar",()=>apply(a))
      case IAssign(x,e) => b2("Assign",()=>apply(x),()=>apply(e))
      case IDiffAssign(x,e) => b2("DiffAssign",()=>apply(x),()=>apply(e))
      case ITest(p) => b1("Test",()=>apply(p))
      case IEvolveODE(ode,con) => b2("EvolveODE",()=>apply(ode),()=>apply(con))
      case IChoice(a,b) => b2("Choice", ()=>apply(a),()=>apply(b))
      case ISequence(a,b) => b2("Sequence", ()=>apply(a),()=>apply(b))
      case ILoop(a) => b1("Loop",()=>a)
    }
  }

  def apply(o:IODE):Unit = {
    o match {
      case IOVar(n) => b1("OVar",()=>apply(n))
      case IOSing(x,e) => b2("OSing",()=>apply(x),()=>apply(e))
      case IOProd(o1,o2) => b2("OProd",()=>apply(o1),()=>apply(o2))
    }
  }

  def apply(f:Iformula):Unit = {
    f match {
      case IGeq(t1,t2) => b2("Geq",()=>apply(t1),()=>apply(t2))
      case IProp(name,args) => b2("Prop",()=>apply(name),()=>emptyElse(args,()=>bff(args,apply(_:Itrm))))
      case INot(f) => b1("Not",()=>apply(f))
      case IAnd(p,q) => b2("And",()=>apply(p),()=>apply(q))
      case IExists(x,p) => b2("Exists",()=>apply(x),()=>apply(p))
      case IDiamond(a,p) => b2("Diamond",()=>apply(a),()=>apply(p))
      case IInContext(n,p) => b2("InContext",()=>apply(n),()=>apply(p))
    }
  }

  def apply(rr:Irrule):Unit = {
    rr match {
      case ICutRight(fml) => b1("CutRight", ()=> apply(fml))
      case IImplyR() => b0("ImplyR")
      case IAndR() => b0("AndR")
      case IHideR() => b0("HideR")
      case ICohideR() => b0("CohideR")
      case ICohideRR() => b0("CohideRR")
      case ITrueR() => b0("TrueR")
      case IEquivR() => b0("EquivR")
      case IEquivifyR() => b0("EquivifyR")
      case ICommuteEquivR() => b0("CommuteEquivR")
      case ISkolem() => b0("Skolem")
    }
  }

  def apply(lr:Ilrule):Unit = {
    lr match {
      case IHideL() => b0("HideL")
      case IImplyL() => b0("ImplyL")
      case IAndL() => b0("AndL")
      case IEquivBackwardL() => b0("EquivBackwardL")
      case IEquivForwardL() => b0("EquivForwardL")
    }
  }

  def apply(ra:IruleApp):Unit = {
    ra match {
      case IURename(w,r) => b2("URename",()=>apply(w),()=>apply(r))
      case IBRename(w,r) => b2("BRename",()=>apply(w),()=>apply(r))
      case IRrule(rr,n) => b2("Rrule", ()=>apply(rr), ()=>nat(n))
      case ILrule(lr,n) => b2("Lrule", ()=>apply(lr), ()=>nat(n))
      case ICloseId(i,j) => b2("CloseId",()=>nat(i),()=>nat(j))
      case ICohide2(i,j) => b2("Cohide2",()=>nat(i),()=>nat(j))
      case ICut(f) => b1("Cut",()=>apply(f))
    }
  }

  def nat(i:Int):Unit = {
    val s = i.toString
    sb.++=("Nata(");sb.++=(s);sb.++=(")")
  }

  def apply(br:Int):Unit = {
    val s = br.toString
    sb.++=("int_of_integer(");sb.++=(s);sb.++=(")")
  }

  def apply(ar:IaxRule):Unit = {
    ar match {
      case ICT() => b0("CT")
      case ICQ() => b0("CQ")
      case ICE() => b0("CE")
      case IG() => b0("CG")
      case Imonb() => b0("monb")
    }
  }

  def apply(ax:Iaxiom):Unit = {
    ax match {
      case IAloopIter() => b0("AloopIter")
      case IAI() => b0("AI")
      case IAtest() => b0("Atest")
      case IAbox() => b0("Abox")
      case IAchoice() => b0("Achoice")
      case IAK() => b0("AK")
      case IAV() => b0("AV")
      case IAassign() => b0("Aassign")
      case IAdassign() => b0("Adassign")
      case IAdvar() => b0("Advar")
      case IAdConst() => b0("AdConst")
      case IAdPlus() => b0("AdPlus")
      case IAdMult() => b0("AdMult")
      case IADW() => b0("ADW")
      case IADE() => b0("ADE")
      case IADC() => b0("ADC")
      case IADS() => b0("ADS")
      case IADIGeq() => b0("ADIGeq")
      case IAEquivReflexive() => b0("AEquivReflexive")
      case IADiffEffectSys() => b0("ADiffEffectSys")
      case IADIGr() => b0("ADIGr")
      case IADG() => b0("ADG")
    }
  }


  def apply(subst:Isubst):Unit = {
    val Isubst(fun,pred,con,prog,ode) = subst
    //Isubst(SFunctions:List[Itrm], SPredicates:List[Iformula], SContexts:List[Iformula], SPrograms:List[Ihp], SODEs:List[IODE])
    b6("subst_exta",()=>noneElse(fun,()=>bff(fun,apply(_:Option[Itrm]))),
       ()=>noneElse(fun,()=>bff(pred,apply(_:Option[Iformula]))),
       ()=>noneElse(fun,()=>bff(con,apply(_:Option[Iformula]))),
       ()=>noneElse(fun,()=>bff(prog,apply(_:Option[Ihp]))),
       ()=>noneElse(fun,()=>bff(ode,apply(_:Option[IODE]))),{() => sb.++=("()")})
  }

  def apply[T](t:Option[T]):Unit = {
    t match {
      case None => sb.++=("None")
      case Some(x:Itrm) => b1("Some", ()=> apply(x))
      case Some(x:Iformula) => b1("Some", ()=> apply(x))
      case Some(x:Ihp) => b1("Some", ()=> apply(x))
      case Some(x:IODE) => b1("Some", ()=> apply(x))
      case _ => throw ConversionException("Need extra case in option conversion")
    }
  }


  def apply(seq:Isequent):Unit = {
    btup(()=>blist(seq._1,apply(_:Iformula)),()=>blist(seq._2,apply(_:Iformula)))
  }

  // Build string for scala string representation of a proof term
  def apply(pt:Ipt):Unit = {
    pt match {
      case IFOLRConstant(f) => b1("FOLRConstant",()=>apply(f))
      case IRuleApp (child, ra,branch) => b3("RuleApp",()=>apply(child),()=>apply(ra),()=>nat(branch))
      case IAxRule(ar) => b1("AxRule", ()=>apply(ar))
      case IPrUSubst(child, subst) => b2("PrUSubst",()=>apply(child),()=>apply(subst))
      case IAx(ax) => b1("Ax", ()=>apply(ax))
      case IFNC(child, seq,ra) => b3("FNC",()=>apply(child),()=>apply(seq),()=>apply(ra))
      case IPro(child,pro) => b2("Pro",()=>apply(child),()=>apply(pro))
      case IStart(seq) => b1("Start",()=>apply(seq))
      case ISub(child, sub, branch) => b3("Sub",()=>apply(child),()=>apply(sub),()=>nat(branch))
    }
  }
}