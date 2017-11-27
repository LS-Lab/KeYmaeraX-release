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
  val idtype = "myvars"
  val unittype = "Unit"

  sealed abstract class ID {}
  case class IDEnum(x:String) extends ID
  case class IDUnit() extends ID
  case class IDLeft(child:ID, ltype:String = idtype, rtype:String = idtype) extends ID
  case class IDRight(child:ID, ltype:String = idtype, rtype:String = idtype) extends ID

  type Isequent = (List[Iformula],List[Iformula])
  type Irule = (List[Isequent],Isequent)

  // Keep this in sync with the code generation in Isabelle proof. If the number of IDs is too small then we can't export
  // the proof term, if it's too big then proof checking gets progressively slower
  val ISABELLE_IDS:Seq[String] = Seq(
    "i1","i2","i3","i4","i5","i6","i7","i8","i9","i10","i11","i12","i13","i14","i15","i16","i17","i18","i19","i20"/*,
    "i21","i22","i23","i24","i25","i26","i27","i28","i29","i30","i31","i32","i33","i34","i35","i36","i37","i38","i40"*/
  )

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
    // VAR MAP
    Map((("x_",None), "i1"), (("y_",None), "i2"), (("v_",None), "i1"), (("t_",None),"i2"), (("s_",None),"i3")),

    // FUN FUNL MAP
    // @TODO: Preload with some functionals too
    Map((Left("f"),"i1"), (Left("g"),"i2"),(Left("s"),"i1"),(Left("t"),"i2"),(Left("ctxT"),"i3"),(Left("ctx_"),"i3"), (Left("c"),"i1"), (Left("c_"),"i2"),
      (Right("f"),"i1"), (Right("g"),"i2"), (Right("f_"),"i1"), (Right("g_"),"i2")),

    // PROP MAP
    Map(("p","i1"),("q","i2"),("ctxF_","i1"),("ctx_","i3"),("p_","i1"),("q_","i2")),
    //@TODO: Left is argumented, right is unit, double-check please
    // CON PRED MAP
    Map((Left("p_"),"i1"),(Left("q_"),"i2"),(Left("J"),"i1"), (Left("ctx_"),"i3"),
      (Right("p_"),"i1"),(Right("q_"),"i2"),(Right("P"),"i1"),(Right("p"),"i1"), (Right("q"),"i2") , (Right("r"),"i3")),
    Map(("a","i1"),("b","i2"),("a_","i1"),("b_","i2")),
    Map(("c","i1"),("c_","i1"),("d","i2"),("e","i3"),("a_","i1"), ("a","i1")),
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

  def ofFuncl(name:String, repl:Expression, acc:IDMap):IDMap = {
    ofExp(repl,acc).addFuncl(name)
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
      case (acc,(UnitFunctional(name,_,_),repl)) =>
//        println("Translating functional replaced with: " + repl)
        ofFuncl(name,repl,acc)
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
              try {
                DerivedRuleInfo.allInfo.find(info => info.codeName.toLowerCase() == name.toLowerCase()).get.provable.underlyingProvable
              } catch {
                case e : NoSuchElementException => println("Couldn't find rule: " + name)
                  throw e
              }
          }
        ofProvable(r,acc)
      case UsubstProvableTerm(child: ProofTerm, substitution: USubst) =>
        ofSubst(substitution,ofProofTerm(child,acc))
      case AxiomTerm(name: String) => ofFormula(AxiomInfo(name).formula,acc)
      case ForwardNewConsequenceTerm(child: ProofTerm, newConsequence: Sequent, rule: Rule) =>
        ofSequent(newConsequence,ofProofTerm(child,acc))
      case ProlongationTerm(child: ProofTerm, prolongation: ProofTerm) =>
        ofProofTerm(child,ofProofTerm(prolongation,acc))
      case StartProof(phi:Sequent) =>
        ofSequent(phi,acc)
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
                 /* Functions, Functionals */
                 funMap:Map[Either[String,String],String],
                 predMap:Map[String,String],
                 /* Contexts, Predicationals? */
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
    else if(maxVar < ISABELLE_IDS.size) {
      IDMap(varMap.+(((name,ind),ISABELLE_IDS(maxVar))),funMap,predMap,conMap,progMap,odeMap,fArity,pArity,maxVar+1,maxFun,maxPred,maxCon,maxProg,maxOde)
    } else {
      throw ConversionException("Need more Isabelle identifiers, not enough to convert variable identifier: " + name)
    }
  }

  def addProg(name:String):IDMap = {
    if(progMap.contains(name)) { this }
    else if(maxProg < ISABELLE_IDS.size) {
      IDMap(varMap,funMap,predMap,conMap,progMap.+((name,ISABELLE_IDS(maxProg))),odeMap,fArity,pArity,maxVar,maxFun,maxPred,maxCon,maxProg+1,maxOde)
    } else {
      throw ConversionException("Need more Isabelle identifiers, not enough to convert program identifier: " + name)
    }
  }

  def addDiffProg(name:String):IDMap = {
    if(odeMap.contains(name)) { this }
    else if(maxOde < ISABELLE_IDS.size) {
      IDMap(varMap,funMap,predMap,conMap,progMap,odeMap.+((name,ISABELLE_IDS(maxOde))),fArity,pArity,maxVar,maxFun,maxPred,maxCon,maxProg,maxOde+1)
    } else {
      throw ConversionException("Need more Isabelle identifiers, not enough to convert differential program identifier: " + name)
    }
  }

  def addUnitPred(name:String):IDMap = {
    if(conMap.contains(Right(name))) { this }
    else if(maxCon < ISABELLE_IDS.size) {
      IDMap(varMap,funMap,predMap,conMap.+((Right(name),ISABELLE_IDS(maxCon))),progMap,odeMap,fArity,pArity,maxVar,maxFun,maxPred,maxCon+1,maxProg,maxOde)
    } else {
      throw ConversionException("Need more Isabelle identifiers, not enough to convert nullary predicational identifier: " + name)
    }
  }

  def addCon(name:String):IDMap = {
    if(conMap.contains(Left(name))) { this }
    else if(maxCon  < ISABELLE_IDS.size) {
      IDMap(varMap,funMap,predMap,conMap.+((Left(name),ISABELLE_IDS(maxCon))),progMap,odeMap,fArity,pArity,maxVar,maxFun,maxPred,maxCon+1,maxProg,maxOde)
    } else {
      throw ConversionException("Need more Isabelle identifiers, not enough to convert unary predicational identifier: " + name)
    }
  }

  def addFunc(name:String, arity:Int):IDMap = {
    if(funMap.contains(Left(name))) {
      this
    } else if(maxFun < ISABELLE_IDS.size) {
      IDMap(varMap,funMap.+((Left(name),ISABELLE_IDS(maxFun))),predMap,conMap,progMap,odeMap,fArity.max(arity),pArity,maxVar,maxFun+1,maxPred,maxCon,maxProg,maxOde)
    } else {
      throw ConversionException("Need more Isabelle identifiers, not enough to convert function identifier: " + name)
    }
  }

  def addFuncl(name:String):IDMap = {
    if(funMap.contains(Right(name))) {
      this
    } else if(maxFun < ISABELLE_IDS.size) {
      IDMap(varMap,funMap.+((Right(name),ISABELLE_IDS(maxFun))),predMap,conMap,progMap,odeMap,fArity,pArity,maxVar,maxFun+1,maxPred,maxCon,maxProg,maxOde)
    } else {
      throw ConversionException("Need more Isabelle identifiers, not enough to convert functional identifier: " + name)
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
case class IConst(int:Int,sm:SymMode=NonSubst()) extends Itrm {}
case class IFunction(f:ID, args:List[Itrm]) extends Itrm {}
case class IFunctional(f:ID) extends Itrm {}
case class IPlus(left:Itrm, right:Itrm) extends Itrm {}
case class ITimes(left:Itrm, right:Itrm) extends Itrm {}
case class IDifferential(child:Itrm) extends Itrm {}

sealed trait IODE {}
case class IOVar(id:ID, sp:Ispace) extends IODE {}
case class IOSing(x:ID, t:Itrm) extends IODE {}
case class IOProd(left:IODE,right:IODE) extends IODE {}

sealed trait Ihp {}
case class IPvar(id:ID) extends Ihp {}
case class IAssign(id:ID, t:Itrm) extends Ihp {}
case class IAssignRand(id:ID) extends Ihp {}
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

object IaxiomaticRule {
  def apply(n:String):IaxiomaticRule = {
    n match {
      case "CT" => ICT()
      case "CQ equation congruence" => ICQ()
      case "CE congruence" => ICE()
      case "goedel" => IG()
      case "monb" => Imonb()
      case _ =>
        throw ConversionException("Unrecognized axiomatic rule: " + n)
    }
  }
}
sealed trait IaxiomaticRule {}
case class ICT() extends IaxiomaticRule {}
case class ICQ() extends IaxiomaticRule {}
case class ICE() extends IaxiomaticRule {}
case class IG() extends IaxiomaticRule {}
case class Imonb() extends IaxiomaticRule {}

//object IruleApp {}
sealed trait IruleApp {}
case class IURename(what:ID,repl:ID) extends IruleApp {}
case class IApplyRrule(r:Irrule, i:Int) extends IruleApp {}
case class IApplyLrule(r:Ilrule, i:Int) extends IruleApp {}
case class ICloseId(i:Int,j:Int) extends IruleApp {}
case class ICohide2(i:Int,j:Int) extends IruleApp {}
case class ICut(f:Iformula) extends IruleApp {}
case class IDIGeqSchema(o:IODE, t1:Itrm, t2:Itrm) extends IruleApp {}

sealed trait Ilrule {}
case class IHideL() extends Ilrule {}
case class IImplyL() extends Ilrule {}
case class IAndL() extends Ilrule {}
//@TODO: These are different from the KyX rule
case class IEquivForwardL() extends Ilrule{}
case class IEquivBackwardL() extends Ilrule{}

case class IEquivL() extends Ilrule{}
case class INotL() extends Ilrule {}
case class ICutLeft(f:Iformula) extends Ilrule {}
case class IBRenameL(what:ID,repl:ID) extends Ilrule {}

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
case class IBRenameR(what:ID,repl:ID) extends Irrule {}

object Iaxiom {
  def apply(n:String):Iaxiom = {
    n match {
      case "(+)'" => IAdPlus()
      case "(*)'" => IAdMult()
      //@TODO: These names are all wrong; update them
      case "[*]" => IAloopIter()
      case "I induction" => IAI()
      case "[?] test" => IAtest()
      case "[] box" => IAbox()
      case "[++] choice" => IAchoice()
      case "K modal modus ponens" => IAK()
      case "V vacuous" => IAV()
      case "[:*] assign nondet" => IAassignany()
      case "[:=] assign" => IAassign()
      case "[':=] differential assign" => IAdassign()
      case "x' derive var" => IAdvar()
      case "c()' derive constant fn" => IAdConst()
      case "DW differential weakening" => IADW()
      case "DE differential effect" => IADE()
      case "DC differential cut" => IADC()
      case "DS differential solve" => IADS()
      //@TODO: specialize based on shape of differential formula
      case "DI differential invariant" =>
        throw ConversionException("Needed to convert proof using general-case DI to specific-case DI but didn't")
        //IADIGeq() // e.g. IADIGr()
      case "G goedel" => {
        val 2 = 1 + 1
        println("Encountered goedel axiom, thought it should be rule")
        ???
      }
      case "<-> reflexive" => IAEquivReflexive()
      case "DE differential effect (system)" => IADiffEffectSys()
      case "all instantiate" => IAallInst()
      case "[:=] assign equality" => IAassignEq()
      case "-' derive minus" => IAdMinus()
      case "const formula congruence" => IAconstFcong()
      case "[;] compose" => IAcompose()
      case "-> self" => IAImpSelf()
      case "[] split" => IABoxSplit()
      case "' linear" => IADiffLinear()
      case "all eliminate" => IAAllElim()
      case "= commute" => IAEqualCommute()
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
case class IAassignany() extends Iaxiom {}
case class IAdassign() extends Iaxiom {}
case class IAdvar() extends Iaxiom {}

case class IAdConst() extends Iaxiom {}
case class IAdPlus() extends Iaxiom {}
case class IAdMult() extends Iaxiom {}
case class IADW() extends Iaxiom {}
case class IADE() extends Iaxiom {}
case class IADC() extends Iaxiom {}
case class IADS() extends Iaxiom {}
case class IADIEq() extends Iaxiom {}
/*case class IADIGeq() extends Iaxiom {}
case class IADIGr() extends Iaxiom {}*/
case class IADG() extends Iaxiom {}
case class IAEquivReflexive() extends Iaxiom {}
case class IADiffEffectSys() extends Iaxiom {}

//case class IADILeq() extends Iaxiom {}
case class IAAllElim() extends Iaxiom {}
case class IADiffLinear() extends Iaxiom {}
case class IABoxSplit() extends Iaxiom {}
case class IAImpSelf() extends Iaxiom {}
case class IAcompose() extends Iaxiom {}
case class IAconstFcong() extends Iaxiom {}
case class IAassignEq() extends Iaxiom {}
case class IAdMinus() extends Iaxiom {}
case class IAallInst() extends Iaxiom {}
case class IAEqualCommute() extends Iaxiom {}


sealed trait Ispace {}
case class IAllSpace() extends Ispace{}
case class INBSpace(id:String) extends Ispace{}


/* @TODO: Represent this type magic in Scala or in generated code as necessary
  SFunctions       :: "'a ⇀ ('a + 'c, 'c) trm"
  SFuncls          :: "'a ⇀ ('a, 'c) trm"
  SPredicates      :: "'c ⇀ ('a + 'c, 'b, 'c) formula"
  SContexts        :: "'b ⇀ ('a, 'b + unit, 'c) formula"
  SPrograms        :: "'c ⇀ ('a, 'b, 'c) hp"
  SODEs            :: "'c ⇀ ('a, 'c) ODE"
*/
case class Isubst(
SFunctions:List[Option[Itrm]],
SFuncls:List[Option[Itrm]],
SPredicates:List[Option[Iformula]],
SContexts:List[Option[Iformula]], SPrograms:List[Option[Ihp]],
SODEs:List[Option[IODE]],
// NB: code-generated proof checker supports different spaces for different (and even same) ode identifier,
// but we don't need that yet
SSpace:Ispace)

sealed trait Ipt {}
case class IFOLRConstant(f:Iformula) extends Ipt {}
case class IRuleApplication (child:Ipt, ra:IruleApp,branch:Int) extends Ipt {}
case class IAxRule(ar:IaxiomaticRule) extends Ipt {}
case class IPrUSubst(child:Ipt, sub:Isubst) extends Ipt {}
case class IAx(ax:Iaxiom) extends Ipt {}
case class IFNC(child:Ipt, seq:Isequent,ra:IruleApp) extends Ipt {}
case class IPro(child:Ipt,pro:Ipt) extends Ipt {}
case class IStart(seq:Isequent) extends Ipt {}
case class ISub(child:Ipt, sub:Ipt, branch:Int) extends Ipt {}


abstract sealed class SymMode {
  def base:SymMode
  def isDefun:Boolean = {
    this match {
      case Defun(_) => true
      case Depred(sm) => sm.isDefun
      case BananaODE(sm) => sm.isDefun
      case _ => false
    }
  }
  def isDepred:Boolean = {
    this match {
      case Defun(sm) => sm.isDepred
      case BananaODE(sm) => sm.isDepred
      case Depred(sm) => true
      case _ => false
    }
  }
  def isBananaODE:Boolean = {
    this match {
      case BananaODE(sm) => true
      case Defun(sm) => sm.isBananaODE
      case Depred(sm) => sm.isBananaODE
      case _ => false
    }
  }

}

case class NonSubst() extends SymMode {
  def base = this
}
case class BananaODE(sm:SymMode) extends SymMode {
  def base = sm.base
}
case class Defun(sm:SymMode) extends SymMode {
  def base = sm.base
}
case class Depred(sm:SymMode) extends SymMode {
  def base = sm.base
}
case class DefunSubst() extends SymMode {
  def base = this
}
case class DepredSubst() extends SymMode {
  def base = this
}
case class FunSubst() extends SymMode {
  def base = this
}
case class ConSubst() extends SymMode {
  def base = this
}

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
      case ("Close", (a:AntePos)::(s:SeqPos)::Nil, _) => ICloseId(a.getIndex,s.getIndex)
      case ("cut", _, (f:Formula) :: Nil) => ICut(apply(f,NonSubst()))
      case ("CoHide2", (a:AntePos) :: (s:SuccPos) :: Nil, _) => ICohide2(a.getIndex,s.getIndex)


      case ("cut Left", (a:AntePos) :: Nil, (f:Formula) :: Nil) => IApplyLrule(ICutLeft(apply(f,NonSubst())), a.getIndex)
      case ("Not Left", (a:AntePos)::Nil, _) => IApplyLrule(INotL(),a.getIndex)
      case ("Imply Left", (a:AntePos)::Nil, _) => IApplyLrule(IImplyL(),a.getIndex)
      case ("And Left", (a:AntePos)::Nil, _) => IApplyLrule(IAndL(),a.getIndex)
      case ("Equiv Left", (a:AntePos)::Nil, _) => IApplyLrule(IEquivL(),a.getIndex)
      case ("Equiv Left1", (a:AntePos)::Nil, _) => IApplyLrule(IEquivForwardL(),a.getIndex)
      case ("Equiv Left2", (a:AntePos)::Nil, _) => IApplyLrule(IEquivBackwardL(),a.getIndex)
      case ("HideLeft", (a:AntePos)::Nil, _) => IApplyLrule(IHideL(),a.getIndex)
      case ("Bound Renaming", (a:AntePos) :: Nil, BaseVariable(n1,ind1,_) :: BaseVariable(n2,ind2,_) :: Nil) =>
        IApplyLrule(IBRenameL(IDEnum(m.varMap((n1,ind1))),IDEnum(m.varMap((n2,ind2)))), a.getIndex)

      case ("cut Right", (s:SuccPos) :: Nil, (f:Formula) :: Nil) => IApplyRrule(ICutRight(apply(f,NonSubst())), s.getIndex)
      case ("Imply Right", (s:SuccPos)::Nil, _) => IApplyRrule(IImplyR(), s.getIndex)
      case ("CoHideRight", (s:SuccPos)::Nil, _) => IApplyRrule(ICohideRR(), s.getIndex)
      case ("Cohide Right 2", (s:SuccPos)::Nil, _) => IApplyRrule(ICohideR(), s.getIndex)
      case ("CloseTrue", (s:SuccPos)::Nil, _) => IApplyRrule(ITrueR(), s.getIndex)
      case ("Equiv Right", (s:SuccPos)::Nil, _) => IApplyRrule(IEquivR(), s.getIndex)
      case ("EquivifyRight", (s:SuccPos)::Nil, _) => IApplyRrule(IEquivifyR(), s.getIndex)
      case ("CommuteEquivRight", (s:SuccPos)::Nil, _) => IApplyRrule(ICommuteEquivR(), s.getIndex)
      case ("All Right", (s:SuccPos)::Nil, _) => IApplyRrule(ISkolem(), s.getIndex)
      case ("And Right", (s:SuccPos)::Nil, _) => IApplyRrule(IAndR(), s.getIndex)
      case ("HideRight", (s:SuccPos)::Nil, _) => IApplyRrule(IHideR(), s.getIndex)
      case ("Skolemize", (s:SuccPos)::Nil, _) => IApplyRrule(ISkolem(), s.getIndex)
      case ("Bound Renaming", (s:SuccPos) :: Nil, BaseVariable(n1,ind1,_) :: BaseVariable(n2,ind2,_) :: Nil) =>
        IApplyRrule(IBRenameR(IDEnum(m.varMap((n1,ind1))),IDEnum(m.varMap((n2,ind2)))), s.getIndex)
      case _ =>
        throw ConversionException("Unrecognized non-axiomatic rule: " + name + ","  + seqPos.toList +", " + expArgs.toList)
    }
  }

  private def sortSubs[T](seq:Seq[(Expression,Expression)], f:(Expression => String), g:((Expression,Expression) => T)):List[(String,T)] = {
    val withKeys = seq.map({case (ns,e) => (ns,e,f(ns))})
    val s1 = withKeys.sortBy({case (ns,e,key) => key})
    val s2 = s1.map{case (ns,e,i) => (i,g(ns,e))}.toList
    s2
    /*def undentify(xs:List[(Expression,Expression,String)],ys:List[String]):List[(String,Expression] = {
      (xs,ys) match {
        case ((_,rep,where)::xss,here::yss) if (where == here) =>
          rep::undentify(xss,yss)
        case ((_,rep,where)::xss,here::yss) if (where != here) =>
          Number(0)::undentify(xs,yss)
        case (Nil,x::xs) => Number(0)::undentify(Nil,xs)
        case (Nil,Nil) => Nil
      }
    }*/
    //val s2 = undentify(s1.toList, ISABELLE_IDS.toList)
    //val s3 = s2.map(g)

  }


  var subst_so_far = 0
  // @TODO: Surely has type issues
  // @TODO: Have to ensure identifier renaming preserves choice of reserved identifiers in axioms/axiomatic rules
  def apply(sub:USubst, defun:Boolean=false , depred:Boolean=false,space:Ispace = IAllSpace()):Isubst = {
    /*if(defun)
      println("DEFUN")
    else
      println("NO-DEFUN")

    println("This sub ("+subst_so_far+"): " + sub)*/
    subst_so_far = subst_so_far + 1

    def extendSub[T](l:List[(String,T)],ids:List[String] = ISABELLE_IDS.toList):List[Option[T]] = {
      (l, ids) match {
        case ((i,x)::ls,id::idss) =>
          if(i == id) { Some(x) :: extendSub(ls,idss)}
          else { None :: extendSub(l, idss)}
        case (Nil, id::idss) => None :: extendSub(Nil,idss)
        case (Nil, Nil) => Nil
        case (a::b, Nil) =>
          println("wot")
          ???
      }
    }
    val pairs = sub.subsDefsInput.map({case SubstitutionPair(what,repl) => (what,repl)})
    val (fun, t1) =
      if (defun) {
        pairs.partition({ case (_: FuncOf, _) => true case (_ : UnitFunctional, _) => true case _ => false })
      } else {
        pairs.partition({ case (_: FuncOf, _) => true case _ => false })
      }
    val (pred, t2) = if (depred) {
      t1.partition({ case (_: PredOf, _) => true case (_ : UnitPredicational, _) => true case _ => false })
    } else {
      t1.partition({ case (_: PredOf, _) => true case _ => false })
    }
    val (con, t3) =
      if(depred) {
        t2.partition({ case (_: PredicationalOf, _) => true case _ => false })
      } else {
        t2.partition({ case (_: PredicationalOf, _) => true case (_: UnitPredicational, _) => true case _ => false })
      }
    val (prog, t4) = t3.partition({case (_: ProgramConst, _) => true case (_:SystemConst, _) => true case _ => false})
    val (ode, t5) = t4.partition({case (_: DifferentialProgramConst, _) => true case _ => false})
    val (unitFun, t6) =
      if (defun)  {
        t5.partition(_ => false)
      } else {
        t5.partition({ case (_: UnitFunctional, _) => true case _ => false })
      }
    if(unitFun.exists({case (_,FuncOf(Function("V",_,_,_,_),_)) => true case _ => false})) {
      val 2 = 1 + 1
    }
    assert(t6.isEmpty, "Forgot to handle symbols in substitution: " + t6)
    // @TODO: Need to insert lefts/rights in ids on RHS
    val res =
    Isubst(
      // @TODO: This probably breaks if you have functions and functionals in the same substitution
      extendSub(sortSubs(fun, {case FuncOf(Function(name,_,_,_,_),_) => m.funMap(Left(name)) case UnitFunctional(name,_,_) => m.funMap(Right(name))},
        {case (_:UnitFunctional ,e:Term)=> apply(e, sm = if(defun)DefunSubst() else FunSubst()) case (_:FuncOf,e:Term) => apply(e, sm = FunSubst())})),
      extendSub(sortSubs(unitFun, {case UnitFunctional(name,_,_) => m.funMap(Right(name))}, {case (_,e:Term) => apply(e,NonSubst())})),
      // @TODO: Not clear what mode
      extendSub(sortSubs(pred, {case PredOf(Function(name,_,_,_,_),_) => m.predMap(name) case UnitPredicational(name, _) => m.conMap(Right(name))},
        {
          case (_:PredOf,e:Formula) => apply(e, FunSubst())
          case (_:UnitPredicational,e:Formula) => apply(e, if(depred)DepredSubst() else FunSubst())
        })),
      extendSub(sortSubs(con, {case PredicationalOf(Function(name,_,_,_,_),_) => m.conMap(Left(name)) case UnitPredicational(name, _) => m.conMap(Right(name))}, {case (_,e:Formula) => apply(e, sm=ConSubst())})),
      extendSub(sortSubs(prog, {case ProgramConst(name) =>  m.progMap(name) case SystemConst(name) =>  m.progMap(name)}, {case (_,e:Program) => apply(e,NonSubst())})),
      extendSub(sortSubs(ode, {case DifferentialProgramConst(name,_) =>  m.odeMap(name)}, {case (_,e:DifferentialProgram) => apply(e,NonSubst())})),
      space)
    res
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
            println(reflFml+"\n\n\n"+equivReflSubst)
            ISub(IStart(apply(reflFml,NonSubst())),IPrUSubst(IAx(Iaxiom("<-> reflexive")),apply(equivReflSubst)), where)
/*      case Sub(Sub(RuleApplication(StartProof(reflFml),"cut Right",_,_,_),
          ForwardNewConsequenceTerm(
          ForwardNewConsequenceTerm(ProlongationTerm(UsubstProvableTerm(AxiomTerm(<=' derive <=),USubst{(f(||)~>x), (g(||)~>m()-V()*(ep()-t))}),UsubstProvableTerm(RuleTerm(CE congruence),USubst{(ctx_{⎵}~>⎵<->(x<=m()-V()*(ep()-t))'), (p_(||)~>(x<=m()-V()*(ep()-t))'), (q_(||)~>(x)'<=(m()-V()*(ep()-t))')})),  ==>  ((x<=m()-V()*(ep()-t))'<->(x<=m()-V()*(ep()-t))')->((x)'<=(m()-V()*(ep()-t))'<->(x<=m()-V()*(ep()-t))'),EquivifyRight at 1),  ==>  ((x<=m()-V()*(ep()-t))'<->(x<=m()-V()*(ep()-t))')->((x)'<=(m()-V()*(ep()-t))'<->(x<=m()-V()*(ep()-t))'),CoHideRight at 1),1),UsubstProvableTerm(AxiomTerm(<-> reflexive),USubst{(p_()~>(x<=m()-V()*(ep()-t))')}),0)*/
      case Sub(Sub(RuleApplication(StartProof(reflFml), "cut Right", _, _, _),
          ForwardNewConsequenceTerm(
          ForwardNewConsequenceTerm(ProlongationTerm(UsubstProvableTerm(AxiomTerm("<=' derive <="), _),
          UsubstProvableTerm(RuleTerm("CE congruence"), _)), _, _: EquivifyRight), _, _: CoHideRight), _),
          UsubstProvableTerm(AxiomTerm("<-> reflexive"), equivReflSubst), where) =>
            println(reflFml+"\n\n\n"+equivReflSubst)
            ISub(IStart(apply(reflFml,NonSubst())),IPrUSubst(IAx(Iaxiom("<-> reflexive")),apply(equivReflSubst)), where)
      case Sub(Sub(RuleApplication(StartProof(reflFml), "cut Right", _, _, _),
      ForwardNewConsequenceTerm(
      ForwardNewConsequenceTerm(ProlongationTerm(UsubstProvableTerm(AxiomTerm("=' derive ="), _),
      UsubstProvableTerm(RuleTerm("CE congruence"), _)), _, _: EquivifyRight), _, _: CoHideRight), _),
      UsubstProvableTerm(AxiomTerm("<-> reflexive"), equivReflSubst), where) =>
        println(reflFml+"\n\n\n"+equivReflSubst)
        ISub(IStart(apply(reflFml,NonSubst())),IPrUSubst(IAx(Iaxiom("<-> reflexive")),apply(equivReflSubst)), where)
      case _ =>
        val 2 = 1 + 1
        ???
    }
  }

  private def isDiffEffectSysInstance(pt:ProofTerm):Boolean = {
    pt match {
        // todo: symmetried version too
      case UsubstProvableTerm(AxiomTerm("DE differential effect (system)"), sub) => true
      // symmetric version of DEsys
      // @todo might not be right
      case UsubstProvableTerm(Sub(RuleApplication(StartProof(seq),a,b,c,d),e,f),sub) if seqNeedsDefun(seq)=>
        true
      case _ => false
    }
  }

  private def translateDiffEffectSysInstance(pt:ProofTerm):Ipt = {
    pt match {
      case UsubstProvableTerm(AxiomTerm("DE differential effect (system)"), sub) =>
        val axTerm =  IAx(Iaxiom("DE differential effect (system)"))
        val defun = true
        val depred = false
        val space = INBSpace("i1")
        val subst = apply(sub, defun = defun, depred = depred, space)
        IPrUSubst(axTerm,subst)
      // symmetric version of DEsys
      // @todo might not be right
      case UsubstProvableTerm(Sub(RuleApplication(StartProof(seq),a,b,c,d),e,f),sub) if seqNeedsDefun(seq)=>
        //val axTerm =  IAx(Iaxiom("DE differential effect (system)"))
        val defun = true
        val depred = false
        val space = INBSpace("i1")
        val subst = apply(sub, defun = defun, depred = depred, space)
        val child = apply(Sub(RuleApplication(StartProof(seq),a,b,c,d),e,f))
        //val ruleApp = IRuleApplication(apply(StartProof(seq),NonSubst()),apply())
        IPrUSubst(child,subst)
      case _ =>
        val 2 = 1 + 1
        ???
    }
  }


private def or(p:Iformula,q:Iformula):Iformula = {
    INot(IAnd(INot(p),INot(q)))
  }

  private def implies(p:Iformula,q:Iformula):Iformula = {
    or(q,INot(p))
  }

  private def dpredl(id:String):Iformula = {
    IProp(IDEnum(id), ISABELLE_IDS.map( i => IVar(IDEnum(i))).toList)
  }

  private def box(a:Ihp,p:Iformula):Iformula = {
    INot(IDiamond(a,INot(p)))
  }

  private def diGeqConclusion(o:IODE,t1:Itrm,t2:Itrm):Iformula = {
    implies(implies(dpredl("i1"),IAnd(IGeq(t1,t2),
      box(IEvolveODE(o,dpredl("i1")),IGeq(IDifferential(t1),IDifferential(t2))))),
      box(IEvolveODE(o,dpredl("i1")),IGeq(t1,t2)))
  }

  private def translateDiffTermChase(pttt: ProofTerm):Ipt = {
    pttt match {
      case RuleApplication(Sub(a,Sub(b,UsubstProvableTerm(AxiomTerm("DI differential invariant"),sub),c),d),e,f,g,h)    =>
        val csym = DifferentialProgramConst("c")
        val cc:DifferentialProgram = sub(csym)
        val psym = UnitPredicational("p",AnyArg)
        val p = sub(psym)
        val qsym = UnitPredicational("q",AnyArg)
        val q = sub(qsym)
        p match {
          case GreaterEqual(l:Term,r:Term) =>
            val fsym = UnitFunctional("f", AnyArg, Real)
            val gsym = UnitFunctional("g", AnyArg, Real)
            val bigSubst = USubst(collection.immutable.Seq(SubstitutionPair(csym,cc),SubstitutionPair(qsym,q),SubstitutionPair(fsym,l),SubstitutionPair(gsym,r)))
            val smallSubst = USubst(collection.immutable.Seq(SubstitutionPair(psym,q)))
            val smallApp = apply(smallSubst, depred = true)
            val ode = apply(cc,NonSubst())
            val left = apply(l,Defun(NonSubst()))
            val right = apply(r,Defun(NonSubst()))
            println("Doin the translate, left: " + left + " and right: " + right)
            val ruleApp = IDIGeqSchema(ode,left,right)
            //val ax = IADIGeq()
            val inst:Iformula = diGeqConclusion(ode,left,right)
            val instSeq = (List(), List(inst))
            val result = IPrUSubst(IRuleApplication(IStart(instSeq), ruleApp,0),smallApp)
            val foo = ProofChecker(pttt)
            println("Thesubst >=: ************" + bigSubst + "\n******************")
            IRuleApplication(ISub(apply(a),ISub(apply(b),result,c),d),apply(e,g,h),f)
          /*case LessEqual(r,l) =>
            val fsym = UnitFunctional("f", AnyArg, Real)
            val gsym = UnitFunctional("g", AnyArg, Real)
            val subst = USubst(collection.immutable.Seq(SubstitutionPair(csym,cc),SubstitutionPair(qsym,q),SubstitutionPair(fsym,l),SubstitutionPair(gsym,r)))
            val theapp = apply(subst)
            val ax = IADIGeq()
            val result = IPrUSubst(IAx(ax),theapp)
            val foo = ProofChecker(pttt)
            println("Thesubst <=: " + subst)
            IRuleApplication(ISub(apply(a),ISub(apply(b),result,c),d),apply(e,g,h),f)
          case Equal(r,l) =>
            val fsym = UnitFunctional("f", AnyArg, Real)
            val gsym = UnitFunctional("g", AnyArg, Real)
            val subst = USubst(collection.immutable.Seq(SubstitutionPair(csym,cc),SubstitutionPair(qsym,q),SubstitutionPair(fsym,l),SubstitutionPair(gsym,r)))
            val theapp = apply(subst)
            val ax = IADIEq()
            val result = IPrUSubst(IAx(ax),theapp)
            val foo = ProofChecker(pttt)
            println("Thesubst =: " + subst)
            IRuleApplication(ISub(apply(a),ISub(apply(b),result,c),d),apply(e,g,h),f)
            //result*/
          case _ => throw ConversionException("Unsupported differential invariant type: " + p)
        }
      case _ => ???
    }
  }

  private def isDiffTermChase(pt:ProofTerm):Boolean = {
    pt match {
      case RuleApplication(Sub(a,Sub(b,UsubstProvableTerm(AxiomTerm("DI differential invariant"),sub),c),d),e,f,g,h) => true
      case _ => false
    }
  }

  /* When substituting into a formula (usually but not always a proper axiom) we need to identify any prime-free unit functionals
  * which need to be compiled down to functions in the substitution (compiling them down in the axiom itself is done elsewhere).
  * this occurs for any axiom that has a functional under a prime or ODE RHS, and, unfortunately, also the commutation of the DESys
  * axiom*/
  private def axiomNeedsDefunctionalization(pt:ProofTerm):Boolean = {
    pt match {
      case AxiomTerm("DE differential effect (system)") => true
      case AxiomTerm("' linear") => true
      case AxiomTerm("-' derive minus") => true
        // commuted DESys... yechh
      case Sub(RuleApplication(StartProof(seq),_,_,_,_),_,_) if seqNeedsDefun(seq)=>
        true
      case AxiomTerm(n) => /*println("Normal ax: " + pt); */false
      case _ => false
    }
  }

  private def axiomNeedsDepredicationalization(pt:ProofTerm):Boolean = {
    pt match {
  //    case AxiomTerm("DE differential effect (system)") => true
      case AxiomTerm("DI differential invariant") => false //true
      // commuted DESys... yechh
      case Sub(RuleApplication(StartProof(seq),_,_,_,_),_,_) if seqNeedsDepred(seq)=>
        false//true
      case AxiomTerm(n) => /*println("Normal ax: " + pt); */false
      case _ => false
    }
  }


  def apply(pt:ProofTerm):Ipt = {
    if(isDiffTermChase(pt)) {
      translateDiffTermChase(pt)
    } else if(isDiffFormulaChase(pt)) {
      translateDiffFormulaChase(pt)
    } else if(isDiffEffectSysInstance(pt)) {
      translateDiffEffectSysInstance(pt)
    } else {
      pt match {
        case FOLRConstant(f) => IFOLRConstant(apply(f,NonSubst()))
        case RuleTerm(name) => IAxRule(IaxiomaticRule(name))
        case AxiomTerm(name) => IAx(Iaxiom(name))
        case RuleApplication(child, name, sub, seqPos, expArgs) =>
          IRuleApplication(apply(child), apply(name, seqPos, expArgs), sub)
        case UsubstProvableTerm(child, subst) =>
          val defun = axiomNeedsDefunctionalization(child)
          val depred = axiomNeedsDepredicationalization(child)
          val kid = apply(child)
          val sub = apply(subst, defun = defun, depred = depred)
          IPrUSubst(kid,sub)
        case ForwardNewConsequenceTerm(child, con, r) =>
          val kid = apply(child)
          IFNC(kid, apply(con,NonSubst()), apply(r.name, rulePoses(r), ruleExps(r)))
        case ProlongationTerm(sub, pro) =>
          val left = apply(sub)
          val right = apply(pro)
          IPro(left, right)
        case Sub(child, sub, idx) =>
          val left = apply(child)
          val right = apply(sub)
          ISub(left, right, idx)
        case StartProof(seq) =>
          // If we spin off subproofs that mention unit functionals under primes, translate them to n-ary functions.
          // so far i've only seen this used for commuted DE-sys.
          val sm0 = NonSubst()
          val sm1 = if(seqNeedsDefun(seq)) { Defun(sm0) } else sm0
          val sm2 = if(seqNeedsDepred(seq)) { Depred(sm0) } else sm1
          val space = if(seqNeedsBanana(seq)) { INBSpace("i1") } else {IAllSpace()}
          val sm3 = if(seqNeedsBanana(seq)) {
            println("Bananizing startproof: " + seq)
            BananaODE(sm2)
          } else sm2
          if(sm3 != NonSubst()) {
            println("Interesting startproof: " + sm3)
          }
          IStart(apply(seq,sm3))
        case NoProof() => throw ConversionException("Encountered unproven subproof")
      }
    }
  }

  private def seqNeedsDefun(phi:Sequent):Boolean = {
    def reverse(f:Formula) = { f match {case Equiv(l,r) => Equiv(r,l)}}
    // only one sequent ever needs this so far
    val specials:List[Sequent] = List(
      new Sequent(collection.immutable.IndexedSeq(),collection.immutable.IndexedSeq(reverse(AxiomInfo("DE differential effect (system)").formula)))
    )
    specials.contains(phi)
  }

  private def seqNeedsDepred(phi:Sequent):Boolean = {
    false
    /*def reverse(f:Formula) = { f match {case Equiv(l,r) => Equiv(r,l)}}
    // only one sequent ever needs this so far
    val specials:List[Sequent] = List(
      new Sequent(collection.immutable.IndexedSeq(),collection.immutable.IndexedSeq(reverse(AxiomInfo("DE differential effect (system)").formula)))
    )
    specials.contains(phi)*/
  }

  private def seqNeedsBanana(phi:Sequent):Boolean = {
    def reverse(f:Formula) = { f match {case Equiv(l,r) => Equiv(r,l)}}
    // only one sequent ever needs this so far
    val specials:List[Sequent] = List(
      new Sequent(collection.immutable.IndexedSeq(),collection.immutable.IndexedSeq(reverse(AxiomInfo("DE differential effect (system)").formula)))
    )
    specials.contains(phi)
  }



  private def ddefun(sm:SymMode):SymMode = {
    sm
    /*sm match {
      case Defun(sm) => Defun(sm)
      case sm => Defun(sm)
    }*/
  }

  def apply(f:Formula,sm:SymMode):Iformula = {
    (f,sm.isDepred) match {
      case (DotFormula,_) => IInContext(IDRight(IDUnit(),"myvars","Unit"), IGeq(IConst(0),IConst(0)))
      case (GreaterEqual(l,r),_) => IGeq(apply(l,sm), apply(r,sm))
      case (Greater(l,r),_) =>
        val (al,ar) = (apply(l,sm), apply(r,sm))
        IAnd(IGeq(al,ar), INot(IGeq(ar,al)))
      case (LessEqual(l,r) ,_)=> IGeq(apply(r,sm), apply(l,sm))
      case (Less(l,r) ,_)=>
        val (al,ar) = (apply(l,sm), apply(r,sm))
        IAnd(IGeq(ar,al), INot(IGeq(al,ar)))
      case (Equal(l,r) ,_)=>
        val (al,ar) = (apply(l,sm), apply(r,sm))
        IAnd(IGeq(al,ar),IGeq(ar,al))
      case (NotEqual(l,r),_) =>
        val (al,ar) = (apply(l,sm), apply(r,sm))
        IAnd(IGeq(al,ar),IGeq(ar,al))
      case (PredOf(Function(name,_,_,_,_), arg),_) =>
        val propId = if(sm.base == FunSubst()) {IDLeft(IDEnum(m.predMap(name)))} else {IDEnum(m.predMap(name))}
        val args = IsabelleConverter.detuple(arg)
        val allArgs = padArgs(args, m.pArity)
        IProp(propId, allArgs.map(apply(_,sm)))

      case (PredicationalOf(Function(name,_,_,_,_),child),_) =>
        val predId = if(sm.base == ConSubst()) {IDLeft(IDEnum(m.conMap(Left(name))),"myvars","Unit")} else {IDEnum(m.conMap(Left(name)))}
        IInContext(predId, apply(child,sm))
        // @TODO: is anything needed here
      /*case UnitPredicational(name,_) if sm.base == DepredSubst() => {
        val predId = if(sm.base == ConSubst()) {IDLeft(IDEnum(m.conMap(Right(name))),"myvars","Unit")} else {IDEnum(m.conMap(Right(name)))}
        IInContext(predId, IGeq(IConst(0), IConst(0)))
      }*/
/*      case (UnitFunctional(name, _space, _sort),true) =>
        val tmp = m.funMap(Right(name))
        // @TODO: This is mad hax because we're getting function <-> functional id collisions
        val fid = tmp//if (tmp == "i1")  {println("Doin first magic: " ); "i2"} else tmp
        IFunction(IDEnum(fid),ISABELLE_IDS.map( i => IVar(IDEnum(i))).toList)
      //IFunctional(IDEnum(m.funMap(Right(name))))
      case (UnitFunctional(name, _space, _sort),_)if sm.base == DefunSubst() || sm.base == FunSubst()=>
        val tmp = m.funMap(Right(name))
        val fid = tmp//if (tmp == "i1")  {println("Doin second magic: " ); "i2"} else tmp
        IFunctional(IDLeft(IDEnum(fid)))*/

      case (UnitPredicational(name,_),true) => {
        val predId = if(sm.base == ConSubst()) {IDLeft(IDEnum(m.conMap(Right(name))),"myvars","Unit")} else {IDEnum(m.conMap(Right(name)))}
        IProp(predId, ISABELLE_IDS.map( i => IVar(IDEnum(i))).toList)
      }
      case (UnitPredicational(name,_),false) => {
        val predId = if(sm.base == ConSubst()) {IDLeft(IDEnum(m.conMap(Right(name))),"myvars","Unit")} else {IDEnum(m.conMap(Right(name)))}
        IInContext(predId, IGeq(IConst(0), IConst(0)))
      }
      case (Not(f),_) => INot(apply(f,sm))
        //INot(IAnd(IGeq(al,ar),IGeq(ar
      case (And(l,r),_) => IAnd(apply(l,sm),apply(r,sm))
      case (Or(l,r),_) => INot(IAnd(INot(apply(l,sm)),INot(apply(r,sm))))
      // @TODO: Double-negation eliminate, but need to do that in isabelle land too
      case (Imply(l,r),_) => INot(IAnd(INot(apply(r,sm)),INot(INot(apply(l,sm)))))
      // @TODO: Double-negation eliminate, but need to do that in isabelle land too
      case (Equiv(l,r),_) =>
        val (al,ar) = (apply(l,sm), apply(r,sm))
        INot(IAnd(INot(IAnd(al,ar)),INot(IAnd(INot(al),INot(ar)))))
      case (Exists(vars,child),_) =>
        val BaseVariable(x,ind,_) = vars.head
        IExists(IDEnum(m.varMap((x,ind))),apply(child,sm))
      case (Forall(vars,child),_) =>
        val BaseVariable(x,ind,_) = vars.head
        INot(IExists(IDEnum(m.varMap((x,ind))),INot(apply(child,sm))))
      case (Diamond(a,p),_) => IDiamond(apply(a,sm),apply(p,sm))
      case (Box(a,p),_) => INot(IDiamond(apply(a,sm),INot(apply(p,sm))))
      case (True,_) => IGeq(IConst(0),IConst(0))
      case (False,_) => IGeq(IConst(0),IConst(1))
      case (DifferentialFormula(GreaterEqual(t1,t2)) ,_)=>
        IGeq(IDifferential(apply(t1,ddefun(sm))),IDifferential(apply(t2, ddefun(sm) )))
      case (DifferentialFormula(Greater(t1,t2)) ,_)=>
        IGeq(IDifferential(apply(t1,ddefun(sm))),IDifferential(apply(t2,ddefun(sm))))
      case (DifferentialFormula(LessEqual(l,r)),_) => IGeq(IDifferential(apply(r,ddefun(sm))), IDifferential(apply(l,ddefun(sm))))
      case (DifferentialFormula(Less(l,r)),_) => IGeq(IDifferential(apply(r, ddefun(sm))), IDifferential(apply(l, ddefun(sm))))
      case (DifferentialFormula(Equal(l,r)),_) =>
        val (al,ar) = (IDifferential(apply(l,ddefun(sm))), IDifferential(apply(r,ddefun(sm))))
        IAnd(IGeq(al,ar),IGeq(ar,al))
      case (DifferentialFormula(NotEqual(l,r)),_) =>
        val (al,ar) = (IDifferential(apply(l, ddefun(sm))), IDifferential(apply(r, ddefun(sm))))
        IAnd(IGeq(al,ar),IGeq(ar,al))
      case (DifferentialFormula(And(p,q)),_) =>
        val (al,ar) = (apply(DifferentialFormula(p),ddefun(sm)), apply(DifferentialFormula(q),ddefun(sm)))
        IAnd(al,ar)
      case (DifferentialFormula(Or(p,q)),_) =>
        val (al,ar) = (apply(DifferentialFormula(p),ddefun(sm)), apply(DifferentialFormula(q),ddefun(sm)))
        IAnd(al,ar)
      case (_ : UnitFunctional,_) => throw ConversionException("Functionals not supported yet")
    }
  }

  val emptyArgs:List[Itrm] = List.tabulate(m.fArity)(_ =>IConst(0))

  def apply(t:Term,sm:SymMode):Itrm = {
    (t,sm.isDefun) match {
      case (Nothing,_) =>
        val 2 = 1 + 1
        ???
      case (UnitFunctional(name, _space, _sort),true) =>
        val tmp = m.funMap(Right(name))
        // @TODO: This is mad hax because we're getting function <-> functional id collisions
        val fid = tmp//if (tmp == "i1")  {println("Doin first magic: " ); "i2"} else tmp
        IFunction(IDEnum(fid),ISABELLE_IDS.map( i => IVar(IDEnum(i))).toList)
      //IFunctional(IDEnum(m.funMap(Right(name))))
      case (UnitFunctional(name, _space, _sort),_)if sm.base == DefunSubst() || sm.base == FunSubst()=>
        val tmp = m.funMap(Right(name))
        val fid = tmp//if (tmp == "i1")  {println("Doin second magic: " ); "i2"} else tmp
        if(fid == "i5") println("!!! 1")
        IFunctional(IDLeft(IDEnum(fid)))
      //case UnitFunctional(name, _space, _sort) if sm == FunSubst()=> IFunctional(IDLeft(IDEnum(m.funMap(Right(name)))))
      case (UnitFunctional(name, _space, _sort),_) => IFunctional(IDEnum(m.funMap(Right(name))))
      case (DotTerm(s,None),_) => IFunction(IDRight(IDEnum("i1")), emptyArgs)
      case (DotTerm(s,Some(n)),_) => IFunction(IDRight(IDEnum("i"+n)), emptyArgs)
      case (BaseVariable(x,ind,_),_) if (sm.base == DefunSubst() || sm.base == DepredSubst()) =>
        IFunction(IDRight(IDEnum(m.varMap((x,ind)))), emptyArgs)
      case (BaseVariable(x,ind,_),_) => IVar(IDEnum(m.varMap((x,ind))))
      case (DifferentialSymbol(BaseVariable(x,ind,_)),_) if (sm.base == DefunSubst() /*|| sm.base == DepredSubst()*/) => ???
      case (DifferentialSymbol(BaseVariable(x,ind,_)),_) => IDiffVar(IDEnum(m.varMap((x,ind))))
      case (Number(n),_) =>
        if(n.isValidInt) {
          IConst(n.intValue(),sm)
        } else {
          throw ConversionException("Can't convert non-integer literal: " + n)
        }
      case (FuncOf(Function(name,_,_,_,_), arg),_) =>
        val args = IsabelleConverter.detuple(arg)
        val allArgs = padArgs(args, m.fArity)
        val funId =
          // @todo: should depredsubst be here
          if(sm.base == FunSubst() || sm.base == DefunSubst() || sm.base == DepredSubst()) {
            println("Funcof: " + name + " mode: " + sm + " id: " + m.funMap(Left(name)))
            IDLeft(IDEnum(m.funMap(Left(name))))
          } else {
            IDEnum(m.funMap(Left(name)))
          }
        //println("Garbage: " + name + " is " + funId)
        IFunction(funId, allArgs.map(apply(_,sm)))
      case (Times(l,r),_) => ITimes(apply(l,sm),apply(r,sm))
      case (Plus(l,r),_) => IPlus(apply(l,sm),apply(r,sm))
      case (Minus(l,r),_) => IPlus(apply(l,sm),ITimes(apply(r,sm),IConst(-1)))
      case (Neg(t),_) => ITimes(apply(t,sm),IConst(-1))
      case (Differential(t),_) => IDifferential(apply(t,ddefun(sm)))
      case (Divide(l,r),_) => throw ConversionException("Converter currently does not support conversion of divisions")
      case (Power(l,r),_) => throw ConversionException("Converter currently does not support conversion of powers")
    }
  }

  def apply(o:DifferentialProgram,sm:SymMode):IODE = {
    o match {
      case AtomicODE(DifferentialSymbol(BaseVariable(x,ind,_)),e) =>
        IOSing(IDEnum(m.varMap(x,ind)), apply(e,ddefun(sm)))
      case DifferentialProduct(l,r) => IOProd(apply(l,sm),apply(r,sm))
      case DifferentialProgramConst(c,_) if sm.isBananaODE =>
        IOVar(IDEnum(m.odeMap(c)), INBSpace("i1"))
      case DifferentialProgramConst(c,_) => IOVar(IDEnum(m.odeMap(c)), IAllSpace())
    }
  }

  def apply(hp:Program,sm:SymMode):Ihp = {
    hp match {
      case SystemConst(name) => IPvar(IDEnum(m.progMap((name))))
      case ProgramConst(name) => IPvar(IDEnum(m.progMap((name))))
      case Assign(BaseVariable(x,ind,_),e) => IAssign(IDEnum(m.varMap((x,ind))),apply(e,sm))
      case Assign(DifferentialSymbol(BaseVariable(x,ind,_)),e) => IDiffAssign(IDEnum(m.varMap((x,ind))),apply(e,ddefun(sm)))
      case Test(p) => ITest(apply(p,sm))
      case ODESystem(ode,con) => IEvolveODE(apply(ode,sm),apply(con,sm))
      case Choice(a,b) => IChoice(apply(a,sm),apply(b,sm))
      case Compose(a,b) => ISequence(apply(a,sm),apply(b,sm))
      case Loop(a) => ILoop(apply(a,sm))
      case AssignAny(BaseVariable(x,ind,_)) => IAssignRand(IDEnum(m.varMap((x,ind))))
    }
  }

  def apply(seq:Sequent,sm:SymMode):Isequent = {
    (seq.ante.map(apply(_,sm)).toList,seq.succ.map(apply(_,sm)).toList)
  }

  def apply(pr:Provable):Irule = {
    (pr.subgoals.map(apply(_,NonSubst())).toList, apply(pr.conclusion,NonSubst()))
  }

  val INIT_CAPACITY = 1000000

  def scalaExpr:String = {
    val sb = new StringBuilder(INIT_CAPACITY)
    new ScalaBuilder(sb)(apply(pt))
    sb.toString()
  }

  def sexp:String = {
    val sb = new StringBuilder(INIT_CAPACITY)
    new SexpBuilder(sb)(apply(pt))
    sb.toString()
  }

  private def writeObjects(sb:StringBuilder,objName:String, fieldName:String,mainName:String):Unit = {
    val imports = List("Real","Rat","Int","Proof_Checker","Syntax", "Nat", "USubst","Scratch", "Sum_Type")
    // Writing everything out in full detail is quite verbose. Let's give the Scala parser (and anyone debugging) a break by using some abbreviations
    val defs = List(
      "val z:trm[myvars,myvars] = Const(Ratreal(Frct((int_of_integer(0),int_of_integer(1)))))",
      s"val e:(myvars => trm[myvars,myvars]) = {${ISABELLE_IDS.map(i => s"case $i() => z").mkString(" ")}}",
      "val zst:trm[sum[myvars,myvars],myvars] = Const(Ratreal(Frct((int_of_integer(0),int_of_integer(1)))))",
      s"val est:(myvars => trm[sum[myvars,myvars],myvars]) = {${ISABELLE_IDS.map(i => s"case $i() => zst").mkString(" ")}}",
      //trm[sum[myvars,myvars],myvars]
      s"def ns[T]:(myvars => Option[T]) =   {${ISABELLE_IDS.map(i => s"case $i() => None").mkString(" ")}}",
      s"def s(t:trm[myvars,myvars]):(myvars =>trm[myvars,myvars]) = {case ${ISABELLE_IDS.head}() => t ${ISABELLE_IDS.tail.map(i => s"case $i() => z").mkString(" ")}}",
      s"def sst(t:trm[sum[myvars,myvars],myvars]):(myvars =>trm[sum[myvars,myvars],myvars]) = {case ${ISABELLE_IDS.head}() => t ${ISABELLE_IDS.tail.map(i => s"case $i() => zst").mkString(" ")}}"
    )++
    ISABELLE_IDS.map{case id => s"val ${id}mv:myvars = ${id}()"}
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

abstract class SourceBuilder(sb:StringBuilder) {
  def b0(name:String, tparam:Option[String]=None):Unit
  def b1(name:String,f:(() => Unit),tparam:Option[String]=None):Unit
  def b2(name:String,f:(()=> Unit),g:(()=> Unit)):Unit
  def b3(name:String,f:(()=> Unit),g:(()=> Unit),h:(()=> Unit)):Unit
  def b7(name:String,f1:(()=> Unit),f2:(()=> Unit),f3:(()=> Unit),f4:(()=> Unit),f5:(()=> Unit),f6:(()=> Unit),f7:(()=> Unit)):Unit
  def btup(f:(()=>Unit),g:(()=>Unit)):Unit
  def blist[T](l:List[T],f:(T=>Unit)):Unit
  def brat(n:Int):Unit
  def bff[T](l:List[T],f:(T=>Unit)):Unit


  private def emptyElse(args:List[Itrm], f:(() => Unit), sm:SymMode):Unit = {
    if(args.forall({case IConst(0,sm) => true case _ => false})) {
      sm match {case _:FunSubst => sb.++=("est") case _ => sb.++=("e")}
    } else if (args.length >= 1 && args.tail.forall({case IConst(0,sm) => true case _ => false})) {
      val name = sm match {case _:FunSubst => "sst" case _ => "s"}
      b1(name, ()=> apply(args.head))
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
      case IDEnum(n) => sb.++=(n+"mv")
      // final case class Inl[A, B](a: A) extends sum[A, B]
      // final case class Inr[B, A](a: B) extends sum[A, B]
      case IDLeft(id,ltype,rtype) => b1("Inl", ()=>apply(id), Some(ltype+","+rtype))
      case IDRight(id,ltype,rtype) => b1("Inr", ()=>apply(id), Some(rtype+","+ltype))
      case IDUnit() => b0("")
    }
  }

  def apply(t:Itrm):Unit = {
    t match {
      case IVar(x) => b1("Var", () => apply(x))
      case IConst(n,sm:NonSubst) if n == 0 => sb.++=("z")
      case IConst(n,sm:ConSubst) if n == 0 => sb.++=("z")
      case IConst(n,sm) if n == 0 => sb.++=("zst")
      case IConst(n,sm) =>  b1("Const",()=>brat(n))
      case IFunction(n,args) =>
        val sm = n match {case _:IDEnum => NonSubst() case _ => FunSubst()}
        b2("Function",()=>apply(n),()=> emptyElse(args,()=>bff(args,apply(_:Itrm)),sm))
      case IFunctional(n) => b1("Functional",()=>apply(n))
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
      case IAssignRand(x) => b1("AssignRand", ()=>apply(x))
      case IDiffAssign(x,e) => b2("DiffAssign",()=>apply(x),()=>apply(e))
      case ITest(p) => b1("Test",()=>apply(p))
      case IEvolveODE(ode,con) => b2("EvolveODE",()=>apply(ode),()=>apply(con))
      case IChoice(a,b) => b2("Choice", ()=>apply(a),()=>apply(b))
      case ISequence(a,b) => b2("Sequence", ()=>apply(a),()=>apply(b))
      case ILoop(a) => b1("Loop",()=>apply(a))
    }
  }

  def apply(o:IODE):Unit = {
    o match {
      case IOVar(n, sp) => b2("OVar",()=>apply(n),()=>apply(sp))
      case IOSing(x,e) => b2("OSing",()=>apply(x),()=>apply(e))
      case IOProd(o1,o2) => b2("OProd",()=>apply(o1),()=>apply(o2))
    }
  }

  def apply(f:Iformula):Unit = {
    f match {
      case IGeq(t1,t2) => b2("Geq",()=>apply(t1),()=>apply(t2))
      case IProp(name,args) =>
        val sm = name match {case _:IDEnum => NonSubst() case _ => FunSubst()}
        b2("Prop",()=>apply(name),()=>emptyElse(args,()=>bff(args,apply(_:Itrm)),sm))
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
      case IBRenameR(w,r) => b2("BRenameR",()=>apply(w),()=>apply(r))
    }
  }

  def apply(lr:Ilrule):Unit = {
    lr match {
      case IHideL() => b0("HideL")
      case IImplyL() => b0("ImplyL")
      case IAndL() => b0("AndL")
      case INotL() => b0("NotL")
      case IEquivBackwardL() => b0("EquivBackwardL")
      case IEquivForwardL() => b0("EquivForwardL")
      case IEquivL() => b0("EquivL")
      case ICutLeft(fml) => b1("CutLeft", ()=> apply(fml))
      case IBRenameL(w,r) => b2("BRenameL",()=>apply(w),()=>apply(r))
    }
  }

  def apply(ra:IruleApp):Unit = {
    ra match {
      case IURename(w,r) => b2("URename",()=>apply(w),()=>apply(r))
      case IApplyRrule(rr,n) => b2("Rrule", ()=>apply(rr), ()=>nat(n))
      case IApplyLrule(lr,n) => b2("Lrule", ()=>apply(lr), ()=>nat(n))
      case ICloseId(i,j) => b2("CloseId",()=>nat(i),()=>nat(j))
      case ICohide2(i,j) => b2("Cohide2",()=>nat(i),()=>nat(j))
      case ICut(f) => b1("Cut",()=>apply(f))
      case IDIGeqSchema(o, t1, t2) => b3("DIGeqSchema",()=>apply(o),()=>apply(t1),()=>apply(t2))
    }
  }

  def nat(i:Int):Unit = {
    b1("Nata", ()=>sb.++=(i.toString))
  }

  def apply(br:Int):Unit = {
    b1("int_of_integer", ()=>sb.++=(br.toString))
  }

  def apply(ar:IaxiomaticRule):Unit = {
    ar match {
      case ICT() => b0("CT")
      case ICQ() => b0("CQ")
      case ICE() => b0("CE")
      case IG() => b0("G")
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
      case IAassignany() => b0("Aassignany")
      case IAdassign() => b0("Adassign")
      case IAdvar() => b0("Advar")
      case IAdConst() => b0("AdConst")
      case IAdPlus() => b0("AdPlus")
      case IAdMult() => b0("AdMult")
      case IADW() => b0("ADW")
      case IADE() => b0("ADE")
      case IADC() => b0("ADC")
      case IADS() => b0("ADS")
      case IAEquivReflexive() => b0("AEquivReflexive")
      case IADiffEffectSys() => b0("ADiffEffectSys")
      case IADG() => b0("ADG")
      case IAAllElim() => b0("AAllElim")
      case IADiffLinear()  => b0("ADiffLinear")
      case IABoxSplit() => b0("ABoxSplit")
      case IAImpSelf() => b0("AImpSelf")
      case IAcompose() => b0("Acompose")
      case IAconstFcong() => b0("AconstFcong")
      case IAassignEq() => b0("AassignEq")
      case IAdMinus() => b0("AdMinus")
      case IAallInst()  => b0("AallInst")

    }
  }


  def apply(subst:Isubst):Unit = {
    val Isubst(fun,funcl,pred,con,prog,ode,space) = subst
    //Isubst(SFunctions:List[Itrm], SPredicates:List[Iformula], SContexts:List[Iformula], SPrograms:List[Ihp], SODEs:List[IODE])
    b7("subst_exta",
      {()=>{noneElse(fun,()=>bff(fun,apply(_:Option[Itrm])))/*;sb.++=("\n")*/}},
      {()=>{noneElse(funcl,()=>bff(funcl,apply(_:Option[Itrm])));/*sb.++=("\n")*/}},
      {()=>{noneElse(pred,()=>bff(pred,apply(_:Option[Iformula])));/*sb.++=("\n")*/}},
      {()=>{noneElse(con,()=>bff(con,apply(_:Option[Iformula])));/*sb.++=("\n")*/}},
      {()=>{noneElse(prog,()=>bff(prog,apply(_:Option[Ihp])));/*sb.++=("\n")*/}},
      {()=>{noneElse(ode,()=>bff(ode,apply(_:Option[IODE])));/*sb.++=("\n")*/}},
      {()=>{apply(space)}}
    )
  }

  def apply(sp:Ispace):Unit = {
    sp match {
      case IAllSpace() => sb.++=("All")
      case INBSpace(id) => b1("NB", ()=>sb.++=(id))
    }
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
      case IRuleApplication (child, ra,branch) => b3("RuleApp",()=>apply(child),()=>apply(ra),()=>nat(branch))
      case IAxRule(ar) => b1("AxRule", ()=>apply(ar))
      case IPrUSubst(child, subst) => b2("PrUSubst",()=>apply(child),()=>apply(subst))
      case IAx(ax) => b1("Ax", ()=>apply(ax))
      case IFNC(child, seq,ra) => b3("FNC",()=>apply(child),()=>apply(seq),()=>apply(ra))
      case IPro(child,pro) => b2("Pro",()=>apply(child),()=>apply(pro))
      case IStart(seq) => b1("Start",()=>apply(seq))
      case ISub(child, sub, branch) => b3("Sub",()=>apply(child),()=>apply(sub),()=>nat(branch))/*;sb.++=("\n")*/
    }
  }
  }

class ScalaBuilder(sb:StringBuilder) extends SourceBuilder(sb) {
  override def b0(name:String, tparam:Option[String]=None):Unit = {
    sb.++=(name)
    tparam match {
      case None => ()
      case Some(tp) =>
        sb.++=("[")
        sb.++=(tp)
        sb.++=("]")
    }
    sb.++=("()")
  }

  override def b1(name:String,f:(() => Unit),tparam:Option[String]=None):Unit = {
    sb.++=(name)
    tparam match {
      case None => ()
      case Some(tp) =>
        sb.++=("[")
        sb.++=(tp)
        sb.++=("]")
    }
    sb.++=("(")
    f()
    sb.++=(")")
  }

  override  def b2(name:String,f:(()=> Unit),g:(()=> Unit)):Unit = {
    sb.++=(name)
    sb.++=("(")
    f()
    sb.++=(",")
    g()
    sb.++=(")")
  }

  override def b3(name:String,f:(()=> Unit),g:(()=> Unit),h:(()=> Unit)):Unit = {
    sb.++=(name);sb.++=("(");f();sb.++=(",");g();sb.++=(",");h();sb.++=(")")
  }

  override def b7(name:String,f1:(()=> Unit),f2:(()=> Unit),f3:(()=> Unit),f4:(()=> Unit),f5:(()=> Unit),f6:(()=> Unit),f7:(()=> Unit)/*,f7:(()=>Unit)*/):Unit = {
    sb.++=(name);sb.++=("(");f1();sb.++=(",");f2();sb.++=(",");f3();sb.++=(",");f4();sb.++=(",");f5();sb.++=(",");f6();sb.++=(",");f7();sb.++=(",())")
  }

  override def btup(f:(()=>Unit),g:(()=>Unit)):Unit = {
    sb.++=("(");f();sb.++=(",");g();sb.++=(")")
  }

  override def blist[T](l:List[T],f:(T=>Unit)):Unit = {
    sb.++=("List(")
    l match {
      case Nil => ()
      case x::xs =>
        f(x)
        xs.foreach({case y => sb.++=(","); f(y)})
    }
    sb.++=(")")
  }

  override def brat(n:Int):Unit = {
    b1("Ratreal",{()=>b1("Frct",{()=>btup({()=>apply(n)},{()=>apply(1)})})})
  }

  // finite functions over identifiers
  override def bff[T](l:List[T],f:(T=>Unit)):Unit = {
    val cases = l.zip(ISABELLE_IDS)
    sb.++=("{")
    cases.foreach({case(v,id) =>
      sb.++=("case "); sb.++=(id); sb.++=("() => ");f(v);sb.++=(" ")
    })
    sb.++=("}")
  }

}

class SexpBuilder(sb:StringBuilder) extends SourceBuilder(sb) {
  override def b0(name:String, tparam:Option[String]=None):Unit = {
    sb.++=("(")
    sb.++=(name)
    sb.++=(")")
  }

  override def b1(name:String,f:(() => Unit),tparam:Option[String]=None):Unit = {
    sb.++=("(")
    sb.++=(name)
    sb.++=(" ")
    f()
    sb.++=(")")
  }

  override  def b2(name:String,f:(()=> Unit),g:(()=> Unit)):Unit = {
    sb.++=("(")
    sb.++=(name)
    sb.++=(" ")
    f()
    sb.++=(" ")
    g()
    sb.++=(")")
  }

  override def b3(name:String,f:(()=> Unit),g:(()=> Unit),h:(()=> Unit)):Unit = {
    sb.++=("(");sb.++=(name);sb.++=(" ");f();sb.++=(" ");g();sb.++=(" ");h();sb.++=(")")
  }

  override def b7(name:String,f1:(()=> Unit),f2:(()=> Unit),f3:(()=> Unit),f4:(()=> Unit),f5:(()=> Unit),f6:(()=> Unit),f7:(()=>Unit)):Unit = {
    sb.++=("(");sb.++=(name);sb.++=(" ");f1();sb.++=(" ");f2();sb.++=(" ");f3();sb.++=(" ");f4();sb.++=(" ");f5();sb.++=(" ");f6();sb.++=(" ");f7();sb.++=(")")
  }

  override def btup(f:(()=>Unit),g:(()=>Unit)):Unit = {
    sb.++=("(");f();sb.++=(" ");g();sb.++=(")")
  }

  override def blist[T](l:List[T],f:(T=>Unit)):Unit = {
    sb.++=("(")
    l match {
      case Nil => ()
      case x::xs =>
        f(x)
        xs.foreach({case y => sb.++=(" "); f(y)})
    }
    sb.++=(")")
  }

  override def brat(n:Int):Unit = {
    b1("Ratreal",{()=>b1("Frct",{()=>btup({()=>apply(n)},{()=>apply(1)})})})
  }

  // finite functions over identifiers
  override def bff[T](l:List[T],f:(T=>Unit)):Unit = {
    blist(l,f)
  }

  override def apply(id:ID):Unit = {
    id match {
      case IDEnum(n) => sb.++=(n)
      case IDLeft(id,ltype,rtype) => b1("Inl", ()=>apply(id), Some(ltype+","+rtype))
      case IDRight(id,ltype,rtype) => b1("Inr", ()=>apply(id), Some(rtype+","+ltype))
      case IDUnit() => b0("")
    }
  }

}

