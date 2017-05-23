package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.ExpressionTraversal.{ExpressionTraversalFunction, StopTraversal}
import edu.cmu.cs.ls.keymaerax.core.{Variable, _}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.{NoProofTermProvable, ProvableSig}

import scala.collection.immutable

/**
  * Created by bbohrer on 12/2/16.
  */
object Kaisar {
  abstract class Resource
  case class ProgramVariable(a:Variable) extends Resource
  case class FactVariable(p:Variable) extends Resource

  type ProofStep = (List[Resource], BelleExpr)
  type Proof = (Formula, SP)
  type VBase = String
  type TimeName = String

  /* Here we make horrible abuses of the existing expression syntax in order to avoid defining it ourselves.
  * Everywhere we refer to an expression, it is either:
  * (a) a pattern, if we are comparing the expression against some known expression
  * (b) an extended term, if we are constructing a new expression from scratch
  *
  * An extended term can refer to definitions introduced through previous pattern-matches and refer to nominal terms
  * of previous states.
  * The nominal of theta at time t is written as a function application t(theta).
  * Bound term variables are functions f(), bound program variables are program constants "a", and predicate constants
  * are unit predicationals P().
  *
  * Patterns allow all the constructs of extended terms, and additionally existential variables which are like those in
  * extended terms except with an underscore appended to the name. They also allow the following constructs:
  * - Positive variable occurrence, with predicate application p(x1,...,xn)
  * - Negative variable occurrence, with predicates applied to *negated variables* -x1, ...., -xn
  * - union, intersection, and negation patterns on *terms only* due to technical reasons at the moment:
  *    function union(e1,e2), inter(e1,e2), neg(e).
  * */
  abstract class RuleSpec
  case class RIdent (x:String) extends RuleSpec
  case class RBAssign(hp:Assign) extends RuleSpec
  case class RBConsequence(fml:Formula) extends RuleSpec
  case class RBCase() extends RuleSpec
  case class RBAssume(x:Variable,fml:Formula) extends RuleSpec
  case class RBSolve(t:Variable,fmlT:Formula,dc:Variable,fmlDC:Formula,sols:List[(Variable,Formula)]) extends RuleSpec
  case class RBAssignAny(x:Variable)extends RuleSpec
  case class RBInv(ip:IP) extends RuleSpec

  case class RDAssign(hp:Assign) extends RuleSpec
  case class RDConsequence(fml:Formula) extends RuleSpec
  case class RDCase(a:Program) extends RuleSpec
  case class RDAssert(x:Variable,fml:Formula) extends RuleSpec
  case class RDSolve(t:Variable,fmlT:Formula,dc:Variable,fmlDC:Formula,sols:List[(Variable,Formula)]) extends RuleSpec
  case class RDAssignAny(x:Variable, xVal:Term) extends RuleSpec

  abstract class Method
  case class Simp() extends Method
  case class Auto() extends Method
  case class RCF() extends Method
  case class CloseId() extends Method

  case class UP(use:List[Either[Expression,FP]], method:Method)

  abstract class IP
  case class Inv(fml:Formula, pre:SP, inv:SP, tail:IP) extends IP
  case class Ghost(gvar:Variable, gterm:Term, ginv:Formula, pre:SP, inv:SP, tail:IP) extends IP
  case class Finally(tail:SP) extends IP

  abstract class FP
  case class FPat(e:Expression) extends FP
  case class FMP(fp1: FP, fp2:FP) extends FP
  case class FInst(fp:FP, t:Term) extends FP

  abstract class SP
  case class Show (phi:Formula, proof: UP) extends SP
  case class Let (pat:Expression, e:Expression, tail:SP) extends SP
  case class Note (x:Variable, fp:FP, tail: SP) extends SP
  case class Have (x:Variable, fml:Formula, sp:SP, tail: SP) extends SP
  case class BRule (r:RuleSpec, tails: List[SP]) extends SP
  case class PrintGoal(msg:String, sp:SP) extends SP
  case class State (st:TimeName, tail: SP) extends SP
  case class Run (a:VBase, hp:Program, tail:SP) extends SP


  abstract class HistChange
  case class HCAssign(hp:Assign) extends HistChange {
    def rename(from: Variable, to:Variable):HCAssign = {
      val (name, e) = (hp.x, hp.e)
      HCAssign(Assign(if(name == from) to else name, URename(from,to)(e)))
    }
  }
  case class HCRename(baseName:BaseVariable, permName:BaseVariable, defn:Option[AntePos] = None) extends HistChange {assert (baseName.name == permName.name && baseName.index.isEmpty)}
  case class HCTimeStep(ts:TimeName) extends HistChange

  // map:Map[VBase,List[(TimeName,Either[Term,Unit])]]
  // todo: need to rename "current x" for clarities
  case class History (steps:List[HistChange]){
    def hasTimeStep(ts:TimeName):Boolean = { steps.exists({case hcts: HCTimeStep => hcts.ts == ts case _ => false})}
    def advance(t:TimeName):History = {History(HCTimeStep(t)::steps)}
    def now:TimeName = steps.collectFirst({case HCTimeStep(ts) => ts}).get
    def nextIndex(x:VBase):Int = {steps.count{case HCRename(b,_,_) => b.name == x case _ => false}}
    def update(x:VBase, e:Term):History = {
      History(HCAssign(Assign(Variable(x), e))::steps)
    }
    def updateRen(baseName:BaseVariable, permName:BaseVariable, defn:AntePos):History = {
      History(HCRename(baseName, permName, Some(defn))::steps)
    }
    private def partBefore[A](xs:List[A], f:(A => Boolean)):(List[A],List[A]) = {
      xs match {
        case Nil => (Nil, Nil)
        case (x::xs) =>
          if(f(x)) {
            (Nil, x::xs)
          } else {
            partBefore(xs,f) match {
              case (xs,ys) => (x::xs, ys)
            }
          }
      }
    }

    private def partAfter[A](xs:List[A], f:(A => Boolean)):(List[A],List[A]) = {
      partBefore(xs, f) match {
        case (xs, y::ys) => (xs ++ List(y), ys)
        case _ => ???
      }
    }

    def update(x:VBase):History = {
      // TODO: Optimize by keeping count of renames per variable
      val from = Variable(x)
      val isRename:(HistChange => Boolean)={case HCRename(bn, _, _) => bn.name==x}
      val to = Variable(x, Some(steps.count(isRename)))
      val (recent, old) = partBefore(steps, isRename)
      val hist = recent.map{case ch : HCAssign => ch.rename(from, to) case x => x} ++ old
      History(HCRename(from, to)::hist)
    }

    def replay(changes:List[HCAssign], e:Term):Term = {
      import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._
      changes.foldLeft(e)({case (e:Term,hc) => e.replaceFree(hc.hp.x,hc.hp.e)})
    }

    def resolve(x:VBase, theSteps:List[HistChange] = steps):Term = {
      val isThisRename:(HistChange => Boolean)={case HCRename(from,to, _) => from.name == x case _ => false}
      val isThisAssign:(HistChange => Boolean)={case HCAssign(Assign(xx,_)) => xx.name == x case _ => false}
      val (changes, postChange) = partBefore(theSteps,isThisRename)
      //TODO: might be bug val fullName = postChange match {case Nil => Variable(x) case ((y:HCRename)::ys) => y.permName case _ => ???}
      val fullName = Variable(x)
      val xChanges = changes.filter(isThisAssign)
      replay(xChanges.asInstanceOf[List[HCAssign]], fullName)
    }

    def resolve(x:VBase, at:TimeName):Term = {
      val isThisTime:(HistChange => Boolean)={case HCTimeStep(ts) => ts == at case _ => false}
      val (_, relevant) = partAfter(steps, isThisTime)
      resolve(x, relevant)
    }

    def eval(e:Term, at:Option[TimeName] = None):Term = {
      ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
        override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] =
          e match {
            case v: Variable => Right(at match {case Some(at) => resolve(v.name, at) case None => resolve(v.name)})
            case _ => Left(None)
          }
      }, e).get
    }
  }
  object History {
    var empty = new History(List(HCTimeStep("init")))
  }

  case class Context (gmap:Map[Variable,Position], defmap:Map[VBase, Expression]){
    def concat(other: Context): Context = Context(gmap.++(other.gmap), defmap.++(other.defmap))
    def add(x:Variable, at:AntePos):Context = {
      Context(gmap.+((x,at)),defmap)
    }
    def inter(other: Context): Context = Context(gmap.filter({case (k,v) => other.gmap(k) == v}), defmap.filter({case (k,v) => other.defmap(k) == v}))
    def usubst:USubst = {
      USubst(defmap.toList.toIndexedSeq.map({
        case(name, e: DifferentialProgram) => SubstitutionPair(DifferentialProgramConst(name), e)
        case(name, e: Program) => SubstitutionPair(ProgramConst(name), e)
        case(name, e: Term) => SubstitutionPair(FuncOf(Function(name, domain = Unit, sort = Real), Nothing), e)
        case(name, e: Formula) => SubstitutionPair(PredOf(Function(name, domain = Unit, sort = Bool), Nothing), e)
        case _ => ???
      }))
    }

  }
  object Context {
    var empty = new Context(Map(),Map())
    def ofDef(base:VBase, e:Expression):Context = {
      new Context(Map(), Map(base -> e))
    }
  }


  def eval(method:Method, pr:Provable):Provable = {
    val e:BelleExpr =
      method match {
        case Simp() => SimplifierV3.fullSimpTac()
        case Auto() => TactixLibrary.master()
        case RCF() => TactixLibrary.QE()
        case CloseId() => TactixLibrary.closeId
      }
    interpret(e, pr)
  }

  def eval(up:UP, h:History, c:Context, g:Provable):Provable = {
    val use = up.use
    val method =  up.method
    val pats = use.filter({case Left(_) => true case _ => false}).map({case Left(x) => x case _ => ???})
    val fps = use.filter({case Right(_) => true case _ => false}).map({case Right(x) => x case _ => ???})
    val seq = g.subgoals.head
    val ante = seq.ante
    val fprvs = fps.foldLeft[(List[Provable], immutable.IndexedSeq[Formula])]((Nil, ante))({case ((prvs:List[Provable], ante2:immutable.IndexedSeq[Formula]), fp:FP) =>
        val prv:Provable = eval(fp, h, c, ante2)
        (prv::prvs, ante2 ++ immutable.IndexedSeq(prv.conclusion.ante.head))
      })._1
    val withFacts:Provable = fprvs.foldLeft[Provable](g)({case (pr:Provable, next:Provable) => pr(Cut(next.conclusion.succ.head),0)(next,1)})
    val inds:immutable.IndexedSeq[Int] = withFacts.subgoals.head.ante.zipWithIndex.filter({case (f,i) => pats.exists({case pat => doesMatch(pat, f)})}).map({case (f,i) => i}).reverse
    val pr = inds.foldLeft[Provable](withFacts)({case (pr2:Provable,i:Int) => pr2(HideLeft(AntePos(i)),0)})
    eval(method, pr)
  }

  def interpret(e:BelleExpr, pr:Provable):Provable = {
    SequentialInterpreter()(e, BelleProvable(NoProofTermProvable(pr))) match {
      case BelleProvable(result,_) => result.underlyingProvable
    }
  }

  // TODO: Do we need impI
  //val frules = List("ande1", "ande2", "andi", "ore", "ori1", "ori2", "ne", "ni", "existsi")
  val propAxioms:Map[String,Formula] = Map(
    "ande1" -> "p() & q() -> p()".asFormula,
    "ande2" -> "p() & q() -> q()".asFormula,
    "andi" -> "p() -> q() -> p() & q()".asFormula,
    "ore" -> "(p() | q()) -> (p() -> r()) -> (q() -> r()) -> r()".asFormula,
    "ori1" -> "p() -> (p() | q())".asFormula,
    "ori2" -> "q() -> (p() | q())".asFormula,
    "ne" -> "!p() -> p() -> q()".asFormula,
    "ni" -> "(p() -> false) -> !p()".asFormula,
    "existsi" -> "p(f()) -> \\exists x p(x)".asFormula
    // todo: add all inst
  )

  private def doTravel(h:History):ExpressionTraversalFunction = {
    new ExpressionTraversalFunction() {
      override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] =
        e match {
          case v: Variable =>
            Right(h.eval(v))
          case FuncOf(Function(fname,_,_,_,_), arg) =>
            if(h.hasTimeStep(fname)) {
              Right(h.eval(arg, Some(fname)))
            } else {
              Left(None)
            }
          case _ => Left(None)
        }
    }
  }
  // TODO: Support time-travel
  def expand(e:Term, h:History, c:Context):Term       = {c.usubst(ExpressionTraversal.traverse(doTravel(h), e).get)}
  def expand(e:Formula, h:History, c:Context):Formula = {
    val traveled = ExpressionTraversal.traverse(doTravel(h), e)
    c.usubst(traveled.get)
  }
  def expand(e:Program, h:History, c:Context):Program = {c.usubst(ExpressionTraversal.traverse(doTravel(h), e).get)}
  def expand(e:Expression, h:History, c:Context):Expression = {
    e match {
      case t:Term => expand(t,h,c)
      case f:Formula => expand(f,h,c)
      case p:Program => expand(p,h,c)
    }
  }

  def eval(fp:FP, h:History, c:Context, ante:immutable.IndexedSeq[Formula]):Provable = {
    fp match {
      case FPat(BaseVariable(id, _,_)) if propAxioms.keySet.contains(id.toLowerCase) =>
        val fml = propAxioms(id)
        val pr:Provable = Provable.startProof(Sequent(ante, immutable.IndexedSeq(fml)))
        val pr2:Provable = pr(CoHideRight(SuccPos(0)),0)
        interpret(prop, pr2)
      case FMP(fp1, fp2) =>
        val pr1:Provable = eval(fp1, h, c, ante)
        val pr2:Provable = eval(fp2, h, c, ante)
        assert(pr1.conclusion.succ.nonEmpty && pr2.conclusion.succ.nonEmpty)
        (pr1.conclusion.succ.head, pr2.conclusion.succ.head) match {
          case (Imply(p1,q), p2) =>
            try {
              val subst:Subst = UnificationMatch(p1, p2)
              val q2=subst(q)
              val seq = Sequent(ante, immutable.IndexedSeq(q2))
              val argPos = AntePos(ante.length)
              val impPos = AntePos(ante.length+1)
              val pr1b = pr1(subst.usubst)
              // todo: positioning
              Provable.startProof(seq) (Cut(p2),0)(pr2,1)  (Cut(Imply(p2,q2)),0)(pr1b,1) (ImplyLeft(impPos),0) (Close(argPos,SuccPos(0)),0) (Close(AntePos(0),SuccPos(0)),0)
            } catch {
              case e : UnificationException => throw new Exception("proposition mismatch in modus ponens", e)
            }
          case _ => throw new Exception("proposition mismatch in modus ponens")
         }
      case FInst(fp1, term) =>
        val t2 = expand(term,h, c)
        val pr1:Provable = eval(fp1, h, c, ante)
        assert(pr1.conclusion.succ.nonEmpty)
        val goal = pr1.conclusion.succ.head
        goal  match {
          case (Forall(xs,q)) =>
            try {
              val subst:Subst = UnificationMatch(AxiomInfo("all instantiate").provable.conclusion.succ.head.asInstanceOf[Imply].left, goal)
              val pair = SubstitutionPair(FuncOf(Function("f", None, Real, Real), DotTerm()), t2)
              val subst2 = USubst(immutable.IndexedSeq.concat(immutable.IndexedSeq[SubstitutionPair](pair), subst.usubst.subsDefsInput))
              val q2=subst2(q)
              val p2:Provable=subst2(AxiomInfo("all instantiate").provable).underlyingProvable
              val seq = Sequent(ante, immutable.IndexedSeq(q2))
              val impPos = AntePos(ante.length)
              val allPos = AntePos(ante.length+1)
              val pr1b = pr1(subst.usubst)
              Provable.startProof(seq) (Cut(p2.conclusion.succ.head), 0)(p2,1) (Cut(pr1.conclusion.succ.head),0)(pr1,1) (ImplyLeft(impPos), 0) (Close(allPos,SuccPos(0)),0) (Close(AntePos(0),SuccPos(0)),0)
            } catch {
              case e : UnificationException => throw new Exception("proposition mismatch in all instantiation", e)
            }
          case _ => throw new Exception("proposition mismatch in all instantiation")
        }
    }
  }

/* @requires  provable is
*  [a](P_j -> ... -> P_n -> Q) |- [a]Q
*  -----------------------------------
*                   [a]Q
*
*  facts is ([a]P_j, ..., [a]P_n)
*  @ensures provable is proved.
* */
def polyK(pr:Provable, facts:List[Provable], onSecond:Boolean = false, impAtEnd:Boolean = false): Provable = {
  val doPrint = false
  facts match {
    case Nil => /*NoProofTermProvable(pr) */ interpret(DebuggingTactics.debug("foobar", doPrint = doPrint) & close, pr)
    case fact::facts =>
      val pos = if(impAtEnd) {pr.subgoals(if(onSecond) 1 else 0).ante.length-1} else 0
      val Box(a,Imply(p,q)) = pr.subgoals(if(onSecond) 1 else 0).ante(pos)
      val e:BelleExpr =
        cut(Imply(Box(a,Imply(p,q)),Imply(Box(a,p),Box(a,q)))) <(
          DebuggingTactics.debug("a", doPrint = doPrint) &
          /* Use */ implyL(-(pos + 2)) <(/* use */ debug("b") & close,
            DebuggingTactics.debug("c", doPrint = doPrint) &
          implyL(-(pos+2)) <( DebuggingTactics.debug("d", doPrint = doPrint) & hide(1) & DebuggingTactics.debug("d", doPrint = doPrint) &  useAt(NoProofTermProvable(fact), PosInExpr(Nil))(1)
            , DebuggingTactics.debug("d1", doPrint = doPrint) & nil )
        ),
          DebuggingTactics.debug("e", doPrint = doPrint) &
          /* show */ cohideR(2) & useAt("K modal modus ponens", PosInExpr(Nil))(1,Nil)) &
      hide(-1) &
          DebuggingTactics.debug("before recur", doPrint = doPrint)
      polyK(interpret(if(onSecond) { nil <(nil, e)} else {e}, pr), facts)
  }
}

def collectLoopInvs(ip: IP):(List[Formula], List[SP], List[SP], IP) = {
  ip match {
    case Inv(fml, pre, inv, tail) =>
      val (f,p,i,t) = collectLoopInvs(tail)
      (fml::f, pre::p, inv::i, t)
    case _ : Finally => (Nil, Nil, Nil, ip)
    case _ => ???
  }
}

def eval(ip:IP, h:History, c:Context, g:Provable, nInvs:Int = 0):Provable = {
  val gg = interpret(andL('L)*, g)
  val seq = gg.subgoals(0)
  val ante = seq.ante
  val goal = seq.succ.head
  (ip, goal) match {
    // TODO: Names to refer the invariants
    // TODO: Update invariant names for the inductive step what with the vacuation
    case (nextInv : Inv, Box(Loop(a),post)) => {
      // Inv (fml: Formula, pre: SP, inv: SP, tail: IP)
      val (fmls, pres, invs, lastTail) = collectLoopInvs(nextInv)
      val conj = fmls.reduceRight(And)
      def baseCase(fmlPres:List[(Formula,SP)], done:List[Formula] = Nil):BelleExpr = {
        fmlPres match {
          case Nil => ???
          case (fml, pre:SP)::Nil =>
            val preSeq = Sequent(ante, immutable.IndexedSeq(fml))
            println("base case useat base nohiding " + (done.length) + ": " + preSeq)
            val tail = eval(pre, h, c, Provable.startProof(preSeq))
            DebuggingTactics.debug("base", doPrint = true) & useAt(NoProofTermProvable(tail), PosInExpr(Nil))(1)
          case (fml, pre:SP)::fps =>
            val preSeq = Sequent(ante, immutable.IndexedSeq(fml))
            println("Ind case useat ind nohiding " + (done.length) + ": " + preSeq)
            val tail = eval(pre, h, c, Provable.startProof(preSeq))
            val e1 = useAt(NoProofTermProvable(tail), PosInExpr(Nil))(1)
            val e2 = baseCase(fps, fml::done)
            andR(1) <(DebuggingTactics.debug("left", doPrint = true) & e1, DebuggingTactics.debug("right", doPrint = true) & e2)
        }
      }
      def indCase(fmlPres:List[(Formula,SP)], done:immutable.IndexedSeq[Formula] = immutable.IndexedSeq()):BelleExpr = {
        fmlPres match {
          case Nil => ???
          case (fml, inv:SP)::Nil =>
            val invSeq = Sequent(done ++ immutable.IndexedSeq(fml), immutable.IndexedSeq(Box(a,fml)))
            println("Ind case useat base hiding " + (ante.length - (done.length + 1)) + ": " + invSeq)
            val e = hideL('Llast)*(ante.length - (done.length + 1))
            val tail = eval(inv, h, c, Provable.startProof(invSeq))
            DebuggingTactics.debug("preHide icubh", doPrint = true) & e & DebuggingTactics.debug("postHide", doPrint = true) & useAt(NoProofTermProvable(tail), PosInExpr(Nil))(1)
          case (fml, pre:SP)::fps =>
            val invSeq = Sequent(done ++ immutable.IndexedSeq(fml), immutable.IndexedSeq(Box(a,fml)))
            println("Ind case useat inductive hiding " + (ante.length - done.length) + ": " + invSeq)
            val hide = hideL('Llast)*(ante.length - (done.length + 1))
            val tail = NoProofTermProvable(eval(pre, h, c, Provable.startProof(invSeq)))
            val e1 = DebuggingTactics.debug("preHide", doPrint = true) &  hide & DebuggingTactics.debug("postHide", doPrint = true)& useAt(tail, PosInExpr(Nil))(1)
            val e2 = indCase(fps, done ++ immutable.IndexedSeq(fml))
            boxAnd(1) & andR(1) <(e1, e2)
        }
      }
      val e:BelleExpr = DLBySubst.loop(conj)(1) <( DebuggingTactics.debug("base case", doPrint = true) & baseCase(fmls.zip(pres)), nil, (andL('L)*) & DebuggingTactics.debug("inductive case", doPrint = true) & indCase(fmls.zip(invs)))
      /*val invSeq: immutable.IndexedSeq[Formula] = ante.takeRight(nInvs).map({ case Box(_, p) => p })
      val invAnte:immutable.IndexedSeq[Formula] = invSeq ++ immutable.IndexedSeq(fml)
      val preSeq = Sequent(ante, immutable.IndexedSeq(fml))
      val prPre: Provable = eval(pre, h, c, Provable.startProof(preSeq))
      val indSeq:Sequent =  Sequent(invAnte, immutable.IndexedSeq(Box(a, fml)))
      val prInv: Provable = eval(inv, h,c, Provable.startProof(indSeq))
      val bigImp:Formula = invSeq.foldRight[Formula](Imply(fml,Box(a,post)))({case (acc,p) => Imply(p,acc)})
      val impRs: BelleExpr = List.tabulate(invSeq.length)({case _ => implyR(1)}).foldLeft(nil)({case (e1,e2) => e1 & e2})
      //  P & [a*](P -> [a]P) -> [a*]P
      //DLBySubst.loop(invariant, nil)
      val e:BelleExpr =
        cut(Box(Loop(a),fml)) <(nil, hideR(1) & DLBySubst.loop(fml, nil)(1) <(
          useAt(NoProofTermProvable(prPre), key = PosInExpr(Nil))(1),
          close,
          useAt(NoProofTermProvable(prInv), key = PosInExpr(Nil))(1))
        )*/

      //val e:BelleExpr = // cut(bigImp) <(nil, hideR(1) & impRs & DebuggingTactics.debug("The thing", doPrint = true) & useAt(NoProofTermProvable(prInv))(1))
//        cut(Box(Loop(a),fml)) <(nil, hideR(1) & cut(bigImp) <(nil, hideR(1) & impRs & DebuggingTactics.debug("The thing", doPrint = true) & useAt(NoProofTermProvable(prInv))(1)))
      val pr:Provable = interpret(e, gg)
      println("Done first step of interpreting thing: " + pr.prettyString)
      // polyK(pr, invSeq.map{case fml => interpret(TactixLibrary.close, Provable.startProof(Sequent(invSeq,immutable.IndexedSeq(fml))))}.toList)
      eval(lastTail, h, c, pr, nInvs+1)
    }
    case (Inv (fml: Formula, pre: SP, inv: SP, tail: IP), Box(ODESystem(ode,constraint),post)) => {
      //TODO: deal with time and context management
      val e:BelleExpr = dC(fml)(1) <(nil, DebuggingTactics.debug("Blah", doPrint = true) &  dI()(1))
      val pr = interpret(e, g)
      eval(tail, h,c,pr, nInvs+1)
    }
    case (Ghost (gvar: Variable, gterm: Term, ginv: Formula, pre: SP, inv: SP, tail: IP), _) => ???
    // TODO: Hardcore polyK with vacuity
    case (Finally(tail: SP), Box(ODESystem(ode,constraint),post)) =>
      //TODO: Context management
      eval(tail, h, c, interpret(dW(1) & implyR(1), g))
    case (Finally (tail: SP),post) =>  {
      eval(tail, h, c, g)
      /*val invSeq: immutable.IndexedSeq[Formula] = ante.takeRight(nInvs).map({ case Box(_, p) => p })
      val indSeq:Sequent =  Sequent(invSeq, immutable.IndexedSeq(post))
      val prEnd:Provable = eval(tail, h, c, Provable.startProof(indSeq))
      val bigImp:Formula = invSeq.foldRight[Formula](post)({case (acc,p) => Imply(p,acc)})
      val bigBox:Formula = Box(Loop(a), bigImp)
      println("*******\n" + prEnd.prettyString + "\n****")
      val impRs: BelleExpr = List.tabulate(invSeq.length)({case _ => implyR(1)}).foldLeft(nil)({case (e1,e2) => e1 & e2})
      val e:BelleExpr = cut(bigBox) <(DebuggingTactics.debug("barFoo", doPrint = true), hideR(1) & abstractionb(1) & cohideR(1) & (allR(1)*)  & DebuggingTactics.debug("Foobar", doPrint = true) & impRs  & useAt(NoProofTermProvable(prEnd), key = PosInExpr(Nil))(1))
      val pr:Provable = interpret(e, g)
      println("|*******\n" + pr.prettyString + "\n****")
      val subPrs = invSeq.map{case fml => interpret(TactixLibrary.close, Provable.startProof(Sequent(pr.subgoals.head.ante,immutable.IndexedSeq(Box(Loop(a),fml)))))}.toList
      subPrs.map({case sp => println("||*******\n" + sp.prettyString + "\n****")})
      polyK(pr, subPrs, impAtEnd = true)*/
    }
  }
}

case class BadBranchingFactorException(had:Int,wanted:Int) extends Exception

def assertBranches(had:Int, wanted:Int):Unit =  {if(had != wanted) throw BadBranchingFactorException(had,wanted)}

def eval(brule:RuleSpec, sp:List[SP], h:History, c:Context, g:Provable):Provable = {
  val sequent = g.subgoals.head
  val goal = sequent.succ.head
  goal match {
    case (Box(Compose(a,b),p)) =>
      eval(brule, sp, h, c, interpret(useAt("[;] compose")(1), g))
    case (Box(Test(_),p)) =>
      eval(brule, sp, h, c, interpret(useAt("[?] test")(1), g))
    case _ =>
      (brule, goal) match {
          // TODO: More readable match error
        case (RBAssign(hp:Assign), Box(Assign(x,theta),p)) if hp.x == x =>
          assertBranches(sp.length, 1)
          // TODO: Renaming of stuff
          try {
            val hh = h.update(hp.x.name, theta)
            eval(sp.head, hh, c, interpret(useAt("[:=] assign")(1), g))
          } catch {
            case _ : Throwable =>
              val gg = interpret(DLBySubst.assignEquality(1), g)
              val defn:Equal = gg.subgoals.head.ante.last.asInstanceOf[Equal]
              val base = defn.left.asInstanceOf[BaseVariable]
              val hh = h.updateRen(Variable(base.name), Variable(base.name, Some(h.nextIndex(base.name))), AntePos(gg.subgoals.head.ante.length-1))
              eval(sp.head, hh, c, gg)
          }
        case (RBConsequence(fml:Formula), Box(Compose(a,b),p)) =>
          assertBranches(sp.length, 2)
          // TODO: How many assumptions stick around?
          val seq1:Sequent = Sequent(sequent.ante, immutable.IndexedSeq(Box(a,fml)) ++ sequent.succ.tail)
          val seq2:Sequent = Sequent(immutable.IndexedSeq(fml), immutable.IndexedSeq(Box(a,p)))
          val pr1:Provable = eval(sp(0),h,c,Provable.startProof(seq1))
          val pr2:Provable = eval(sp(1),h,c,Provable.startProof(seq2))
          // TODO: Not right, need a cut somewhere
          val prr:Provable = interpret(TactixLibrary.monb, g)
          prr(pr1,0)(pr2,0)
        case (RBCase(), Box(Choice(a,b),p)) =>
          assertBranches(sp.length, 2)
          val seq1:Sequent = Sequent(sequent.ante, immutable.IndexedSeq(Box(a,p)) ++ sequent.succ.tail)
          val seq2:Sequent = Sequent(sequent.ante, immutable.IndexedSeq(Box(b,p)) ++ sequent.succ.tail)
          val pr1:Provable = eval(sp(0),h,c,Provable.startProof(seq1))
          val pr2:Provable = eval(sp(1),h,c,Provable.startProof(seq2))
          // TODO: Not right, need a cut somewhere
          val prr:Provable = interpret(TactixLibrary.choiceb & andR(1), g)
          prr(pr1,0)(pr2,0)
        case (RBAssume(x:Variable,fml:Formula),Imply(p,q)) =>
          assertBranches(sp.length, 1)
          val newPos = AntePos(sequent.ante.length)
          val cc:Context = c.add(x,newPos)
          eval(sp.head, h, cc, g(ImplyRight(SuccPos(0)),0))
        case (RBSolve(t:Variable,fmlT:Formula,dc:Variable,fmlDC:Formula,sols:List[(Variable,Formula)]),Box(ODESystem(ode,q),p)) => ???
        case (RBAssignAny(x:Variable),Box(AssignAny(y),p)) if x == y =>
          assertBranches(sp.length, 1)
          val hh = h.update(x.name)
          eval(sp.head, hh, c, interpret(TactixLibrary.randomb(1) & allR(1), g))
        case (RBInv(ip:IP), _) =>
          assertBranches(sp.length, 0)
          eval(ip, h, c, g)
        case (RIdent (x:String), _) => ???
        case (RDAssign(hp:Assign), _)  => ???
        case (RDConsequence(fml:Formula), _)  => ???
        case (RDCase(a:Program), _) => ???
        case (RDAssert(x:Variable,fml:Formula), _) => ???
        case (RDSolve(t:Variable,fmlT:Formula,dc:Variable,fmlDC:Formula,sols:List[(Variable,Formula)]), _) => ???
        case (RDAssignAny(x:Variable, xVal:Term), _)  => ???

      }
  }
}

def eval(sp:SP, h:History, c:Context, g:Provable):Provable = {
  assert(g.subgoals.length == 1, "Expected 1 subgoal, got: " + g.subgoals.length)
  assert(g.subgoals.head.succ.nonEmpty)
  val goal = g.subgoals.head.succ.head
  sp match {
    case Show (phi:Formula, proof: UP)  =>
      val expanded = expand(phi,h,c)
      val cc = pmatch(expanded, goal)
      val ccc = c.concat(cc)
      eval(proof, h, ccc, g)
    case Let (pat:Expression, e:Expression, tail:SP) =>
      val cc = pmatch(expand(pat,h,c), e)
      eval(tail, h, cc, g)
    case Note (x:Variable, fp:FP, tail: SP)  =>
      val fpr:Provable = eval(fp, h, c, g.subgoals.head.ante)
      assert(fpr.conclusion.succ.nonEmpty)
      val size = fpr.conclusion.ante.size
      val newPos = AntePos(size)
      val res:Formula = fpr.conclusion.succ.head
      eval(tail, h, c.add(x,newPos), fpr(Cut(res), 0)(fpr,1))
    case Have (x:Variable, fml:Formula, sp:SP, tail: SP)  =>
      val fmlExpanded = expand(fml,h,c)
      val seq = Sequent(g.subgoals.head.ante, immutable.IndexedSeq(fmlExpanded))
      val prIn = Provable.startProof(seq)
      val prOut = eval(sp, h, c, prIn)
      val size = prOut.conclusion.ante.size
      val newPos = AntePos(size)
      eval(tail,h,c.add(x,newPos), g(Cut(fmlExpanded),0)(HideRight(SuccPos(0)),1)(prOut,1))
    case BRule (r:RuleSpec, tails: List[SP]) => eval(r,tails,h,c,g)
    case State (st:TimeName, tail: SP) => eval(tail,h.advance(st),c,g)
    case PrintGoal(msg,tail) =>
      println("====== " + msg + " ======\n" + g.prettyString)
      eval(tail, h,c,g)
    case Run (a:VBase, hp:Program, tail:SP) => ???
  }
}

  /*- union, intersection, and negation patterns on *terms only* due to technical reasons at the moment:
  *    function union(e1,e2), inter(e1,e2), neg(e). */
def collectVarPat(t:Term):Option[List[BaseVariable]] = {
  t match {
    case (Pair(x, y)) =>
      (collectVarPat(x), collectVarPat(y)) match {
        case (Some(vs1), Some(vs2)) => Some(vs1 ++ vs2)
        case _ => None
      }
    case (v : BaseVariable) => Some(List(v))
    case _ => None
  }
}

def collectNegVarPat(t:Term):Option[List[BaseVariable]] = {
  t match {
    case (Pair(x, y)) =>
      (collectVarPat(x), collectVarPat(y)) match {
        case (Some(vs1), Some(vs2)) => Some(vs1 ++ vs2)
        case _ => None
      }
    case Neg(v : BaseVariable) => Some(List(v))
    case _ => None
  }
}

case class PatternMatchError(msg:String) extends Exception { override def toString:String = "Pattern Match Error: " + msg}

/* TODO: I think these need to be filled in with gammas first */
def pmatch(pat:Expression, e:Expression):Context = {
  def patExn(pat:Expression, e:Expression, additional:String = "N/A"):PatternMatchError = { PatternMatchError("Expected expression " + e + " to match pattern " + pat + " Additional message?: " + additional)}
  val exn:PatternMatchError = patExn(pat, e)
  def atom(e1:Expression, e2:Expression, additional:String = "N/A") = {
    if(e1 == e2) { Context.empty } else { throw new PatternMatchError("Expected atomic expression " + e2 + " to match atomic pattern " + e1 + " Additional message?: " + additional) }
  }
  pat match {
    case PredOf(Function("p", _, _, _, _), args) if collectVarPat(args).isDefined || collectNegVarPat(args).isDefined =>
      (collectVarPat(args), collectNegVarPat(args)) match {
        case (Some(pos), _) =>
          val posvs:SetLattice[Variable] = SetLattice(pos.toSet.asInstanceOf[Set[Variable]])
          val fvs:SetLattice[Variable] = StaticSemantics.freeVars(e)
          if (posvs.subsetOf(fvs)) {
            Context.empty
          } else {
            throw patExn(pat, e, "Bad variable occurrence")
          }
        case (_, Some(neg)) =>
          val negvs:SetLattice[Variable] = SetLattice(neg.toSet.asInstanceOf[Set[Variable]])
          val fvs:SetLattice[Variable] = StaticSemantics.freeVars(e)
          if (negvs.intersect(fvs).isEmpty) {
            Context.empty
          } else {
            throw patExn(pat, e, "Bad negative variable occurrence")
          }
        case _ => throw patExn(pat, e, "Invalid variable occurrence pattern syntax")
      }
    case PredOf(Function("union", _, _, _, _), Pair(pat1, pat2)) =>
      try { pmatch(pat1,e) }
      catch {case _ : Throwable => pmatch(pat2,e) }
    case PredOf(Function("inter", _, _, _, _), Pair(pat1, pat2)) =>
      pmatch(pat1,e).inter(pmatch(pat2,e))
    case PredOf(Function("neg", _, _, _, _) , pat1) =>
      try { pmatch(pat1,e); throw patExn(pat1, e, "Pattern should not have matched but did: " + pat1.prettyString)}
      catch {case _ : Throwable => Context.empty }
    case FuncOf(Function("f", _, _, _, _), args) =>
      (collectVarPat(args), collectNegVarPat(args)) match {
        case (Some(pos), _) =>
          val posvs:SetLattice[Variable] = SetLattice(pos.toSet.asInstanceOf[Set[Variable]])
          val fvs:SetLattice[Variable] = StaticSemantics.freeVars(e)
          if (posvs.subsetOf(fvs)) {
            Context.empty
          } else {
            throw patExn(pat, e, "Bad variable occurrence")
          }
        case (_, Some(neg)) =>
          val negvs:SetLattice[Variable] = SetLattice(neg.toSet.asInstanceOf[Set[Variable]])
          val fvs:SetLattice[Variable] = StaticSemantics.freeVars(e)
          if (negvs.intersect(fvs).isEmpty) {
            Context.empty
          } else {
            throw patExn(pat, e, "Bad negative variable occurrence")
          }
        case _ => throw patExn(pat, e, "Invalid variable occurrence pattern syntax")
      }
    case FuncOf(Function("union", _, _, _, _), Pair(pat1, pat2)) =>
      try { pmatch(pat1,e) }
      catch {case _ : Throwable => pmatch(pat2,e) }
    case FuncOf(Function("inter", _, _, _, _), Pair(pat1, pat2)) =>
      pmatch(pat1,e).inter(pmatch(pat2,e))
    case FuncOf(Function("neg", _, _, _, _) , pat1) =>
      try { pmatch(pat1,e); throw PatternMatchError("Pattern should not have matched but did: " + pat1.prettyString)}
      catch {case _ : Throwable => Context.empty }
    case FuncOf(Function("wild", _, _, _, _), pat) => Context.empty
    case PredOf(Function("wild", _, _, _, _), pat) => Context.empty
    case PredicationalOf(Function("wild", _, _, _, _), pat) => Context.empty
    case UnitPredicational("wild", _) => Context.empty
    case BaseVariable(vname, _, _) =>
      if(vname.last == '_') {
        Context.ofDef(vname.dropRight(1), e)
      } else if (pat == e) {
        Context.empty
      } else {
        throw exn
      }
    case FuncOf(fn: Function, Nothing) =>
      if(fn.name.last == '_') {
        Context.ofDef(fn.name.dropRight(1), e)
      } else if (pat == e) {
        Context.empty
      } else {
        throw exn
      }
    case UnitFunctional(name: String, _, _) =>
      if(name.last == '_') {
        Context.ofDef(name.dropRight(1), e)
      } else if (pat == e) {
        Context.empty
      } else {
        throw exn
      }
    case DifferentialProgramConst(name: String,  _) =>
      if(name.last == '_') {
        Context.ofDef(name.dropRight(1), e)
      } else if (pat == e) {
        Context.empty
      } else {
        throw exn
      }
    case ProgramConst(name: String) =>
      if(name.last == '_') {
        Context.ofDef(name.dropRight(1), e)
      } else if (pat == e) {
        Context.empty
      } else {
        throw exn
      }
    case SystemConst(name: String) =>
      if(name.last == '_') {
        Context.ofDef(name.dropRight(1), e)
      } else if (pat == e) {
        Context.empty
      } else {
        throw exn
      }
    case PredicationalOf(fn: Function, _) =>
      if(fn.name.last == '_') {
        Context.ofDef(fn.name.dropRight(1), e)
      } else if (pat == e) {
        Context.empty
      } else {
        throw exn
      }
    case PredOf(fn: Function, _) =>
      if(fn.name.last == '_') {
        Context.ofDef(fn.name.dropRight(1), e)
      } else if (pat == e) {
        Context.empty
      } else {
        throw exn
      }
    case UnitPredicational(name:String, _) =>
      if(name.last == '_') {
        Context.ofDef(name.dropRight(1), e)
      } else if (pat == e) {
        Context.empty
      } else {
        throw exn
      }
    case _ =>
      (pat, e) match {
        case (e1: DifferentialSymbol, e2: DifferentialSymbol) => atom(e1, e2)
        case (e1: Number, e2: Number) => atom(e1, e2)
        case (e1: DotTerm, e2: DotTerm) => atom(e1, e2)
        case (Nothing, Nothing) => Context.empty
        case (True, True) => Context.empty
        case (False, False) => Context.empty
        case (e1: Plus, e2: Plus) =>
          pmatch(e1.left, e2.left).concat(pmatch(e1.right,e2.right))
        case (e1: Minus, e2: Minus) =>
          pmatch(e1.left, e2.left).concat(pmatch(e1.right,e2.right))
        case (e1: Times, e2: Times) =>
          pmatch(e1.left, e2.left).concat(pmatch(e1.right,e2.right))
        case (e1: Divide, e2: Divide) =>
          pmatch(e1.left, e2.left).concat(pmatch(e1.right,e2.right))
        case (e1: Power, e2: Power) =>
          pmatch(e1.left, e2.left).concat(pmatch(e1.right,e2.right))
        case (e1: Pair, e2: Pair) =>
          pmatch(e1.left, e2.left).concat(pmatch(e1.right,e2.right))
        case (e1: Equal, e2: Equal) =>
          pmatch(e1.left, e2.left).concat(pmatch(e1.right,e2.right))
        case (e1: NotEqual, e2: NotEqual) =>
          pmatch(e1.left, e2.left).concat(pmatch(e1.right,e2.right))
        case (e1: GreaterEqual, e2: GreaterEqual) =>
          pmatch(e1.left, e2.left).concat(pmatch(e1.right,e2.right))
        case (e1: Greater, e2: Greater) =>
          pmatch(e1.left, e2.left).concat(pmatch(e1.right,e2.right))
        case (e1: LessEqual, e2: LessEqual) =>
          pmatch(e1.left, e2.left).concat(pmatch(e1.right,e2.right))
        case (e1: Less, e2: Less) =>
          pmatch(e1.left, e2.left).concat(pmatch(e1.right,e2.right))
        case (e1: And, e2: And) =>
          pmatch(e1.left, e2.left).concat(pmatch(e1.right,e2.right))
        case (e1: Or, e2: Or) =>
          pmatch(e1.left, e2.left).concat(pmatch(e1.right,e2.right))
        case (e1: Imply, e2: Imply) =>
          pmatch(e1.left, e2.left).concat(pmatch(e1.right,e2.right))
        case (e1: Equiv, e2: Equiv) =>
          pmatch(e1.left, e2.left).concat(pmatch(e1.right,e2.right))
        case (e1: Box, e2: Box) =>
          pmatch(e1.program, e2.program).concat(pmatch(e1.child,e2.child))
        case (e1: Diamond, e2: Diamond) =>
          pmatch(e1.program, e2.program).concat(pmatch(e1.child,e2.child))
        case (e1: Choice, e2: Choice) =>
          pmatch(e1.left, e2.left).concat(pmatch(e1.right,e2.right))
        case (e1: Compose, e2: Compose) =>
          pmatch(e1.left, e2.left).concat(pmatch(e1.right,e2.right))
        case (e1: DifferentialProduct, e2: DifferentialProduct) =>
          pmatch(e1.left, e2.left).concat(pmatch(e1.right,e2.right))
        case (e1: Forall, e2: Forall) =>
          if(e1.vars != e2.vars) { throw exn }
          else { pmatch(e1.child, e2.child) }
        case (e1: Exists, e2: Exists) =>
          if(e1.vars != e2.vars) { throw exn }
          else { pmatch(e1.child, e2.child) }
        case (e1: Assign, e2: Assign) => atom(e1,e2)
        case (e1: AssignAny, e2: AssignAny) => atom(e1,e2)
        case(e1:Test, e2:Test) => pmatch(e1.cond, e2.cond)
        case(e1:ODESystem, e2:ODESystem) => pmatch(e1.ode,e2.ode).concat(pmatch(e1.constraint,e2.constraint))
        case(e1:AtomicODE, e2:AtomicODE) =>
          if (e1.xp != e2.xp) { throw exn }
          else { pmatch(e1.e, e2.e)}
        case(e1:Neg, e2:Neg) => pmatch(e1.child,e2.child)
        case(e1:Differential, e2:Differential) => pmatch(e1.child,e2.child)
        case(e1:Not, e2:Not) => pmatch(e1.child,e2.child)
        case(e1:DifferentialFormula, e2:DifferentialFormula) => pmatch(e1.child,e2.child)
        case(e1:Loop, e2:Loop) => pmatch(e1.child,e2.child)
        case(e1:Dual, e2:Dual) => pmatch(e1.child,e2.child)
      }
  }
}
def doesMatch(pat:Expression, e:Expression):Boolean = {try {pmatch(pat, e); true} catch {case _:Throwable => false}}


/* TODO: Better to skip *all* skippable formulas, but that makes recovering the original theorem
     /*def add(a:Variable, hp:Program): History = {
       val nextTime = vmap.size
       History(vmap.+((a,(nextTime,hp))), tmap.+((nextTime,(a,hp))))
     }

     def time(a:ProgramVariable):Int = vmap(a.a)._1
     def tmax:Int = tmap.size-1
     def extent(tp:(Int, Formula,Provable)):Int = {
       var (t, phi,_) = tp
       var fv = StaticSemantics(phi).fv
       while (tmap.contains(t) && fv.intersect(StaticSemantics(tmap(t)._2).bv).isEmpty) {
         t = t + 1
       }
       t
     }*/
      * more work, so do it later. */
/*def extend(phi:Formula,tmin:Int,tmax:Int):Formula = {
  var t = tmax
  var p = phi
  while(t >= tmin) {
    p = Box(tmap(t)._2, p)
    t = t -1
  }
  p
}*/ /*
  def apply(p:FactVariable):(Int, Formula,Provable) = xmap(p.p)
  def add(a:Variable, phi:Formula, pr:Provable,time:Int): Context = {
    val nextTime = xmap.size
    Context(xmap.+((a,(time,phi,pr))),fmap.+((phi,pr)))
  }
  def findProvable(fml:Formula):Provable = fmap(fml)*/
/*private def min(seq:Seq[Int]):Int =
  seq.fold(Int.MaxValue)((x,y) => Math.min(x,y))

def interpret(e:BelleExpr, pr:Provable):ProvableSig = {
  SequentialInterpreter()(e, BelleProvable(NoProofTermProvable(pr))) match {
    case BelleProvable(result,_) => result
  }
}
def cutEZ(c: Formula, t: BelleExpr): BelleExpr = cut(c) & Idioms.<(skip, /* show */ t & done)

def implicate(fs:List[Formula],acc:Formula):Formula = {
   fs.reverse.foldLeft(acc)((acc,f) => Imply(f,acc))
}

def unboxProg(f:Formula, n:Int):(List[Program], Formula) = {
  (f, n) match {
    case (_, 0) => (Nil, f)
    case (Box(a,p), _) =>
      val (as:List[Program], p2:Formula) = unboxProg(p,n-1)
      (a::as, p2)
  }
}

def unbox(f:Formula, n:Int):Formula = {
  unboxProg(f,n)._2
}

def composeProgs(progs:List[Program]):Program = {
  val (prog::progs1) = progs//.reverse
  progs1.foldLeft(prog)((a,b) => Compose(a,b))
}

def composify(progs:List[Program],fml:Formula):Formula = {
  Box(composeProgs(progs), fml)
}

def reboxify(progs:List[Program],fml:Formula):Formula = {
  progs.reverse.foldLeft(fml)((p,a) => Box(a,p))
}

def transboxify(progs:List[Program],fml:Formula):Formula = {
  val Box(_,p) = fml
  reboxify(progs, p)
}
*/
/*
def doGreatProof(userProof:ProvableSig, a:Program, maybeFacts:List[Formula], factProofs:List[ProvableSig], result:Formula): ProvableSig = {
  val pr = Provable.startProof(Box(a,result))
  val e = cutEZ(Box(a,implicate(maybeFacts,result)), debug("wat") & hide(1) & useAt(userProof,PosInExpr(Nil))(1))
  val pr2 = interpret(e,pr).underlyingProvable
  polyK(pr2, factProofs)
}

def eval(hist: History, ctx: Context, step:Statement):(History,Context) = {
  step match {
    case Run(a,hp) => (hist.add(a,hp), ctx
    case Show(x,phi,(resources, e)) =>
      val (progs:Seq[ProgramVariable], facts:Seq[FactVariable]) =
        resources.partition({case _: ProgramVariable => true case _:FactVariable => false})
      val tmax = hist.tmax
      val tphi = min(facts.map{case p:FactVariable => hist.extent(ctx(p))})
      val ta = min(progs.map{case a:ProgramVariable => hist.time(a)})
      val tmin = min(Seq(tphi,ta, tmax))
      val assms:Seq[Formula] = facts.map{case p:FactVariable =>
        val tp = ctx(p)
        hist.extend(tp._2, tmin, tp._1)
      }
      val concl:Formula = hist.extend(phi, 0, tmax)
      val pr:Provable = Provable.startProof(Sequent(assms.toIndexedSeq, collection.immutable.IndexedSeq(concl)))
      var concE = e
      var t = tmin-1
      while (t >= 0) {
        concE = TactixLibrary.G(1) & concE
        t = t -1
      }
      val addedProvable:Provable =
        tmin match {
          case 0 | -1 =>
            SequentialInterpreter()(concE, BelleProvable(NoProofTermProvable(pr))) match {
              case BelleProvable(result, _) =>
                assert(result.isProved)
                result.underlyingProvable
            }
          case _ =>
            val boxen = tmin
            val (as, p) = unboxProg(concl, boxen)
            val fmls = assms.map(f => unbox(f, boxen)).toList
            val toProve = composify(as, implicate(fmls,p))
            val seqifyTac = debug ("hmm") & G(1) & List.fill(assms.size)(implyR(1)).fold(nil)((e1,e2) => e1 & e2) & debug ("hmm2")
            val userProof = interpret(seqifyTac & e, Provable.startProof(toProve))
            val factProofs:List[ProvableSig] = facts.map{case p:FactVariable =>
                NoProofTermProvable(ctx(p)._3)
            }.toList
            val giveUp = Int.MaxValue
            val breadth = 1
            val facterProofs:List[ProvableSig] = factProofs.map{case (p:ProvableSig) =>
              val pr = p.underlyingProvable
              val (as1, p1) = unboxProg(p.conclusion.succ(0), boxen)
              val pr2 = Provable.startProof(composify(as1,p1))
              val e = debug("a") & chase(breadth, giveUp, ((e:Expression) => e match {case Box(Compose(_,_),_) => List("[;] compose") case _ => Nil}))(1) & debug ("b") & useAt(p, PosInExpr(Nil))(1) & debug("c")
              val newProof = interpret(e, pr2)
              newProof
            }

            val foo = doGreatProof(userProof, composeProgs(as), fmls, facterProofs, p)
            val bestProof = Provable.startProof(transboxify(as,foo.underlyingProvable.conclusion.succ(0)))
            val bestE = debug("a") & chase(breadth, giveUp, ((e:Expression) => e match {case Box(Compose(_,_),_) => List("[;] compose") case _ => Nil}))(1) & debug ("b") & useAt(foo, PosInExpr(Nil))(1) & debug("c")
            val lastProof = interpret(e, bestProof)
            lastProof.underlyingProvable
        }

      (hist, ctx.add(x,concl,addedProvable,hist.tmax))
  }
}

def eval(hist: History, ctx: Context, steps:List[Statement]):(History,Context) = {
  steps match {
    case (Nil) => (hist, Context.empty)
    case (step :: steps) =>
      var AD1 = eval(hist, ctx, step)
      var AD2 = eval(AD1._1, AD1._2, steps)
      (AD2._1, AD1._2.concat(AD2._2))
  }
}

def eval(pf:Proof):Provable = {
  val (fml, steps) = pf
  val (h,c) = eval(History.empty,Context.empty, steps)
  val pr:Provable = c.findProvable(fml)
  assert(pr.conclusion == Sequent(collection.immutable.IndexedSeq(), collection.immutable.IndexedSeq(fml)))
  assert(pr.isProved)
  pr
}*/
}
