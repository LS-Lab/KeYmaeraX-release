package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.infrastruct.ExpressionTraversal.{ExpressionTraversalFunction, StopTraversal}
import edu.cmu.cs.ls.keymaerax.core.{Variable, _}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary.{existsR, _}
import edu.cmu.cs.ls.keymaerax.btactics.arithmetic.speculative.ArithmeticSpeculativeSimplification
import edu.cmu.cs.ls.keymaerax.infrastruct._
import edu.cmu.cs.ls.keymaerax.btactics.macros._
import DerivationInfoAugmentors._
import edu.cmu.cs.ls.keymaerax.parser.Declaration
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.{ElidingProvable, ProvableSig}

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

  /*
  * Important notes on implementation: The implementation is absolutely a prototype and a work in progress, though the
  * examples and case study we have implemented definitely demonstrate its applicability for non-trivial proofs.
  * Major TODOs for implementation:
  *  - At present we lack a parser. Our tests are performed with a deep embedding which is then fed to the parser.
  *    This gives a clear separation between the Kaisar language and Scala, which is what's important for validating the
  *    language, but obviously not desirable for production use.
  *  - We reuse existing parsers and data structures everywhere we can, which means reusing their concrete syntax too.
  *    Therefore until we write a parser much of the concrete syntax will be uglier than the abstract syntax in the paper.
  *  - Features which are not yet used in any proof are unimplemented, namely liveness proofs.
  *  However, even given these caveats, this implementation and its tests validate the claim that Kaisar can be
  *  implemented and prove non-trivial models.
  *
  * Assorted notes:
  *
  * - One of the main implementation hurdles which is more evident here than in the writeup is that both the prover core
  * and the unstructured Bellerophon tactics language do everything with numerical indices for formula positions in
  * contexts. Our implementation reduces named contexts to indexed contexts outside of the core and thus does a lot of
  * position-munging. This all makes the low-level proofs very difficult to write/read/debug/understand - you may not
  * want to read them.
  *
  * - Note also that there are far more cases in the grammar of dL as it appears in KeYmaera X than you see in the paper.
  *  This is because the KeYmaera X core is based on the calculus of:
  *  "Andre Platzer. [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 59(2), pp. 219-266, 2017."
  *  And even then has a number of constructs needed in practice but not mentioned there.
  *
  *
  *
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

  // Backward-chaining box rules
  abstract class RuleSpec
  case class RIdent (x:String) extends RuleSpec
  case class RBAssign(hp:Assign) extends RuleSpec
  case class RBMid(x:Variable, fml:Formula) extends RuleSpec
  case class RBCase(pats:List[Expression]) extends RuleSpec
  case class RBCaseImplyL(p:Variable, patp:Formula, q:Variable, patq:Formula) extends RuleSpec
  case class RBCaseOrL(x1:Variable, pat1:Expression, x2:Variable, pat2:Expression) extends RuleSpec
  case class RBCaseOrR(x1:Variable, x2:Variable) extends RuleSpec
  case class RBAssume(x:Variable,fml:Formula) extends RuleSpec
  case class RBSolve(t:Variable,fmlT:Formula,dc:Variable,fmlDC:Formula,sols:List[(Variable,Formula)]) extends RuleSpec
  case class RBAssignAny(x:Variable)extends RuleSpec
  case class RBInv(ip:IP) extends RuleSpec
  // Added to make some of the proofs easier
  case class RBAbbrev(xphi:Variable, x:Variable, theta:Term) extends RuleSpec

  // Backward-chaining diamond rules
  case class RDAssign(hp:Assign) extends RuleSpec
  case class RDMid(fml:Formula) extends RuleSpec
  case class RDCase(a:Program) extends RuleSpec
  case class RDAssert(x:Variable,fml:Formula) extends RuleSpec
  case class RDSolve(t:Variable,fmlT:Formula,dc:Variable,fmlDC:Formula,sols:List[(Variable,Formula)]) extends RuleSpec
  case class RDAssignAny(x:Variable, xVal:Term) extends RuleSpec

  // Unstructured proof methods
  abstract class Method
  case class Simp() extends Method
  case class Auto() extends Method
  case class RCF() extends Method
  case class SmartQE() extends Method
  case class CloseId() extends Method

  case class UP(use:List[Either[Expression,FP]], method:Method)

  // Invariant proof
  abstract class IP
  case class Inv(x:Variable, fml:Formula, pre:SP, inv:SP, tail:IP) extends IP
  case class Ghost(gvar:Variable, gterm:Term, ginv:Formula, x0:Term, pre:SP, inv:SP, tail:IP) extends IP
  case class Finally(tail:SP) extends IP

  // Forward proof
  abstract class FP
  case class FPat(e:Expression) extends FP
  case class FMP(fp1: FP, fp2:FP) extends FP
  case class FInst(fp:FP, t:Term) extends FP

  // Structured proof
  abstract class SP
  case class Show(phi:Formula, proof: UP) extends SP
  case class SLet(pat:Expression, e:Expression, tail:SP) extends SP
  case class FLet(x:VBase, arg:VBase, e:Expression, tail:SP) extends SP
  case class Note(x:Variable, fp:FP, tail: SP) extends SP
  case class Have(x:Variable, fml:Formula, sp:SP, tail: SP) extends SP
  case class BRule(r:RuleSpec, tails: List[SP]) extends SP
  case class State (st:TimeName, tail: SP) extends SP
  case class Run (a:VBase, hp:Program, tail:SP) extends SP
  // For debugging
  case class PrintGoal(msg:String, sp:SP) extends SP


  // History records hr
  abstract class HistChange
  case class HCAssign(hp:Assign) extends HistChange {
    def rename(from: Variable, to:Variable):HCAssign = {
      val (name, e) = (hp.x, hp.e)
      HCAssign(Assign(if(name == from) to else name, URename(from,to)(e)))
    }
  }
  case class HCRename(baseName:BaseVariable, permName:BaseVariable, defn:Option[AntePos] = None) extends HistChange {assert (baseName.name == permName.name && baseName.index.isEmpty)}
  case class HCTimeStep(ts:TimeName) extends HistChange

  // helpers
  def patIdent(e:Expression):Option[String] = {
    e match {
      case PredOf(Function(id, _, _, _, _), _)  => Some(id)
      case FuncOf(Function(id, _, _, _, _), _) => Some(id)
      case PredicationalOf(Function(id, _, _, _, _), _) => Some(id)
      case UnitPredicational(id, _) => Some(id)
      case BaseVariable(id, _, _) => Some(id)
      case UnitFunctional(id, _, _) => Some(id)
      case ProgramConst(id, _) => Some(id)
      case SystemConst(id, _) => Some(id)
      case _ => None
    }
  }
  def patChild(e:Expression):Option[Expression] = {
    e match {
      case PredOf(Function(id, _, _, _, _), x)  => Some(x)
      case FuncOf(Function(id, _, _, _, _), x) => Some(x)
      case PredicationalOf(Function(id, _, _, _, _), x) => Some(x)
      case _ => None
    }
  }
  // static traces H
  // map:Map[VBase,List[(TimeName,Either[Term,Unit])]]
  case class History (steps:List[HistChange]) {
    def hasTimeStep(ts: TimeName): Boolean = {
      steps.exists({ case hcts: HCTimeStep => hcts.ts == ts case _ => false })
    }

    def advance(t: TimeName): History = {
      History(HCTimeStep(t) :: steps)
    }

    def now: TimeName = steps.collectFirst({ case HCTimeStep(ts) => ts }).get

    def nextIndex(x: VBase): Int = {
      steps.count { case HCRename(b, _, _) => b.name == x case _ => false }
    }

    def update(x: VBase, e: Term): History = {
      History(HCAssign(Assign(Variable(x), e)) :: steps)
    }

    def updateRen(baseName: BaseVariable, permName: BaseVariable, defn: AntePos): History = {
      History(HCRename(baseName, permName, Some(defn)) :: steps)
    }

    private def partBefore[A](xs: List[A], f: (A => Boolean)): (List[A], List[A]) = {
      xs match {
        case Nil => (Nil, Nil)
        case (x :: xs) =>
          if (f(x)) {
            (Nil, x :: xs)
          } else {
            partBefore(xs, f) match {
              case (xs, ys) => (x :: xs, ys)
            }
          }
      }
    }

    private def partAfter[A](xs: List[A], f: (A => Boolean)): (List[A], List[A]) = {
      partBefore(xs, f) match {
        case (xs, y :: ys) => (xs ++ List(y), ys)
        case (xs, Nil) => (xs ,Nil)
      }
    }

    def update(x: VBase): History = {
      // TODO: Optimize by keeping count of renames per variable
      val from = Variable(x)
      val isRename: (HistChange => Boolean) = {
        case HCRename(bn, _, _) => bn.name == x
        case _ => false
      }
      val to = Variable(x, Some(steps.count(isRename)))
      val (recent, old) = partBefore(steps, isRename)
      val hist = recent.map { case ch: HCAssign => ch.rename(from, to) case x => x } ++ old
      History(HCRename(from, to) :: hist)
    }

    def replay(changes: List[HCAssign], e: Term): Term = {
      import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
      changes.foldLeft(e)({ case (e: Term, hc) => e.replaceFree(hc.hp.x, hc.hp.e) })
    }

    def resolveHelp(x: VBase, renSteps: List[HistChange] = Nil, subSteps: List[HistChange] = steps): Term = {
      val isThisRename: (HistChange => Boolean) = {
        case HCRename(from, to, _) => from.name == x
        case _ => false
      }
      val isThisAssign: (HistChange => Boolean) = {
        case HCAssign(Assign(xx, _)) => xx.name == x
        case _ => false
      }
      val rs = renSteps.filter(isThisRename)
      val ss = subSteps.filter(isThisAssign)
      val fullName = rs.reverse match {case (HCRename(_,to,_)::_) => to case _ => Variable(x)}
      val xChanges = ss.filter(isThisAssign)
      val xxChanges = if(xChanges.length  > 1 ) {xChanges.take(1)} else xChanges
      replay(xxChanges.asInstanceOf[List[HCAssign]], fullName)
    }

    def resolve(x: VBase, at: Option[TimeName]): Term = {
      at match {
        case Some(att) =>
          val isThisTime: (HistChange => Boolean) = {
            case HCTimeStep(ts) => ts == att
            case _ => false
          }
          // TODO: Part before or after?
          val (renSteps, subSteps) = partAfter(steps, isThisTime)
          resolveHelp(x, renSteps, subSteps)
        case None =>
          val isOtherTime:(HistChange => Boolean) = {
            case _ : HCTimeStep => true
            case _ => false
          }
          val (subSteps, _) = partBefore(steps, isOtherTime)
          resolveHelp(x, Nil, subSteps)
      }

    }

    def eval(e: Term, at: Option[TimeName] = None): Term = {
      ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
        override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] =
          e match {
            case v: Variable => Right(resolve(v.name, at))
            case _ => Left(None)
          }
      }, e).get
    }

    def eval(e:Formula, at:Option[TimeName]):Formula = {
      ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
        override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] =
          e match {
            case v: Variable => Right(resolve(v.name, at))
            case _ => Left(None)
          }
      }, e).get
    }
  }
  object History {
    var empty = new History(List(HCTimeStep("init")))
  }

  // Named contexts \Gamma
  case class Context (gmap:Map[Variable,Position], defmap:Map[VBase, Expression], fundefmap:Map[VBase,(VBase,Expression)]){
    def concat(other: Context): Context = Context(gmap.++(other.gmap), defmap.++(other.defmap), fundefmap.++(other.fundefmap))
    def addFun(x:VBase,arg:VBase,e:Expression):Context = Context(gmap,defmap,fundefmap.+((x,(arg,e)))  )
    def add(x:Variable, at:AntePos):Context = {
      Context(gmap.+((x,at)),defmap, fundefmap)
    }
    def inter(other: Context): Context = Context(gmap.filter({case (k,v) => other.gmap(k) == v}), defmap.filter({case (k,v) => other.defmap(k) == v}), fundefmap.filter({case (k,v) => other.fundefmap(k) == v}))
    def usubst:USubst = {
      USubst(defmap.toList.toIndexedSeq.map({
        case(name, e: DifferentialProgram) => SubstitutionPair(DifferentialProgramConst(name), e)
        case(name, e: Program) => SubstitutionPair(ProgramConst(name), e)
        case(name, e: Term) => SubstitutionPair(FuncOf(Function(name, domain = Unit, sort = Real), Nothing), e)
        case(name, e: Formula) => SubstitutionPair(PredOf(Function(name, domain = Unit, sort = Bool), Nothing), e)
        case _ => ???
      }))
    }
    def hasAssm(ident:String):Boolean = gmap.contains(Variable(ident))
    def getAssm(ident:String, ante:immutable.IndexedSeq[Formula]):Formula =
      try {
        ante(gmap(Variable(ident)).checkAnte.index0)
      } catch {
        case e: IndexOutOfBoundsException =>
          val 2 = 1 + 1
          ???
      }
    def getDef(ident:String):Expression = {
      if(defmap.contains(ident)) {defmap(ident)}
      else if (ident.last == '_' && defmap.contains(ident.dropRight(1))) {
        defmap(ident.dropRight(1))
      } else {
        throw new Exception("Tried to get invalid definition for " + ident )
      }
    }
    def stripNominal(nom:VBase, e:Expression, at:Option[TimeName]):Expression = {
      val f:ExpressionTraversalFunction =
        new ExpressionTraversalFunction() {
          override def preT(p: PosInExpr, t: Term): Either[Option[StopTraversal], Term] = {
            t match {
              case FuncOf(Function(fname,_,_,_,_),args) if fname == nom =>
                at match {
                  case Some(atTime) => Right(FuncOf(Function(atTime, domain = Real, sort = Real), args.asInstanceOf[Term]))
                  case None => Right(args.asInstanceOf[Term])
                }
              case _ =>
                Left(None)
            }
          }
          override def preF(p:PosInExpr, f:Formula): Either[Option[StopTraversal], Formula] = {
            f match {
              case PredicationalOf(Function(fname,_,_,_,_),args) if fname == nom =>
                at match {
                  case Some(atTime) => Right(PredicationalOf(Function(atTime, domain = Bool, sort = Bool), args.asInstanceOf[Formula]))
                  case None => Right(args.asInstanceOf[Formula])
                }
              case _ =>
                Left(None)
            }
          }
        }
      e match {
        case ee: Term => ExpressionTraversal.traverse(f, ee).get
        case ee: Formula => ExpressionTraversal.traverse(f, ee).get
        case ee: Program => ExpressionTraversal.traverse(f, ee).get
        //case ee: ODESystem => ???
      }
    }
    def getFunDef(ident:String, at:Option[TimeName]):Expression = {
      val (tVar, body) =
        if(fundefmap.contains(ident)) { fundefmap(ident) }
        else if(ident.last == '_' && fundefmap.contains(ident.dropRight(1))) {
          fundefmap(ident.dropRight(1))
        } else {
          throw new Exception("Tried to get invalid function definition for " + ident )
        }
      stripNominal(tVar,body, at)
    }
    def hasDef(ident:String):Boolean = {
      defmap.contains(ident) || (ident.last == '_' && defmap.contains(ident.dropRight(1)))
    }
    def hasFunDef(ident:String):Boolean = {
      fundefmap.contains(ident) || (ident.last == '_' && fundefmap.contains(ident.dropRight(1)))
    }
  }
  object Context {
    var empty = new Context(Map(),Map(), Map())
    def ofDef(base:VBase, e:Expression):Context = {
      new Context(Map(), Map(base -> e), Map())
    }
  }

  // proof-checking
  def eval(method:Method, pr:Provable):Provable = {
    val e:BelleExpr =
      method match {
        case Simp() => SimplifierV3.fullSimpTac()
        case Auto() => TactixLibrary.master()
        case RCF() => TactixLibrary.QE
        case SmartQE() => ArithmeticSpeculativeSimplification.speculativeQE
        case CloseId() => TactixLibrary.id
      }
    interpret(e, pr)
  }

  // proof-checking
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

    def matchesAssm(i:Int,pat:Expression):Boolean = {
      (patIdent(pat), patChild(pat)) match {
        case (None, _) => false
          // TODO: Faster: do only index cmp
        case (Some("neg"), Some(p)) =>
          !matchesAssm(i, p)
        case (Some(id), _) =>
          val hasOne = c.hasAssm(id)
          hasOne && c.getAssm(id,ante) == ante(i)
      }
    }
    val inds:immutable.IndexedSeq[Int] = withFacts.subgoals.head.ante.zipWithIndex.filter({case (f,i) => !pats.exists({case pat =>
      val dm = doesMatch(pat, f,c, ante)
      dm })}).map({case (f,i) => i}).reverse
    //TODO: Optimize the default case
    val indss = if(use.isEmpty) { immutable.IndexedSeq[Int]()} else {inds}
    val pr = indss.foldLeft[Provable](withFacts)({case (pr2:Provable,i:Int) => pr2(HideLeft(AntePos(i)),0)})
    eval(method, pr)
  }

  def interpret(e:BelleExpr, pr:Provable):Provable = {
    BelleInterpreter(e, BelleProvable.plain(ElidingProvable(pr, Declaration(Map.empty)))) match {
      case BelleProvable(result, _) => result.underlyingProvable
    }
  }

  // TODO: Do we need impI
  // built-in forward-chaining rules
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

  private def doTravel(h:History,c:Context, at:Option[TimeName]):ExpressionTraversalFunction = {
    new ExpressionTraversalFunction() {
      override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] =
      e match {
          case v: Variable =>
            Right(h.resolve(v.name,at))
          // Note: if there's a nominal but it's not in h, this isn't necessarily an error - we use this when expanding FLet's for the first time during definition to make sure
          // argument references stick around and don't get expanded
          case FuncOf(Function(fname,_,_,_,_), arg) if h.hasTimeStep(fname) =>
            Right(expand(arg,h,c,Some(fname)))
          case FuncOf(Function(fname,_,_,_,_), arg) if c.hasFunDef(fname) =>
            Right(expand(c.getFunDef(fname, at).asInstanceOf[Term],h,c,at))
          case FuncOf(Function(fname,_,_,_,_), arg) if c.hasDef(fname) =>
            Right(c.getDef(fname).asInstanceOf[Term])
          case _ =>
            Left(None)
        }
      override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] =
        e match {
          case PredOf(Function(fname,_,_,_,_), arg) if c.hasDef(fname)=>
            Right(c.getDef(fname).asInstanceOf[Formula])
          case PredicationalOf(Function(fname,_,_,_,_), arg) if c.hasDef(fname) =>
            Right(c.getDef(fname).asInstanceOf[Formula])
          case UnitPredicational(fname, arg) if c.hasDef(fname) =>
            Right(c.getDef(fname).asInstanceOf[Formula])
          case PredOf(Function(fname,_,_,_,_), arg) if c.hasFunDef(fname)=>
            Right(expand(c.getFunDef(fname, at).asInstanceOf[Formula],h,c,at))
          case PredicationalOf(Function(fname,_,_,_,_), arg) if c.hasFunDef(fname) =>
            Right(expand(c.getFunDef(fname, at).asInstanceOf[Formula],h,c,at))
          case UnitPredicational(fname, arg) if c.hasFunDef(fname) =>
            Right(expand(c.getFunDef(fname, at).asInstanceOf[Formula],h,c,at))
          case PredicationalOf(Function(fname,_,_,_,_), arg) if h.hasTimeStep(fname) =>
            Right(expand(arg,h,c,Some(fname)))
          case _ => Left(None)
        }
      override def preP(p: PosInExpr, e: Program): Either[Option[StopTraversal], Program] =
        e match {
          case ProgramConst(fname,_) if c.hasDef(fname) =>
            Right(c.getDef(fname).asInstanceOf[Program])
          case SystemConst(fname,_) if c.hasDef(fname) =>
            Right(c.getDef(fname).asInstanceOf[Program])
          case DifferentialProgramConst(fname,_) if c.hasDef(fname) =>
            Right(c.getDef(fname).asInstanceOf[Program])
          case _ => Left(None)
        }
    }
  }
  // Expansion of (arbitrary) nominal expressions, not just terms.
  def expand(e:Term, h:History, c:Context, at:Option[TimeName]):Term       = {ExpressionTraversal.traverse(doTravel(h,c, at), e).get}
  def expand(e:Formula, h:History, c:Context, at:Option[TimeName]):Formula = {
    val traveled = ExpressionTraversal.traverse(doTravel(h,c, at), e)
    traveled.get
  }
  def expand(e:Program, h:History, c:Context, at:Option[TimeName]):Program = {ExpressionTraversal.traverse(doTravel(h,c, at), e).get}
  def expand(e:Expression, h:History, c:Context, at:Option[TimeName]):Expression = {
    e match {
      case t:Term => expand(t,h,c,at)
      case f:Formula => expand(f,h,c,at)
      case p:Program => expand(p,h,c,at)
    }
  }

  // helper
  def uniqueMatch(pat:Expression, c:Context, ante:immutable.IndexedSeq[Formula]):Int = {
    val ident:Option[String] = pat match {case ns:NamedSymbol => Some(ns.name) case f:ApplicationOf => Some(f.func.name ) case _ => None}
    val ofIdent:Option[Position] = ident.flatMap{case x => c.gmap.get(Variable(x))}
    ofIdent match {
      case Some(pos)  => pos.checkAnte.index0
      case None =>
        val matches:immutable.IndexedSeq[(Formula,Int)] = ante.zipWithIndex.filter({case (fml,_) => doesMatch(pat, fml,c, ante)})
        matches.toList match {
          case ((_,i)::Nil) => i
          case ms =>
            throw new Exception("Non-unique match for pattern " + pat + " in pattern-matching construct: " + ms)
        }

    }
  }

  // proof-checking
  def eval(fp:FP, h:History, c:Context, ante:immutable.IndexedSeq[Formula]):Provable = {
    fp match {
      case (FPat(ns : NamedSymbol)) if propAxioms.keySet.contains(ns.name.toLowerCase) =>
        val id = ns.name
        val fml = propAxioms(id)
        val pr:Provable = Provable.startProof(Sequent(ante, immutable.IndexedSeq(fml)))
        val pr2:Provable = pr(CoHideRight(SuccPos(0)),0)
        interpret(prop, pr2)
      case FPat(f : ApplicationOf) if propAxioms.keySet.contains(f.func.name.toLowerCase) =>
        val id = f.func.name
        val fml = propAxioms(id.toLowerCase)
        val pr:Provable = Provable.startProof(Sequent(ante, immutable.IndexedSeq(fml)))
        val pr2:Provable = pr(CoHideRight(SuccPos(0)),0)
        interpret(prop, pr2)
      case FPat(e : Expression) =>
        val i = uniqueMatch(e, c, ante)
        val fml = ante(i)
        val pr:Provable = Provable.startProof(Sequent(ante, immutable.IndexedSeq(fml)))
        pr(Close(AntePos(i),SuccPos(0)),0)
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
              val step1 = Provable.startProof(seq)
              val step2 = step1(Cut(p2),0)
              val step3 = step2(HideRight(SuccPos(0)),1)(pr2,1)
              val step4 = step3(Cut(Imply(p2,q2)),0)
              val step5 = step4(HideRight(SuccPos(0)),1)
              val step6 = step5(HideLeft(argPos),1)
              val step7 = step6(pr1b,1)
              val step8 = step7(ImplyLeft(impPos),0)
              val step9 = step8(Close(argPos,SuccPos(1)),0)
              val step10 = step9(Close(impPos,SuccPos(0)),0)
              step10

            } catch {
              case e : UnificationException =>
                println(e)
                throw new Exception("proposition mismatch in modus ponens", e)
            }
          case _ => throw new Exception("proposition mismatch in modus ponens")
         }
      case FInst(fp1, term) =>
        val t2 = expand(term,h, c, None)
        val pr1:Provable = eval(fp1, h, c, ante)
        assert(pr1.conclusion.succ.nonEmpty)
        val goal = pr1.conclusion.succ.head
        goal  match {
          case (Forall(xs,q)) =>
            try {
              def repvTerm(e:Formula, x:Variable, t:Term):Formula = {
                ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
                  override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] =
                    e match {
                      case y: Variable if x == y => Right(t)
                      case _ => Left(None)
                    }
                }, e).get
              }
              val subst:Subst = UnificationMatch(AxiomInfo("all instantiate").provable.conclusion.succ.head.asInstanceOf[Imply].left, goal)
              val pair = (FuncOf(Function("f", None, Unit, Real), Nothing), t2)
              val vpair = (Variable("x_"), xs.head)
              val renu:RenUSubst = RenUSubst(immutable.IndexedSeq.concat(immutable.IndexedSeq[(Expression,Expression)](vpair,pair), subst.usubst.subsDefsInput.map({case x => (x.what, x.repl)})))
              val q2=repvTerm(q,xs.head, t2)
              val ax=AxiomInfo("all instantiate").provable
              val p2:Provable=renu.toForward(ax).underlyingProvable
              val seq = Sequent(ante, immutable.IndexedSeq(q2))
              val impPos = AntePos(ante.length)
              val allPos = AntePos(ante.length+1)
              val pr1b = renu.toForward(ElidingProvable(pr1, Declaration(Map.empty))).underlyingProvable
              val s1 = Provable.startProof(seq)(Cut(p2.conclusion.succ.head), 0)
              val s1a = s1(CoHideRight(SuccPos(1)),1)
              val s2 = s1a(p2,1)
              val s3 = s2(Cut(pr1.conclusion.succ.head),0)
              val s3a = s3(HideRight(SuccPos(0)),1)
              val s3b = s3a(HideLeft(AntePos(s3a.subgoals(1).ante.length-1)),1)
              val s4 = s3b(pr1,1)
              val s5 = s4(ImplyLeft(impPos), 0)
              val s6 = s5(Close(impPos,SuccPos(1)),0)
              val s7 = s6(Close(impPos,SuccPos(0)),0)
              s7
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
          /* Use */ implyL(-(pos + 2)) <(/* use */ close,
          implyL(-(pos+2)) <(  hide(1) &  useAt(ElidingProvable(fact, Declaration(Map.empty)), PosInExpr(Nil))(1)
            ,  nil )
        ),
          DebuggingTactics.debug("e", doPrint = doPrint) &
          /* show */ cohideR(2) & useAt(Ax.K, PosInExpr(Nil))(1,Nil)) &
      hide(-1) &
          DebuggingTactics.debug("before recur", doPrint = doPrint)
      polyK(interpret(if(onSecond) { nil <(nil, e)} else {e}, pr), facts)
  }
}

/* Two histories for base case/ind case so we can return the name of the invariant formula in both states*/
def collectLoopInvs(ip: IP,h:History,hh:History,c:Context):(List[Variable], List[Formula], List[Formula], List[SP], List[SP], IP) = {
  ip match {
    case Inv(x, fml, pre, inv, tail) =>
      val (vs, f,ff, p,i,t) = collectLoopInvs(tail,h,hh,c)
      val baseFml = expand(fml,h,c, None)
      val indFml = expand(fml,hh,c, None)
      (x::vs, baseFml::f, indFml::ff, pre::p, inv::i, t)
    case _ : Finally => (Nil, Nil, Nil, Nil, Nil, ip)
    case _ => ???
  }
}

abstract class OdeInvInfo
case class DiffCutInfo(proofVar:Variable, bcFml: Formula, indFml: Formula, bcProof:SP, indProof:SP) extends OdeInvInfo
case class DiffGhostInfo(dgVar:Variable, dgPrime:Term, dg0:Term) extends OdeInvInfo

def collectODEInvs(ip: IP,h:History,hh:History,c:Context):(List[OdeInvInfo], IP) = {
  ip match {
    case Inv(x, fml, pre, inv, tail) =>
      val (infs,t) = collectODEInvs(tail,h,hh,c)
      (DiffCutInfo(proofVar = x, bcFml = expand(fml,h,c, None), indFml = expand(fml,hh,c, None), pre, inv)::infs,t)
    case Ghost(gvar,gterm,ginv,x0,pre,inv,tail) =>
      val (infs,t) = collectODEInvs(tail,h,hh,c)
      (DiffGhostInfo(gvar,gterm,x0)::infs,t)
    case _ : Finally => (Nil, ip)
    case _ => ???
  }
}

  def rotAnte(pr:Provable):Provable = {
    val fml = pr.subgoals.head.ante.head
    interpret(cut(fml) <(hideL(-1), close), pr)
  }
def eval(ip:IP, h:History, c:Context, g:Provable, nInvs:Int = 0):Provable = {
  val gg = g
  val seq = gg.subgoals(0)
  val ante = seq.ante
  val goal = seq.succ.head
  (ip, goal) match {
    // TODO: Names to refer the invariants
    // TODO: Update invariant names for the inductive step what with the vacuation
    case (nextInv : Inv, Box(Loop(a),post)) => {
      val bvs = StaticSemantics.boundVars(a).toSet.filter({case _ : BaseVariable => true case _ => false}:(Variable=>Boolean))
      val (ggg:Provable, saved)  = saveVars(gg, bvs, invCurrent = false)
      val anteConst = ggg.subgoals.head.ante.take(ante.length)
      //TODO: Intermediate hh and cc
      val hh =  bvs.foldLeft(h)({case(acc, v) => acc.update(v.name)})
      val (vars, baseFmls, indFmls, pres, invs, lastTail) = collectLoopInvs(nextInv,h, hh,c)
      val conj = indFmls.reduceRight(And)
      val cc = vars.zipWithIndex.foldLeft(c)({case (acc, (v,i)) => acc.add(v, AntePos(anteConst.length + i))})
      def baseCase(fmlPres:List[(Formula,SP)], done:List[Formula] = Nil):BelleExpr = {
        fmlPres match {
          case Nil => ???
          case (fml, pre:SP)::Nil =>
            val preSeq = Sequent(ante, immutable.IndexedSeq(fml))
            val tail = eval(pre, h, c, Provable.startProof(preSeq))
            assert(tail.isProved, "Failed to prove first base case subgoal " + fml + " in subproof " + pre + ", left behind provable " + tail.prettyString)
            DebuggingTactics.debug("BASE0 I WANTED", doPrint = true) & useAt(ElidingProvable(tail, Declaration(Map.empty)), PosInExpr(Nil))(1) & DebuggingTactics.debug("BASE0B", doPrint = true)
          case (fml, pre:SP)::fps =>
            val preSeq = Sequent(ante, immutable.IndexedSeq(fml))
            val tail = eval(pre, h, c, Provable.startProof(preSeq))
            assert(tail.isProved, "Failed to prove additional base case subgoal " + fml + " in subproof " + pre + ", left behind provable " + tail.prettyString)
            val e1 = useAt(ElidingProvable(tail, Declaration(Map.empty)), PosInExpr(Nil))(1)
            val e2 = baseCase(fps, fml::done)
            andR(1) <(DebuggingTactics.debug("left", doPrint = true) & e1, DebuggingTactics.debug("right", doPrint = true) & e2)
        }
      }
      def indCase(fmlPres:List[(Variable,(Formula,SP))], c:Context, done:immutable.IndexedSeq[Formula] = immutable.IndexedSeq()):BelleExpr = {
        fmlPres match {
          case Nil => ???
          case (x,(fml, inv:SP))::Nil =>
            val invSeq = Sequent(anteConst ++ done ++ immutable.IndexedSeq(fml), immutable.IndexedSeq(Box(a,fml)))
            val cc = c.add(x, AntePos(invSeq.ante.length-1))
            val e = hideL('Llast)*(invs.length - (done.length + 1))
            val tail = eval(inv, hh, cc, Provable.startProof(invSeq))
            assert(tail.isProved, "Failed to prove first inductive case subgoal " + fml + " in subproof " + inv + ", left behind provable " + tail.prettyString)
            e  & useAt(ElidingProvable(tail, Declaration(Map.empty)), PosInExpr(Nil))(1)
          case (x, (fml,pre:SP))::fps =>
            val invSeq = Sequent(anteConst ++ done ++ immutable.IndexedSeq(fml), immutable.IndexedSeq(Box(a,fml)))
            val cc = c.add(x, AntePos(invSeq.ante.length-1))
            val hide = hideL('Llast)*(invs.length - (done.length + 1))
            val tail = ElidingProvable(eval(pre, hh, cc, Provable.startProof(invSeq)), Declaration(Map.empty))
            assert(tail.isProved, "Failed to prove additional inductive case subgoal " + fml + " in subproof " + pre + ", left behind provable " + tail.prettyString)
            val e1 = hide & useAt(tail, PosInExpr(Nil))(1)
            val e2 = indCase(fps, cc, done ++ immutable.IndexedSeq(fml))
            boxAnd(1) & andR(1) <(e1, e2)
        }
      }
      //by(t: (ProvableSig, SuccPosition) => ProvableSig)

      //(andL('L)*(Math.max(0, invs.length-1)))
      val unpack:BelleExpr =
        if (invs.length > 1) {
            andL(AntePosition(1)) &
            andL('Llast) * (invs.length - 2)
        }
          else {
          def rot(pr:ProvableSig,p:SuccPosition):ProvableSig = ElidingProvable(rotAnte(pr.underlyingProvable), pr.defs)
          val e =
            TacticFactory.anon((pos: ProvableSig, seq: SuccPosition) =>{rot(pos,seq)})(1)
          e
        }
      val e:BelleExpr =
        DLBySubst.loop(conj, pre = nil)(1) <(
          unsaveVars(gg, bvs, rewritePost = true)
          & baseCase(baseFmls.zip(pres)), nil,
          unpack
          & indCase(vars.zip(indFmls.zip(invs)),c))
      val pr:Provable = interpret(e, ggg)
      val pr1 = rotAnte(pr)
      val killAnds = if(invs.length <= 1) TactixLibrary.nil else (andL('Llast)*(invs.length-1))
      val pr2 = interpret(killAnds,pr1)
      eval(lastTail, hh, cc, pr2, nInvs+1)
    }
    case (firstInv, Box(ODESystem(ode,constraint),post)) if !firstInv.isInstanceOf[Finally]=> {
      val bvs = StaticSemantics(ode).bv.toSet.filter({case _:BaseVariable => true case _ => false}:(Variable=>Boolean))
      val hh =  bvs.foldLeft(h)({case(acc, v) => acc.update(v.name)})
      // TODO: Contexts
      val (infs, t) = collectODEInvs(ip, h, hh, c)
      val (ggg, saved) = saveVars(gg, bvs.toSet, invCurrent = false)
      val anteSize = gg.subgoals.head.ante.size
      var cutsSoFar = 0
      def proveInvs(pr:Provable, infs:List[OdeInvInfo], c:Context):(Provable,Context) = {
        infs match {
          case Nil => (pr,c)
          case DiffCutInfo(proofVar, bcFml, indFml, bcProof, indProof)::invTail =>
            val e:BelleExpr = dC(indFml)(1) <(nil, DebuggingTactics.debug("Blah", doPrint = true) &  (dI()(1) | (DebuggingTactics.debug("Blahhh", doPrint = true)  & dW(1) & master())))
            val pos = AntePos(anteSize + cutsSoFar)
            cutsSoFar = cutsSoFar + 1
            val prr = interpret(e, pr)
            proveInvs(prr, invTail, c.add(proofVar, pos))
          case DiffGhostInfo(dgVar, dgPrime, dG0)::invTail =>
            val e:BelleExpr = dG(AtomicODE(DifferentialSymbol(dgVar), dgPrime), None)(1)
            val ee = e & existsR(dG0)(1) & DebuggingTactics.debug("after ghost", doPrint = true)
            val prr = interpret(ee, pr)
            proveInvs(prr, invTail, c)
        }
      }
      val (g3,cc) = proveInvs(ggg, infs,c)
      val g4 = interpret(dW(1) & implyR(1), g3)
      val nInvs = infs.filter{case _:DiffCutInfo => true case _ => false}.length
      val conjPos = AntePosition(anteSize+1)
      val oneAnd = andL(conjPos)
      // The conjunction in the domain constraint is associated in a way that makes t positioning nasty.First reassociate it.
      def flatAnd(f:Formula, n:Int):List[Formula] = {f match {case And(a,b) if n > 0 => flatAnd(a,n-1) ++ List(b) case ff => List(ff)}}
      def unflatAnd(l:List[Formula]):Formula = l match {case List(l) => l case (x::xs) => And(x,unflatAnd(xs))}
      val conj = unflatAnd(flatAnd(g4.subgoals.head.ante.last,nInvs))
      val cutConj = cut(conj)<(hideL(conjPos), hideR(1) & (hideL(-1)*(anteSize-1)) & prop)
      val killAnds = if(nInvs > 0) {andL('Llast)*(nInvs)} else nil
      val killTrue = if(nInvs > 0) {hideL(AntePosition(anteSize+1))} else {hideL('Llast)}
      val pr = interpret(cutConj & killAnds & killTrue, g4)
      eval(t.asInstanceOf[Finally].tail, hh, cc, pr)
    }

    case (Finally(tail: SP), Box(ODESystem(ode,constraint),post)) =>
      //TODO: Delete because handled elsewhere
      eval(tail, h, c, interpret(dW(1) & implyR(1), g))
    case (Finally (tail: SP),post) =>  {
      eval(tail, h, c, g)
    }
  }
}

case class BadBranchingFactorException(had:Int,wanted:Int) extends Exception

def assertBranches(had:Int, wanted:Int):Unit =  {if(had != wanted) throw BadBranchingFactorException(had,wanted)}


private def saveVars(pr:Provable, savedVars:Set[Variable], invCurrent:Boolean = true, hide:Boolean = true):(Provable, List[Variable]) = {
  savedVars.foldRight[(Provable,List[(Variable)])]((pr,Nil))({case(v:Variable,(acc,accVs)) =>
    val vv:Variable = TacticHelper.freshNamedSymbol(v,acc.subgoals.head) // was once pr1.conclusion
    val last = acc.subgoals.head.ante.length+1
    val e:BelleExpr =
      discreteGhost(v,Some(vv))(1) &
      TactixLibrary.exhaustiveEqR2L(hide=false)('Llast) &
      TactixLibrary.eqL2R(-last)(1) &
      (if (invCurrent) {TactixLibrary.eqL2R(-last)(1 + accVs.length - last)} else { nil })
    (interpret(e, acc), vv::accVs)
  })
}

private def unsaveVars(pr:Provable, bvs:Set[Variable], rewritePost:Boolean = false, hide:Boolean = true):BelleExpr = {
  val poses = List.tabulate(bvs.size)({case i => AntePosition(bvs.size + pr.subgoals.head.ante.length - i)})
  poses.foldLeft[BelleExpr](nil)({case (acc, pos) =>
    val numRens = pos.index0
    val rens = List.tabulate(numRens)({case i => TactixLibrary.eqL2R(pos)(AntePosition(1 + i))}).foldLeft[BelleExpr](nil)({case (acc,e) => acc & e})
    val doHide = if(hide) {hideL(pos)} else nil
    val renss = if(rewritePost) {rens & DebuggingTactics.debug("Rewriting post " + pos, doPrint = true) & TactixLibrary.eqL2R(pos)(SuccPosition(1))} else rens
    acc & DebuggingTactics.debug("unsaving " + pos, doPrint = true) & /*(TactixLibrary.eqL2R(pos)('L)*)*/ renss & DebuggingTactics.debug("unsave huh " + pos, doPrint = true)& doHide & DebuggingTactics.debug("unsaved " + pos, doPrint = true)})
}

def eval(brule:RuleSpec, sp:List[SP], h:History, c:Context, g:Provable):Provable = {
  val sequent = g.subgoals.head
  val goal = sequent.succ.head
  val ante = sequent.ante
  goal match {
    case _ =>
      (brule, goal) match {
          // TODO: More readable match error
        case (RBAssign(hp:Assign), Box(Assign(x,theta),p)) if hp.x == x =>
          assertBranches(sp.length, 1)
          // TODO: Renaming of stuff
          val hh = h.update(hp.x.name, theta)
          var gsub:Option[Provable] = None
          try {
            gsub = Some(interpret(useAt(Ax.assignbAxiom)(1), g))
          } catch {
            case e : Throwable =>
              println("Doing equational assignment because of " + e)
              val gg = interpret(DLBySubst.assignEquality(1), g)
              val defn:Equal = gg.subgoals.head.ante.last.asInstanceOf[Equal]
              val base = defn.left.asInstanceOf[BaseVariable]
              val hh = h.updateRen(Variable(base.name), Variable(base.name, Some(h.nextIndex(base.name))), AntePos(gg.subgoals.head.ante.length-1))
              return eval(sp.head, hh, c, gg)
          }
          eval(sp.head, hh, c, gsub.get)
        case (RBMid(varName:Variable,fml:Formula), Box(a,Box(b,p))) =>
          assertBranches(sp.length, 2)
          val bvs = StaticSemantics.boundVars(a)
          val hh = bvs.toSet.foldLeft(h)({case (acc,v) => (acc.update(v.name))})
          val fmlEarly = expand(fml, h, c, None)
          val fmlLate = expand(fml,hh,c,None)
          val (pr1prep,_) = saveVars(g,bvs.toSet)
          val seq1:Sequent = Sequent(pr1prep.subgoals.head.ante, immutable.IndexedSeq(Box(a,fmlLate)) ++ sequent.succ.tail)
          val pr1:Provable = eval(sp(0),hh,c,Provable.startProof(seq1))
          assert(pr1.isProved, "Failed to prove subgoal in subproof " + sp(0) + ", left behind provable " + pr1.prettyString)
          // TODO: Document the proof tree for this proof.
          // TODO: How many assumptions stick around?
          val seq2:Sequent = Sequent(sequent.ante ++ immutable.IndexedSeq(fml), immutable.IndexedSeq(Box(b,p)))
          val pr2a:Provable = Provable.startProof(seq2)
          val (rename,renVs) = saveVars(pr2a,bvs.toSet)
          //val hh = renVs.foldRight(h)({case (v, acc) => acc.update(v.name)})
          //val fmlLate = expand(fml, hh,c,None)
          val pr2Help = Provable.startProof(rename.subgoals.head.updated(AntePos(sequent.ante.length),fmlLate))
          val G1 = pr2Help.conclusion.ante
          val FG1:Formula = G1.reduceRight(And)
          val pr2Hid = interpret(hideL('Llast)*(bvs.toSet.size), pr2Help)
          val pr2Start = Provable.startProof(pr2Hid.subgoals.head)
          val G2 = pr2Hid.subgoals.head.ante//.tail
          val FG2:Formula = And(G2.last, G2.dropRight(1).reduceRight(And))
          val cc = c.add(varName,AntePos(pr2Start.conclusion.ante.length-1))
          val pr2:Provable = eval(sp(1),hh,cc,pr2Start)
          assert(pr2.isProved, "Failed to prove subgoal in subproof " + sp(1) + ", left behind provable " + pr2.prettyString)
          val pp1:Provable = saveVars(g,bvs.toSet, invCurrent = false)._1
          val poses = List.tabulate(bvs.toSet.size)({case i => AntePosition(pp1.subgoals.head.ante.length - i)})
          val e = poses.foldLeft[BelleExpr](nil)({case (acc, pos) => acc & TactixLibrary.eqR2L(pos)(-1) & hideL(pos)})
          //
          //
          //
          /* interpret(cut(Box(a,FG2)) <(hideL(-1)*(G1.length-1) & monb & ((andL('L))*)& useAt(NoProofTermProvable(pr2), PosInExpr(Nil))(1),
                   hideR(1) & boxAnd(1) & andR(1)  <( e & useAt("V vacuous")(1) & prop, hideL('Llast)*bvs.toSet.size & useAt(NoProofTermProvable(pr1),PosInExpr(Nil))(1))), pp1)*/

          val pp2 = interpret(cut(Box(a,FG2)), pp1)
          val ppa = Provable.startProof(pp2.subgoals.head)
          val ppa1 = interpret(hideL(-1)*(G1.length-1), ppa)
          val ppa2 = interpret(monb, ppa1)
          val ppa3 = interpret(((andL('Llast))*(G2.length-1)), ppa2)
          val ppa35 = rotAnte(ppa3)
          val ppa4 = interpret(useAt(ElidingProvable(pr2, Declaration(Map.empty)), PosInExpr(Nil))(1), ppa35)
          val ppb = Provable.startProof(pp2.subgoals.tail.head)
          val ppb1 = interpret(hideR(1), ppb)
          val ppb2 = interpret(boxAnd(1) & andR(1),ppb1)
          val ppc = Provable.startProof(ppb2.subgoals.tail.head)
          val ppc1 = interpret(e, ppc)
          val ppc2 = interpret(useAt(Ax.V)(1), ppc1)
          val ppc3 = interpret(prop, ppc2)
          val ppd = Provable.startProof(ppb2.subgoals.head)
          val ppd1 = interpret(unsaveVars(g, bvs.toSet, rewritePost = false, hide = false), ppd)
          //val ppd1 = interpret(hideL('Llast)*bvs.toSet.size, ppd)
          val ppd2 = interpret(useAt(ElidingProvable(pr1, Declaration(Map.empty)),PosInExpr(Nil))(1), ppd1)
          val b3 = ppb2(ppd2,0)
          val b2 = b3(ppc3,0)
          val b4 = pp2(ppa4,0)
          val prr =b4(b2,0)

          /*val prr:Provable = interpret(cut(Box(a,FG2)) <(DebuggingTactics.debug("DooD " + (G1.length-1), doPrint = true) & hideL(-1)*(G1.length-1) & DebuggingTactics.debug("hmmm", doPrint = true) & monb & ((andL('L))*) & DebuggingTactics.debug("The useat time ", doPrint = true ) & useAt(NoProofTermProvable(pr2), PosInExpr(Nil))(1),
            hideR(1) & boxAnd(1) & andR(1) & DebuggingTactics.debug("stuff", doPrint = true) <( e & useAt("V vacuous")(1) & prop, hideL('Llast)*bvs.toSet.size & useAt(NoProofTermProvable(pr1),PosInExpr(Nil))(1))), pp1)*/
          prr
        case (RBCase(pat1::pat2::Nil), Box(Choice(a,b),p)) if doesMatch(pat1,a,c, ante) && doesMatch(pat2,b,c, ante) =>
          assertBranches(sp.length, 2)
          val seq1:Sequent = Sequent(sequent.ante, immutable.IndexedSeq(Box(a,p)) ++ sequent.succ.tail)
          val seq2:Sequent = Sequent(sequent.ante, immutable.IndexedSeq(Box(b,p)) ++ sequent.succ.tail)
          val pr1:Provable = eval(sp(0),h,c,Provable.startProof(seq1))
          val pr2:Provable = eval(sp(1),h,c,Provable.startProof(seq2))
          // TODO: Not right, need a cut somewhere
          val prr:Provable = interpret(TactixLibrary.choiceb(1) & andR(1), g)
          prr(pr1,0)(pr2,0)
        case (RBCase(pat1::pat2::Nil), Box(a,And(p,q))) if doesMatch(pat1,p,c, ante) && doesMatch(pat2,q,c, ante) =>
          assertBranches(sp.length, 2)
          val seq1:Sequent = Sequent(sequent.ante, immutable.IndexedSeq(Box(a,p)) ++ sequent.succ.tail)
          val seq2:Sequent = Sequent(sequent.ante, immutable.IndexedSeq(Box(a,q)) ++ sequent.succ.tail)
          val pr1:Provable = eval(sp(0),h,c,Provable.startProof(seq1))
          val pr2:Provable = eval(sp(1),h,c,Provable.startProof(seq2))
          val prr:Provable = interpret(TactixLibrary.boxAnd(1) & andR(1), g)
          prr(pr1,0)(pr2,0)
        case (RBCase(pat1::pat2::Nil), And(p,q)) if doesMatch(pat1,p,c,ante) && doesMatch(pat2,q,c,ante) =>
          assertBranches(sp.length, 2)
          val seq1:Sequent = Sequent(sequent.ante, immutable.IndexedSeq(p) ++ sequent.succ.tail)
          val seq2:Sequent = Sequent(sequent.ante, immutable.IndexedSeq(q) ++ sequent.succ.tail)
          val pr1:Provable = eval(sp(0),h,c,Provable.startProof(seq1))
          val pr2:Provable = eval(sp(1),h,c,Provable.startProof(seq2))
          val prr:Provable = interpret(andR(1), g)
          prr(pr1,0)(pr2,0)
        // TODO: Decide whether to keep around the old variable
        case (RBCaseOrL(x1,pat1:Formula,x2,pat2:Formula), _)  =>
          //TODO continue search if cant find one
          assertBranches(sp.length, 2)
          val pat = expand(Or(pat1,pat2),h,c, None)
          val i =  uniqueMatch(pat, c, sequent.ante)
          val (Or(p,q)) = sequent.ante(i)
          val seq1:Sequent = Sequent(sequent.ante.updated(i,p), sequent.succ)
          val seq2:Sequent = Sequent(sequent.ante.updated(i,q), sequent.succ)
          val pr1:Provable = eval(sp(0),h,c,Provable.startProof(seq1))
          val pr2:Provable = eval(sp(1),h,c,Provable.startProof(seq2))
          val prr:Provable = interpret(TactixLibrary.orL(-(i+1)), g)
          prr(pr1,0)(pr2,0)

        case (RBAbbrev(xphi, x, theta),_) =>
          assertBranches(sp.length, 1)
          val hh = h.update(x.name,theta)
          val cc = c.add(xphi, AntePos(sequent.ante.length))
          val e = EqualityTactics.abbrv(theta,Some(x))
          val pr1 = interpret(e, g)
          val pr = eval(sp.head,h,cc,pr1)
          pr
        case (RBCaseImplyL(p,patp,q,patq), _ ) =>
          assertBranches(sp.length, 2)
          val pat = expand(Imply(patp,patq),h,c,None)
          val i = uniqueMatch(pat,c,sequent.ante)
          val (Imply(pfml,qfml)) = sequent.ante(i)
          val seq1:Sequent = sequent.updated(AntePos(i), Sequent(immutable.IndexedSeq(), immutable.IndexedSeq(pfml)))
          val seq2:Sequent = Sequent(sequent.ante.updated(i,qfml), sequent.succ)
          //ante.sli
          //TODO add p,q to contexts, also shift positioning on all other
          val pr1:Provable = eval(sp(0),h,c,Provable.startProof(seq1))
          val pr2:Provable = eval(sp(1),h,c,Provable.startProof(seq2))
          val prr:Provable = interpret(TactixLibrary.implyL(-(i+1)), g)
          prr(pr1,0)(pr2,0)
        case (RBCaseOrR(x1:Variable, x2:Variable),Or(p,q)) =>
          assertBranches(sp.length, 1)
          val seq1:Sequent = Sequent(sequent.ante, immutable.IndexedSeq(p,q) ++ sequent.succ.tail)
          val pr1:Provable = eval(sp(0),h,c,Provable.startProof(seq1))
          val prr:Provable = interpret(TactixLibrary.orR(1),g)
          prr(pr1,0)
        case (RBAssume(x:Variable,fml:Formula),Imply(p,q)) =>
          assertBranches(sp.length, 1)
          val cc = pmatch(expand(fml,h,c,None), p,c, sequent.ante)
          val newPos = AntePos(sequent.ante.length)
          val ccc:Context = c.concat(cc).add(x,newPos)
          eval(sp.head, h, ccc, g(ImplyRight(SuccPos(0)),0))
        case (RBSolve(t:Variable,fmlT:Formula,dc:Variable,fmlDC:Formula,sols:List[(Variable,Formula)]),Box(ODESystem(ode,q),p)) =>
          val pr = interpret(solve(1) & allR(1) & implyR(1), g)
          eval(sp.head, h, c, pr)
        case (RBAssignAny(x:Variable),Box(AssignAny(y),p)) if x == y =>
          assertBranches(sp.length, 1)
          val hh = h.update(x.name)
          eval(sp.head, hh, c, interpret(TactixLibrary.randomb(1) & allR(1), g))
        case (RBInv(ip:IP), Box(_:Loop,_)) =>
          assertBranches(sp.length, 0)
          eval(ip, h, c, g)
        case (RBInv(ip:IP), Box(_:ODESystem,_)) =>
          assertBranches(sp.length, 0)
          eval(ip, h, c, g)
        case (RIdent (x:String), _) => ???
        case (RDAssign(hp:Assign), _)  => ???
        case (RDMid(fml:Formula), _)  => ???
        case (RDCase(a:Program), _) => ???
        case (RDAssert(x:Variable,fml:Formula), _) => ???
        case (RDSolve(t:Variable,fmlT:Formula,dc:Variable,fmlDC:Formula,sols:List[(Variable,Formula)]), _) => ???
        case (RDAssignAny(x:Variable, xVal:Term), _)  => ???
        case (_, Box(Compose(a,b),p)) =>
          eval(brule, sp, h, c, interpret(useAt(Ax.composeb)(1), g))
        case (_, Box(Test(_),p)) =>
          eval(brule, sp, h, c, interpret(useAt(Ax.testb)(1), g))
        case (RBCase(pats), fml) =>
          fml match {
            case Box(Choice(a,b), p) =>
              //if doesMatch(pat1,a,c)
              if (pats.nonEmpty && !doesMatch(pats.head,a,c,ante)) {
                println("In choice: pattern " + pats.head + " did not match program " + a)
              }
              if (pats.length > 1 && !doesMatch(pats.tail.head,b,c,ante)) {
                println("In choice: pattern " + pats.tail.head + " did not match program " + b)
              }
          }
          println("Patterns " + pats + " did not match " + fml + " in case")
          ???
      }
  }
}

def eval(sp:SP, h:History, c:Context, g:Provable):Provable = {
  assert(g.subgoals.length == 1, "Expected 1 subgoal, got: " + g.subgoals.length)
  assert(g.subgoals.head.succ.nonEmpty)
  val ante = g.subgoals.head.ante
  val goal = g.subgoals.head.succ.head
  sp match {
    case Show(phi:Formula, proof: UP)  =>
      val succ = g.subgoals.head.succ
      def ifilter[T,S](p:(T,Int)=>Boolean, f:(T,Int)=>S, xs: IndexedSeq[T]):IndexedSeq[S] = {
        xs.zipWithIndex.flatMap({case (x,i) => if (p(x,i)) {IndexedSeq(f(x,i))} else {IndexedSeq()}})
      }
      val expanded = expand(phi,h,c, None)
      val hideInds = ifilter({case (x,i) => !doesMatch(expanded, x, c,ante)}:((Formula,Int) => Boolean), {case (x,i) => i}:((Formula,Int) => Int), succ)
      val upsucc = ifilter({case (x,i) => !hideInds.contains(i)}:((Formula,Int) => Boolean), {case (x,i) => x}:((Formula,Int) => Formula), succ)
      val cxts = upsucc.map(pmatch(expanded,_, c, g.subgoals.head.ante))
      val ccc = cxts.foldLeft(c)({case(acc,x) => x.concat(acc)})
      val hideTac = hideInds.reverse.foldLeft[BelleExpr](TactixLibrary.nil)({case (e, i) => e & hideR(i+1)})
      val prIn = interpret(hideTac, g)
      val pr =eval(proof, h, ccc, prIn)
      assert(pr.isProved, "Shown formula not proved: " + phi + " not proved by " + pr.prettyString + "\\n\\n at " + g.prettyString)
      pr
    case SLet(pat:Expression, e:Expression, tail:SP) =>
      //TODO: Expand e?
      val cc = pmatch(expand(pat,h,c,None), expand(e,h,c, None),c,g.subgoals.head.ante)
      eval(tail, h, c.concat(cc), g)
    case FLet(x:VBase, arg:VBase, e:Expression, tail:SP) =>
      eval(tail, h, c.addFun(x,arg,expand(e,h,c,None)), g)
    case Note(x:Variable, fp:FP, tail: SP)  =>
      val fpr:Provable = eval(fp, h, c, g.subgoals.head.ante)
      assert(fpr.conclusion.succ.nonEmpty)
      val size = fpr.conclusion.ante.size
      val newPos = AntePos(size)
      val res:Formula = fpr.conclusion.succ.head
      val gg = g(Cut(res), 0)(HideRight(SuccPos(0)),1)(fpr,1)
      val cc = c.add(x,newPos)
      eval(tail, h, cc, gg)
    case Have(x:Variable, fml:Formula, sp:SP, tail: SP)  =>
      val fmlExpanded = expand(fml,h,c,None)
      val seq = Sequent(g.subgoals.head.ante, immutable.IndexedSeq(fmlExpanded))
      val prIn = Provable.startProof(seq)
      val prOut = eval(sp, h, c, prIn)
      assert(prOut.isProved, "Failed to prove subgoal " + x + ":" + fml + " in subproof " + sp + ", left behind provable " + prOut.prettyString)
      val size = prOut.conclusion.ante.size
      val newPos = AntePos(size)
      val succSize = g.subgoals.head.succ.length
      def cohideR(g:Provable,n:Int):Provable = if(n == 0) {g} else {cohideR(g(HideRight(SuccPos(0)),1),n-1)}
      val gg = cohideR(g(Cut(fmlExpanded),0),succSize)(prOut,1)
      val res = eval(tail,h,c.add(x,newPos), gg)
      res
    case BRule (r:RuleSpec, tails: List[SP]) => eval(r,tails,h,c,g)
    case State (st:TimeName, tail: SP) => eval(tail,h.advance(st),c,g)
    case PrintGoal(msg,tail) =>
      println("====== " + msg + " ======\n" + "Goal:" + g.prettyString + "\n\nContext:" + c + "\n\nHistory:" + h)
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
def pmatch(pat:Expression, e:Expression, c:Context, ante:immutable.IndexedSeq[Formula]):Context = {
  def patExn(pat:Expression, e:Expression, additional:String = "N/A"):PatternMatchError = { PatternMatchError("Expected expression " + e + " to match pattern " + pat + " Additional message?: " + additional)}
  val exn:PatternMatchError = patExn(pat, e)
  def atom(e1:Expression, e2:Expression, additional:String = "N/A") = {
    if(e1 == e2) { Context.empty } else { throw new PatternMatchError("Expected atomic expression " + e2 + " to match atomic pattern " + e1 + " Additional message?: " + additional) }
  }
  def matchDef(id:String) = {
    if(e == c.getDef(id)) {
      Context.empty
    } else {
      throw PatternMatchError("Bound variable pattern " + id + " only matches expression " + c.getDef(id) + " but instead got " + e)
    }
  }
  pat match {
    case PredOf(Function(id, _, _, _, _), _) if c.hasDef(id) =>  matchDef(id)
    case FuncOf(Function(id, _, _, _, _), _) if c.hasDef(id) => matchDef(id)
    case PredicationalOf(Function(id,_,_,_,_), _) if c.hasDef(id) => matchDef(id)
    case UnitPredicational(id, _) if c.hasDef(id) => matchDef(id)
    case BaseVariable(id, _, _) if c.hasDef(id) => matchDef(id)
    case UnitFunctional(id, _, _) if c.hasDef(id) => matchDef(id)
    case ProgramConst(id, _) if c.hasDef(id) => matchDef(id)
    case SystemConst(id, _) if c.hasDef(id) => matchDef(id)
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
      try { pmatch(pat1,e,c,ante) }
      catch {case _ : Throwable => pmatch(pat2,e,c,ante) }
    case PredOf(Function("inter", _, _, _, _), Pair(pat1, pat2)) =>
      pmatch(pat1,e,c,ante).inter(pmatch(pat2,e,c,ante))
    case PredOf(Function("neg", _, _, _, _) , pat1) =>
      try { pmatch(pat1,e,c,ante)}
      catch {case _ : Throwable => return Context.empty }
      throw patExn(pat1, e, "Pattern should not have matched but did: " + pat1.prettyString)
    case PredOf(Function("assm", _, _, _, _) , which) if patIdent(which).isDefined && c.hasAssm(patIdent(which).get)  =>
      val ident = patIdent(which).get
      val f = c.getAssm(ident, ante)
      if(e == f) {
        Context.empty
      } else {
        throw patExn(pat, e, "Expression did not match assumption " + ident)
      }
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
      try { pmatch(pat1,e,c,ante) }
      catch {case _ : Throwable => pmatch(pat2,e,c,ante) }
    case FuncOf(Function("inter", _, _, _, _), Pair(pat1, pat2)) =>
      pmatch(pat1,e,c,ante).inter(pmatch(pat2,e,c,ante))
    case FuncOf(Function("neg", _, _, _, _) , pat1) =>
      try { pmatch(pat1,e,c,ante) }
      catch {case _ : Throwable => return Context.empty }
      throw PatternMatchError("Pattern should not have matched but did: " + pat1.prettyString)
      // TODO: Wild ODE system should only match ODE systems, but because parser prefers diffprogramconst to programconst we do this instead
    case FuncOf(Function("assm", _, _, _, _) , which) if patIdent(which).isDefined && c.hasAssm(patIdent(which).get)  =>
      val ident = patIdent(which).get
      val f = c.getAssm(ident, ante)
      if(e == f) {
        Context.empty
      } else {
        throw patExn(pat, e, "Expression did not match assumption " + ident)
      }
    case PredicationalOf(Function("assm", _, _, _, _) , which) if patIdent(which).isDefined && c.hasAssm(patIdent(which).get)  =>
      val ident = patIdent(which).get
      val f = c.getAssm(ident, ante)
      if(e == f) {
        Context.empty
      } else {
        throw patExn(pat, e, "Expression did not match assumption " + ident)
      }
    case ProgramConst("wild",AnyArg) => Context.empty
    case ODESystem(DifferentialProgramConst("wild",_),_) => Context.empty
    case FuncOf(Function("wild", _, _, _, _), pat) => Context.empty
    case FuncOf(Function("wild", _, _, _, _), pat) => Context.empty
    case PredOf(Function("wild", _, _, _, _), pat) => Context.empty
    case PredicationalOf(Function("wild", _, _, _, _), pat) => Context.empty
    case UnitPredicational("wild", _) => Context.empty
    case BaseVariable(vname, _, _) =>
      if(vname.last == '_' && !c.hasDef(vname)) {
        Context.ofDef(vname.dropRight(1), e)
      } else if (pat == e) {
        Context.empty
      } else {
        throw exn
      }
    case FuncOf(fn: Function, Nothing) =>
      if(fn.name.last == '_' && !c.hasDef(fn.name)) {
        Context.ofDef(fn.name.dropRight(1), e)
      } else if (pat == e) {
        Context.empty
      } else {
        throw exn
      }
    case UnitFunctional(name: String, _, _) =>
      if(name.last == '_' && !c.hasDef(name)) {
        Context.ofDef(name.dropRight(1), e)
      } else if (pat == e) {
        Context.empty
      } else {
        throw exn
      }
    case DifferentialProgramConst(name: String,  _) =>
      if(name.last == '_' && !c.hasDef(name)) {
        Context.ofDef(name.dropRight(1), e)
      } else if (pat == e) {
        Context.empty
      } else {
        throw exn
      }
    case ProgramConst(name: String, _) =>
      if(name.last == '_' && !c.hasDef(name)) {
        Context.ofDef(name.dropRight(1), e)
      } else if (pat == e) {
        Context.empty
      } else {
        throw exn
      }
    case SystemConst(name: String, _) =>
      if(name.last == '_' && !c.hasDef(name)) {
        Context.ofDef(name.dropRight(1), e)
      } else if (pat == e) {
        Context.empty
      } else {
        throw exn
      }
    case PredicationalOf(fn: Function, _) =>
      if(fn.name.last == '_' && !c.hasDef(fn.name)) {
        Context.ofDef(fn.name.dropRight(1), e)
      } else if (pat == e) {
        Context.empty
      } else {
        throw exn
      }
    case PredOf(fn: Function, _) =>
      if(fn.name.last == '_' && !c.hasDef(fn.name)) {
        Context.ofDef(fn.name.dropRight(1), e)
      } else if (pat == e) {
        Context.empty
      } else {
        throw exn
      }
    case UnitPredicational(name:String, _) =>
      if(name.last == '_' && !c.hasDef(name)) {
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
          pmatch(e1.left, e2.left,c,ante).concat(pmatch(e1.right,e2.right,c,ante))
        case (e1: Minus, e2: Minus) =>
          pmatch(e1.left, e2.left,c,ante).concat(pmatch(e1.right,e2.right,c,ante))
        case (e1: Times, e2: Times) =>
          pmatch(e1.left, e2.left,c,ante).concat(pmatch(e1.right,e2.right,c,ante))
        case (e1: Divide, e2: Divide) =>
          pmatch(e1.left, e2.left,c,ante).concat(pmatch(e1.right,e2.right,c,ante))
        case (e1: Power, e2: Power) =>
          pmatch(e1.left, e2.left,c,ante).concat(pmatch(e1.right,e2.right,c,ante))
        case (e1: Pair, e2: Pair) =>
          pmatch(e1.left, e2.left,c,ante).concat(pmatch(e1.right,e2.right,c,ante))
        case (e1: Equal, e2: Equal) =>
          pmatch(e1.left, e2.left,c,ante).concat(pmatch(e1.right,e2.right,c,ante))
        case (e1: NotEqual, e2: NotEqual) =>
          pmatch(e1.left, e2.left,c,ante).concat(pmatch(e1.right,e2.right,c,ante))
        case (e1: GreaterEqual, e2: GreaterEqual) =>
          pmatch(e1.left, e2.left,c,ante).concat(pmatch(e1.right,e2.right,c,ante))
        case (e1: Greater, e2: Greater) =>
          pmatch(e1.left, e2.left,c,ante).concat(pmatch(e1.right,e2.right,c,ante))
        case (e1: LessEqual, e2: LessEqual) =>
          pmatch(e1.left, e2.left,c,ante).concat(pmatch(e1.right,e2.right,c,ante))
        case (e1: Less, e2: Less) =>
          pmatch(e1.left, e2.left,c,ante).concat(pmatch(e1.right,e2.right,c,ante))
        case (e1: And, e2: And) =>
          pmatch(e1.left, e2.left,c,ante).concat(pmatch(e1.right,e2.right,c,ante))
        case (e1: Or, e2: Or) =>
          pmatch(e1.left, e2.left,c,ante).concat(pmatch(e1.right,e2.right,c,ante))
        case (e1: Imply, e2: Imply) =>
          pmatch(e1.left, e2.left,c,ante).concat(pmatch(e1.right,e2.right,c,ante))
        case (e1: Equiv, e2: Equiv) =>
          pmatch(e1.left, e2.left,c,ante).concat(pmatch(e1.right,e2.right,c,ante))
        case (e1: Box, e2: Box) =>
          pmatch(e1.program, e2.program,c,ante).concat(pmatch(e1.child,e2.child,c,ante))
        case (e1: Diamond, e2: Diamond) =>
          pmatch(e1.program, e2.program,c,ante).concat(pmatch(e1.child,e2.child,c,ante))
        case (e1: Choice, e2: Choice) =>
          pmatch(e1.left, e2.left,c,ante).concat(pmatch(e1.right,e2.right,c,ante))
        case (e1: Compose, e2: Compose) =>
          pmatch(e1.left, e2.left,c,ante).concat(pmatch(e1.right,e2.right,c,ante))
        case (e1: DifferentialProduct, e2: DifferentialProduct) =>
          pmatch(e1.left, e2.left,c,ante).concat(pmatch(e1.right,e2.right,c,ante))
        case (e1: Forall, e2: Forall) =>
          if(e1.vars != e2.vars) { throw exn }
          else { pmatch(e1.child, e2.child,c,ante) }
        case (e1: Exists, e2: Exists) =>
          if(e1.vars != e2.vars) { throw exn }
          else { pmatch(e1.child, e2.child,c,ante) }
        case (e1: Assign, e2: Assign) => atom(e1,e2)
        case (e1: AssignAny, e2: AssignAny) => atom(e1,e2)
        case(e1:Test, e2:Test) => pmatch(e1.cond, e2.cond,c,ante)
        case(e1:ODESystem, e2:ODESystem) => pmatch(e1.ode,e2.ode,c,ante).concat(pmatch(e1.constraint,e2.constraint,c,ante))
        case(e1:AtomicODE, e2:AtomicODE) =>
          if (e1.xp != e2.xp) { throw exn }
          else { pmatch(e1.e, e2.e,c,ante)}
        case(e1:Neg, e2:Neg) => pmatch(e1.child,e2.child,c,ante)
        case(e1:Differential, e2:Differential) => pmatch(e1.child,e2.child,c,ante)
        case(e1:Not, e2:Not) => pmatch(e1.child,e2.child,c,ante)
        case(e1:DifferentialFormula, e2:DifferentialFormula) => pmatch(e1.child,e2.child,c,ante)
        case(e1:Loop, e2:Loop) => pmatch(e1.child,e2.child,c,ante)
        case(e1:Dual, e2:Dual) => pmatch(e1.child,e2.child,c,ante)
        case(e1:FuncOf, e2:FuncOf) =>
          if (e1.func == e2.func) { pmatch(e1.child, e2.child, c,ante)}
          else {throw PatternMatchError("Functions did not match in pattern match: " + e1.func + " vs. " + e2.func)}
      }
  }
}
def doesMatch(pat:Expression, e:Expression, c:Context, ante:immutable.IndexedSeq[Formula]):Boolean = {try {pmatch(pat, e,c, ante); true} catch {case _:Throwable => false}}
}
