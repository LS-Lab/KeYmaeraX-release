package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.ExpressionTraversal.{ExpressionTraversalFunction, StopTraversal}
import edu.cmu.cs.ls.keymaerax.core.{Variable, _}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary.{existsR, _}
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
  case class RBConsequence(x:Variable, fml:Formula) extends RuleSpec
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
  case class Inv(x:Variable, fml:Formula, pre:SP, inv:SP, tail:IP) extends IP
  case class Ghost(gvar:Variable, gterm:Term, ginv:Formula, x0:Term, pre:SP, inv:SP, tail:IP) extends IP
  case class Finally(tail:SP) extends IP

  abstract class FP
  case class FPat(e:Expression) extends FP
  case class FMP(fp1: FP, fp2:FP) extends FP
  case class FInst(fp:FP, t:Term) extends FP

  abstract class SP
  case class Show(phi:Formula, proof: UP) extends SP
  case class SLet(pat:Expression, e:Expression, tail:SP) extends SP
  case class FLet(x:VBase, arg:VBase, e:Expression, tail:SP) extends SP
  case class Note(x:Variable, fp:FP, tail: SP) extends SP
  case class Have(x:Variable, fml:Formula, sp:SP, tail: SP) extends SP
  case class BRule(r:RuleSpec, tails: List[SP]) extends SP
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
      import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._
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
      //val (postRen, _) = partAfter(renSteps, isThisRename)
      //val (_, preSub) = partBefore(subSteps, isThisRename)
      //TODO: might be bug val fullName = postChange match {case Nil => Variable(x) case ((y:HCRename)::ys) => y.permName case _ => ???}
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
    def getAssm(ident:String, ante:immutable.IndexedSeq[Formula]):Formula = ante(gmap(Variable(ident)).checkAnte.index0)
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
        else if(ident.last == '_' && defmap.contains(ident.dropRight(1))) {
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
    def patIdent(e:Expression):Option[String] = {
      e match {
        case PredOf(Function(id, _, _, _, _), _)  => Some(id)
        case FuncOf(Function(id, _, _, _, _), _) => Some(id)
        case PredicationalOf(Function(id, _, _, _, _), _) => Some(id)
        case UnitPredicational(id, _) => Some(id)
        case BaseVariable(id, _, _) => Some(id)
        case UnitFunctional(id, _, _) => Some(id)
        case ProgramConst(id) => Some(id)
        case SystemConst(id) => Some(id)
        case _ => None
      }
    }
    def matchesAssm(i:Int,pat:Expression):Boolean = {
      patIdent(pat) match {
        case None => false
          // TODO: Faster: do only index cmp
        case Some(id) =>
          val hasOne = c.hasAssm(id)
          println("Checking for assm: " ,c,id,ante,i,ante(i), hasOne)
          hasOne && c.getAssm(id,ante) == ante(i)
      }
    }
    val inds:immutable.IndexedSeq[Int] = withFacts.subgoals.head.ante.zipWithIndex.filter({case (f,i) => !pats.exists({case pat =>
      val dm = doesMatch(pat, f,c)
      val ma = matchesAssm(i,pat)
      //println("dm ", pat, f, c, dm)
      //println("ma ", i, pat, ma)
      dm || ma})}).map({case (f,i) => i}).reverse
    //TODO: Optimize the default case
    val indss = if(use.isEmpty) { immutable.IndexedSeq[Int]()} else {inds}
    val pr = indss.foldLeft[Provable](withFacts)({case (pr2:Provable,i:Int) => pr2(HideLeft(AntePos(i)),0)})
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

  // //DifferentialProgramConst(name) ProgramConst(name) FuncOf(Function(name, domain = Unit, sort = Real), Nothing)  PredOf(Function(name, domain = Unit, sort = Bool), Nothing)
  //ExpressionTraversal.traverse(doTravel(h,c), e).get
  private def doTravel(h:History,c:Context, at:Option[TimeName]):ExpressionTraversalFunction = {
    new ExpressionTraversalFunction() {
      override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] =
      //case v: Variable => Right(resolve(v.name, at))

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
          case _ => Left(None)
        }
      override def preP(p: PosInExpr, e: Program): Either[Option[StopTraversal], Program] =
        e match {
          case ProgramConst(fname) if c.hasDef(fname) =>
            Right(c.getDef(fname).asInstanceOf[Program])
          case SystemConst(fname) if c.hasDef(fname) =>
            Right(c.getDef(fname).asInstanceOf[Program])
          case DifferentialProgramConst(fname,_) if c.hasDef(fname) =>
            Right(c.getDef(fname).asInstanceOf[Program])
          case _ => Left(None)
        }
    }
  }
  // TODO: Support time-travel
  def expand(e:Term, h:History, c:Context, at:Option[TimeName]):Term       = {ExpressionTraversal.traverse(doTravel(h,c, at), e).get}
  def expand(e:Formula, h:History, c:Context, at:Option[TimeName]):Formula = {
    val traveled = ExpressionTraversal.traverse(doTravel(h,c, at), e)
    traveled.get
    //c.usubst(traveled.get)
  }
  def expand(e:Program, h:History, c:Context, at:Option[TimeName]):Program = {ExpressionTraversal.traverse(doTravel(h,c, at), e).get}
  def expand(e:Expression, h:History, c:Context, at:Option[TimeName]):Expression = {
    e match {
      case t:Term => expand(t,h,c,at)
      case f:Formula => expand(f,h,c,at)
      case p:Program => expand(p,h,c,at)
    }
  }

  def uniqueMatch(pat:Expression, c:Context, ante:immutable.IndexedSeq[Formula]):Int = {
    val ident:Option[String] = pat match {case ns:NamedSymbol => Some(ns.name) case f:ApplicationOf => Some(f.func.name ) case _ => None}
    val ofIdent:Option[Position] = ident.flatMap{case x => c.gmap.get(Variable(x))}
    ofIdent match {
      case Some(pos)  => pos.checkAnte.index0
      case None =>
        val matches:immutable.IndexedSeq[(Formula,Int)] = ante.zipWithIndex.filter({case (fml,_) => doesMatch(pat, fml,c)})
        matches.toList match {
          case ((_,i)::Nil) => i
          case _ => throw new Exception("Non-unique match in pattern-matching construct")
        }

    }
  }

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
              case e : UnificationException => throw new Exception("proposition mismatch in modus ponens", e)
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
              val q2=repvTerm(q,xs.head, term)
              val ax=AxiomInfo("all instantiate").provable
              //val subst2 = USubst(immutable.IndexedSeq.concat(immutable.IndexedSeq[SubstitutionPair](SubstitutionPair(vpair._1,vpair._2),SubstitutionPair(pair._1,pair._2)), subst.usubst.subsDefsInput))
              val p2:Provable=renu.toForward(ax).underlyingProvable
              val seq = Sequent(ante, immutable.IndexedSeq(q2))
              val impPos = AntePos(ante.length)
              val allPos = AntePos(ante.length+1)
              val pr1b = renu.toForward(NoProofTermProvable(pr1)).underlyingProvable
                //renupr1(subst.usubst)
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

/* Two histories for base case/ind case so we can return the name of the invariant formula in both states*/
def collectLoopInvs(ip: IP,h:History,hh:History,c:Context):(List[Variable], List[Formula], List[Formula], List[SP], List[SP], IP) = {
  ip match {
    case Inv(x, fml, pre, inv, tail) =>
      val (vs, f,ff, p,i,t) = collectLoopInvs(tail,h,hh,c)
      val baseFml = expand(fml,h,c, None)
      val indFml = expand(fml,hh,c, None)
      println("CC Expanding invariant formula: ", fml, " becomes ", expand(fml,h,c, None), " under history ", h, " and context ", c)
      println("DD Expanding invariant formula: ", fml, " becomes ", expand(fml,hh,c, None), " under history ", hh, " and context ", c)
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
      println("AA Expanding invariant formula: ", fml, " becomes ", expand(fml,h,c, None), " under history ", h, " and context ", c)
      println("BB Expanding invariant formula: ", fml, " becomes ", expand(fml,hh,c, None), " under history ", hh, " and context ", c)
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
  val gg = g // interpret(andL('L)*, g)
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
      // Inv (fml: Formula, pre: SP, inv: SP, tail: IP)
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
            println("BASE0 I had ", tail.prettyString)
            DebuggingTactics.debug("BASE0 I WANTED", doPrint = true) & useAt(NoProofTermProvable(tail), PosInExpr(Nil))(1) & DebuggingTactics.debug("BASE0B", doPrint = true)
          case (fml, pre:SP)::fps =>
            val preSeq = Sequent(ante, immutable.IndexedSeq(fml))
            println("BASEN " + (done.length) + ": " + preSeq)
            val tail = eval(pre, h, c, Provable.startProof(preSeq))
            assert(tail.isProved, "Failed to prove additional base case subgoal " + fml + " in subproof " + pre + ", left behind provable " + tail.prettyString)
            val e1 = useAt(NoProofTermProvable(tail), PosInExpr(Nil))(1)
            val e2 = baseCase(fps, fml::done)
            andR(1) <(DebuggingTactics.debug("left", doPrint = true) & e1, DebuggingTactics.debug("right", doPrint = true) & e2)
        }
      }
      def indCase(fmlPres:List[(Formula,SP)], done:immutable.IndexedSeq[Formula] = immutable.IndexedSeq()):BelleExpr = {
        fmlPres match {
          case Nil => ???
          case (fml, inv:SP)::Nil =>
            val invSeq = Sequent(anteConst ++ done ++ immutable.IndexedSeq(fml), immutable.IndexedSeq(Box(a,fml)))
            println("Ind case useat base hiding " + (invs.length - (done.length + 1)) + ": " + invSeq)
            val e = hideL('Llast)*(invs.length - (done.length + 1))
            val tail = eval(inv, hh, c, Provable.startProof(invSeq))
            assert(tail.isProved, "Failed to prove first inductive case subgoal " + fml + " in subproof " + inv + ", left behind provable " + tail.prettyString)
            DebuggingTactics.debug("preHide icubh", doPrint = true) & e & DebuggingTactics.debug("postHide IND0", doPrint = true) & useAt(NoProofTermProvable(tail), PosInExpr(Nil))(1)
          case (fml, pre:SP)::fps =>
            val invSeq = Sequent(anteConst ++ done ++ immutable.IndexedSeq(fml), immutable.IndexedSeq(Box(a,fml)))
            println("Ind case useat inductive hiding " + (invs.length - done.length) + ": " + invSeq)
            val hide = hideL('Llast)*(invs.length - (done.length + 1))
            val tail = NoProofTermProvable(eval(pre, hh, c, Provable.startProof(invSeq)))
            assert(tail.isProved, "Failed to prove additional inductive case subgoal " + fml + " in subproof " + pre + ", left behind provable " + tail.prettyString)
            val e1 = DebuggingTactics.debug("preHide", doPrint = true) &  hide & DebuggingTactics.debug("postINDN", doPrint = true)& useAt(tail, PosInExpr(Nil))(1)
            val e2 = indCase(fps, done ++ immutable.IndexedSeq(fml))
            boxAnd(1) & andR(1) <(e1, e2)
        }
      }
      //by(t: (ProvableSig, SuccPosition) => ProvableSig)

      //(andL('L)*(Math.max(0, invs.length-1)))
      val unpack:BelleExpr =
        if (invs.length > 1) { andL('L)*(invs.length-1) }
        else {
          def rot(pr:ProvableSig,p:SuccPosition):ProvableSig = NoProofTermProvable(rotAnte(pr.underlyingProvable))
          // (t: (ProvableSig, SuccPosition) => ProvableSig)
          import edu.cmu.cs.ls.keymaerax.btactics.Idioms._
          val e =TacticFactory.TacticForNameFactory("ANON").by((pos: ProvableSig, seq: SuccPosition) =>{rot(pos,seq)})
          e(1) & DebuggingTactics.debug("Rotated the ante for you", doPrint = true)
          //by ((pos: Position, seq: Sequent) =>{???})
          //by (rot:((ProvableSig,SuccPosition) => ProvableSig))
        }
      val e:BelleExpr = DebuggingTactics.debug("XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX", doPrint = true) &
        DLBySubst.loop(conj, pre = nil)(1) <(DebuggingTactics.debug("pre-base case", doPrint = true) &
          unsaveVars(gg, bvs, rewritePost = true) & DebuggingTactics.debug("base case", doPrint = true)
          & baseCase(baseFmls.zip(pres)), DebuggingTactics.debug("use case", doPrint = true) &  nil,
            DebuggingTactics.debug("preductive case", doPrint = true) &
          unpack & DebuggingTactics.debug("inductive case", doPrint = true)
          & indCase(indFmls.zip(invs)))
      val pr:Provable = interpret(e, ggg)
      val pr1 = rotAnte(pr)
      //val pr1 = pr
      println("Done first step of interpreting thing: " + pr1.prettyString)
      // polyK(pr, invSeq.map{case fml => interpret(TactixLibrary.close, Provable.startProof(Sequent(invSeq,immutable.IndexedSeq(fml))))}.toList)
      eval(lastTail, hh, cc, pr1, nInvs+1)
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
      def flatAnd(f:Formula):List[Formula] = {f match {case And(a,b) => flatAnd(a) ++ List(b) case ff => List(ff)}}
      def unflatAnd(l:List[Formula]):Formula = l match {case List(l) => l case (x::xs) => And(x,unflatAnd(xs))}
      val conj = unflatAnd(flatAnd(g4.subgoals.head.ante.last))
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
    println("DEBUGGGGG ME1: ", acc.prettyString, last, v, vv)
    val e:BelleExpr =
      DebuggingTactics.debug("DEBUGGGGG ME2:", doPrint = true) &
      discreteGhost(v,Some(vv))(1) &
      DebuggingTactics.debug("DEBUGGGGG ME3:", doPrint = true) &
      DLBySubst.assignEquality(1) &
      DebuggingTactics.debug("DEBUGGGGG ME4:", doPrint = true) &
      TactixLibrary.exhaustiveEqR2L(hide=false)('Llast) &
      DebuggingTactics.debug("DEBUGGGGG ME5:", doPrint = true) &
      TactixLibrary.eqL2R(-last)(1) &
      DebuggingTactics.debug("DEBUGGGGG ME6:", doPrint = true) &
      (if (invCurrent) {TactixLibrary.eqL2R(-last)(1 + accVs.length - last)} else { nil }) &
      DebuggingTactics.debug("DEBUGGGGG ME7:", doPrint = true) /*&
      DebuggingTactics.debug("whomst " + (accVs.length - last), doPrint = true)*/
    (interpret(e, acc), vv::accVs)
  })
}

private def unsaveVars(pr:Provable, bvs:Set[Variable], rewritePost:Boolean = false, hide:Boolean = true):BelleExpr = {
  val poses = List.tabulate(bvs.size)({case i => AntePosition(bvs.size + pr.subgoals.head.ante.length - i)})
  poses.foldLeft(nil)({case (acc, pos) =>
    val numRens = pos.index0
    val rens = List.tabulate(numRens)({case i => TactixLibrary.eqL2R(pos)(AntePosition(1 + i))}).foldLeft(nil)({case (acc,e) => acc & e})
    val doHide = if(hide) {hideL(pos)} else nil
    val renss = if(rewritePost) {rens & DebuggingTactics.debug("Rewriting post " + pos, doPrint = true) & TactixLibrary.eqL2R(pos)(SuccPosition(1))} else rens
    acc & DebuggingTactics.debug("unsaving " + pos, doPrint = true) & /*(TactixLibrary.eqL2R(pos)('L)*)*/ renss & DebuggingTactics.debug("unsave huh " + pos, doPrint = true)& doHide & DebuggingTactics.debug("unsaved " + pos, doPrint = true)})
}

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
          val hh = h.update(hp.x.name, theta)
          var gsub:Option[Provable] = None
          try {
            gsub = Some(interpret(useAt("[:=] assign")(1), g))
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
        case (RBConsequence(varName:Variable,fml:Formula), Box(a,Box(b,p))) =>
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
          val e = poses.foldLeft(nil)({case (acc, pos) => acc & TactixLibrary.eqR2L(pos)(-1) & hideL(pos)})
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
          val ppa4 = interpret(useAt(NoProofTermProvable(pr2), PosInExpr(Nil))(1), ppa35)
          val ppb = Provable.startProof(pp2.subgoals.tail.head)
          val ppb1 = interpret(hideR(1), ppb)
          val ppb2 = interpret(boxAnd(1) & andR(1),ppb1)
          val ppc = Provable.startProof(ppb2.subgoals.tail.head)
          val ppc1 = interpret(e, ppc)
          val ppc2 = interpret(useAt("V vacuous")(1), ppc1)
          val ppc3 = interpret(prop, ppc2)
          val ppd = Provable.startProof(ppb2.subgoals.head)
          val ppd1 = interpret(unsaveVars(g, bvs.toSet, rewritePost = false, hide = false), ppd)
          //val ppd1 = interpret(hideL('Llast)*bvs.toSet.size, ppd)
          val ppd2 = interpret(useAt(NoProofTermProvable(pr1),PosInExpr(Nil))(1), ppd1)
          val b3 = ppb2(ppd2,0)
          val b2 = b3(ppc3,0)
          val b4 = pp2(ppa4,0)
          val prr =b4(b2,0)

          /*val prr:Provable = interpret(cut(Box(a,FG2)) <(DebuggingTactics.debug("DooD " + (G1.length-1), doPrint = true) & hideL(-1)*(G1.length-1) & DebuggingTactics.debug("hmmm", doPrint = true) & monb & ((andL('L))*) & DebuggingTactics.debug("The useat time ", doPrint = true ) & useAt(NoProofTermProvable(pr2), PosInExpr(Nil))(1),
            hideR(1) & boxAnd(1) & andR(1) & DebuggingTactics.debug("stuff", doPrint = true) <( e & useAt("V vacuous")(1) & prop, hideL('Llast)*bvs.toSet.size & useAt(NoProofTermProvable(pr1),PosInExpr(Nil))(1))), pp1)*/
          prr
        case (RBCase(), Box(Choice(a,b),p)) =>
          assertBranches(sp.length, 2)
          val seq1:Sequent = Sequent(sequent.ante, immutable.IndexedSeq(Box(a,p)) ++ sequent.succ.tail)
          val seq2:Sequent = Sequent(sequent.ante, immutable.IndexedSeq(Box(b,p)) ++ sequent.succ.tail)
          val pr1:Provable = eval(sp(0),h,c,Provable.startProof(seq1))
          val pr2:Provable = eval(sp(1),h,c,Provable.startProof(seq2))
          // TODO: Not right, need a cut somewhere
          val prr:Provable = interpret(TactixLibrary.choiceb(1) & andR(1), g)
          prr(pr1,0)(pr2,0)
        case (RBAssume(x:Variable,fml:Formula),Imply(p,q)) =>
          assertBranches(sp.length, 1)
          val newPos = AntePos(sequent.ante.length)
          val cc:Context = c.add(x,newPos)
          eval(sp.head, h, cc, g(ImplyRight(SuccPos(0)),0))
        case (RBSolve(t:Variable,fmlT:Formula,dc:Variable,fmlDC:Formula,sols:List[(Variable,Formula)]),Box(ODESystem(ode,q),p)) =>
          val pr = interpret(solve(1) & allR(1) & implyR(1), g)
          eval(sp.head, h, c, pr)
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
    case Show(phi:Formula, proof: UP)  =>
      val expanded = expand(phi,h,c, None)
      val cc = pmatch(expanded, goal,c)
      val ccc = c.concat(cc)
      eval(proof, h, ccc, g)
    case SLet(pat:Expression, e:Expression, tail:SP) =>
      //TODO: Expand e?
      val cc = pmatch(expand(pat,h,c,None), expand(e,h,c, None),c)
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
      val gg = g(Cut(fmlExpanded),0)(HideRight(SuccPos(0)),1)(prOut,1)
      eval(tail,h,c.add(x,newPos), gg)
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
def pmatch(pat:Expression, e:Expression, c:Context):Context = {
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
    case ProgramConst(id) if c.hasDef(id) => matchDef(id)
    case SystemConst(id) if c.hasDef(id) => matchDef(id)
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
      try { pmatch(pat1,e,c) }
      catch {case _ : Throwable => pmatch(pat2,e,c) }
    case PredOf(Function("inter", _, _, _, _), Pair(pat1, pat2)) =>
      pmatch(pat1,e,c).inter(pmatch(pat2,e,c))
    case PredOf(Function("neg", _, _, _, _) , pat1) =>
      try { pmatch(pat1,e,c); throw patExn(pat1, e, "Pattern should not have matched but did: " + pat1.prettyString)}
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
      try { pmatch(pat1,e,c) }
      catch {case _ : Throwable => pmatch(pat2,e,c) }
    case FuncOf(Function("inter", _, _, _, _), Pair(pat1, pat2)) =>
      pmatch(pat1,e,c).inter(pmatch(pat2,e,c))
    case FuncOf(Function("neg", _, _, _, _) , pat1) =>
      try { pmatch(pat1,e,c); throw PatternMatchError("Pattern should not have matched but did: " + pat1.prettyString)}
      catch {case _ : Throwable => Context.empty }
      // TODO: Wild ODE system should only match ODE systems, but because parser prefers diffprogramconst to programconst we do this instead
    case ProgramConst("wild") => Context.empty
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
    case ProgramConst(name: String) =>
      if(name.last == '_' && !c.hasDef(name)) {
        Context.ofDef(name.dropRight(1), e)
      } else if (pat == e) {
        Context.empty
      } else {
        throw exn
      }
    case SystemConst(name: String) =>
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
          pmatch(e1.left, e2.left,c).concat(pmatch(e1.right,e2.right,c))
        case (e1: Minus, e2: Minus) =>
          pmatch(e1.left, e2.left,c).concat(pmatch(e1.right,e2.right,c))
        case (e1: Times, e2: Times) =>
          pmatch(e1.left, e2.left,c).concat(pmatch(e1.right,e2.right,c))
        case (e1: Divide, e2: Divide) =>
          pmatch(e1.left, e2.left,c).concat(pmatch(e1.right,e2.right,c))
        case (e1: Power, e2: Power) =>
          pmatch(e1.left, e2.left,c).concat(pmatch(e1.right,e2.right,c))
        case (e1: Pair, e2: Pair) =>
          pmatch(e1.left, e2.left,c).concat(pmatch(e1.right,e2.right,c))
        case (e1: Equal, e2: Equal) =>
          pmatch(e1.left, e2.left,c).concat(pmatch(e1.right,e2.right,c))
        case (e1: NotEqual, e2: NotEqual) =>
          pmatch(e1.left, e2.left,c).concat(pmatch(e1.right,e2.right,c))
        case (e1: GreaterEqual, e2: GreaterEqual) =>
          pmatch(e1.left, e2.left,c).concat(pmatch(e1.right,e2.right,c))
        case (e1: Greater, e2: Greater) =>
          pmatch(e1.left, e2.left,c).concat(pmatch(e1.right,e2.right,c))
        case (e1: LessEqual, e2: LessEqual) =>
          pmatch(e1.left, e2.left,c).concat(pmatch(e1.right,e2.right,c))
        case (e1: Less, e2: Less) =>
          pmatch(e1.left, e2.left,c).concat(pmatch(e1.right,e2.right,c))
        case (e1: And, e2: And) =>
          pmatch(e1.left, e2.left,c).concat(pmatch(e1.right,e2.right,c))
        case (e1: Or, e2: Or) =>
          pmatch(e1.left, e2.left,c).concat(pmatch(e1.right,e2.right,c))
        case (e1: Imply, e2: Imply) =>
          pmatch(e1.left, e2.left,c).concat(pmatch(e1.right,e2.right,c))
        case (e1: Equiv, e2: Equiv) =>
          pmatch(e1.left, e2.left,c).concat(pmatch(e1.right,e2.right,c))
        case (e1: Box, e2: Box) =>
          pmatch(e1.program, e2.program,c).concat(pmatch(e1.child,e2.child,c))
        case (e1: Diamond, e2: Diamond) =>
          pmatch(e1.program, e2.program,c).concat(pmatch(e1.child,e2.child,c))
        case (e1: Choice, e2: Choice) =>
          pmatch(e1.left, e2.left,c).concat(pmatch(e1.right,e2.right,c))
        case (e1: Compose, e2: Compose) =>
          pmatch(e1.left, e2.left,c).concat(pmatch(e1.right,e2.right,c))
        case (e1: DifferentialProduct, e2: DifferentialProduct) =>
          pmatch(e1.left, e2.left,c).concat(pmatch(e1.right,e2.right,c))
        case (e1: Forall, e2: Forall) =>
          if(e1.vars != e2.vars) { throw exn }
          else { pmatch(e1.child, e2.child,c) }
        case (e1: Exists, e2: Exists) =>
          if(e1.vars != e2.vars) { throw exn }
          else { pmatch(e1.child, e2.child,c) }
        case (e1: Assign, e2: Assign) => atom(e1,e2)
        case (e1: AssignAny, e2: AssignAny) => atom(e1,e2)
        case(e1:Test, e2:Test) => pmatch(e1.cond, e2.cond,c)
        case(e1:ODESystem, e2:ODESystem) => pmatch(e1.ode,e2.ode,c).concat(pmatch(e1.constraint,e2.constraint,c))
        case(e1:AtomicODE, e2:AtomicODE) =>
          if (e1.xp != e2.xp) { throw exn }
          else { pmatch(e1.e, e2.e,c)}
        case(e1:Neg, e2:Neg) => pmatch(e1.child,e2.child,c)
        case(e1:Differential, e2:Differential) => pmatch(e1.child,e2.child,c)
        case(e1:Not, e2:Not) => pmatch(e1.child,e2.child,c)
        case(e1:DifferentialFormula, e2:DifferentialFormula) => pmatch(e1.child,e2.child,c)
        case(e1:Loop, e2:Loop) => pmatch(e1.child,e2.child,c)
        case(e1:Dual, e2:Dual) => pmatch(e1.child,e2.child,c)
      }
  }
}
def doesMatch(pat:Expression, e:Expression, c:Context):Boolean = {try {pmatch(pat, e,c); true} catch {case _:Throwable => false}}


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
