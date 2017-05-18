package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
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

  class UP(use:List[Either[Expression,FP]], method:Method)

  abstract class IP
  case class Inv(fml:Formula, pre:SP, inv:SP, tail:IP)
  case class Ghost(gvar:Variable, gterm:Term, ginv:Formula, pre:SP, inv:SP, tail:IP)
  case class Finally(tail:SP)

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
  case class State (st:TimeName, tail: SP) extends SP
  case class Run (a:VBase, hp:Program, tail:SP) extends SP


  case class History (steps:List[TimeName], map:Map[VBase,List[(TimeName,Either[Term,Unit])]]){
    def advance(t:TimeName):History = {History(t::steps,map)}
  }
  object History {
    var empty = new History(List("init"), Map())
  }

  case class Context (gmap:Map[Variable,Position], defmap:Map[VBase, Expression]){
    def concat(other: Context): Context = Context(gmap.++(other.gmap), defmap.++(other.defmap))
    def add(x:Variable, at:AntePosition):Context = {
      Context(gmap.+((x,at)),defmap)
    }
  }
  object Context {
    var empty = new Context(Map(),Map())
  }

  /* TODO: I think these need to be filled in with gammas first */
  def pmatch(pat:Expression, e:Expression):Context = { ??? }
  def doesMatch(pat:Expression, e:Expression):Boolean = {try {pmatch(pat, e); true} catch {case _:Throwable => false}}

  def eval(method:Method, pr:Provable):Provable = {
    val e:BelleExpr =
      method match {
        case Simp() => SimplifierV3.fullSimpTac()
        case Auto() => TactixLibrary.master()
        case RCF() => TactixLibrary.QE()
        case CloseId() => TactixLibrary.closeId()
      }
    interpret(e, pr)
  }

  def eval(up:UP, h:History, c:Context, g:Provable):Provable = {
    val (use:List[Either[Expression,FP]], method) = up
    val pats = use.filter({case Left(_) => true case _ => false}).map({case Left(x) => x})
    val fps = use.filter({case Left(_) => true case _ => false}).map({case Left(x) => x})
    val seq = g.subgoals.head
    val ante = seq.ante
    val fprvs = fps.foldLeft[(List[Provable], immutable.IndexedSeq[Formula])]((Nil, ante))({case ((prvs, ante2), fp:FP) =>
        val prv:Provable = eval(fp, h, c, ante2)
        (prv::prvs, ante2 :+ prv.conclusion.ante.head)
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

  def expand(e:Term, c:Context):Term = {???}
  def expand(e:Formula, c:Context):Formula = {???}
  def expand(e:Program, c:Context):Program = {???}

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
        val t2 = expand(term,c)
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

  def eval(sp:SP, h:History, c:Context, g:Provable):Provable = {
    assert(g.subgoals.length == 1)
    assert(g.subgoals.head.succ.nonEmpty)
    val goal = g.subgoals.head.succ.head
    sp match {
      case Show (phi:Formula, proof: UP)  =>
        val cc = pmatch(phi, goal)
        val ccc = c.concat(cc)
        eval(proof, h, ccc, g)
      case Let (pat:Expression, e:Expression, tail:SP) =>
        val cc = pmatch(pat, e)
        eval(tail, h, cc, g)
      case Note (x:Variable, fp:FP, tail: SP)  =>
        val fpr:Provable = eval(fp, h, c, g.subgoals.head.ante)
        assert(fpr.conclusion.succ.nonEmpty)
        val size = fpr.conclusion.ante.size
        val newPos = AntePosition(size+1)
        val res:Formula = fpr.conclusion.succ.head
        eval(tail, h, c.add(x,newPos), fpr(Cut(res), 0)(fpr,1))
      case Have (x:Variable, fml:Formula, sp:SP, tail: SP)  =>
        val seq = Sequent(g.subgoals.head.ante, immutable.IndexedSeq(fml))
        val prIn = Provable.startProof(seq)
        val prOut = eval(sp, h, c, prIn)
        val size = prOut.conclusion.ante.size
        val newPos = AntePosition(size+1)
        eval(tail,h,c.add(x,newPos), g(Cut(fml),0)(prOut,1))
      case BRule (r:RuleSpec, tails: List[SP]) => ???
      case State (st:TimeName, tail: SP) => eval(tail,h.advance(st),c,g)
      case Run (a:VBase, hp:Program, tail:SP) => ???
    }
  }


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
  /* @requires  provable is
  *  [a](P_j -> ... -> P_n -> Q) |- [a]Q
  *  -----------------------------------
  *                   [a]Q
  *
  *  facts is ([a]P_j, ..., [a]P_n)
  *  @ensures provable is proved.
  * */
  /*
  def polyK(pr:Provable, facts:List[ProvableSig]): ProvableSig = {
    facts match {
      case Nil => /*NoProofTermProvable(pr) */ interpret(debug("foobar") & close, pr)
      case fact::facts =>
        val Box(a,Imply(p,q)) = pr.subgoals(0).ante(0)
        val e:BelleExpr =
          cut(Imply(Box(a,Imply(p,q)),Imply(Box(a,p),Box(a,q)))) <(
            debug("a") &
            /* Use */ implyL(-2) <(/* use */ debug("b") & close,
              debug("c") &
            //close &
            implyL(-2) <( debug("d") & hide(1) & debug("d") & cohideR(1) & useAt(fact, PosInExpr(Nil))(1)
              , debug("d1") & nil )
          ),
            debug("e") &
            /* show */ cohideR(2) & useAt("K modal modus ponens", PosInExpr(Nil))(1,Nil)) &
        hide(-1) &
        debug("before recur")
        polyK(interpret(e, pr).underlyingProvable, facts)
    }
  }

  def doGreatProof(userProof:ProvableSig, a:Program, maybeFacts:List[Formula], factProofs:List[ProvableSig], result:Formula): ProvableSig = {
    val pr = Provable.startProof(Box(a,result))
    val e = cutEZ(Box(a,implicate(maybeFacts,result)), debug("wat") & hide(1) & useAt(userProof,PosInExpr(Nil))(1))
    val pr2 = interpret(e,pr).underlyingProvable
    polyK(pr2, factProofs)
  }

  def eval(hist: History, ctx: Context, step:Statement):(History,Context) = {
    step match {
      case Run(a,hp) => (hist.add(a,hp), ctx)
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
