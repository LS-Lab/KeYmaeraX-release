package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.{NoProofTermProvable, ProvableSig}

/**
  * Created by bbohrer on 12/2/16.
  */
object Kaisar {
  abstract class Resource
  case class ProgramVariable(a:Variable) extends Resource
  case class FactVariable(p:Variable) extends Resource

  type ProofStep = (List[Resource], BelleExpr)

  abstract class Statement
  case class Run (a:Variable, hp:Program) extends Statement
  case class Show (x:Variable, phi:Formula, proof: ProofStep) extends Statement

  type Proof = (Formula, List[Statement])

  case class History (vmap:Map[Variable,(Int,Program)], tmap:Map[Int,(Variable,Program)]){
    def add(a:Variable, hp:Program): History = {
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
    }
    /* TODO: Better to skip *all* skippable formulas, but that makes recovering the original theorem
     * more work, so do it later. */
    def extend(phi:Formula,tmin:Int,tmax:Int):Formula = {
      var t = tmax
      var p = phi
      while(t >= tmin) {
        p = Box(tmap(t)._2, p)
        t = t -1
      }
      p
    }
  }
  object History {
    var empty = new History(Map(), Map())
  }

  case class Context (xmap:Map[Variable,(Int,Formula,Provable)], fmap:Map[Formula, Provable]){
    def concat(other: Context): Context = Context(xmap.++(other.xmap), fmap.++(other.fmap))
    def apply(p:FactVariable):(Int, Formula,Provable) = xmap(p.p)
    def add(a:Variable, phi:Formula, pr:Provable,time:Int): Context = {
      val nextTime = xmap.size
      Context(xmap.+((a,(time,phi,pr))),fmap.+((phi,pr)))
    }
    def findProvable(fml:Formula):Provable = fmap(fml)
  }
  object Context {
    var empty = new Context(Map(),Map())
  }

  private def min(seq:Seq[Int]):Int =
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

  /* @requires  provable is
  *  [a](P_j -> ... -> P_n -> Q) |- [a]Q
  *  -----------------------------------
  *                   [a]Q
  *
  *  facts is ([a]P_j, ..., [a]P_n)
  *  @ensures provable is proved.
  * */
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
  }
}
