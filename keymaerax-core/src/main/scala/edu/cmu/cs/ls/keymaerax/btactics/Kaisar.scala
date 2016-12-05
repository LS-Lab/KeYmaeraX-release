package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.core.{Box, Sequent, _}

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
    def add(a:Variable, phi:Formula, pr:Provable): Context = {
      val nextTime = xmap.size
      Context(xmap.+((a,(nextTime,phi,pr))),fmap.+((phi,pr)))
    }
    def findProvable(fml:Formula):Provable = fmap(fml)
  }
  object Context {
    var empty = new Context(Map(),Map())
  }

  private def min(seq:Seq[Int]):Int =
    seq.fold(Int.MaxValue)((x,y) => Math.min(x,y))
/*
  def prUseAt(pr:Provable, pos:Position) = {
    useAt(NoProofTermProvable(pr))

    val sig:ProvableSig = NoProofTermProvable(pr)
    val pex:PosInExpr = ???//PosInExpr(pos)
    useAt("useAt", sig, pex, None)
    //useAt(codeName: String, fact: ProvableSig, key: PosInExpr, inst: Option[Subst]=>Subst
  }*/

  def doGreatProof(): Provable = {
    /*
    val sg: Provable = ???
    val fact: Provable = ???
    cut("[x:=2;](x > 1 -> [x:=x-1;]x>0) -> [x:=2;](x > 1) -> [x:=2;][x:=x-1;]x>0".asFormula) < (
      useAt("K")(1),
      implyR(1) < (
        useAt(sg)(1),
        implyR(1) <(
          useAt(fact)(1),
          nil
          )
        )
      )
*/
    ???
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
          concE = G(1) & concE
          t = t -1
        }
        /*val addedProvable:Provable =
          SequentialInterpreter()(concE, BelleProvable(NoProofTermProvable(pr))) match {
            case BelleProvable(result, _) =>
              assert(result.isProved)
              result.underlyingProvable
              /* Need to actually plug in the assumptions here. */
              /*??? */
              /* TODO: Need to extend with previous programs. */
          }*/
        val addedProvable:Provable = doGreatProof()
        (hist, ctx.add(x,concl,addedProvable))
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
