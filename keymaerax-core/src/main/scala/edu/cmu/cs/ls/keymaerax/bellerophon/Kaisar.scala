package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.pt.NoProofTermProvable

import scala.collection.mutable

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
    def extent(tp:(Int, Formula)):Int = {
      var (t, phi) = tp
      var fv = StaticSemantics(phi).fv
      while (fv.intersect(StaticSemantics(tmap(t)._2).bv).isEmpty) {
        t = t + 1
      }
      t
    }
    /* TODO: Better to skip *all* skippable formulas, but that makes recovering the original theorem
     * more work, so do it later. */
    def extend(phi:Formula,tmin:Int,tmax:Int):Formula = {
      var t = tmax - 1
      var p = phi
      while(t >= tmin) {
        p = Box(tmap(t)._2, phi)
        t = t -1
      }
      p
    }
  }

  case class Context (map:Map[Variable,(Int,Formula)]){
    def concat(other: Context): Context = Context(map.++(other.map))
    def apply(p:FactVariable):(Int, Formula) = map(p)
    def add(a:Variable, phi:Formula): Context = {
      val nextTime = map.size
      Context(map.+((a,(nextTime,phi))))
    }
  }
  object Context {
    var empty = new Context(Map())
  }

  private def min(seq:Seq[Int]):Int =
    seq.fold(Int.MaxValue)((x,y) => Math.min(x,y))

  def eval(hist: History, ctx: Context, step:Statement):(History,Context) = {
    step match {
      case Run(a,hp) => (hist.add(a,hp), ctx)
      case Show(x,phi,(resources, e)) =>
        val (progs:Seq[ProgramVariable], facts:Seq[FactVariable]) =
          resources.partition({case _: ProgramVariable => true case _:FactVariable => false})
        val tphi = min(facts.map{case p:FactVariable => hist.extent(ctx(p))})
        val ta = min(progs.map{case a:ProgramVariable => hist.time(a)})
        val tmin = Math.min(tphi,ta)
        val tmax = hist.tmax
        val assms:Seq[Formula] = progs.map{case p:FactVariable =>
          val tp = ctx(p)
          hist.extend(tp._2, tmin, tp._1)
        }
        val concl:Formula = hist.extend(phi, tmin, tmax)
        val pr:Provable = Provable.startProof(Sequent(assms.toIndexedSeq, collection.immutable.IndexedSeq(concl)))
        val addedProvable =
          SequentialInterpreter()(e, BelleProvable(NoProofTermProvable(pr))) match {
            case BelleProvable(result, _) =>
              assert(result.isProved)
              result
              /* Need to actually plug in the assumptions here. */
              /*??? */
          }
        (hist, ctx.add(x,phi))
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
}
