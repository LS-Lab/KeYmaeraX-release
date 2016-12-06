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
/*
  def prUseAt(pr:Provable, pos:Position) = {
    useAt(NoProofTermProvable(pr))

    val sig:ProvableSig = NoProofTermProvable(pr)
    val pex:PosInExpr = ???//PosInExpr(pos)
    useAt("useAt", sig, pex, None)
    //useAt(codeName: String, fact: ProvableSig, key: PosInExpr, inst: Option[Subst]=>Subst
  }*/

  def interpret(e:BelleExpr, pr:Provable):ProvableSig = {
    SequentialInterpreter()(e, BelleProvable(NoProofTermProvable(pr))) match {
      case BelleProvable(result,_) => result
    }
  }
  def cutEZ(c: Formula, t: BelleExpr): BelleExpr = cut(c) & Idioms.<(skip, /* show */ t & done)

  def implicate(fs:List[Formula],acc:Formula):Formula = {
     fs.reverse.foldLeft(acc)((acc,f) => Imply(f,acc))
  }

  def unbox(f:Formula, n:Int):Formula = {
    (f, n) match {
      case (_, 0) => f
      case (Box(_,p), _) => unbox(p,n-1)
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
    // acc:BelleExpr,
    /*maybeFacts match {
      case Nil => acc
        val theorem:Formula = Box(a,result)/*"[x:=2;][x:=x-1;]x>0".asFormula*/
        val start:Provable = Provable.startProof(theorem)
        interpret(acc, start)
      case firstFact::remainingFacts =>
        def sg: ProvableSig = {
          doGreatProof(acc, a, remainingFacts, result)
          /*val start = Provable.startProof(Box(a, implicate(maybeFacts,result)))
          //val e:BelleExpr =

          interpret(acc, start)*/
        }
        def factPf: ProvableSig = {
          val start = Provable.startProof(Box(a,firstFact))
          val e:BelleExpr = chase(1) & QE
          interpret(e,start)
        }
        val tactic:BelleExpr =
          cutEZ(Imply(Box(a, implicate(maybeFacts,result)), Imply(Box(a,firstFact),Box(a,implicate(remainingFacts,result)))),
            /*)
            cutEZ(("([x:=2;](x > 1 -> [x:=x-1;]x>0)) " +
                "-> ([x:=2;](x > 1)) " +
                "-> [x:=2;][x:=x-1;]x>0").asFormula,*/
            hide(1) & useAt("K modal modus ponens", PosInExpr(Nil))(1,Nil)) &
            implyL(-1) <(
              hide(1) & useAt(sg, PosInExpr(Nil))(1),
              implyL(-1) <(
                hide(1) & useAt(factPf, PosInExpr(Nil))(1),
                close
                )
              )// & nil
        //doGreatProof(tactic, a, remainingFacts, result)
        val theorem:Formula = Box(a,implicate(remainingFacts,result))/*"[x:=2;][x:=x-1;]x>0".asFormula*/
      val start:Provable = Provable.startProof(theorem)
        interpret(tactic, start)
    }
    //val a:Program = "x := 2;".asProgram
    /*val fact:Formula = "x > 1".asFormula
    val facts:Formula = "[x:=x-1;]x>0".asFormula*/
*/
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
              val Box(a, p) = concl
              val boxen = tmin
              val fmls = assms.map(f => unbox(f, boxen)).toList
              val toProve = Box(a,implicate(fmls,p))
              val seqifyTac = debug ("hmm") & G(1) & List.fill(assms.size)(implyR(1)).fold(nil)((e1,e2) => e1 & e2) & debug ("hmm2")
              val userProof = interpret(seqifyTac & e, Provable.startProof(toProve))
              val factProofs:List[ProvableSig] = facts.map{case p:FactVariable =>
                  NoProofTermProvable(ctx(p)._3)
              }.toList
              doGreatProof(userProof, a, fmls, factProofs, p).underlyingProvable
          }
          /*if(concl == "[x:=2;][x:=x-1;]x>0".asFormula) {
            // acc:BelleExpr, a:Program, maybeFacts:List[Formula], result:Formula
            val Box(a, _) = concl
            val boxen = hist.tmin
            doGreatProof(e, a, assms.map(f => unbox(f, boxen)).toList, hist.extend(phi,tmin,tmax)).underlyingProvable
          }
          else {
            SequentialInterpreter()(concE, BelleProvable(NoProofTermProvable(pr))) match {
              case BelleProvable(result, _) =>
                assert(result.isProved)
                result.underlyingProvable
            }
          }*/
        //                doGreatProof(e, a, assms.map(f => unbox(f, boxen)).toList, hist.extend(phi, tmin, tmax)).underlyingProvable
        //}
        /*val  e = G(1) & implyR(1) & //close
          chase(1) &
          QE*/

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
