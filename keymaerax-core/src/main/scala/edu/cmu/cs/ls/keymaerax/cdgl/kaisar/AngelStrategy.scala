package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.KaisarProof.Ident
import edu.cmu.cs.ls.keymaerax.core._

sealed trait AngelStrategy
sealed trait SimpleStrategy extends AngelStrategy

//case object Skip extends DemonStrategy
case class DTest(f: Formula) extends SimpleStrategy
case class DAssign(x: Ident, f: Term) extends SimpleStrategy
case class NDAssign(x: Ident) extends SimpleStrategy
case class DLoop(s: AngelStrategy) extends SimpleStrategy
case class DCompose(l: AngelStrategy, r: AngelStrategy) extends SimpleStrategy
case class DChoice(l: AngelStrategy, r: AngelStrategy) extends SimpleStrategy
case class DODE(ode: ODESystem) extends AngelStrategy

case class ALoop(conv: Formula, body: AngelStrategy) extends AngelStrategy
case class ASwitch(branches: List[(Formula, AngelStrategy)]) extends AngelStrategy
case class AODE(ode: ODESystem, dur: Term) extends AngelStrategy

object SimpleStrategy {
  def apply(fs: AngelStrategy): SimpleStrategy = {
    fs match {
      case DLoop(s) => DLoop(apply(s))
      case DCompose(l, r) => DCompose(apply(l), apply(r))
      case DChoice(l, r) => DChoice(apply(l), apply(r))
      // @TODO: Need better negation of formulas, need more info in Kaisar data structure for that
      case ALoop(conv, body) => DCompose(DLoop(DCompose(DTest(conv), apply(body))), DTest(Not(conv)))
      case ASwitch(branches) => branches.map({case (f, fs) => DCompose(DTest(f), apply(fs))}).reduceRight(DChoice)
      // @TODO: Proof rule somewhere should check duration variable binding side conditions
      //case AODE(ode, dur) => DODE(ode)
      case ss: SimpleStrategy => ss
    }
  }
}

object AngelStrategy {
  private def ofODE(pode: ProveODE): AngelStrategy = {
    val tv = pode.timeVar.getOrElse(Variable("t"))
    val assignT = pode.duration match {
      case Some((_, f)) => DAssign(tv, f)
      case None => NDAssign(tv)
    }
    val coll = pode.dc.collect
    val assms = (coll.assumptions.toList.map(_.f)).reduceRight[Formula](And)
    val invs = (coll.assumptions.toList.map(_.f) ++ coll.assertions.map(_.f)).reduceRight[Formula](And)
    pode.solutions match {
      case None =>
        val assignX = pode.ds.atoms.map(_.dp.xp.x).toList.map(NDAssign).reduceRight(DCompose)
        val assignDX = pode.ds.atoms.map(_.dp).toList.map({ case AtomicODE(xp, e) => DAssign(xp, e) }).reduceRight(DCompose)
        val conds = pode.timeVar match {
          case Some(t) if !pode.isAngelic => And(GreaterEqual(t, Number(0)), invs)
          case _ => invs
        }
        DCompose(assignT, DCompose(assignX, DCompose(assignDX, DTest(conds))))
      case Some(xfs) =>
        val setT = DCompose(NDAssign(tv), DTest(GreaterEqual(tv, Number(0))))
        // @TODO: Should test all 0 <= s <= T  but c'est la vie
        val dc = DTest(if (pode.isAngelic) assms else invs)
        val solAssign = xfs.map({ case (x, f) => DAssign(x, f) }).reduceRight(DCompose)
        DCompose(setT, DCompose(dc, solAssign))
    }
    //DODE(pode.asODESystem)
  }

  private def body(pf: Statement): AngelStrategy = {
    pf match {
      case Assume(pat, f) => DTest(f)
      case BoxChoice(left, right) => DCompose(body(left), body(right))
      case InverseGhost(s) => body(s)
      case Modify(ids, mods) =>
        mods.map({ case (x, None) => NDAssign(x) case (x, Some(f)) => DAssign(x, f) })
          .reduceRight(DCompose)
      case Block(ss) => ss.map(body).reduceRight(DCompose)
      case Switch(scrutinee, pats) => ASwitch(pats.map({ case (x, f, b) => (f, body(b)) }))
      case While(x, j, s) => ALoop(j, body(s))
      case BoxLoop(s, ih) => DLoop(body(s))
      case pode: ProveODE => ofODE(pode)
      case Phi(s) => body(s)
      case _: MetaNode | _: Note | _: Match | _: LetFun | _: Triv | _: Assert | _: Label | _: Ghost => DTest(True)
    }
  }

  def apply(pf: Statement): AngelStrategy = {
    val fv = VariableSets(pf).freeVars
    println("Free variables: " + fv)
    val main = body(pf)
    // @TODO: Need tight freevar computation
    //val inits = fv.toList.map(NDAssign)
    //val strat = inits.foldRight(main)(DCompose)
    //println("Angel strat: " + strat)
    main
  }
}