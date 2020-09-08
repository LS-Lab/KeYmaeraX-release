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
// Note: binary compose is better for backend execution, but n-ary composition looks much nicer in debugger.
case class DCompose(children: List[AngelStrategy]) extends SimpleStrategy
case class DChoice(l: AngelStrategy, r: AngelStrategy) extends SimpleStrategy
case class DODE(ode: ODESystem) extends AngelStrategy

case class ALoop(conv: Formula, body: AngelStrategy) extends AngelStrategy
case class ASwitch(branches: List[(Formula, AngelStrategy)]) extends AngelStrategy
case class AODE(ode: ODESystem, dur: Term) extends AngelStrategy

/** Smart constructors for DCompose */
object Composed {
  def apply(children: List[AngelStrategy]): AngelStrategy = {
    // Careful: Should distinguish "real" ?true from no-ops which should be eliminated
    // @TODO: flatten
    val filtered = children.filter({case DTest(True) => false case _ => true})
    filtered match {
      case Nil => DTest(True)
      case as :: Nil => as
      case _ => DCompose(filtered)
    }
  }
  def apply(l: AngelStrategy, r: AngelStrategy): AngelStrategy = {
    apply(l :: r :: Nil)
  }

  def apply(children: List[SimpleStrategy]): SimpleStrategy = {
    // @TODO: Careful: Should distinguish "real" ?true from no-ops which should be eliminated
    // Note: flattening DCompose's would give more minimal trees, but the unflattened shape is nice in practice:
    // SSA blocks are kept together and can be easily collapsed in debugger
    val filtered = children.filter({case DTest(True) => false case _ => true})
    filtered match {
      case Nil => DTest(True)
      case as :: Nil => as
      case _ => DCompose(filtered)
    }
  }
  def apply(l: SimpleStrategy, r: SimpleStrategy): SimpleStrategy = {
    apply(l :: r :: Nil)
  }
}

object SimpleStrategy {
  def apply(fs: AngelStrategy): SimpleStrategy = {
    fs match {
      case DLoop(s) => DLoop(apply(s))
      case DCompose(children) => DCompose(children.map(apply))
      case DChoice(l, r) => DChoice(apply(l), apply(r))
      // @TODO: Need better negation of formulas, need more info in Kaisar data structure for that
      case ALoop(conv, body) => Composed(DLoop(Composed(DTest(conv), apply(body))), DTest(Not(conv)))
      case ASwitch(branches) => branches.map({case (f, fs) => Composed(DTest(f), apply(fs))}).reduceRight(DChoice)
      // @TODO: Proof rule somewhere should check duration variable binding side conditions
      case ss: SimpleStrategy => ss
      case _: AODE | _: DODE => throw new Exception("ODEs should be eliminated before SimpleStrategy conversion")
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
        val assignX = pode.ds.atoms.map(_.dp.xp.x).toList.map(NDAssign)
        val assignDX = pode.ds.atoms.map(_.dp).toList.map({ case AtomicODE(xp, e) => DAssign(xp, e) })
        val conds = pode.timeVar match {
          case Some(t) if !pode.isAngelic => And(GreaterEqual(t, Number(0)), invs)
          case _ => invs
        }
        Composed(assignT :: (assignX ++ assignDX.+:(DTest(conds))))
      case Some(xfs) =>
        val setT = Composed(NDAssign(tv), DTest(GreaterEqual(tv, Number(0))))
        // @TODO: Should test all 0 <= s <= T  but c'est la vie
        val dc = DTest(if (pode.isAngelic) assms else invs)
        val solAssign = Composed(xfs.map({ case (x, f) => DAssign(x, f) }))
        Composed(setT :: dc :: solAssign :: Nil)
    }
    //DODE(pode.asODESystem)
  }

  private def body(pf: Statement): AngelStrategy = {
    pf match {
      case Assume(pat, f) => DTest(f)
      case BoxChoice(left, right) => Composed(body(left), body(right))
      case InverseGhost(s) => body(s)
      case Modify(ids, mods) =>
        Composed(mods.map({ case (x, None) => NDAssign(x) case (x, Some(f)) => DAssign(x, f) }))
      case Block(ss) => Composed(ss.map(body))
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