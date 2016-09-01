package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms._
import Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.AxiomIndex.AxiomIndex
import edu.cmu.cs.ls.keymaerax.btactics.ExpressionTraversal.{ExpressionTraversalFunction, StopTraversal}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._

import scala.language.postfixOps


/**
  * Tactic Simplifier.simp performs term simplification everywhere within a formula,
  * as many times as possible. Simplification is parameterized over a list of simplification
  * steps. The default set of simplifications is guaranteed to terminate (using the number of constructors in the
  * term as a termination metric), and an optional set of rules is provided for which termination is less clear.
  * Any set of simplifications is allowed, as long as they terminate (the termination metric need not be the number
  * of constructors in the term).
  * Created by bbohrer on 5/21/16.
  */
object Simplifier {
  /* A simplification takes a term t1 and optionally returns a
   * pair (t2, e) of a simpler term t2 and a tactic that proves  |- t1 = t2*/
  type Simplification = (Term => Option[(Term, BelleExpr)])

  val timesZeroLeft:Simplification = {
    case Times(n: Number, t: Term) =>
      if (n.value == 0) {Some(Number(0), useAt(DerivedAxioms.zeroTimes)(Position(1, 0::Nil)) & byUS("= reflexive"))} else None
    case _ => None
  }

  val timesZeroRight:Simplification = {
    case Times(t: Term, n: Number) =>
      if (n.value == 0) {Some((Number(0), useAt(DerivedAxioms.timesZero)(Position(1, 0::Nil)) & byUS("= reflexive")))} else None
    case _ => None
  }

  val timesOneLeft:Simplification = {
    case Times(n: Number, t: Term) =>
      if (n.value == 1) {Some((t,
        useAt(DerivedAxioms.timesCommute)(1, 0::Nil) &
        useAt(DerivedAxioms.timesIdentity)(Position(1, 0::Nil)) &
        byUS("= reflexive")))} else None
    case _ => None
  }

  val timesOneRight:Simplification = {
    case Times(t: Term, n: Number) =>
      if (n.value == 1) {Some((t, useAt(DerivedAxioms.timesIdentity)(Position(1, 0::Nil)) & byUS("= reflexive")))} else None
    case _ => None
  }

  val plusZeroRight:Simplification = {
    case Plus(t: Term, n: Number) =>
      if (n.value == 0) {Some((t, useAt(DerivedAxioms.plusZero)(Position(1, 0::Nil)) & byUS("= reflexive")))} else None
    case _ => None
  }

  val plusZeroLeft:Simplification = {
    case Plus(n: Number, t: Term) =>
      if (n.value == 0) {Some((t, useAt(DerivedAxioms.zeroPlus)(Position(1, 0::Nil)) & byUS("= reflexive")))} else None
    case _ => None
  }

  val powZero:Simplification = {
    case Power(t:Term, n:Number) =>
      if (n.value == 0) {Some (Number(1), QE)} else None
    case _ => None
  }

  val powOne:Simplification = {
    case Power(t:Term, n:Number) =>
      if (n.value == 1) {Some (t, QE)} else None
    case _ => None
  }

  val divOne:Simplification = {
    case Divide(t:Term, n:Number) =>
      if (n.value == 1) {Some (t, QE)} else None
    case _ => None
  }

  val divCancel:Simplification = {
    case Divide(t1:Term, t2:Term) =>
      if (t1 == t2) {Some (Number(1), QE)} else None
    case _ => None
  }

  val minusCancel:Simplification = {
    case Minus(t1:Term, t2:Term) =>
      if(t1 == t2) {Some ((Number(0), QE))} else None
    case _ => None
  }

  val plusConst:Simplification = {
    case Plus(n: Number, m:Number) => Some ((Number(n.value + m.value), QE))
    case _ => None
  }

  val minusConst:Simplification = {
    case Minus(n: Number, m:Number) => Some ((Number(n.value - m.value), QE))
    case _ => None
  }

  val negConst:Simplification = {
    case Neg(n: Number) => Some ((Number(-n.value), QE))
    case _ => None
  }

  val timesConst:Simplification = {
    case Times(n: Number, m:Number) => Some ((Number(n.value * m.value), QE))
    case _ => None
  }

  val divConst:Simplification = {
    case Divide(n: Number, m:Number) if m.value == 0 => None
    case Divide(n: Number, m:Number) => Some ((Number(n.value / m.value), QE))
    case _ => None
  }

  val powConst:Simplification = {
    case Power(n: Number, m:Number) => Some ((Number(n.value.pow(m.value.toIntExact)), QE))
    case _ => None
  }

  val assocPlus:Simplification = {
    case Plus(a:Term, Plus(b:Term, c:Term)) => Some(Plus(Plus(a,b), c), QE)
    case _ => None
  }

  val assocTimes:Simplification = {
    case Times(a:Term, Times(b:Term, c:Term)) => Some(Times(Times(a,b), c), QE)
    case _ => None
  }

  val pushConstPlus:Simplification = {
    case Plus(Plus(t1:Term, t2:Term), n: Number) =>
      if (!t2.isInstanceOf[Number] && !t2.isInstanceOf[Plus]) {print("\n\npushin down " + n + " vs " + t2+"\n\n"); Some(Plus(Plus(t1, n), t2), QE)} else None
    case _ => None
  }

  val flipConstPlus:Simplification = {
    case Plus(t1:Term, n: Number) =>
      if (!t1.isInstanceOf[Number] && !t1.isInstanceOf[Plus]) {print("\n\nflippin "+ t1 + " wit " + n+"\n\n"); Some(Plus(n, t1), QE)} else None
    case _ => None
  }

  val flipConstTimes:Simplification = {
    case Times(t1:Term, n: Number) =>
      if (!t1.isInstanceOf[Number] && !t1.isInstanceOf[Times]) {Some(Times(n, t1), QE)} else None
    case _ => None
  }

  val pushConstTimes:Simplification = {
    case Times(Times(t1:Term, t2:Term), n: Number) =>
      if (!t2.isInstanceOf[Number] && !t2.isInstanceOf[Times]) {Some(Times(Times(t1, n), t2), QE)} else None
    case _ => None
  }

  /* By default, only use simplifications that obviously terminate */
  val defaultSimps: List[Simplification] = List(
    timesZeroLeft,
    timesZeroRight,
    timesOneLeft,
    timesOneRight,
    plusZeroRight,
    plusZeroLeft,
    plusConst,
    minusConst,
    minusCancel,
    negConst,
    timesConst,
    divConst,
    divOne,
    divCancel,
    powConst,
    powOne,
    powZero
  )

  /* When asked, normalize terms by flattening trees of * or + into lists and then
   * pushing all constants toward the end of the list. This enables a more powerful
   * form of constant folding / cancellation */
  val extendedSimps: List[Simplification] =
    defaultSimps ++ List (
      assocPlus,
      assocTimes,
      pushConstPlus,
      flipConstPlus,
      pushConstTimes,
      flipConstTimes
    )

  def trav(simps:List[Simplification]) = new ExpressionTraversalFunction {
    var result:Option[(PosInExpr, Term, BelleExpr)] = None
    override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = {
      simps.find({case simp => simp(e).isDefined}) match {
        case Some(simp) =>
          simp(e) match {
            case Some((newTerm, belle)) =>
              result = Some((p, newTerm, belle))
              Left(Some(ExpressionTraversal.stop))
            case None => throw new ProverException("Bad pattern-match in Simplifier.scala")
          }
        case None => Left(None)
      }
    }
  }
  def simp(simps:List[Simplification], e:Formula):Option[(PosInExpr, Term, BelleExpr)] = {
    val t = trav(simps)
    ExpressionTraversal.traverse(t, e)
    t.result
  }

  def simp(simps:List[Simplification], e:Term):Option[(PosInExpr, Term, BelleExpr)] = {
    val t = trav(simps)
    ExpressionTraversal.traverse(t, e)
    t.result
  }

  def simp(simps:List[Simplification], e:Program):Option[(PosInExpr, Term, BelleExpr)] = {
    val t = trav(simps)
    ExpressionTraversal.traverse(t, e)
    t.result
  }

  def makeCE(fml:Formula, opt:Option[(PosInExpr, Term, BelleExpr)], where:Position):BelleExpr = {
    opt match {
      case Some((pos, t2, e)) =>
        val (ctx, t1:Term) = fml.at(pos)
        print("Trying to prove " + Equal(t1,t2))
        val eqProof = TactixLibrary.proveBy(Equal(t1, t2), e)
        HilbertCalculus.useAt("TODOmakeCE", HilbertCalculus.CE(ctx)(eqProof), PosInExpr(0::Nil))(where)
      case None => TactixLibrary.nil
    }
  }

  def simpOnce(simps:List[Simplification]= defaultSimps):DependentPositionTactic = "simpOnce" by ((pos, sequent) => sequent.sub(pos) match {
    case Some(fml : Formula) => makeCE(fml, simp(simps, fml), pos)
    case None => TactixLibrary.nil
  })

  def simp(simps:List[Simplification] = defaultSimps):DependentPositionTactic = "simp" by ((pos, sequent) =>
    ((simpOnce(simps)(pos))*))
}

