/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleTopLevelLabel, OnAll, SaturateTactic}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.arithmetic.signanalysis.{Bound, Sign, SignAnalysis}
import edu.cmu.cs.ls.keymaerax.btactics.arithmetic.speculative.ArithmeticSpeculativeSimplification
import edu.cmu.cs.ls.keymaerax.btactics.{TacticTestBase, TactixLibrary}
import edu.cmu.cs.ls.keymaerax.btactics.ArithmeticSimplification._
import edu.cmu.cs.ls.keymaerax.core._

import scala.collection.immutable._
import scala.language.postfixOps
import org.scalatest.LoneElement._
import org.scalatest.prop.TableDrivenPropertyChecks._

/** @author Nathan Fulton */
class ArithmeticSimplificationTests extends TacticTestBase {
  "Z3 simplifier tool" should "simplify some terms correctly" in withZ3 { tool =>
    val terms = List(
      "5*x-3*y+2*z-((0+(0*t+5*1))*x0+(1+5*t)*0-((0*t+3*1)*y0+3*t*0)+((0*t+2*1)*z0+2*t*0))".asTerm ->
        "5*x + (-(3))*y + 2*z + (-(5))*x0 + 3*y0 + (-(2))*z0".asTerm,
      "15*x-9*y+6*z-((0*t+15*1)*x0+15*t*0+((0-(0*t+9*1))*y0+(1-9*t)*0)+((0*t+6*1)*z0+6*t*0))".asTerm ->
        "15*x + (-(9))*y + 6*z + (-(15))*x0 + 9*y0 + (-(6))*z0".asTerm,
    )
    forEvery(Table(("Input", "Expected"), terms: _*))({ (t1, t2) => tool.simplify(t1, List.empty) shouldBe t2 })
  }

  "smartHide" should "simplify x=1,y=1 ==> x=1 to x=1 ==> x=1" in withMathematica { _ =>
    proveBy("x=1, y=1 ==> x=1".asSequent, smartHide).subgoals.loneElement shouldBe "x=1 ==> x=1".asSequent
  }

  it should "simplify x>=1,x=1,y=1 ==> x=1 to x=1 ==> x=1" in withMathematica { _ =>
    val result = proveBy("x>=1, x=1, y=1 ==> x>=0".asSequent, smartHide)
    result.subgoals.loneElement shouldBe "x=1 ==> x>=0".asSequent
  }

  it should "hide implied facts" in withMathematica { _ =>
    val s =
      "A>=0, B>0, V()>=0, ep>0, v_0>=0, -B<=a, a<=A, abs(x_0-xo_0)>v_0^2/(2*B)+V()*(v_0/B), abs(x_0-xo_0)>v_0^2/(2*B)+V()*v_0/B+(A/B+1)*(A/2*ep^2+ep*(v_0+V())), -t*V()<=xo-xo_0, xo-xo_0<=t*V(), v=v_0+a*t, -t*(v-a/2*t)<=x-x_0, x-x_0<=t*(v-a/2*t), t>=0, t<=ep, v>=0 ==> abs(x-xo)>v^2/(2*B)+V()*(v/B)"
        .asSequent
    proveBy(s, smartHide).subgoals.loneElement shouldBe
      "A>=0, B>0, V()>=0, ep>0, v_0>=0, -B<=a, a<=A, abs(x_0-xo_0)>v_0^2/(2*B)+V()*v_0/B+(A/B+1)*(A/2*ep^2+ep*(v_0+V())), -t*V()<=xo-xo_0, xo-xo_0<=t*V(), v=v_0+a*t, -t*(v-a/2*t)<=x-x_0, x-x_0<=t*(v-a/2*t), t>=0, t<=ep, v>=0 ==> abs(x-xo)>v^2/(2*B)+V()*(v/B)"
        .asSequent
  }

  it should "not throw away transitivity info" in withMathematica { _ =>
    val goal = "x=y, y=z, z>0 ==> x>0".asSequent
    proveBy(goal, smartHide).subgoals.loneElement shouldBe "x=y, y=z, z>0 ==> x>0".asSequent
    proveBy(goal, smartHide & TactixLibrary.QE) shouldBe Symbol("proved")
  }

  it should "forget useless stuff" in withMathematica { _ =>
    val goal = "x>y, y>z, a>0, z>0 ==> x>0".asSequent
    proveBy(goal, smartHide).subgoals.loneElement shouldBe "x>y, y>z, z>0 ==> x>0".asSequent
    proveBy(goal, smartHide & TactixLibrary.QE) shouldBe Symbol("proved")
  }

  it should "forget useless stuff about ODEs" in withMathematica { _ =>
    val goal = "x>y, y>z, a>0, z>0 ==> [{x'=1}]x>0".asSequent
    val result = proveBy(goal, smartHide)
    result.subgoals.loneElement shouldBe "x>y, y>z, z>0 ==> [{x'=1}]x>0".asSequent
    proveBy(result.subgoals.loneElement, diffInvariant("x>0".asFormula)(1) & dW(1) & QE) shouldBe Symbol("proved")
  }

  "smartSuccHide" should "simplify x=1 ==> x-1,y=1 to x=1 ==> x=1" in {
    proveBy("x=1 ==> x=1, y=1".asSequent, smartSuccHide).subgoals.loneElement shouldBe "x=1 ==> x=1".asSequent
  }

  it should "simplify x=1 ==> x-1,y=x to x=1 ==> x=1" in {
    proveBy("x=1 ==> x=1, y=x".asSequent, smartSuccHide).subgoals.loneElement shouldBe "x=1 ==> x=1".asSequent
  }

  it should "simplify x=1 ==> x-1,[y'=1}y>0 to x=1 ==> x=1" in {
    proveBy("x=1 ==> x=1, [{y'=1}]y>0".asSequent, smartSuccHide).subgoals.loneElement shouldBe "x=1 ==> x=1".asSequent
  }

  "replaceTransform" should "work in the antecedent" in withMathematica { _ =>
    proveBy("t<=ep, v>=0, x>=x_0+v*ep ==> x>=x_0+v*t".asSequent, transformEquality("ep=t".asFormula)(-3) & id) shouldBe
      Symbol("proved")
  }

  it should "work in the succedent" in withMathematica { _ =>
    proveBy(
      "t<=ep, v>=0, x>=x_0+v*ep ==> a<5, x>=x_0+v*t, b<7".asSequent,
      transformEquality("t=ep".asFormula)(2) & id,
    ) shouldBe Symbol("proved")
  }

  "absQE" should "prove abs(x-y)>=t -> abs(x-y+0)>=t+0" in withMathematica { _ =>
    proveBy("abs(x-y)>=t ==> abs(x-y+0)>=t+0".asSequent, ArithmeticSpeculativeSimplification.proveOrRefuteAbs) shouldBe
      Symbol("proved")
  }

  it should "prove abs(x-y)>=t -> abs(x-y)>=t+0" in withMathematica { _ =>
    proveBy("abs(x-y)>=t ==> abs(x-y)>=t+0".asSequent, ArithmeticSpeculativeSimplification.proveOrRefuteAbs) shouldBe
      Symbol("proved")
  }

  it should "prove a Robix example" in withMathematica { _ =>
    // todo: occasionally fails in 'assertNoCEX'. appears to be related to Mathematica
    val fml =
      "A>=0 & B>0 & V()>=0 & ep>0 & v_0>=0 & -B<=a & a<=A & abs(x_0-xo_0)>v_0^2/(2*B)+V()*v_0/B+(A/B+1)*(A/2*ep^2+ep*(v_0+V())) & -t*V()<=xo-xo_0 & xo-xo_0<=t*V() & v=v_0+a*t & -t*(v-a/2*t)<=x-x_0 & x-x_0<=t*(v-a/2*t) & t>=0 & t<=ep & v>=0 -> abs(x-xo)>v^2/(2*B)+V()*(v/B)"
        .asFormula
    val tactic = SaturateTactic(alphaRule) & replaceTransform("ep".asTerm, "t".asTerm)(
      -8,
      "abs(x_0-xo_0)>v_0^2/(2*B)+V()*v_0/B+(A/B+1)*(A/2*ep^2+ep*(v_0+V()))".asFormula,
    ) & ArithmeticSpeculativeSimplification.proveOrRefuteAbs

    proveBy(fml, tactic) shouldBe Symbol("proved")
  }

  "exhaustiveAbsSplit" should "handle nested abs" in withMathematica { _ =>
    proveBy("abs(abs(x)-y)>=0".asFormula, ArithmeticSpeculativeSimplification.exhaustiveAbsSplit).subgoals should
      contain theSameElementsAs List(
        "x>=0, x-y>=0 ==> x-y>=0".asSequent,
        "x < 0, -x-y>=0 ==> -x-y>=0".asSequent,
        "x>=0, x-y < 0 ==> -(x-y)>=0".asSequent,
        "x < 0, -x-y < 0 ==> -(-x-y)>=0".asSequent,
      )
  }

  "autoTransform" should "transform formulas from worst-case bounds to concrete variables" in withMathematica { _ =>
    val s =
      "A>=0, B>0, V()>=0, ep>0, v_0>=0, -B<=a, a<=A, abs(x_0-xo_0)>v_0^2/(2*B)+V()*v_0/B+(A/B+1)*(A/2*ep^2+ep*(v_0+V())), -t*V()<=xo-xo_0, xo-xo_0<=t*V(), v=v_0+a*t, -t*(v-a/2*t)<=x-x_0, x-x_0<=t*(v-a/2*t), t>=0, t<=ep, v>=0 ==> abs(x-xo)>v^2/(2*B)+V()*(v/B)"
        .asSequent
    proveBy(s, ArithmeticSpeculativeSimplification.autoMonotonicityTransform).subgoals.loneElement shouldBe
      "A>=0, B>0, V()>=0, ep>0, v_0>=0, -B<=a, a<=A, abs(x_0-xo_0)>v_0^2/(2*B)+V()*v_0/B+(A/B+1)*(A/2*t^2+t*(v_0+V())), -t*V()<=xo-xo_0, xo-xo_0<=t*V(), v=v_0+a*t, -t*(v-a/2*t)<=x-x_0, x-x_0<=t*(v-a/2*t), t>=0, t<=t, v>=0 ==> abs(x-xo)>v^2/(2*B)+V()*(v/B)"
        .asSequent
  }

  it should "transform formulas from worst-case bounds to concrete variables (2)" in withMathematica { _ =>
    val s =
      "A()>0, -c*(v_0+a*c-a/2*c)<=y-y_0, y-y_0<=c*(v_0+a*c-a/2*c), B()>=b(), dx^2+dy^2=1, b()>0, c>=0, ep()>0, v_0+a*c>=0, c<=ep(), lw()>0, v_0>=0, r_0!=0, abs(y_0-ly())+v_0^2/(2*b()) < lw(), abs(y_0-ly())+v_0^2/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v_0) < lw(), -B()<=a, a<=A(), r!=0\n  ==>  abs(y-ly())+(v_0+a*c)^2/(2*b()) < lw()"
        .asSequent
    proveBy(s, ArithmeticSpeculativeSimplification.autoMonotonicityTransform).subgoals.loneElement shouldBe
      "A()>0, -c*(v_0+a*c-a/2*c)<=y-y_0, y-y_0<=c*(v_0+a*c-a/2*c), B()>=b(), dx^2+dy^2=1, b()>0, c>=0, ep()>0, v_0+a*c>=0, c<=c, lw()>0, v_0>=0, r_0!=0, abs(y_0-ly())+v_0^2/(2*b()) < lw(), abs(y_0-ly())+v_0^2/(2*b())+(A()/b()+1)*(A()/2*c^2+c*v_0) < lw(), -B()<=a, a<=A(), r!=0 ==> abs(y-ly())+(v_0+a*c)^2/(2*b()) < lw()"
        .asSequent
  }

  "Sign analysis" should "compute seed from antecedent" in {
    val s = "A>=0, -B<0, v^2<=2*B*(m-x), A<0, 2*C-C^2>=0 ==> x<=m".asSequent
    SignAnalysis.seedSigns(s) shouldBe Map(
      "A".asVariable -> Map(Sign.Pos0 -> Set(SeqPos(-1)), Sign.Neg0 -> Set(SeqPos(-4))),
      "B".asVariable -> Map(Sign.Pos0 -> Set(SeqPos(-2))),
      "2*B*(m-x)-v^2".asTerm -> Map(Sign.Pos0 -> Set(SeqPos(-3))),
      "v^2".asTerm -> Map(Sign.Pos0 -> Set(SeqPos(-3))),
      "2*B*(m-x)".asTerm -> Map(Sign.Pos0 -> Set(SeqPos(-3))),
      "2*B".asTerm -> Map(Sign.Unknown -> Set(SeqPos(-3))),
      "m-x".asTerm -> Map(Sign.Unknown -> Set(SeqPos(-3))),
      "v".asVariable -> Map(Sign.Unknown -> Set(SeqPos(-3))),
      "m".asVariable -> Map(Sign.Unknown -> Set(SeqPos(-3))),
      "x".asVariable -> Map(Sign.Unknown -> Set(SeqPos(-3))),
      "2".asTerm -> Map(Sign.Pos0 -> Set(SeqPos(-3), SeqPos(-5))),
      "2*C-C^2".asTerm -> Map(Sign.Pos0 -> Set(SeqPos(-5))),
      "C^2".asTerm -> Map(Sign.Pos0 -> Set(SeqPos(-5))),
      "2*C".asTerm -> Map(Sign.Pos0 -> Set(SeqPos(-5))),
      "C".asVariable -> Map(Sign.Pos0 -> Set(SeqPos(-5))),
    )
  }

  it should "aggregate signs from seed" in {
    val s = "A>=0, -B<0, v^2<=2*B*(m-x), A<0, 2*C-C^2>=0 ==> x<=m".asSequent
    SignAnalysis.aggregateSigns(SignAnalysis.seedSigns(s)) shouldBe Map(
      "A".asVariable -> Map(Sign.Pos0 -> Set(SeqPos(-1)), Sign.Neg0 -> Set(SeqPos(-4))),
      "B".asVariable -> Map(Sign.Pos0 -> Set(SeqPos(-2))),
      "2*B*(m-x)-v^2".asTerm -> Map(Sign.Pos0 -> Set(SeqPos(-3))),
      "v^2".asTerm -> Map(Sign.Pos0 -> Set(SeqPos(-3))),
      "2*B*(m-x)".asTerm -> Map(Sign.Pos0 -> Set(SeqPos(-3))),
      "2*B".asTerm -> Map(Sign.Pos0 -> Set(SeqPos(-3))),
      "m-x".asTerm -> Map(Sign.Unknown -> Set(SeqPos(-3))),
      "v".asVariable -> Map(Sign.Unknown -> Set(SeqPos(-3))),
      "m".asVariable -> Map(Sign.Unknown -> Set(SeqPos(-3))),
      "x".asVariable -> Map(Sign.Unknown -> Set(SeqPos(-3))),
      "2".asTerm -> Map(Sign.Pos0 -> Set(SeqPos(-3), SeqPos(-5))),
      "2*C-C^2".asTerm -> Map(Sign.Pos0 -> Set(SeqPos(-5))),
      "C^2".asTerm -> Map(Sign.Pos0 -> Set(SeqPos(-5))),
      "2*C".asTerm -> Map(Sign.Pos0 -> Set(SeqPos(-5))),
      "C".asVariable -> Map(Sign.Pos0 -> Set(SeqPos(-5))),
    )
  }

  it should "pushDown signs from seed after aggregation" in {
    val s = "A>=0, -B<0, v^2<=2*B*(m-x), A<0, 2*C-C^2>=0 ==> x<=m".asSequent
    val seed = SignAnalysis.seedSigns(s)
    SignAnalysis.pushDownSigns(SignAnalysis.aggregateSigns(seed)) shouldBe Map(
      "A".asVariable -> Map(Sign.Pos0 -> Set(SeqPos(-1)), Sign.Neg0 -> Set(SeqPos(-4))),
      "B".asVariable -> Map(Sign.Pos0 -> Set(SeqPos(-2) /*, SeqPos(-3)*/ )),
      "2*B*(m-x)-v^2".asTerm -> Map(Sign.Pos0 -> Set(SeqPos(-3))),
      "v^2".asTerm -> Map(Sign.Pos0 -> Set(SeqPos(-3))),
      "2*B*(m-x)".asTerm -> Map(Sign.Pos0 -> Set(SeqPos(-3))),
      "2*B".asTerm -> Map(Sign.Pos0 -> Set(SeqPos(-3))),
      "m-x".asTerm -> Map(Sign.Pos0 -> Set(SeqPos(-3))),
      "v".asVariable -> Map(Sign.Unknown -> Set(SeqPos(-3))),
      "m".asVariable -> Map(Sign.Unknown -> Set(SeqPos(-3))),
      "x".asVariable -> Map(Sign.Unknown -> Set(SeqPos(-3))),
      "2".asTerm -> Map(Sign.Pos0 -> Set(SeqPos(-3), SeqPos(-5))),
      "2*C-C^2".asTerm -> Map(Sign.Pos0 -> Set(SeqPos(-5))),
      "C^2".asTerm -> Map(Sign.Pos0 -> Set(SeqPos(-5))),
      "2*C".asTerm -> Map(Sign.Pos0 -> Set(SeqPos(-5))),
      "C".asVariable -> Map(Sign.Pos0 -> Set(SeqPos(-5))),
    )
  }

  it should "pingpong until fixpoint" in {
    val s = "A>=0, -B<0, v^2<=2*B*(m-x), A<0, 2*C-C^2>=0 ==> x<=m".asSequent
    SignAnalysis.computeSigns(s) shouldBe Map(
      "A".asVariable -> Map(Sign.Pos0 -> Set(SeqPos(-1)), Sign.Neg0 -> Set(SeqPos(-4))),
      "B".asVariable -> Map(Sign.Pos0 -> Set(SeqPos(-2))),
      "2*B*(m-x)-v^2".asTerm -> Map(Sign.Pos0 -> Set(SeqPos(-3))),
      "v^2".asTerm -> Map(Sign.Pos0 -> Set(SeqPos(-3))),
      "2*B*(m-x)".asTerm -> Map(Sign.Pos0 -> Set(SeqPos(-3))),
      "2*B".asTerm -> Map(Sign.Pos0 -> Set(SeqPos(-3))),
      "m-x".asTerm -> Map(Sign.Pos0 -> Set(SeqPos(-3))),
      "v".asVariable -> Map(Sign.Unknown -> Set(SeqPos(-3))),
      "m".asVariable -> Map(Sign.Unknown -> Set(SeqPos(-3))),
      "x".asVariable -> Map(Sign.Unknown -> Set(SeqPos(-3))),
      "2".asTerm -> Map(Sign.Pos0 -> Set(SeqPos(-3), SeqPos(-5))),
      "2*C-C^2".asTerm -> Map(Sign.Pos0 -> Set(SeqPos(-5))),
      "C^2".asTerm -> Map(Sign.Pos0 -> Set(SeqPos(-5))),
      "2*C".asTerm -> Map(Sign.Pos0 -> Set(SeqPos(-5))),
      "C".asVariable -> Map(Sign.Pos0 -> Set(SeqPos(-5))),
    )
  }

  it should "work on the Robix example" in {
    val fml =
      "A>=0 & B>0 & V()>=0 & ep>0 & v_0>=0 & -B<=a & a<=A & abs(x_0-xo_0)>v_0^2/(2*B)+V()*v_0/B+(A/B+1)*(A/2*ep^2+ep*(v_0+V())) & -t*V()<=xo-xo_0 & xo-xo_0<=t*V() & v=v_0+a*t & -t*(v-a/2*t)<=x-x_0 & x-x_0<=t*(v-a/2*t) & t>=0 & t<=ep & v>=0 -> v=0|abs(x-xo)>v^2/(2*B)+V()*(v/B)"
        .asFormula
    val s = proveBy(fml, SaturateTactic(alphaRule))
    // only check atoms
    val signs = SignAnalysis.computeSigns(s.subgoals.head)
    signs("A".asVariable).keySet should contain only Sign.Pos0
    signs("B".asVariable).keySet should contain only Sign.Pos0
    signs("V()".asTerm).keySet should contain only Sign.Pos0
    signs("v_0".asVariable).keySet should contain only Sign.Pos0
    signs("t".asVariable).keySet should contain only Sign.Pos0
    signs("v".asVariable).keySet should contain only Sign.Pos0
    signs("ep".asVariable).keySet should contain only Sign.Pos0
    signs("a".asVariable).keySet should contain only Sign.Unknown
    signs("xo".asVariable).keySet should contain only Sign.Unknown
    signs("xo_0".asVariable).keySet should contain only Sign.Unknown
    signs("x".asVariable).keySet should contain only Sign.Unknown
  }

  it should "work on another Robix example" in withMathematica { _ =>
    val fml =
      "A>=0 & B>0 & V()>=0 & ep>0 & v_0>=0 & -B<=a & a<=A & abs(x_0-xo_0)>v_0^2/(2*B)+V()*v_0/B+(A/B+1)*(A/2*ep^2+ep*(v_0+V())) & -t*V()<=xo-xo_0 & xo-xo_0<=t*V() & v=v_0+a*t & -t*(v-a/2*t)<=x-x_0 & x-x_0<=t*(v-a/2*t) & t>=0 & t<=ep & v>=0 -> v=0|abs(x-xo)>v^2/(2*B)+V()*(v/B)"
        .asFormula
    val tactic = SaturateTactic(alphaRule) & replaceTransform("ep".asTerm, "t".asTerm)(
      -8,
      s"abs(x_0-xo_0)>v_0^2/(2*B)+V()*v_0/B+(A/B+1)*(A/2*ep^2+ep*(v_0+V()))".asFormula,
    ) & abs(2, 0 :: Nil) & abs(-8, 0 :: Nil) & orL(-18) & OnAll(orL(-17)) & OnAll(SaturateTactic(andL(Symbol("_")))) &
      OnAll(SaturateTactic(exhaustiveEqL2R(hide = true)(Symbol("L"))))
    val s = proveBy(fml, tactic)
    // only check atoms
    val signs = SignAnalysis.computeSigns(s.subgoals.head)
    signs("A".asVariable).keySet should contain only Sign.Pos0
    signs("B".asVariable).keySet should contain only Sign.Pos0
    signs("V()".asTerm).keySet should contain only Sign.Pos0
    signs("v_0".asVariable).keySet should contain only Sign.Pos0
    signs("t".asVariable).keySet should contain only Sign.Pos0
    signs("ep".asVariable).keySet should contain only Sign.Pos0
    signs("a".asVariable).keySet should contain only Sign.Unknown
    signs("xo".asVariable).keySet should contain only Sign.Unknown
    signs("xo_0".asVariable).keySet should contain only Sign.Unknown
    signs("x".asVariable).keySet should contain only Sign.Unknown

    signs("x-xo".asTerm).keySet should contain only Sign.Pos0
    signs("x_0-xo_0".asTerm).keySet should contain only Sign.Pos0
  }

  "Bound computation" should "compute wanted bounds from succedent" in {
    val s = "A>=0, -B<0, v^2<=2*B*(m-x) ==> x+5<=m, v^2<=2*B*(m-x)".asSequent
    val signs = SignAnalysis.computeSigns(s)
    SignAnalysis.bounds(s.succ, signs, SuccPos) shouldBe Map(
      SeqPos(1) -> Map(
        "x".asVariable -> Map(Bound.Upper -> Set()),
        "m".asVariable -> Map(Bound.Lower -> Set()),
        "5".asTerm -> Map(Bound.Exact -> Set()),
      ),
      SeqPos(2) -> Map(
        "x".asVariable -> Map(Bound.Upper -> Set(SeqPos(-3))),
        "m".asVariable -> Map(Bound.Lower -> Set(SeqPos(-3))),
        "B".asVariable -> Map(Bound.Upper -> Set(SeqPos(-3))),
        "v".asVariable -> Map(Bound.Unknown -> Set()),
        "2".asTerm -> Map(Bound.Exact -> Set()),
      ),
    )
  }

  it should "work on a Robix example" in withMathematica { _ =>
    val fml =
      "A>=0 & B>0 & V()>=0 & ep>0 & v_0>=0 & -B<=a & a<=A & abs(x_0-xo_0)>v_0^2/(2*B)+V()*v_0/B+(A/B+1)*(A/2*ep^2+ep*(v_0+V())) & -t*V()<=xo-xo_0 & xo-xo_0<=t*V() & v=v_0+a*t & -t*(v-a/2*t)<=x-x_0 & x-x_0<=t*(v-a/2*t) & t>=0 & t<=ep & v>=0 -> abs(x-xo)>v^2/(2*B)+V()*(v/B)"
        .asFormula
    val tactic = SaturateTactic(alphaRule) & replaceTransform("ep".asTerm, "t".asTerm)(
      -8,
      s"abs(x_0-xo_0)>v_0^2/(2*B)+V()*v_0/B+(A/B+1)*(A/2*ep^2+ep*(v_0+V()))".asFormula,
    ) & abs(1, 0 :: Nil) & abs(-8, 0 :: Nil) & orL(-18) & OnAll(orL(-17)) & OnAll(SaturateTactic(andL(Symbol("_")))) &
      OnAll(SaturateTactic(exhaustiveEqL2R(hide = true)(Symbol("L"))))
    val s = proveBy(fml, tactic)
    val signs = SignAnalysis.computeSigns(s.subgoals.head)
    val bounds = SignAnalysis.bounds(s.subgoals.head.succ, signs, SuccPos)
    bounds(SeqPos(1).asInstanceOf[SuccPos]) should contain theSameElementsAs Map(
      "x".asVariable -> Map(Bound.Lower -> Set()),
      "xo".asVariable -> Map(Bound.Upper -> Set()),
      "a".asVariable -> Map(Bound.Upper -> Set(SeqPos(-13))),
      "V()".asTerm -> Map(Bound.Upper -> Set(SeqPos(-3))),
      "v_0".asVariable -> Map(Bound.Upper -> Set(SeqPos(-15))),
      "B".asVariable -> Map(Bound.Lower -> Set(SeqPos(-15))),
      "t".asVariable -> Map(Bound.Upper -> Set(SeqPos(-13))),
      "1".asTerm -> Map(Bound.Exact -> Set()),
      "2".asTerm -> Map(Bound.Exact -> Set()),
    )
  }

  "Bounds hiding" should "find formulas with non-matching bounds" in withMathematica { _ =>
    val s = "v>=0, -B<0, v^2<=2*B*(m-x), v<0, x>m, 2*C-C^2>=0 ==> x<=m".asSequent
    proveBy(s, QE) shouldBe Symbol("proved")
    SignAnalysis.boundHideCandidates(s) should contain only SeqPos(-5)
  }

  it should "find formulas with non-matching bounds (2)" in withMathematica { _ =>
    val s = "-t*V <= x-x_0, x-x_0 <= t*V, V>=0, t>=0 ==> x-xo >= 2*V*t".asSequent
    SignAnalysis.boundHideCandidates(s) should contain only SeqPos(-2)
  }

  it should "not choke on !=" in withMathematica { _ =>
    val s = "-t*V <= x-x_0, x-x_0 <= t*V, V>=0, t>=0, r!=0 ==> x-xo >= 2*V*t".asSequent
    SignAnalysis.boundHideCandidates(s) should contain only SeqPos(-2)
  }

  it should "hide formulas with non-matching bounds" in withMathematica { _ =>
    val s = "v>=0, -B<0, v^2<=2*B*(m-x), v<0, x>m, 2*C-C^2>=0 ==> x<=m".asSequent
    proveBy(s, QE) shouldBe Symbol("proved")
    val boundHidden = proveBy(s, ArithmeticSpeculativeSimplification.hideNonmatchingBounds)
    boundHidden.subgoals.loneElement shouldBe "v>=0, -B<0, v^2<=2*B*(m-x), v<0, 2*C-C^2>=0 ==> x<=m".asSequent
    proveBy(boundHidden.subgoals.loneElement, ArithmeticSpeculativeSimplification.speculativeQE) shouldBe
      Symbol("proved")
  }

  it should "work on a Robix example" in withMathematica { _ =>
    val fml =
      "A>=0 & B>0 & V()>=0 & ep>0 & v_0>=0 & -B<=a & a<=A & abs(x_0-xo_0)>v_0^2/(2*B)+V()*v_0/B+(A/B+1)*(A/2*ep^2+ep*(v_0+V())) & -t*V()<=xo-xo_0 & xo-xo_0<=t*V() & v=v_0+a*t & -t*(v-a/2*t)<=x-x_0 & x-x_0<=t*(v-a/2*t) & t>=0 & t<=ep & v>=0 -> abs(x-xo)>v^2/(2*B)+V()*(v/B)"
        .asFormula
    val tactic = SaturateTactic(alphaRule) & replaceTransform("ep".asTerm, "t".asTerm)(
      -8,
      s"abs(x_0-xo_0)>v_0^2/(2*B)+V()*v_0/B+(A/B+1)*(A/2*ep^2+ep*(v_0+V()))".asFormula,
    ) & abs(1, 0 :: Nil) & abs(-8, 0 :: Nil) & orL(-18) & OnAll(orL(-17)) & OnAll(SaturateTactic(andL(Symbol("_")))) &
      OnAll(SaturateTactic(exhaustiveEqL2R(hide = true)(Symbol("L"))))

    // @todo hideNonmatchingBounds does not yet work on the "middle" (<= vs. >=) abs branches
    val s = proveBy(
      fml,
      tactic switch
        (
          ("x_0-xo_0>=0&abs__0=x_0-xo_0//x-xo>=0&abs_=x-xo".asLabel, ArithmeticSpeculativeSimplification.speculativeQE),
          ("x_0-xo_0 < 0&abs__0=-(x_0-xo_0)//x-xo>=0&abs_=x-xo".asLabel, skip),
          (
            "x_0-xo_0 < 0&abs__0=-(x_0-xo_0)//x-xo < 0&abs_=-(x-xo)".asLabel,
            ArithmeticSpeculativeSimplification.speculativeQE,
          ),
          ("x_0-xo_0>=0&abs__0=x_0-xo_0//x-xo < 0&abs_=-(x-xo)".asLabel, skip),
        ),
    )
    s.subgoals should have size 2
  }

  "Sign hiding" should "find inconsistent sign formulas" in {
    val s = "v>=0, -B<0, v^2<=2*B*(m-x), v<0, x>m, 2*C-C^2>=0 ==> x<=m".asSequent
    SignAnalysis.signHideCandidates(s) should contain theSameElementsAs
      List(SeqPos(-2), SeqPos(-3), SeqPos(-5), SeqPos(-6), SeqPos(1))
  }

  it should "hide inconsistent sign formulas" in withMathematica { _ =>
    val s = "v>=0, -B<0, v^2<=2*B*(m-x), v<0, x>m, 2*C-C^2>=0 ==> x<=m".asSequent
    proveBy(s, ArithmeticSpeculativeSimplification.hideInconsistentSigns & QE) shouldBe Symbol("proved")
  }

  "Multiple hidings together" should "figure it out" in withMathematica { _ =>
    val s = "v>=0, -B<0, v^2<=2*B*(m-x), v<0, x>m, 2*C-C^2>=0 ==> x<=m".asSequent
    val boundHidden = proveBy(s, ArithmeticSpeculativeSimplification.hideNonmatchingBounds)
    boundHidden.subgoals.loneElement shouldBe "v>=0, -B<0, v^2<=2*B*(m-x), v<0, 2*C-C^2>=0 ==> x<=m".asSequent
    val smartHidden = proveBy(boundHidden.subgoals.loneElement, smartHide)
    smartHidden.subgoals.loneElement shouldBe "v>=0, -B<0, v^2<=2*B*(m-x), v<0 ==> x<=m".asSequent
    proveBy(smartHidden.subgoals.loneElement, QE) shouldBe Symbol("proved")
  }

  "smartQE" should "support using notation" in withMathematica { _ =>
    proveBy(
      "a^2<=1, abs(x)<=a, b=2 ==> abs(x)^2<=1".asSequent,
      """ smartQE using "a^2<=1 :: abs(x)<=a :: abs(x)^2<=1 :: nil" """.asTactic,
    ) shouldBe Symbol("proved")
  }
}
