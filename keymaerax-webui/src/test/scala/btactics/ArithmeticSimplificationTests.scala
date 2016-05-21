/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package btactics

import edu.cmu.cs.ls.keymaerax.btactics.ArithmeticSimplification._
import edu.cmu.cs.ls.keymaerax.bellerophon.{OnAll, TheType}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.arithmetic.signanalysis.{Bound, Sign, SignAnalysis}
import edu.cmu.cs.ls.keymaerax.btactics.arithmetic.speculative.ArithmeticSpeculativeSimplification
import edu.cmu.cs.ls.keymaerax.btactics.{ArithmeticSimplification, TacticTestBase, TactixLibrary}
import edu.cmu.cs.ls.keymaerax.core._

import scala.collection.immutable._
import scala.language.postfixOps

/**
  * @author Nathan Fulton
  */
class ArithmeticSimplificationTests extends TacticTestBase {
  "smartHide" should "simplify x=1,y=1 ==> x=1 to x=1 ==> x=1" in {withMathematica(implicit qeTool => {
    val tactic = TactixLibrary.implyR(1) & TactixLibrary.andL(-1) & ArithmeticSimplification.smartHide
    val result = proveBy("x=1 & y=1 -> x=1".asFormula, tactic)
    result.subgoals(0).ante shouldBe result.subgoals(0).succ
  })}

  it should "not throw away transitivity info" in {withMathematica(implicit qeTool => {
    val tactic = TactixLibrary.implyR(1) & TactixLibrary.andL('L)*@(TheType()) & ArithmeticSimplification.smartHide
    val goal = "x=y & y=z & z > 0 -> x>0".asFormula
    val result = proveBy(goal, tactic)
    result.subgoals(0).ante.length shouldBe 3
    proveBy(goal, tactic & TactixLibrary.QE) shouldBe 'proved
  })}

  it should "forget useless stuff" in {withMathematica(implicit qeTool => {
    val tactic = TactixLibrary.implyR(1) & TactixLibrary.andL('L)*@(TheType()) & ArithmeticSimplification.smartHide
    val goal = "x>y & y>z & a > 0 & z > 0 -> x>0".asFormula
    val result = proveBy(goal, tactic)
    result.subgoals(0).ante.length shouldBe 3 //forget about a>0
    result.subgoals(0).ante.contains("a>0".asFormula) shouldBe false
    proveBy(goal, tactic & TactixLibrary.QE) shouldBe 'proved
  })}

  "replaceTransform" should "work in the antecedent" in withMathematica { tool =>
    proveBy("t<=ep & v>=0 & x>=x_0+v*ep -> x>=x_0+v*t".asFormula,
      prop & transformEquality("ep=t".asFormula)(-3) & closeId) shouldBe 'proved
  }

  it should "work in the succedent" in withMathematica { tool =>
    proveBy("t<=ep & v>=0 & x>=x_0+v*ep -> a<5 | x>=x_0+v*t | b<7".asFormula,
      prop & transformEquality("t=ep".asFormula)(2) & closeId) shouldBe 'proved
  }

  "Sign analysis" should "compute seed from antecedent" in {
    val s = Sequent(Nil,
      IndexedSeq("A>=0".asFormula, "-B<0".asFormula, "v^2<=2*B*(m-x)".asFormula, "A<0".asFormula, "2*C-C^2>=0".asFormula),
      IndexedSeq("x<=m".asFormula))
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
      "C".asVariable -> Map(Sign.Pos0 -> Set(SeqPos(-5)))
    )
  }

  it should "aggregate signs from seed" in {
    val s = Sequent(Nil,
      IndexedSeq("A>=0".asFormula, "-B<0".asFormula, "v^2<=2*B*(m-x)".asFormula, "A<0".asFormula, "2*C-C^2>=0".asFormula),
      IndexedSeq("x<=m".asFormula))
    val seed = SignAnalysis.aggregateSigns(SignAnalysis.seedSigns(s)) shouldBe Map(
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
      "C".asVariable -> Map(Sign.Pos0 -> Set(SeqPos(-5)))
      )
  }

  it should "pushDown signs from seed after aggregation" in {
    val s = Sequent(Nil,
      IndexedSeq("A>=0".asFormula, "-B<0".asFormula, "v^2<=2*B*(m-x)".asFormula, "A<0".asFormula, "2*C-C^2>=0".asFormula),
      IndexedSeq("x<=m".asFormula))
    val seed = SignAnalysis.seedSigns(s)
    SignAnalysis.pushDownSigns(SignAnalysis.aggregateSigns(seed)) shouldBe Map(
      "A".asVariable -> Map(Sign.Pos0 -> Set(SeqPos(-1)), Sign.Neg0 -> Set(SeqPos(-4))),
      "B".asVariable -> Map(Sign.Pos0 -> Set(SeqPos(-2), SeqPos(-3))),
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
      "C".asVariable -> Map(Sign.Pos0 -> Set(SeqPos(-5)))
    )
  }

  it should "pingpong until fixpoint" in {
    val s = Sequent(Nil,
      IndexedSeq("A>=0".asFormula, "-B<0".asFormula, "v^2<=2*B*(m-x)".asFormula, "A<0".asFormula, "2*C-C^2>=0".asFormula),
      IndexedSeq("x<=m".asFormula))
    SignAnalysis.computeSigns(s) shouldBe Map(
      "A".asVariable -> Map(Sign.Pos0 -> Set(SeqPos(-1)), Sign.Neg0 -> Set(SeqPos(-4))),
      "B".asVariable -> Map(Sign.Pos0 -> Set(SeqPos(-2), SeqPos(-3))),
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
      "C".asVariable -> Map(Sign.Pos0 -> Set(SeqPos(-5)))
    )
  }

  it should "work on the Robix example" in {
    val fml = "A>=0 & B>0 & V()>=0 & ep>0 & v_0>=0 & -B<=a & a<=A & abs(x_0-xo_0)>v_0^2/(2*B)+V()*v_0/B+(A/B+1)*(A/2*ep^2+ep*(v_0+V())) & -t*V()<=xo-xo_0 & xo-xo_0<=t*V() & v=v_0+a*t & -t*(v-a/2*t)<=x-x_0 & x-x_0<=t*(v-a/2*t) & t>=0 & t<=ep & v>=0 -> v=0|abs(x-xo)>v^2/(2*B)+V()*(v/B)".asFormula
    val s = proveBy(fml, alphaRule*@TheType())
    // only check atoms
    val signs = SignAnalysis.computeSigns(s.subgoals.head)
    println(signs)
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

  it should "work on another Robix example" in withMathematica { tool =>
    val fml = "A>=0 & B>0 & V()>=0 & ep>0 & v_0>=0 & -B<=a & a<=A & abs(x_0-xo_0)>v_0^2/(2*B)+V()*v_0/B+(A/B+1)*(A/2*ep^2+ep*(v_0+V())) & -t*V()<=xo-xo_0 & xo-xo_0<=t*V() & v=v_0+a*t & -t*(v-a/2*t)<=x-x_0 & x-x_0<=t*(v-a/2*t) & t>=0 & t<=ep & v>=0 -> v=0|abs(x-xo)>v^2/(2*B)+V()*(v/B)".asFormula
    val tactic = alphaRule*@TheType() &
      replaceTransform("ep".asTerm, "t".asTerm)(-8, s"abs(x_0-xo_0)>v_0^2/(2*B)+V()*v_0/B+(A/B+1)*(A/2*ep^2+ep*(v_0+V()))".asFormula) &
      abs(2, 0::Nil) & abs(-8, 0::Nil) & orL(-18) & OnAll(orL(-17) partial) &
      OnAll(andL('_)*@TheType() partial) & OnAll(exhaustiveEqL2R(hide=true)('L)*@TheType() partial)
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
    val s = Sequent(Nil,
      IndexedSeq("A>=0".asFormula, "-B<0".asFormula, "v^2<=2*B*(m-x)".asFormula),
      IndexedSeq("x+5<=m".asFormula, "v^2<=2*B*(m-x)".asFormula))
    SignAnalysis.bounds(s.succ, SuccPos) shouldBe Map(
      SeqPos(1) -> Map(
        "x".asVariable -> Bound.Upper,
        "m".asVariable -> Bound.Lower),
      SeqPos(2) -> Map(
        "x".asVariable -> Bound.Upper,
        "m".asVariable -> Bound.Lower,
        "B".asVariable -> Bound.Lower,
        "v".asVariable -> Bound.Unknown)
    )
  }

  it should "work on a Robix example" in withMathematica { tool =>
    val fml = "A>=0 & B>0 & V()>=0 & ep>0 & v_0>=0 & -B<=a & a<=A & abs(x_0-xo_0)>v_0^2/(2*B)+V()*v_0/B+(A/B+1)*(A/2*ep^2+ep*(v_0+V())) & -t*V()<=xo-xo_0 & xo-xo_0<=t*V() & v=v_0+a*t & -t*(v-a/2*t)<=x-x_0 & x-x_0<=t*(v-a/2*t) & t>=0 & t<=ep & v>=0 -> v=0|abs(x-xo)>v^2/(2*B)+V()*(v/B)".asFormula
    val tactic = alphaRule*@TheType() &
      replaceTransform("ep".asTerm, "t".asTerm)(-8, s"abs(x_0-xo_0)>v_0^2/(2*B)+V()*v_0/B+(A/B+1)*(A/2*ep^2+ep*(v_0+V()))".asFormula) &
      abs(2, 0::Nil) & abs(-8, 0::Nil) & orL(-18) & OnAll(orL(-17) partial) &
      OnAll(andL('_)*@TheType() partial) & OnAll(exhaustiveEqL2R(hide=true)('L)*@TheType() partial)
    val s = proveBy(fml, tactic)
    val bounds = SignAnalysis.bounds(s.subgoals.head.succ, SuccPos)
    bounds shouldBe Map(
      SeqPos(1) -> Map(
        "v_0".asVariable -> Bound.Exact,
        "a".asVariable -> Bound.Exact,
        "t".asVariable -> Bound.Exact
      ),
      SeqPos(2) -> Map(
        "x".asVariable -> Bound.Lower,
        "xo".asVariable -> Bound.Upper,
        "a".asVariable -> Bound.Upper,
        "V()".asTerm -> Bound.Upper,
        "v_0".asVariable -> Bound.Upper,
        "B".asVariable -> Bound.Lower,
        "t".asVariable -> Bound.Upper
      )
    )
  }

  "Bounds hiding" should "find formulas with non-matching bounds" in withMathematica { tool =>
    val s = Sequent(Nil,
      IndexedSeq("v>=0".asFormula, "-B<0".asFormula, "v^2<=2*B*(m-x)".asFormula, "v<0".asFormula, "x>m".asFormula, "2*C-C^2>=0".asFormula),
      IndexedSeq("x<=m".asFormula))

    proveBy(s, QE) shouldBe 'proved

    SignAnalysis.boundHideCandidates(s) should contain only SeqPos(-5)
  }

  it should "hide formulas with non-matching bounds" in withMathematica { tool =>
    val s = Sequent(Nil,
      IndexedSeq("v>=0".asFormula, "-B<0".asFormula, "v^2<=2*B*(m-x)".asFormula, "v<0".asFormula, "x>m".asFormula, "2*C-C^2>=0".asFormula),
      IndexedSeq("x<=m".asFormula))

    proveBy(s, QE) shouldBe 'proved

    val boundHidden = proveBy(s, ArithmeticSpeculativeSimplification.hideNonmatchingBounds)
    boundHidden.subgoals should have size 1
    boundHidden.subgoals.head.ante should contain theSameElementsAs List("v>=0".asFormula, "-B<0".asFormula, "v^2<=2*B*(m-x)".asFormula, "v<0".asFormula, "2*C-C^2>=0".asFormula)
    boundHidden.subgoals.head.succ should contain only "x<=m".asFormula

    proveBy(boundHidden.subgoals.head, QE) shouldBe 'proved
  }

  "Sign hiding" should "find inconsistent sign formulas" in {
    val s = Sequent(Nil,
      IndexedSeq("v>=0".asFormula, "-B<0".asFormula, "v^2<=2*B*(m-x)".asFormula, "v<0".asFormula, "x>m".asFormula, "2*C-C^2>=0".asFormula),
      IndexedSeq("x<=m".asFormula))

    SignAnalysis.signHideCandidates(s) should contain theSameElementsAs List(SeqPos(-2), SeqPos(-3), SeqPos(-5), SeqPos(-6), SeqPos(1))
  }

  it should "hide inconsistent sign formulas" in withMathematica { tool =>
    val s = Sequent(Nil,
      IndexedSeq("v>=0".asFormula, "-B<0".asFormula, "v^2<=2*B*(m-x)".asFormula, "v<0".asFormula, "x>m".asFormula, "2*C-C^2>=0".asFormula),
      IndexedSeq("x<=m".asFormula))

    proveBy(s, ArithmeticSpeculativeSimplification.hideInconsistentSigns & QE) shouldBe 'proved
  }

  "Multiple hidings together" should "figure it out" in withMathematica { implicit tool =>
    val s = Sequent(Nil,
      IndexedSeq("v>=0".asFormula, "-B<0".asFormula, "v^2<=2*B*(m-x)".asFormula, "v<0".asFormula, "x>m".asFormula, "2*C-C^2>=0".asFormula),
      IndexedSeq("x<=m".asFormula))

    val boundHidden = proveBy(s, ArithmeticSpeculativeSimplification.hideNonmatchingBounds)
    boundHidden.subgoals should have size 1
    boundHidden.subgoals.head.ante should contain theSameElementsAs List("v>=0".asFormula, "-B<0".asFormula, "v^2<=2*B*(m-x)".asFormula, "v<0".asFormula, "2*C-C^2>=0".asFormula)
    boundHidden.subgoals.head.succ should contain only "x<=m".asFormula

    val smartHidden = proveBy(boundHidden.subgoals.head, smartHide)
    smartHidden.subgoals should have size 1
    smartHidden.subgoals.head.ante should contain theSameElementsAs List("v>=0".asFormula, "-B<0".asFormula, "v^2<=2*B*(m-x)".asFormula, "v<0".asFormula)
    smartHidden.subgoals.head.succ should contain only "x<=m".asFormula

    proveBy(smartHidden.subgoals.head, QE) shouldBe 'proved
  }
}
