/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package btactics

import edu.cmu.cs.ls.keymaerax.btactics.ArithmeticSimplification._
import edu.cmu.cs.ls.keymaerax.bellerophon.TheType
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.arithmetic.signanalysis.{Bound, Sign, SignAnalysis}
import edu.cmu.cs.ls.keymaerax.btactics.{ArithmeticSimplification, TacticTestBase, TactixLibrary}
import edu.cmu.cs.ls.keymaerax.core.{SeqPos, Sequent}

import scala.collection.immutable._

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

  it should "compute wanted bounds from succedent" in {
    val s = Sequent(Nil,
      IndexedSeq("A>=0".asFormula, "-B<0".asFormula, "v^2<=2*B*(m-x)".asFormula),
      IndexedSeq("x+5<=m".asFormula, "v^2<=2*B*(m-x)".asFormula))
    SignAnalysis.bounds(s) shouldBe Map(
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
}
