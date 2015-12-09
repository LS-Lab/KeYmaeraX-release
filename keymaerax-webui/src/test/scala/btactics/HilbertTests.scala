package btactics

/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/


import edu.cmu.cs.ls.keymaerax.btactics.UnifyUSCalculus
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tactics.{Context, PosInExpr, Position, SuccPosition, TactixLibrary}
import edu.cmu.cs.ls.keymaerax.tags.{SummaryTest, UsualTest}
import test.RandomFormula
import testHelper.KeYmaeraXTestTags

import scala.collection.immutable._

/**
 * Tests Hilbert Calculus.
 * @author Andre Platzer
 */
@SummaryTest
@UsualTest
class HilbertTests extends TacticTestBase {

  object TestLib extends UnifyUSCalculus

  val randomTrials = 10
  val randomComplexity = 3
  val rand = new RandomFormula() //(-4317240407825764493L)

  "UseAt" should "reduce x>5 |- [x:=x+1;x:=2*x;]x>1 to x>5 |- [x:=x+1;][x:=2*x;]x>1 by useAt" in {
    proveBy("[x:=x+1;x:=2*x;]x>1".asFormula, TestLib.useAt("[;] compose")(SuccPosition(0))).subgoals should contain only
      Sequent(Nil, IndexedSeq(), IndexedSeq("[x:=x+1;][x:=2*x;]x>1".asFormula))
  }

  it should "reduce x>5 |- [x:=x+1;][x:=2*x;]x>1 to x>5 |- [x:=x+1;x:=2*x;]x>1 by useAt backwards" in {
    proveBy(Sequent(Nil, IndexedSeq("x>5".asFormula), IndexedSeq("[x:=x+1;][x:=2*x;]x>1".asFormula)),
      TestLib.useAt("[;] compose", PosInExpr(1::Nil))(SuccPos(0))).subgoals should contain only Sequent(Nil, IndexedSeq("x>5".asFormula), IndexedSeq("[x:=x+1;x:=2*x;]x>1".asFormula))
  }

  it should "reduce [x:=x+1;x:=2*x;]x>1 |- x>5 to [x:=x+1;][x:=2*x;]x>1 |- x>5 by useAt" in {
    proveBy(Sequent(Nil, IndexedSeq("[x:=x+1;x:=2*x;]x>1".asFormula), IndexedSeq("x>5".asFormula)),
      TestLib.useAt("[;] compose")(AntePos(0))).subgoals should contain only Sequent(Nil, IndexedSeq("[x:=x+1;][x:=2*x;]x>1".asFormula), IndexedSeq("x>5".asFormula))
  }

  it should "reduce [x:=x+1;][x:=2*x;]x>1 |- x>5 to [x:=x+1;x:=2*x;]x>1 |- x>5 by useAt backwards" in {
    proveBy(Sequent(Nil, IndexedSeq("[x:=x+1;][x:=2*x;]x>1".asFormula), IndexedSeq("x>5".asFormula)),
      TestLib.useAt("[;] compose", PosInExpr(1::Nil))(AntePos(0))).subgoals should contain only Sequent(Nil, IndexedSeq("[x:=x+1;x:=2*x;]x>1".asFormula), IndexedSeq("x>5".asFormula))
  }


  it should "reduce x>5 |- [c;d;]x>1 to x>5 |- [c;][d;]x>1 by useAt" in {
    proveBy(Sequent(Nil, IndexedSeq("x>5".asFormula), IndexedSeq("[c;d;]x>1".asFormula)),
      TestLib.useAt("[;] compose")(SuccPos(0))).subgoals should contain only Sequent(Nil, IndexedSeq("x>5".asFormula), IndexedSeq("[c;][d;]x>1".asFormula))
  }

  it should "reduce x>5 |- [c;][d;]x>1 to x>5 |- [c;d;]x>1 by useAt backwards" in {
    proveBy(Sequent(Nil, IndexedSeq("x>5".asFormula), IndexedSeq("[c;][d;]x>1".asFormula)),
      TestLib.useAt("[;] compose", PosInExpr(1::Nil))(SuccPos(0))).subgoals should contain only Sequent(Nil, IndexedSeq("x>5".asFormula), IndexedSeq("[c;d;]x>1".asFormula))
  }

  it should "reduce [c;d;]x>1 |- x>5 to [c;][d;]x>1 |- x>5 by useAt" in {
    proveBy(Sequent(Nil, IndexedSeq("[c;d;]x>1".asFormula), IndexedSeq("x>5".asFormula)),
      TestLib.useAt("[;] compose")(AntePos(0))).subgoals should contain only Sequent(Nil, IndexedSeq("[c;][d;]x>1".asFormula), IndexedSeq("x>5".asFormula))
  }

  it should "reduce [c;][d;]x>1 |- x>5 to [c;d;]x>1 |- x>5 by useAt backwards" in {
    proveBy(Sequent(Nil, IndexedSeq("[c;][d;]x>1".asFormula), IndexedSeq("x>5".asFormula)),
      TestLib.useAt("[;] compose", PosInExpr(1::Nil))(AntePos(0))).subgoals should contain only Sequent(Nil, IndexedSeq("[c;d;]x>1".asFormula), IndexedSeq("x>5".asFormula))
  }

  "CMon monotonicity" should "prove x<99 -> y<2 & x>5 |- x<99 -> y<2 & x>2 from x>5 |- x>2" in {
    val done = TestLib.CMon(Context("x<99 -> y<2 & ⎵".asFormula)) (Provable.startProof(Sequent(Nil, IndexedSeq("x>5".asFormula), IndexedSeq("x>2".asFormula))))
    done.subgoals shouldBe List(Sequent(Nil, IndexedSeq("x>5".asFormula), IndexedSeq("x>2".asFormula)))
    done.conclusion shouldBe Sequent(Nil, IndexedSeq("x<99 -> y<2 & x>5".asFormula), IndexedSeq("x<99 -> y<2 & x>2".asFormula))
  }

  it should "prove x<99 -> y<2 & x>5 |- x<99 -> y<2 & x>2 from provable x>5 |- x>2" in {
    val done = TestLib.CMon(Context("x<99 -> y<2 & ⎵".asFormula)) (basicImpl)
    done shouldBe 'proved
    done.conclusion shouldBe Sequent(Nil, IndexedSeq("x<99 -> y<2 & x>5".asFormula), IndexedSeq("x<99 -> y<2 & x>2".asFormula))
  }

  private def shouldCMon(ctx: Context[Formula], basic: Provable = basicImpl): Unit = {
    require(basic.isProved)
    require(basic.conclusion.ante.length==1 && basic.conclusion.succ.length==1)
    val done = TestLib.CMon(ctx)(basic)
    done shouldBe 'proved
    done.conclusion shouldBe Sequent(Nil, IndexedSeq(ctx(basic.conclusion.ante.head)), IndexedSeq(ctx(basic.conclusion.succ.head)))
  }

  private def shouldCMonA(ctx: Context[Formula], basic: Provable = basicImpl): Unit = {
    require(basic.isProved)
    require(basic.conclusion.ante.length==1 && basic.conclusion.succ.length==1)
    val done = TestLib.CMon(ctx)(basic)
    done shouldBe 'proved
    done.conclusion shouldBe Sequent(Nil, IndexedSeq(ctx(basic.conclusion.succ.head)), IndexedSeq(ctx(basic.conclusion.ante.head)))
  }

  it should "prove y<2 & x>5 |- y<2 & x>2 from x>5 |- x>2" in {shouldCMon(Context("y<2 & ⎵".asFormula))}
  it should "prove x>5 & y<2 |- x>2 & y<2 from x>5 |- x>2" in {shouldCMon(Context("⎵ & y<2".asFormula))}
  it should "prove x<99 -> x>5 |- x<99 -> x>2 from x>5 |- x>2" in {shouldCMon(Context("x<99 -> ⎵".asFormula))}
  it should "prove x<99 | x>5 |- x<99 | x>2 from x>5 |- x>2" in {shouldCMon(Context("x<99 | ⎵".asFormula))}
  it should "prove in monotone context x<99 | _ & y<2" in {shouldCMon(Context("x<99 | ⎵ & y<2".asFormula))}
  it should "prove in monotone context (x<99 | _) & y<2" in {shouldCMon(Context("(x<99 | ⎵) & y<2".asFormula))}
  it should "prove in monotone context x<7 -> (x<99 | _) & y<2" in {shouldCMon(Context("x<7 -> (x<99 | ⎵) & y<2".asFormula))}
  it should "prove in monotone context x<y -> x<7 -> (x<99 | x<10 -> (_ & z=2 | x=5 & y=3)) & y<2" in {shouldCMon(Context("x<y -> x<7 -> (x<99 | x<10 -> (⎵ & z=2 | x=5 & y=3)) & y<2".asFormula))}
  it should "prove in monotone context \\forall y _" in {shouldCMon(Context("\\forall y ⎵".asFormula))}
  it should "prove in monotone context \\forall x _" in {shouldCMon(Context("\\forall x ⎵".asFormula))}
  it should "prove in monotone context \\exists y _" in {shouldCMon(Context("\\exists y ⎵".asFormula))}
  it should "prove in monotone context \\exists x _" in {shouldCMon(Context("\\exists x ⎵".asFormula))}
  it should "prove in monotone context \\forall y (_ | x<y)" in {shouldCMon(Context("\\forall y (⎵ | x<y)".asFormula))}
  it should "prove in monotone context \\forall x (_ | x<y)" in {shouldCMon(Context("\\forall x (⎵ | x<y)".asFormula))}
  it should "prove in monotone context \\exists y (_ | x<y)" in {shouldCMon(Context("\\exists y (⎵ | x<y)".asFormula))}
  it should "prove in monotone context \\exists x (_ | x<y)" in {shouldCMon(Context("\\exists x (⎵ | x<y)".asFormula))}
  it should "prove in antimonotone context _ -> y<2" in {shouldCMonA(Context("⎵ -> y<2".asFormula))}
  it should "prove in antimonotone context _ -> y<2 & x<10" in {shouldCMonA(Context("⎵ -> y<2 & x<10".asFormula))}
  it should "prove in antimonotone context (_ -> y<2) & x<10" in {shouldCMonA(Context("(⎵ -> y<2) & x<10".asFormula))}
  it should "prove in antimonotone context (_ -> y<2) & x<10 | x=7" in {shouldCMonA(Context("(⎵ -> y<2) & x<10 | x=7".asFormula))}
  it should "prove in antimonotone context (<x:=5;>_ -> y<2) & x<10 | x=7" in {shouldCMonA(Context("(<x:=5;>⎵ -> y<2) & x<10 | x=7".asFormula))}
  it should "prove in antimonotone context (a=3|<x:=5;>_ -> y<2) & x<10 | x=7" in {shouldCMonA(Context("(a=3|<x:=5;>⎵ -> y<2) & x<10 | x=7".asFormula))}
  it should "prove in antimonotone context (<x:=5;>_&a=3 -> y<2) & x<10 | x=7" in {shouldCMonA(Context("(<x:=5;>⎵&a=3 -> y<2) & x<10 | x=7".asFormula))}
  it should "prove in antiantimonotone context ((_ -> y<2) -> z=0) & x<10 | x=7" in {shouldCMon(Context("((⎵ -> y<2) -> z=0) & x<10 | x=7".asFormula))}

  lazy val basicImpl = TactixLibrary.proveBy(Sequent(Nil, IndexedSeq("x>5".asFormula), IndexedSeq("x>2".asFormula)),
    TactixLibrary.QE)

  ignore should "prove C{x>5} |- C{x>2} from provable x>5 |- x>2 in random positive contexts" in {
    println("Starting random contexts\n\n")
    for (i <- 1 to randomTrials) {
      val ctx = rand.nextFormulaContext(randomComplexity)
      if (ctx.isFormulaContext) {
        println("Context: " + ctx)
        //@todo discard ctx unless positive
        //@todo discard ctx if DotFormula within a program
        //@todo discard ctx if DotFormula somewhere underneath an Equiv
        try {
          val done = TestLib.CMon(ctx)(basicImpl)
          done shouldBe 'proved
          done.conclusion shouldBe Sequent(Nil, IndexedSeq(ctx("x>5".asFormula)), IndexedSeq(ctx("x>2".asFormula)))
        } catch {
          case e: ProverException => if (e.toString.startsWith("No monotone context")) println("context discarded") else throw e
        }
      }
    }
  }

  lazy val basicEq = TactixLibrary.proveBy("1=0*x+1".asFormula, TactixLibrary.QE)
  lazy val basicEquiv = TactixLibrary.proveBy("-2<x&x<2 <-> x^2<4".asFormula, TactixLibrary.QE)

  private def shouldReduceTo(input: Formula, pos: Position, result: Formula, fact: Provable = basicEq): Unit =
    proveBy(input, TestLib.CE(fact)(pos)).subgoals should contain only
      new Sequent(Nil, IndexedSeq(), IndexedSeq(result))

  private def shouldReduceTo(input: Formula, pos: Position, result: Formula, fact: Provable, C: Context[Formula]): Unit =
    proveBy(input, TestLib.CE(fact, C)(pos)).subgoals should contain only
      new Sequent(Nil, IndexedSeq(), IndexedSeq(result))

  "CE(Provable) equation magic" should "reduce 0*x+1<=3 to 1<=3" in {
    shouldReduceTo("0*x+1<=3".asFormula, SuccPosition(0, PosInExpr(0::Nil)), "1<=3".asFormula)
  }

  it should "reduce x<5 & 0*x+1<=3 | x>=2 to x<5 & 1<=3 | x>=2" taggedAs KeYmaeraXTestTags.SummaryTest in {
    shouldReduceTo("x<5 & 0*x+1<=3 | x>=2".asFormula, SuccPosition(0, PosInExpr(0::1::0::Nil)), "x<5 & 1<=3 | x>=2".asFormula)
  }

  it should "reduce \\forall x 0*x+1<=3 to \\forall x 1<=3" in {
    shouldReduceTo("\\forall x 0*x+1<=3".asFormula, SuccPosition(0, PosInExpr(0::0::Nil)), "\\forall x 1<=3".asFormula)
  }

  ignore should "reduce x<5 & \\forall x 0*x+1<=3 | x>=2 to x<5 & \\forall x 1<=3 | x>=2" taggedAs KeYmaeraXTestTags.SummaryTest in {
    shouldReduceTo("x<5 & \\forall x 0*x+1<=3 | x>=2".asFormula, SuccPosition(0, PosInExpr(0::1::0::0::Nil)), "x<5 & \\forall x 1<=3 | x>=2".asFormula)
  }

  it should "reduce [x:=7;]0*x+1<=3 to [x:=7;]1<=3" in {
    shouldReduceTo("[x:=7;]0*x+1<=3".asFormula, SuccPosition(0, PosInExpr(1::0::Nil)), "[x:=7;]1<=3".asFormula)
  }

  it should "reduce [x:=7;?0*x+1<=3;]x<9 to [x:=7;?1<=3;]x<9" in {
    shouldReduceTo("[x:=7;?0*x+1<=3;]x<9".asFormula, SuccPosition(0, PosInExpr(0::1::0::0::Nil)), "[x:=7;?1<=3;]x<9".asFormula)
  }

  it should "reduce [x:=0*x+1;]x<9 to [x:=1;]x<9" in {
    shouldReduceTo("[x:=0*x+1;]x<9".asFormula, SuccPosition(0, PosInExpr(0::1::Nil)), "[x:=1;]x<9".asFormula)
  }

  ignore should "reduce [x:=7;x:=0*x+1;]x<9 to [x:=7;x:=1;]x<9" in {
    shouldReduceTo("[x:=7;x:=0*x+1;]x<9".asFormula, SuccPosition(0, PosInExpr(0::1::1::Nil)), "[x:=7;x:=1;]x<9".asFormula)
  }

  it should "reduce [{x' = 7 & 0*x+1<2}]x>=2 to [{x' = 7 & 1<2}]x>=2" in {
    shouldReduceTo("[{x' = 7 & 0*x+1<2}]x>=2".asFormula, SuccPosition(0, PosInExpr(0::1::0::Nil)), "[{x' = 7 & 1<2}]x>=2".asFormula)
  }

  ignore should "reduce [{x' = 0*x+1 & 5=5}]x>=2 to [{x' = 1 & 5=5}]x>=2" in {
    shouldReduceTo("[{x' = 0*x+1 & 5=5}]x>=2".asFormula, SuccPosition(0, PosInExpr(0::0::1::Nil)), "[{x' = 1 & 5=5}]x>=2".asFormula)
  }


  "CE(Provable) equivalence magic" should "reduce x^2<4 to -2<x&x<2" in {
    shouldReduceTo("x^2<4".asFormula, SuccPosition(0, PosInExpr(Nil)), "-2<x&x<2".asFormula, basicEquiv)
  }

  it should "reduce !(x^2<4) to !(-2<x&x<2)" in {
    shouldReduceTo("!x^2<4".asFormula, SuccPosition(0, PosInExpr(0::Nil)), "!(-2<x&x<2)".asFormula, basicEquiv)
  }

  it should "reduce x<5 & x^2<4 | x>=2 to x<5 & (-2<x&x<2) | x>=2" in {
    shouldReduceTo("x<5 & x^2<4| x>=2".asFormula, SuccPosition(0, PosInExpr(0::1::Nil)), "x<5 & (-2<x&x<2) | x>=2".asFormula, basicEquiv)
  }

  it should "reduce x<5 & \\forall x x^2<4 | x>=2 to x<5 & \\forall x (-2<x&x<2) | x>=2" in {
    shouldReduceTo("x<5 & \\forall x x^2<4| x>=2".asFormula, SuccPosition(0, PosInExpr(0::1::0::Nil)), "x<5 & \\forall x (-2<x&x<2) | x>=2".asFormula, basicEquiv)
  }

  it should "reduce [{x' = 5*x & x^2<4}]x>=1 to [{x' = 5*x & -2<x&x<2}]x>=1" taggedAs KeYmaeraXTestTags.SummaryTest in {
    shouldReduceTo("[{x' = 5*x & x^2<4}]x>=1".asFormula, SuccPosition(0, PosInExpr(0::1::Nil)), "[{x' = 5*x & -2<x&x<2}]x>=1".asFormula, basicEquiv)
  }

  it should "reduce x<5 & x^2<4 -> [{x' = 5*x & x^2<4}](x^2<4 & x>=1) to x<5 & (-2<x&x<2) -> [{x' = 5*x & -2<x&x<2}]((-2<x&x<2) & x>=1)" in {
    val C = Context("x<5 & ⎵ -> [{x' = 5*x & ⎵}](⎵ & x>=1)".asFormula)
    shouldReduceTo("x<5 & x^2<4 -> [{x' = 5*x & x^2<4}](x^2<4 & x>=1)".asFormula, SuccPosition(0), "x<5 & (-2<x&x<2) -> [{x' = 5*x & -2<x&x<2}]((-2<x&x<2) & x>=1)".asFormula, basicEquiv, C)
  }
}
