package btactics

/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/


import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, BelleValue, BelleProvable, SequentialInterpreter}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXPrettyPrinter, KeYmaeraXParser}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.tactics.SuccPosition
import edu.cmu.cs.ls.keymaerax.tags.{SummaryTest, UsualTest}
import edu.cmu.cs.ls.keymaerax.tools.{KeYmaera, Mathematica}
import org.scalatest.{BeforeAndAfterEach, FlatSpec, Matchers}
import test.RandomFormula
import testHelper.ParserFactory._
import testHelper.{KeYmaeraXTestTags, ProvabilityTestHelper}

import scala.collection.immutable._

/**
 * Tests Hilbert Calculus.
 * @author Andre Platzer
 */
@SummaryTest
@UsualTest
class HilbertTests extends FlatSpec with Matchers with BeforeAndAfterEach {

  object TestLib extends UnifyUSCalculus

  val randomTrials = 10
  val randomComplexity = 3
  val rand = new RandomFormula() //(-4317240407825764493L)

  val theInterpreter = SequentialInterpreter()

  override def beforeEach() = {
    PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter.pp)
  }

  private def proveBy(fml: Formula, tactic: BelleExpr): BelleValue = {
    val v = BelleProvable(Provable.startProof(fml))
    theInterpreter.apply(tactic, v)
  }

  "Hilbert calculus" should "prove 2=2" in {
    proveBy("2=2".asFormula, TestLib.useAt("= reflexive")) match {
      case BelleProvable(provable) => provable.subgoals shouldBe empty
      case r => fail("Unexpected tactic result " + r)
    }
  }

  "UseAt" should "reduce x>5 |- [x:=x+1;x:=2*x;]x>1 to x>5 |- [x:=x+1;][x:=2*x;]x>1 by useAt" in {
    proveBy("[x:=x+1;x:=2*x;]x>1".asFormula, TestLib.useAt("[;] compose")(SuccPosition(0))) match {
      case BelleProvable(provable) => provable.subgoals should contain only Sequent(Nil, IndexedSeq(), IndexedSeq("[x:=x+1;][x:=2*x;]x>1".asFormula))
      case r => fail("Unexpected tactic result " + r)
    }
  }

//  it should "reduce x>5 |- [x:=x+1;][x:=2*x;]x>1 to x>5 |- [x:=x+1;x:=2*x;]x>1 by useAt backwards" in {
//    proveBy(Sequent(Nil, IndexedSeq("x>5".asFormula), IndexedSeq("[x:=x+1;][x:=2*x;]x>1".asFormula)),
//      useAt("[;] compose", PosInExpr(1::Nil))(1)).subgoals should contain only Sequent(Nil, IndexedSeq("x>5".asFormula), IndexedSeq("[x:=x+1;x:=2*x;]x>1".asFormula))
//  }
//
//  it should "reduce [x:=x+1;x:=2*x;]x>1 |- x>5 to [x:=x+1;][x:=2*x;]x>1 |- x>5 by useAt" in {
//    proveBy(Sequent(Nil, IndexedSeq("[x:=x+1;x:=2*x;]x>1".asFormula), IndexedSeq("x>5".asFormula)),
//      useAt("[;] compose")(-1)).subgoals should contain only Sequent(Nil, IndexedSeq("[x:=x+1;][x:=2*x;]x>1".asFormula), IndexedSeq("x>5".asFormula))
//  }
//
//  it should "reduce [x:=x+1;][x:=2*x;]x>1 |- x>5 to [x:=x+1;x:=2*x;]x>1 |- x>5 by useAt backwards" in {
//    proveBy(Sequent(Nil, IndexedSeq("[x:=x+1;][x:=2*x;]x>1".asFormula), IndexedSeq("x>5".asFormula)),
//      useAt("[;] compose", PosInExpr(1::Nil))(-1)).subgoals should contain only Sequent(Nil, IndexedSeq("[x:=x+1;x:=2*x;]x>1".asFormula), IndexedSeq("x>5".asFormula))
//  }
//
//
//  it should "reduce x>5 |- [c;d;]x>1 to x>5 |- [c;][d;]x>1 by useAt" in {
//    proveBy(Sequent(Nil, IndexedSeq("x>5".asFormula), IndexedSeq("[c;d;]x>1".asFormula)),
//      useAt("[;] compose")(1)).subgoals should contain only Sequent(Nil, IndexedSeq("x>5".asFormula), IndexedSeq("[c;][d;]x>1".asFormula))
//  }
//
//  it should "reduce x>5 |- [c;][d;]x>1 to x>5 |- [c;d;]x>1 by useAt backwards" in {
//    proveBy(Sequent(Nil, IndexedSeq("x>5".asFormula), IndexedSeq("[c;][d;]x>1".asFormula)),
//      useAt("[;] compose", PosInExpr(1::Nil))(1)).subgoals should contain only Sequent(Nil, IndexedSeq("x>5".asFormula), IndexedSeq("[c;d;]x>1".asFormula))
//  }
//
//  it should "reduce [c;d;]x>1 |- x>5 to [c;][d;]x>1 |- x>5 by useAt" in {
//    proveBy(Sequent(Nil, IndexedSeq("[c;d;]x>1".asFormula), IndexedSeq("x>5".asFormula)),
//      useAt("[;] compose")(-1)).subgoals should contain only Sequent(Nil, IndexedSeq("[c;][d;]x>1".asFormula), IndexedSeq("x>5".asFormula))
//  }
//
//  it should "reduce [c;][d;]x>1 |- x>5 to [c;d;]x>1 |- x>5 by useAt backwards" in {
//    proveBy(Sequent(Nil, IndexedSeq("[c;][d;]x>1".asFormula), IndexedSeq("x>5".asFormula)),
//      useAt("[;] compose", PosInExpr(1::Nil))(-1)).subgoals should contain only Sequent(Nil, IndexedSeq("[c;d;]x>1".asFormula), IndexedSeq("x>5".asFormula))
//  }
}
