/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tactics.{AntePosition, PosInExpr, RootNode, SuccPosition, EqualityRewritingImpl,
  Interpreter, Tactics}
import edu.cmu.cs.ls.keymaerax.tactics.EqualityRewritingImpl.{constFormulaCongruenceT, eqLeft}
import edu.cmu.cs.ls.keymaerax.tools.{KeYmaera, Mathematica}
import testHelper.ProvabilityTestHelper
import org.scalatest.{BeforeAndAfterEach, Matchers, FlatSpec}
import testHelper.SequentFactory._

import scala.collection.immutable.Map

/**
 * Created by smitsch on 3/16/15.
 * @author Stefan Mitsch
 */
class EqualityRewritingTests extends FlatSpec with Matchers with BeforeAndAfterEach {
  // TODO mathematica is only necessary because of ProofFactory -> make ProofFactory configurable

  val helper = new ProvabilityTestHelper((x) => println(x))
  val mathematicaConfig: Map[String, String] = helper.mathematicaConfig

  override def beforeEach() = {
    Tactics.KeYmaeraScheduler = new Interpreter(KeYmaera)
    Tactics.MathematicaScheduler = new Interpreter(new Mathematica)
    Tactics.MathematicaScheduler.init(mathematicaConfig)
    Tactics.KeYmaeraScheduler.init(Map())
  }

  override def afterEach() = {
    Tactics.MathematicaScheduler.shutdown()
    Tactics.KeYmaeraScheduler.shutdown()
    Tactics.MathematicaScheduler = null
    Tactics.KeYmaeraScheduler = null
  }

//  "Equality rewriting" should "not apply <-> unsoundly" in {
//    val s = sequent(Nil, "x'=0".asFormula :: "(x*y())' <= 0 <-> 0 <= 0".asFormula :: Nil,
//      "[x':=1;]0<=0 -> [x':=1;]((x*y()) <= 0)'".asFormula :: Nil)
//    val tactic = EqualityRewritingImpl.equalityRewriting(AntePosition(1), SuccPosition(0, PosInExpr(1::1::Nil)))
//    tactic.applicable(new RootNode(s)) shouldBe false
//
//    an [IllegalArgumentException] should be thrownBy
//      new EqualityRewriting(AntePosition(0), SuccPosition(0, PosInExpr(1::1::Nil))).apply(s)
//  }
//
//  it should "not apply = unsoundly" in {
//    val s = sequent(Nil, "x'=0".asFormula :: "(x*y())' = 0".asFormula :: Nil,
//      "[x':=1;]0<=0 -> [x':=1;](x*y())' <= 0".asFormula :: Nil)
//    val tactic = EqualityRewritingImpl.equalityRewriting(AntePosition(1), SuccPosition(0, PosInExpr(1::1::Nil)))
//    tactic.applicable(new RootNode(s)) shouldBe false
//
//    an [IllegalArgumentException] should be thrownBy
//      new EqualityRewriting(AntePosition(0), SuccPosition(0, PosInExpr(1::1::Nil))).apply(s)
//  }

  "Const formula congruence" should "rewrite x*y=0 to 0*y=0 using x=0" in {
    val s = sequent(Nil, "x=0".asFormula::Nil, "x*y=0".asFormula::Nil)
    val tactic = constFormulaCongruenceT(AntePosition(0), left = true, exhaustive = false)(SuccPosition(0, PosInExpr(0::0::Nil)))
    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only "x=0".asFormula
    result.openGoals().flatMap(_.sequent.succ) should contain only "0*y=0".asFormula
  }

  it should "rewrite complicated" in {
    val s = sequent(Nil, "x=0".asFormula::Nil, "x*y=0 & x+3>2 | \\forall y y+x>=0".asFormula::Nil)
    val tactic =
      constFormulaCongruenceT(AntePosition(0), left = true, exhaustive = false)(SuccPosition(0, PosInExpr(0::0::0::0::Nil))) &
      constFormulaCongruenceT(AntePosition(0), left = true, exhaustive = false)(SuccPosition(0, PosInExpr(0::1::0::0::Nil))) &
      constFormulaCongruenceT(AntePosition(0), left = true, exhaustive = false)(SuccPosition(0, PosInExpr(1::0::0::1::Nil)))
    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only "x=0".asFormula
    result.openGoals().flatMap(_.sequent.succ) should contain only "0*y=0 & 0+3>2 | \\forall y y+0>=0".asFormula
  }

  it should "rewrite complicated exhaustively" in {
    val s = sequent(Nil, "x=0".asFormula::Nil, "x*y=0 & x+3>2 | \\forall y y+x>=0 & \\exists x x>0".asFormula::Nil)
    val tactic =
      constFormulaCongruenceT(AntePosition(0), left = true)(SuccPosition(0))
    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only "x=0".asFormula
    result.openGoals().flatMap(_.sequent.succ) should contain only "0*y=0 & 0+3>2 | \\forall y y+0>=0 & \\exists x x>0".asFormula
  }

  ignore should "throw a substitution clash exception if it tries to rename bound" in {
    val s = sequent(Nil, "x=0".asFormula::Nil, "\\forall x y+x>=0".asFormula::Nil)
    val tactic = constFormulaCongruenceT(AntePosition(0), left = true, exhaustive = false)(SuccPosition(0, PosInExpr(0::0::1::Nil)))
    // somehow, the exception is thrown but swallowed somewhere
    a [SubstitutionClashException] should be thrownBy helper.runTactic(tactic, new RootNode(s))
  }

  it should "rewrite x*y=0 to 0*y=0 using 0=x" in {
    val s = sequent(Nil, "0=x".asFormula::Nil, "x*y=0".asFormula::Nil)
    val tactic = constFormulaCongruenceT(AntePosition(0), left = false, exhaustive = false)(SuccPosition(0, PosInExpr(0::0::Nil)))
    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only "0=x".asFormula
    result.openGoals().flatMap(_.sequent.succ) should contain only "0*y=0".asFormula
  }

  "EqLeft" should "rewrite a single formula exhaustively" in {
    val s = sequent(Nil, "x=0".asFormula::Nil, "x*y=0".asFormula :: "z>2".asFormula :: "z<x+1".asFormula :: Nil)
    val tactic = eqLeft(exhaustive=true)(AntePosition(0))
    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only "x=0".asFormula
    result.openGoals().flatMap(_.sequent.succ) should contain only ("0*y=0".asFormula, "z>2".asFormula, "z<0+1".asFormula)
  }

  it should "rewrite formulas exhaustively" in {
    val s = sequent(Nil, "x=0".asFormula :: "z=x".asFormula :: Nil, "x*y=0".asFormula :: "z>2".asFormula :: "z<x+1".asFormula :: Nil)
    val tactic = eqLeft(exhaustive=true)(AntePosition(0))
    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only ("x=0".asFormula, "z=0".asFormula)
    result.openGoals().flatMap(_.sequent.succ) should contain only ("0*y=0".asFormula, "z>2".asFormula, "z<0+1".asFormula)
  }

  it should "rewrite formulas exhaustively everywhere" in {
    val s = sequent(Nil, "z=x".asFormula :: "x=0".asFormula :: Nil, "x*y=0".asFormula :: "z>2".asFormula :: "z<x+1".asFormula :: Nil)
    val tactic = eqLeft(exhaustive=true)(AntePosition(1))
    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only ("x=0".asFormula, "z=0".asFormula)
    result.openGoals().flatMap(_.sequent.succ) should contain only ("0*y=0".asFormula, "z>2".asFormula, "z<0+1".asFormula)
  }

  it should "work even if there is only one other formula" in {
    val s = sequent(Nil, "x<5".asFormula :: "x=0".asFormula :: Nil, Nil)
    val tactic = eqLeft(exhaustive=true)(AntePosition(1))
    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only ("0<5".asFormula, "x=0".asFormula)
    result.openGoals().flatMap(_.sequent.succ) shouldBe empty
  }

  it should "replace arbitary terms" in {
    val s = sequent(Nil, "a+b<5".asFormula :: "a+b=c".asFormula :: Nil, Nil)
    val tactic = eqLeft(exhaustive=true)(AntePosition(1))
    val result = helper.runTactic(tactic, new RootNode(s))

    result.openGoals() should have size 1
    result.openGoals().head.sequent.ante should contain only ("c<5".asFormula, "a+b=c".asFormula)
    result.openGoals().head.sequent.succ shouldBe empty
  }

  // rewriting numbers is disallowed, because otherwise we run into endless rewriting
  it should "not rewrite numbers" in {
    val s = sequent(Nil, "0<5".asFormula :: "0=0".asFormula :: Nil, Nil)
    val tactic = eqLeft(exhaustive=true)(AntePosition(1))
    tactic.applicable(new RootNode(s)) shouldBe false
  }

  "Equivalence rewriting" should "rewrite if lhs occurs in succedent" in {
    val s = sequent(Nil, "x>=0 <-> y>=0".asFormula :: Nil, "x>=0".asFormula :: Nil)
    val tactic = EqualityRewritingImpl.equivRewriting(AntePosition(0), SuccPosition(0))
    val result = helper.runTactic(tactic, new RootNode(s))

    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "y>=0".asFormula
  }

  it should "rewrite if rhs occurs in succedent" in {
    val s = sequent(Nil, "x>=0 <-> y>=0".asFormula :: Nil, "y>=0".asFormula :: Nil)
    val tactic = EqualityRewritingImpl.equivRewriting(AntePosition(0), SuccPosition(0))
    val result = helper.runTactic(tactic, new RootNode(s))

    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "x>=0".asFormula
  }

  it should "rewrite if lhs occurs in antecedent" in {
    val s = sequent(Nil, "x>=0 <-> y>=0".asFormula :: "x>=0".asFormula :: Nil, Nil)
    val tactic = EqualityRewritingImpl.equivRewriting(AntePosition(0), AntePosition(1))
    val result = helper.runTactic(tactic, new RootNode(s))

    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only "y>=0".asFormula
    result.openGoals().flatMap(_.sequent.succ) shouldBe empty
  }

  it should "rewrite if lhs occurs in antecedent before assumption" in {
    val s = sequent(Nil, "x>=0".asFormula :: "x>=0 <-> y>=0".asFormula :: Nil, Nil)
    val tactic = EqualityRewritingImpl.equivRewriting(AntePosition(1), AntePosition(0))
    val result = helper.runTactic(tactic, new RootNode(s))

    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only "y>=0".asFormula
    result.openGoals().flatMap(_.sequent.succ) shouldBe empty
  }

  it should "rewrite if rhs occurs in antecedent" in {
    val s = sequent(Nil, "x>=0 <-> y>=0".asFormula :: "y>=0".asFormula :: Nil, Nil)
    val tactic = EqualityRewritingImpl.equivRewriting(AntePosition(0), AntePosition(1))
    val result = helper.runTactic(tactic, new RootNode(s))

    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only "x>=0".asFormula
    result.openGoals().flatMap(_.sequent.succ) shouldBe empty
  }

  it should "rewrite if rhs occurs in antecedent before assumption" in {
    val s = sequent(Nil, "y>=0".asFormula :: "x>=0 <-> y>=0".asFormula :: Nil, Nil)
    val tactic = EqualityRewritingImpl.equivRewriting(AntePosition(1), AntePosition(0))
    val result = helper.runTactic(tactic, new RootNode(s))

    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only "x>=0".asFormula
    result.openGoals().flatMap(_.sequent.succ) shouldBe empty
  }

  "Abbrv tactic" should "abbreviate a+b to z" in {
    val s = sucSequent("a+b < c".asFormula)
    val tactic = EqualityRewritingImpl.abbrv(Variable("z"))(SuccPosition(0).first)
    val result = helper.runTactic(tactic, new RootNode(s))

    result.openGoals() should have size 1
    result.openGoals().head.sequent.ante should contain only "z = a+b".asFormula
    result.openGoals().head.sequent.succ should contain only "z < c".asFormula
  }

  it should "abbreviate min(a,b) to z" in {
    val s = sucSequent("min(a,b) < c".asFormula)
    val tactic = EqualityRewritingImpl.abbrv(Variable("z"))(SuccPosition(0).first)
    val result = helper.runTactic(tactic, new RootNode(s))

    result.openGoals() should have size 1
    result.openGoals().head.sequent.ante should contain only "z = min(a,b)".asFormula
    result.openGoals().head.sequent.succ should contain only "z < c".asFormula
  }
}
