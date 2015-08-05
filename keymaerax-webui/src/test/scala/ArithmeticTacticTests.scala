/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
import edu.cmu.cs.ls.keymaerax.tactics._
import edu.cmu.cs.ls.keymaerax.tools.{Mathematica, KeYmaera}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import testHelper.ProvabilityTestHelper
import org.scalatest.{BeforeAndAfterEach, Matchers, FlatSpec}
import testHelper.SequentFactory._
import edu.cmu.cs.ls.keymaerax.tactics.SearchTacticsImpl.{locateAnte,locateSucc}
import edu.cmu.cs.ls.keymaerax.tactics.ArithmeticTacticsImpl._

import scala.collection.immutable
import scala.collection.immutable.Map

/**
 * Created by smitsch on 2/14/15.
 * @author Stefan Mitsch
 */
class ArithmeticTacticTests extends FlatSpec with Matchers with BeforeAndAfterEach {
  val helper = new ProvabilityTestHelper((x) => println(x))
  val mathematicaConfig: Map[String, String] = helper.mathematicaConfig

  override def beforeEach() = {
    Tactics.KeYmaeraScheduler = new Interpreter(KeYmaera)
    Tactics.KeYmaeraScheduler.init(Map())
    Tactics.MathematicaScheduler = new Interpreter(new Mathematica)
    Tactics.MathematicaScheduler.init(mathematicaConfig)
  }

  override def afterEach() = {
    Tactics.MathematicaScheduler.shutdown()
    Tactics.KeYmaeraScheduler.shutdown()
    Tactics.KeYmaeraScheduler = null
    Tactics.MathematicaScheduler = null
  }

  "NegateEqualsT" should "negate = in succedent" in {
    val s = sucSequent("x=0".asFormula)
    val tactic = locateSucc(NegateEqualsT)
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("!(x!=0)".asFormula)
    ))
  }

  it should "negate !(!=) in succedent" in {
    val s = sucSequent("!(x!=0)".asFormula)
    val tactic = locateSucc(NegateEqualsT)
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("x=0".asFormula)
    ))
  }

  it should "negate = in antecedent" in {
    val s = sequent(Nil, "x=0".asFormula :: Nil, Nil)
    val tactic = locateAnte(NegateEqualsT)
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sequent(Nil, "!(x!=0)".asFormula :: Nil, Nil)
    ))
  }

  it should "negate !(!=) in antecedent" in {
    val s = sequent(Nil, "!(x!=0)".asFormula :: Nil, Nil)
    val tactic = locateAnte(NegateEqualsT)
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sequent(Nil, "x=0".asFormula :: Nil, Nil)
    ))
  }

  it should "negate at position" in {
    val s = sequent(Nil, "a=b & !(x!=0)".asFormula :: Nil, Nil)
    val tactic = NegateEqualsT(AntePosition(0, PosInExpr(1::Nil)))
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sequent(Nil, "a=b & x=0".asFormula :: Nil, Nil)
    ))
  }

  it should "negate inside formula derivative" in {
    val s = sequent(Nil, "(!(x!=0))'".asFormula :: Nil, Nil)
    val tactic = NegateEqualsT(AntePosition(0, PosInExpr(0::Nil)))
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sequent(Nil, "(x=0)'".asFormula :: Nil, Nil)
    ))
  }

  "NegateNotEqualsT" should "negate != in succedent" in {
    val s = sucSequent("x!=0".asFormula)
    val tactic = locateSucc(NegateNotEqualsT)
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("!(x=0)".asFormula)
    ))
  }

  it should "negate !(=) in succedent" in {
    val s = sucSequent("!(x=0)".asFormula)
    val tactic = locateSucc(NegateNotEqualsT)
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("x!=0".asFormula)
    ))
  }

  it should "negate != in antecedent" in {
    val s = sequent(Nil, "x!=0".asFormula :: Nil, Nil)
    val tactic = locateAnte(NegateNotEqualsT)
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sequent(Nil, "!(x=0)".asFormula :: Nil, Nil)
    ))
  }

  it should "negate !(=) in antecedent" in {
    val s = sequent(Nil, "!(x=0)".asFormula :: Nil, Nil)
    val tactic = locateAnte(NegateNotEqualsT)
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sequent(Nil, "x!=0".asFormula :: Nil, Nil)
    ))
  }

  it should "negate != inside formulas that contain multiple occurrences" in {
    val s = sucSequent("a=b & (x!=y & y!=z)".asFormula)
    val tactic = NegateNotEqualsT(SuccPosition(0, PosInExpr(1::0::Nil)))
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("a=b & (!(x=y) & y!=z)".asFormula)
    ))
  }

  it should "negate != inside formulas that contain occurrences of its negation" in {
    val s = sucSequent("a=b & (x!=y & !y!=z)".asFormula)
    val tactic = NegateNotEqualsT(SuccPosition(0, PosInExpr(1::0::Nil)))
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("a=b & (!x=y & !y!=z)".asFormula)
    ))
  }

  it should "negate != in the context of boxes" in {
    val s = sucSequent("[x:=2;]x!=y".asFormula)
    val tactic = NegateNotEqualsT(SuccPosition(0, PosInExpr(1::Nil)))
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[x:=2;](!x=y)".asFormula)
    ))
  }

  it should "negate != in the context of boxes of propositional stuff" in {
    val s = sucSequent("[x:=2;](a=b & x!=y)".asFormula)
    val tactic = NegateNotEqualsT(SuccPosition(0, PosInExpr(1::1::Nil)))
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[x:=2;](a=b & (!x=y))".asFormula)
    ))
  }

  it should "negate != in the context of propositional stuff and boxes" in {
    val s = sucSequent("a=b & [x:=2;]x!=y".asFormula)
    val tactic = NegateNotEqualsT(SuccPosition(0, PosInExpr(1::1::Nil)))
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("a=b & [x:=2;](!x=y)".asFormula)
    ))
  }

  it should "negate != in the context of multiple boxes" in {
    val s = sucSequent("[x:=2;][x:=3;]x!=y".asFormula)
    val tactic = NegateNotEqualsT(SuccPosition(0, PosInExpr(1::1::Nil)))
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[x:=2;][x:=3;](!x=y)".asFormula)
    ))
  }

  it should "negate != in the context of propositional stuff and boxes with propositional stuff" in {
    val s = sucSequent("a=b & [x:=2;](a=b & x!=y)".asFormula)
    val tactic = NegateNotEqualsT(SuccPosition(0, PosInExpr(1::1::1::Nil)))
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("a=b & [x:=2;](a=b & (!x=y))".asFormula)
    ))
  }

  "LessEqualSplitT" should "split <= in succedent" in {
    val s = sucSequent("x<=0".asFormula)
    val tactic = locateSucc(LessEqualSplitT)
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("x<0 | x=0".asFormula)
    ))
  }

  it should "unite <|= in succedent" in {
    val s = sucSequent("x<0 | x=0".asFormula)
    val tactic = locateSucc(LessEqualSplitT)
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("x<=0".asFormula)
    ))
  }

  it should "not unite <|= with deviating lhs" in {
    val s = sucSequent("x<0 | y=0".asFormula)
    val tactic = locateSucc(LessEqualSplitT)
    tactic.applicable(new RootNode(s)) shouldBe false
  }

  it should "not unite <|= with deviating rhs" in {
    val s = sucSequent("x<0 | x=1".asFormula)
    val tactic = locateSucc(LessEqualSplitT)
    tactic.applicable(new RootNode(s)) shouldBe false
  }

  it should "split <= in antecedent" in {
    val s = sequent(Nil, "x<=0".asFormula :: Nil, Nil)
    val tactic = locateAnte(LessEqualSplitT)
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sequent(Nil, "x<0 | x=0".asFormula :: Nil, Nil)
    ))
  }

  it should "unite <|= in antecedent" in {
    val s = sequent(Nil, "x<0 | x=0".asFormula :: Nil, Nil)
    val tactic = locateAnte(LessEqualSplitT)
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sequent(Nil, "x<=0".asFormula :: Nil, Nil)
    ))
  }

  "NegateLessThanT" should "negate < in succedent" in {
    val s = sucSequent("x<0".asFormula)
    val tactic = locateSucc(NegateLessThanT)
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("!(x>=0)".asFormula)
    ))
  }

  it should "negate !(>=) in succedent" in {
    val s = sucSequent("!(x>=0)".asFormula)
    val tactic = locateSucc(NegateLessThanT)
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("x<0".asFormula)
    ))
  }

  it should "negate < in antecedent" in {
    val s = sequent(Nil, "x<0".asFormula :: Nil, Nil)
    val tactic = locateAnte(NegateLessThanT)
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sequent(Nil, "!(x>=0)".asFormula :: Nil, Nil)
    ))
  }

  it should "negate !(>=) in antecedent" in {
    val s = sequent(Nil, "!(x>=0)".asFormula :: Nil, Nil)
    val tactic = locateAnte(NegateLessThanT)
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sequent(Nil, "x<0".asFormula :: Nil, Nil)
    ))
  }

  "NegateGreaterEqualsT" should "negate >= in succedent" in {
    val s = sucSequent("x>=0".asFormula)
    val tactic = locateSucc(NegateGreaterEqualsT)
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("!(x<0)".asFormula)
    ))
  }

  it should "negate >= inside formulas" in {
    val s = sucSequent("a=b & x>=0".asFormula)
    val tactic = NegateGreaterEqualsT(SuccPosition(0, PosInExpr(1::Nil)))
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("a=b & !(x<0)".asFormula)
    ))
  }

  it should "negate >= inside implication" in {
    val s = sucSequent("a=b -> x>=0".asFormula)
    val tactic = NegateGreaterEqualsT(SuccPosition(0, PosInExpr(1::Nil)))
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("a=b -> !(x<0)".asFormula)
    ))
  }

  it should "negate >= inside formulas that contain multiple occurrences" in {
    val s = sucSequent("a=b & (x>=y & y>=z)".asFormula)
    val tactic = NegateGreaterEqualsT(SuccPosition(0, PosInExpr(1::0::Nil)))
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("a=b & (!(x<y) & y>=z)".asFormula)
    ))
  }

  it should "negate >= inside formulas that contain occurrences of its negation" in {
    val s = sucSequent("a=b & (x>=y & !y<z)".asFormula)
    val tactic = NegateGreaterEqualsT(SuccPosition(0, PosInExpr(1::0::Nil)))
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("a=b & (!(x<y) & !y<z)".asFormula)
    ))
  }

  it should "negate !(<) in succedent" in {
    val s = sucSequent("!(x<0)".asFormula)
    val tactic = locateSucc(NegateGreaterEqualsT)
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("x>=0".asFormula)
    ))
  }

  it should "negate !(<) inside formulas in succedent" in {
    val s = sucSequent("a=b | !(x<0)".asFormula)
    val tactic = NegateGreaterEqualsT(SuccPosition(0, PosInExpr(1::Nil)))
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sequent(Nil, Nil, "a=b | x>=0".asFormula :: Nil)
    ))
  }

  it should "negate >= in antecedent" in {
    val s = sequent(Nil, "x>=0".asFormula :: Nil, Nil)
    val tactic = locateAnte(NegateGreaterEqualsT)
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sequent(Nil, "!(x<0)".asFormula :: Nil, Nil)
    ))
  }

  it should "negate !(<) in antecedent" in {
    val s = sequent(Nil, "!(x<0)".asFormula :: Nil, Nil)
    val tactic = locateAnte(NegateGreaterEqualsT)
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sequent(Nil, "x>=0".asFormula :: Nil, Nil)
    ))
  }

  it should "negate !(<) inside formulas in antecedent" in {
    val s = sequent(Nil, "a=b -> !(x<0)".asFormula :: Nil, Nil)
    val tactic = NegateGreaterEqualsT(AntePosition(0, PosInExpr(1::Nil)))
    val node = helper.runTactic(tactic, new RootNode(s))
    node.openGoals().flatMap(_.sequent.ante) should contain only "a=b -> x>=0".asFormula
    node.openGoals().flatMap(_.sequent.succ) shouldBe empty
  }

  "GreaterThanFlipT" should "flip > in succedent" in {
    val s = sucSequent("x>0".asFormula)
    val tactic = locateSucc(GreaterThanFlipT)
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("0<x".asFormula)
    ))
  }

  it should "flip < in succedent" in {
    val s = sucSequent("x<0".asFormula)
    val tactic = locateSucc(GreaterThanFlipT)
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("0>x".asFormula)
    ))
  }

  it should "flip > in antecedent" in {
    val s = sequent(Nil, "x>0".asFormula::Nil, Nil)
    val tactic = locateAnte(GreaterThanFlipT)
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sequent(Nil, "0<x".asFormula::Nil, Nil)
    ))
  }

  it should "flip < in antecedent" in {
    val s = sequent(Nil, "x<0".asFormula::Nil, Nil)
    val tactic = locateAnte(GreaterThanFlipT)
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sequent(Nil, "0>x".asFormula::Nil, Nil)
    ))
  }

  "GreaterEqualsFlipT" should "flip >= in succedent" in {
    val s = sucSequent("x>=0".asFormula)
    val tactic = locateSucc(GreaterEqualFlipT)
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("0<=x".asFormula)
    ))
  }

  it should "flip <= in succedent" in {
    val s = sucSequent("x<=0".asFormula)
    val tactic = locateSucc(GreaterEqualFlipT)
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("0>=x".asFormula)
    ))
  }

  it should "flip >= in antecedent" in {
    val s = sequent(Nil, "x>=0".asFormula::Nil, Nil)
    val tactic = locateAnte(GreaterEqualFlipT)
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sequent(Nil, "0<=x".asFormula::Nil, Nil)
    ))
  }

  it should "flip <= in antecedent" in {
    val s = sequent(Nil, "x<=0".asFormula::Nil, Nil)
    val tactic = locateAnte(GreaterEqualFlipT)
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sequent(Nil, "0>=x".asFormula::Nil, Nil)
    ))
  }

  "NegateGreaterThanT" should "negate > in succedent" in {
    val s = sucSequent("x>0".asFormula)
    val tactic = locateSucc(NegateGreaterThanT)
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("!(x<=0)".asFormula)
    ))
  }

  it should "negate > inside formula" in {
    val s = sucSequent("a=b & x>0".asFormula)
    val tactic = NegateGreaterThanT(SuccPosition(0, PosInExpr(1::Nil)))
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("a=b & !(x<=0)".asFormula)
    ))
  }

  it should "negate !(<=) in succedent" in {
    val s = sucSequent("!(x<=0)".asFormula)
    val tactic = locateSucc(NegateGreaterThanT)
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("x>0".asFormula)
    ))
  }

  it should "negate > in antecedent" in {
    val s = sequent(Nil, "x>0".asFormula :: Nil, Nil)
    val tactic = locateAnte(NegateGreaterThanT)
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sequent(Nil, "!(x<=0)".asFormula :: Nil, Nil)
    ))
  }

  it should "negate !(<=) in antecedent" in {
    val s = sequent(Nil, "!(x<=0)".asFormula :: Nil, Nil)
    val tactic = locateAnte(NegateGreaterThanT)
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sequent(Nil, "x>0".asFormula :: Nil, Nil)
    ))
  }

  "NegateLessEqualsT" should "negate <= in succedent" in {
    val s = sucSequent("x<=0".asFormula)
    val tactic = locateSucc(NegateLessEqualsT)
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("!(x>0)".asFormula)
    ))
  }

  it should "negate <= inside formula" in {
    val s = sucSequent("a=b & x<=0".asFormula)
    val tactic = NegateLessEqualsT(SuccPosition(0, PosInExpr(1::Nil)))
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("a=b & !(x>0)".asFormula)
    ))
  }

  it should "negate !(>) in succedent" in {
    val s = sucSequent("!(x>0)".asFormula)
    val tactic = locateSucc(NegateLessEqualsT)
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("x<=0".asFormula)
    ))
  }

  it should "negate <= in antecedent" in {
    val s = sequent(Nil, "x<=0".asFormula :: Nil, Nil)
    val tactic = locateAnte(NegateLessEqualsT)
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sequent(Nil, "!(x>0)".asFormula :: Nil, Nil)
    ))
  }

  "Quantifier elimination" should "prove x<0 -> x<=0" in {
    val s = sequent(Nil, "x<0".asFormula :: Nil, "x<=0".asFormula :: Nil)
    val tactic = PropositionalTacticsImpl.ConsolidateSequentT & FOQuantifierTacticsImpl.universalClosureT(SuccPosition(0)) &
      TacticLibrary.debugT("Foo") &
      quantifierEliminationT("Mathematica")
    helper.runTactic(tactic, new RootNode(s)) shouldBe 'closed
  }

  "Abs axiom tactic" should "expand abs(x) = y in succedent" in {
    val s = sucSequent("abs(x) = y".asFormula)
    val tactic = ArithmeticTacticsImpl.AbsAxiomT(SuccPosition(0))
    val result = helper.runTactic(tactic, new RootNode(s))

    result.openGoals() should have size 1
    result.openGoals().head.sequent.ante shouldBe empty
    result.openGoals().head.sequent.succ should contain only "(x>=0 & y=x) | (x<=0 & y=-x)".asFormula
  }

  it should "expand abs(x) = y in antecedent" in {
    val s = sequent(Nil, immutable.IndexedSeq("abs(x) = y".asFormula), immutable.IndexedSeq())
    val tactic = ArithmeticTacticsImpl.AbsAxiomT(AntePosition(0))
    val result = helper.runTactic(tactic, new RootNode(s))

    result.openGoals() should have size 1
    result.openGoals().head.sequent.ante should contain only "(x>=0 & y=x) | (x<=0 & y=-x)".asFormula
    result.openGoals().head.sequent.succ shouldBe empty
  }

  "Abs tactic" should "expand abs(x) in succedent" in {
    val s = sucSequent("abs(x) >= 5".asFormula)
    val tactic = ArithmeticTacticsImpl.AbsT(SuccPosition(0, PosInExpr(0 :: Nil)))
    val result = helper.runTactic(tactic, new RootNode(s))

    result.openGoals() should have size 1
    result.openGoals().head.sequent.ante should contain only "x>=0&abs_0=x | x<=0&abs_0=-x".asFormula
    result.openGoals().head.sequent.succ should contain only "abs_0>=5".asFormula
  }

  it should "expand abs(x) in antecedent" in {
    val s = sequent(Nil, immutable.IndexedSeq("abs(x) >= 5".asFormula), immutable.IndexedSeq())
    val tactic = ArithmeticTacticsImpl.AbsT(AntePosition(0, PosInExpr(0 :: Nil)))
    val result = helper.runTactic(tactic, new RootNode(s))

    result.openGoals() should have size 1
    result.openGoals().head.sequent.ante should contain only ("x>=0&abs_0=x | x<=0&abs_0=-x".asFormula, "abs_0>=5".asFormula)
    result.openGoals().head.sequent.succ shouldBe empty
  }

  it should "be able to prove x>2 -> abs(x) > 2" in {
    val s = sucSequent("x>2 -> abs(x) > 2".asFormula)
    val tactic = TactixLibrary.implyR(SuccPosition(0)) &
      ArithmeticTacticsImpl.AbsT(SuccPosition(0, PosInExpr(0 :: Nil))) &
      TactixLibrary.orL(AntePosition(1)) & TactixLibrary.andL(AntePosition(1)) & TactixLibrary.QE

    helper.runTactic(tactic, new RootNode(s)) shouldBe 'closed
  }

  "Min axiom tactic" should "expand min(x,y) = z in succedent" in {
    val s = sucSequent("min(x,y) = z".asFormula)
    val tactic = ArithmeticTacticsImpl.MinMaxAxiomT(SuccPosition(0))
    val result = helper.runTactic(tactic, new RootNode(s))

    result.openGoals() should have size 1
    result.openGoals().head.sequent.ante shouldBe empty
    result.openGoals().head.sequent.succ should contain only "(x<=y & z=x) | (x>=y & z=y)".asFormula
  }

  "Min tactic" should "expand min(x,y) in succedent" in {
    val s = sucSequent("min(x,y) >= 5".asFormula)
    val tactic = ArithmeticTacticsImpl.MinMaxT(SuccPosition(0, PosInExpr(0 :: Nil)))
    val result = helper.runTactic(tactic, new RootNode(s))

    result.openGoals() should have size 1
    result.openGoals().head.sequent.ante should contain only "x<=y&min_0=x | x>=y&min_0=y".asFormula
    result.openGoals().head.sequent.succ should contain only "min_0>=5".asFormula
  }

  it should "expand min(x,y) in antecedent" in {
    val s = sequent(Nil, immutable.IndexedSeq("min(x,y) >= 5".asFormula), immutable.IndexedSeq())
    val tactic = ArithmeticTacticsImpl.MinMaxT(AntePosition(0, PosInExpr(0 :: Nil)))
    val result = helper.runTactic(tactic, new RootNode(s))

    result.openGoals() should have size 1
    result.openGoals().head.sequent.ante should contain only ("x<=y&min_0=x | x>=y&min_0=y".asFormula, "min_0>=5".asFormula)
    result.openGoals().head.sequent.succ shouldBe empty
  }

  "Max axiom tactic" should "expand max(x,y) = z in succedent" in {
    val s = sucSequent("max(x,y) = z".asFormula)
    val tactic = ArithmeticTacticsImpl.MinMaxAxiomT(SuccPosition(0))
    val result = helper.runTactic(tactic, new RootNode(s))

    result.openGoals() should have size 1
    result.openGoals().head.sequent.ante shouldBe empty
    result.openGoals().head.sequent.succ should contain only "(x>=y & z=x) | (x<=y & z=y)".asFormula
  }

  "Max tactic" should "expand max(x,y) in succedent" in {
    val s = sucSequent("max(x,y) >= 5".asFormula)
    val tactic = ArithmeticTacticsImpl.MinMaxT(SuccPosition(0, PosInExpr(0 :: Nil)))
    val result = helper.runTactic(tactic, new RootNode(s))

    result.openGoals() should have size 1
    result.openGoals().head.sequent.ante should contain only "x>=y&max_0=x | x<=y&max_0=y".asFormula
    result.openGoals().head.sequent.succ should contain only "max_0>=5".asFormula
  }

  it should "expand max(x,y) in antecedent" in {
    val s = sequent(Nil, immutable.IndexedSeq("max(x,y) >= 5".asFormula), immutable.IndexedSeq())
    val tactic = ArithmeticTacticsImpl.MinMaxT(AntePosition(0, PosInExpr(0 :: Nil)))
    val result = helper.runTactic(tactic, new RootNode(s))

    result.openGoals() should have size 1
    result.openGoals().head.sequent.ante should contain only ("x>=y&max_0=x | x<=y&max_0=y".asFormula, "max_0>=5".asFormula)
    result.openGoals().head.sequent.succ shouldBe empty
  }

}
