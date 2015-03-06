import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary._
import edu.cmu.cs.ls.keymaera.tactics.{Interpreter, Config, BranchLabels, Tactics}
import edu.cmu.cs.ls.keymaera.tests.ProvabilityTestHelper
import org.scalatest.{BeforeAndAfterEach, Matchers, FlatSpec}
import testHelper.SequentFactory._
import testHelper.StringConverter._
import edu.cmu.cs.ls.keymaera.tactics.ArithmeticTacticsImpl._

import scala.collection.immutable.Map

/**
 * Created by smitsch on 2/14/15.
 * @author Stefan Mitsch
 */
class ArithmeticTacticTests extends FlatSpec with Matchers with BeforeAndAfterEach {
  val helper = new ProvabilityTestHelper((x) => println(x))

  override def beforeEach() = {
    Tactics.KeYmaeraScheduler = new Interpreter(KeYmaera)
    Tactics.KeYmaeraScheduler.init(Map())
  }

  override def afterEach() = {
    Tactics.KeYmaeraScheduler.shutdown()
    Tactics.KeYmaeraScheduler = null
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
}
