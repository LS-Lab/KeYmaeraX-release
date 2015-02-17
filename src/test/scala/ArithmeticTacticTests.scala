import edu.cmu.cs.ls.keymaera.core.{RootNode, ToolBase}
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary._
import edu.cmu.cs.ls.keymaera.tactics.Tactics
import edu.cmu.cs.ls.keymaera.tests.ProvabilityTestHelper
import org.scalatest.{BeforeAndAfterEach, Matchers, FlatSpec}
import testHelper.SequentFactory._
import testHelper.StringConverter._
import edu.cmu.cs.ls.keymaera.tactics.ArithmeticTacticsImpl._

/**
 * Created by smitsch on 2/14/15.
 * @author Stefan Mitsch
 */
class ArithmeticTacticTests extends FlatSpec with Matchers with BeforeAndAfterEach {
  val helper = new ProvabilityTestHelper((x) => println(x))

  override def beforeEach() = {
    Tactics.KeYmaeraScheduler.init(Map())
  }

  override def afterEach() = {
    Tactics.KeYmaeraScheduler.shutdown()
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

  it should "negate !(<) in succedent" in {
    val s = sucSequent("!(x<0)".asFormula)
    val tactic = locateSucc(NegateGreaterEqualsT)
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("x>=0".asFormula)
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

  "NegateGreaterThanT" should "negate > in succedent" in {
    val s = sucSequent("x>0".asFormula)
    val tactic = locateSucc(NegateGreaterThanT)
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("!(x<=0)".asFormula)
    ))
  }

  /* TODO not implemented yet */
  ignore should "negate !(<=) in succedent" in {
    val s = sucSequent("!(x<=0)".asFormula)
    val tactic = locateSucc(NegateGreaterThanT)
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("x>0".asFormula)
    ))
  }

  /* TODO not implemented yet */
  ignore should "negate > in antecedent" in {
    val s = sequent(Nil, "x>0".asFormula :: Nil, Nil)
    val tactic = locateAnte(NegateGreaterThanT)
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sequent(Nil, "!(x<=0)".asFormula :: Nil, Nil)
    ))
  }

  /* TODO not implemented yet */
  ignore should "negate !(<=) in antecedent" in {
    val s = sequent(Nil, "!(x<=0)".asFormula :: Nil, Nil)
    val tactic = locateAnte(NegateGreaterThanT)
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sequent(Nil, "x>0".asFormula :: Nil, Nil)
    ))
  }
}
