import edu.cmu.cs.ls.keymaera.core.ExpressionTraversal.{StopTraversal, ExpressionTraversalFunction, TraverseToPosition}
import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary._
import edu.cmu.cs.ls.keymaera.tactics._
import edu.cmu.cs.ls.keymaera.tactics.Tactics.{ConstructionTactic, ApplyRule, Tactic, PositionTactic}
import edu.cmu.cs.ls.keymaera.tests.ProvabilityTestHelper
import testHelper.StringConverter._
import testHelper.SequentFactory._
import org.scalatest.{BeforeAndAfterEach, Matchers, FlatSpec}

/**
* Created by smitsch on 1/13/15.
* @author Stefan Mitsch
* @author Ran Ji
*/
class AlphaConversionTests extends FlatSpec with Matchers with BeforeAndAfterEach {
  val helper = new ProvabilityTestHelper((x) => println(x))

  def alpha(from: String, to: String): PositionTactic = TacticLibrary.alphaRenamingT(from, None, to, None)
  def globalAlpha(from: String, to: String) = TacticLibrary.globalAlphaRenamingT(from, None, to, None)

  def alphaRule(from: String, to: String): PositionTactic = new PositionTactic("Alpha Renaming") {

    import scala.language.postfixOps

    override def applies(s: Sequent, p: Position): Boolean = /*s(p) match*/ {
      var applicable = false
      ExpressionTraversal.traverse(TraverseToPosition(p.inExpr, new ExpressionTraversalFunction {
        override def preF(pos: PosInExpr, f: Formula): Either[Option[StopTraversal], Formula] = {
          f match {
            case Forall(vars, _) => applicable = vars.exists(v => v.name == from && v.index == None)
            case Exists(vars, _) => applicable = vars.exists(v => v.name == from && v.index == None)
            case _ => applicable = false
          }
          Left(Some(ExpressionTraversal.stop))
        }
      }), s(p))
      applicable
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        Some(new ApplyRule(new AlphaConversion(from, None, to, None, Some(p))) {
          override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
        } & hideT(p.topLevel))
      }
    }
  }

  def globalAlphaRule(from: String, to: String): Tactic = new ConstructionTactic("Alpha Renaming") {
    import scala.language.postfixOps
    override def applicable(node: ProofNode): Boolean = true
    override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
      Some(new ApplyRule(new AlphaConversion(from, None, to, None, None)) {
        override def applicable(node: ProofNode): Boolean = true
      })
    }
  }

  override def beforeEach() = {
    Tactics.KeYmaeraScheduler = new Interpreter(KeYmaera)
    Tactics.KeYmaeraScheduler.init(Map())
  }

  override def afterEach() = {
    Tactics.KeYmaeraScheduler.shutdown()
    Tactics.KeYmaeraScheduler = null
  }

  /**
   * ==================================================
   * test cases for \alpha-conversion rule
   */

  "Alpha-conversion rule" should "rename free variables" in {
    val s = sucSequent("x>0".asFormula)
    val tactic = globalAlphaRule("x", "t")
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[t:=x;]t>0".asFormula)
    ))
  }

  // (1) Forall(v, phi)

  "Alpha-conversion rule on universal quantifier" should "be forall t. t>0 with (x,t) on forall x. x>0" in {
    val s = sucSequent("\\forall x. x>0".asFormula)
    helper.runTactic(locateSucc(alphaRule("x", "t")), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("\\forall t. t>0".asFormula)
    ))
    helper.runTactic(globalAlphaRule("x", "t"), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[t:=x;]\\forall t. t>0".asFormula)
    ))
  }

  it should "be forall t. [t:=t+1;]t>0 with (x,t) on forall x. [x:=x+1;]x>0" in {
    val s = sucSequent("\\forall x. [x:=x+1;]x>0".asFormula)
    helper.runTactic(locateSucc(alphaRule("x", "t")), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("\\forall t. [t:=t+1;]t>0".asFormula)
    ))
    helper.runTactic(globalAlphaRule("x", "t"), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[t:=x;]\\forall t. [t:=t+1;]t>0".asFormula)
    ))
  }

  it should "be y=5 <-> forall t. [t:=t+1;]t>0 with (x,t) on y=5 <-> forall x. [x:=x+1;]x>0" in {
    val s = sucSequent("y=5 <-> \\forall x. [x:=x+1;]x>0".asFormula)
    helper.runTactic(alphaRule("x", "t")(SuccPosition(0, PosInExpr(1::Nil))), new RootNode(s)).openGoals().
      foreach(_.sequent should be (sucSequent("y=5 <-> \\forall t. [t:=t+1;]t>0".asFormula)
    ))
    alphaRule("y", "t")(SuccPosition(0, PosInExpr(1::Nil))).applicable(new RootNode(s)) shouldBe false
    helper.runTactic(globalAlphaRule("x", "t"), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[t:=x;](y=5 <-> \\forall t. [t:=t+1;]t>0)".asFormula)
    ))
  }

  it should "be forall x. [t:=x+1;]x>0 with (y,t) on forall x. [y:=x+1;]x>0" in {
    val s = sucSequent("\\forall x. [y:=x+1;]x>0".asFormula)
    locateSucc(alphaRule("y", "t")).applicable(new RootNode(s)) shouldBe false
    helper.runTactic(globalAlphaRule("y", "t"), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[t:=y;]\\forall x. [t:=x+1;]x>0".asFormula)))
  }

  it should "be forall t. [y:=t+1;]t>0 with (x,t) on forall x. [y:=x+1;]x>0" in {
    val s = sucSequent("\\forall x. [y:=x+1;]x>0".asFormula)
    helper.runTactic(locateSucc(alphaRule("x", "t")), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("\\forall t. [y:=t+1;]t>0".asFormula)
    ))
    helper.runTactic(globalAlphaRule("x", "t"), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[t:=x;]\\forall t. [y:=t+1;]t>0".asFormula)
    ))
  }

  it should "be forall t. [t:=t+1;][y:=t+1;]t>0 with (x,t) on forall x. [x:=x+1;][y:=x+1;]x>0" in {
    val s = sucSequent("\\forall x. [x:=x+1;][y:=x+1;]x>0".asFormula)
    helper.runTactic(locateSucc(alphaRule("x", "t")), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("\\forall t. [t:=t+1;][y:=t+1;]t>0".asFormula)
    ))
    helper.runTactic(globalAlphaRule("x", "t"), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[t:=x;]\\forall t. [t:=t+1;][y:=t+1;]t>0".asFormula)
    ))
  }

  it should "be forall t. [y'=t+1;]t>0 with (x,t) on forall x. [y'=x+1;]x>0" in {
    val s = sucSequent("\\forall x. [y'=x+1;]x>0".asFormula)
    helper.runTactic(locateSucc(alphaRule("x", "t")), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("\\forall t. [y'=t+1;]t>0".asFormula)
    ))
    helper.runTactic(globalAlphaRule("x", "t"), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[t:=x;]\\forall t. [y'=t+1;]t>0".asFormula)
    ))
  }

  it should "be forall t. [t'=t+1;]t>0 with (x,t) on forall x. [x'=x+1;]x>0" in {
    val s = sucSequent("\\forall x. [x'=x+1;]x>0".asFormula)
    helper.runTactic(locateSucc(alphaRule("x", "t")), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("\\forall t. [t'=t+1;]t>0".asFormula)
    ))
    helper.runTactic(globalAlphaRule("x", "t"), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[t:=x;]\\forall t. [t'=t+1;]t>0".asFormula)
    ))
  }

  // (2) Exists(v, phi)

  "Alpha-conversion rule on existential quantifier" should "be exists t. t>0 with (x,t) on exists x. x>0" in {
    val s = sucSequent("\\exists x. x>0".asFormula)
    helper.runTactic(locateSucc(alphaRule("x", "t")), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("\\exists t. t>0".asFormula)
    ))
    helper.runTactic(globalAlphaRule("x", "t"), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[t:=x;]\\exists t. t>0".asFormula)
    ))
  }

  it should "be exists t. [t:=t+1;]t>0 with (x,t) on exists x. [x:=x+1;]x>0" in {
    val s = sucSequent("\\exists x. [x:=x+1;]x>0".asFormula)
    helper.runTactic(locateSucc(alphaRule("x", "t")), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("\\exists t. [t:=t+1;]t>0".asFormula)
    ))
    helper.runTactic(globalAlphaRule("x", "t"), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[t:=x;]\\exists t. [t:=t+1;]t>0".asFormula)
    ))
  }

  it should "be exists t. [t:=t+1;][y:=t+1;]t>0 with (x,t) on exists x. [x:=x+1;][y:=x+1;]x>0" in {
    val s = sucSequent("\\exists x. [x:=x+1;][y:=x+1;]x>0".asFormula)
    helper.runTactic(locateSucc(alphaRule("x", "t")), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("\\exists t. [t:=t+1;][y:=t+1;]t>0".asFormula)
    ))
    helper.runTactic(globalAlphaRule("x", "t"), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[t:=x;]\\exists t. [t:=t+1;][y:=t+1;]t>0".asFormula)
    ))
  }

  // (3) Modality(BoxModality(Assign(x, e)), phi)

  "Alpha-conversion on assignment" should "be [t:=t+1;]t>0 with (x,t) on [x:=x+1;]x>0" in {
    val s = sucSequent("[x:=x+1;]x>0".asFormula)
    helper.runTactic(globalAlphaRule("x", "t"), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[t:=x;][t:=t+1;]t>0".asFormula)
    ))
  }

  it should "be [y:=t+1;]x>0 with (x,t) on [y:=x+1;]x>0" in {
    val s = sucSequent("[y:=x+1;]x>0".asFormula)
    helper.runTactic(globalAlphaRule("x", "t"), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[t:=x;][y:=t+1;]t>0".asFormula)
    ))
  }

  it should "be [t:=x+1;][y:=t+1;]t>0 with (x,t) on [x:=x+1;][y:=x+1;]x>0" in {
    val s = sucSequent("[x:=x+1;][y:=x+1;]x>0".asFormula)
    helper.runTactic(globalAlphaRule("x", "t"), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[t:=x;][t:=t+1;][y:=t+1;]t>0".asFormula)
    ))
  }

  it should "be [t:=x+1;][x:=t+1;]x>0 with (x,t) on [x:=x+1;][x:=x+1;]x>0" in {
    val s = sucSequent("[x:=x+1;][x:=x+1;]x>0".asFormula)
    helper.runTactic(globalAlphaRule("x", "t"), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[t:=x;][t:=t+1;][t:=t+1;]t>0".asFormula)
    ))
  }

  "Alpha conversion rule on nondeterministic choice" should "be [{t:=1 ++ t:=x+1};][{x:=1 ++ x:=t+1};]x>0 with (x,t) on [{x:=1 ++ x:=x+1};{x:=1 ++ x:=x+1};]x>0" in {
    val s = sucSequent("[{x:=1 ++ x:=x+1};][{x:=1 ++ x:=x+1};]x>0".asFormula)
    helper.runTactic(globalAlphaRule("x", "t"), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[t:=x;][{t:=1 ++ t:=t+1}][{t:=1 ++ t:=t+1};]t>0".asFormula)
    ))
  }

  it should "be [t:=1 ++ t:=x+1 ++ z:=x;]t>0 with (x,t) on [x:=1 ++ x:=x+1 ++ z:=x;]x>0" in {
    val s = sucSequent("[x:=1 ++ x:=x+1 ++ z:=x;]x>0".asFormula)
    helper.runTactic(globalAlphaRule("x", "t"), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[t:=x;][t:=1 ++ t:=t+1 ++ z:=t;]t>0".asFormula)
    ))
  }

  it should "be [t:=1 ++ t:=x+1;]t>0 with (x,t) on [x:=1 ++ x:=x+1;]x>0" in {
    val s = sucSequent("[x:=1 ++ x:=x+1;]x>0".asFormula)
    helper.runTactic(globalAlphaRule("x", "t"), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[t:=x;][t:=1 ++ t:=t+1;]t>0".asFormula)
    ))
  }

  it should "be [t:=1 ++ {t:=2;t:=3;};]t>0 with (x,t) on [x:=1 ++ {x:=2;x:=3;};]x>0" in {
    val s = sucSequent("[x:=1 ++ {x:=2;x:=3;};]x>0".asFormula)
    helper.runTactic(globalAlphaRule("x", "t"), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[t:=x;][t:=1 ++ {t:=2;t:=3;};]t>0".asFormula)))
  }

  // (4) Modality(DiamondModality(Assign(x, e)), phi)

  "Alpha-conversion rule on diamond assignment" should "be <t:=x+1;>t>0 with (x,t) on <x:=x+1;>x>0" in {
    val s = sucSequent("<x:=x+1;>x>0".asFormula)
    helper.runTactic(globalAlphaRule("x", "t"), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[t:=x;]<t:=t+1;>t>0".asFormula)
    ))
  }

  it should "be <y:=x+1;>x>0 with (x,t) on <y:=x+1;>x>0" in {
    val s = sucSequent("<y:=x+1;>x>0".asFormula)
    helper.runTactic(globalAlphaRule("x", "t"), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[t:=x;]<y:=t+1;>t>0".asFormula)
    ))
  }

  it should "be <t:=x+1;><y:=x+1;>x>0 with (x,t) on <x:=x+1;><y:=x+1;>x>0" in {
    val s = sucSequent("<x:=x+1;><y:=x+1;>x>0".asFormula)
    helper.runTactic(globalAlphaRule("x", "t"), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[t:=x;]<t:=t+1;><y:=t+1;>t>0".asFormula)
    ))
  }

  it should "be <t:=x+1;><x:=x+1;>x>0 with (x,t) on <x:=x+1;><x:=x+1;>x>0" in {
    val s = sucSequent("<x:=x+1;><x:=x+1;>x>0".asFormula)
    helper.runTactic(globalAlphaRule("x", "t"), new RootNode(s)).openGoals().foreach(_.sequent should be(
      sucSequent("[t:=x;]<t:=t+1;><t:=t+1;>t>0".asFormula)
    ))
  }

  it should "throw an IllegalArgumentException with (x,t) on <x:=x+1;><x:=t+1;>x>0" in {
    val s = sucSequent("<x:=x+1;><x:=t+1;>x>0".asFormula)
//    an [IllegalArgumentException] should be thrownBy helper.runTactic(tactic, new RootNode(s))
    helper.runTactic(globalAlphaRule("x", "t"), new RootNode(s)).openGoals().foreach(_.sequent should be (s))
  }

  // (5) Modality(BoxModality(NDetAssign(x)), phi)


  // (6) Modality(DiamondModality(Choice(a,b), phi)

  // should work with new alpha conversion rule
  "Alpha-conversion rule on diamond nondeterministic choice" should "be <t:=1 ++ t:=x+1;>t>0 with (x,t) on <x:=1 ++ x:=x+1;>x>0" in {
    val s = sucSequent("<x:=1 ++ x:=x+1;>x>0".asFormula)
    helper.runTactic(globalAlphaRule("x", "t"), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[t:=x;]<t:=1 ++ t:=t+1;>t>0".asFormula)
    ))
  }

  it should "be <{t:=1 ++ t:=x+1};><{x:=1 ++ x:=t+1};>x>0 with (x,t) on <{x:=1 ++ x:=x+1};{x:=1 ++ x:=x+1};>x>0" in {
    val s = sucSequent("<{x:=1 ++ x:=x+1};><{x:=1 ++ x:=x+1};>x>0".asFormula)
    helper.runTactic(globalAlphaRule("x", "t"), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[t:=x;]<{t:=1 ++ t:=t+1};><{t:=1 ++ t:=t+1};>t>0".asFormula)
    ))
  }

  it should "be <t:=x;><{x:=1 ++ x:=t+1}*;>x>0 with (x,t) on <{x:=1 ++ x:=x+1}*;>x>0" in {
    val s = sucSequent("<{x:=1 ++ x:=x+1}*;>x>0".asFormula)
    helper.runTactic(globalAlphaRule("x", "t"), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[t:=x;]<{t:=1 ++ t:=t+1}*;>t>0".asFormula)
    ))
  }

  it should "be <t:=1 ++ t:=x+1 ++ z:=x;>t>0 with (x,t) on <x:=1 ++ x:=x+1 ++ z:=x;>x>0" in {
    val s = sucSequent("<x:=1 ++ x:=x+1 ++ z:=x;>x>0".asFormula)
    helper.runTactic(globalAlphaRule("x", "t"), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[t:=x;]<t:=1 ++ t:=t+1 ++ z:=t;>t>0".asFormula)))
  }

  // (7) Modality(BoxModality(DifferentialProgram | IncompleteSystem, _), phi)

  "Alpha-conversion rule on ODEs" should "be [y:=1;][t:=x;][t'=1;]x>0 with (x,t) on [y:=1;][x'=1;]x>0" in {
    val s = sucSequent("[y:=1;][x'=1;]x>0".asFormula)
    helper.runTactic(globalAlphaRule("x", "t"), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[t:=x;][y:=1;][t'=1;]t>0".asFormula)
    ))
  }

  it should "rename in ODEs and store initial value" in {
    val s = sucSequent("[y'=1;]true".asFormula)
    helper.runTactic(globalAlphaRule("y", "x"), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[x:=y;][x'=1;]true".asFormula)))
  }

  ignore should "rename and store not only at top level" in {
    val s = sucSequent("[x:=x+1;][x'=1;]x>0".asFormula)
    val tactic = alphaRule("x", "t")(new SuccPosition(0, new PosInExpr(1 :: Nil)))
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[x:=x+1;][t:=x;][t'=1;]t>0".asFormula)
    ))
  }

  it should "also store initial value if variable to rename does not occur in ODE" in {
    val s = sucSequent("[y'=1;]true".asFormula)
    helper.runTactic(globalAlphaRule("x", "t"), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[t:=x;][y'=1;]true".asFormula)
    ))
  }

  it should "not store initial value if variable to rename is bound outside and does not occur in ODE" in {
    val s = sucSequent("\\forall x. [y'=1;]true".asFormula)
    helper.runTactic(locateSucc(alphaRule("x", "t")), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("\\forall t. [y'=1;]true".asFormula)))
    helper.runTactic(globalAlphaRule("x", "t"), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[t:=x;]\\forall t. [y'=1;]true".asFormula)))
  }

  it should "not store initial value if variable to rename is constant in ODE" in {
    val s = sucSequent("\\forall x. [y'=x+1;]true".asFormula)
    helper.runTactic(locateSucc(alphaRule("x", "t")), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("\\forall t. [y'=t+1;]true".asFormula)
    ))
    helper.runTactic(globalAlphaRule("x", "t"), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[t:=x;]\\forall t. [y'=t+1;]true".asFormula)
    ))
  }

  it should "be [y:=z;][y'=y+1;]y>0 with (z,y) on [z'=z+1;]z>0" in {
    val s = sucSequent("[z'=z+1;]z>0".asFormula)
    helper.runTactic(globalAlphaRule("z", "y"), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[y:=z;][y'=y+1;]y>0".asFormula)
    ))
  }

  it should "be [t:=x;][t'=1;]t>0 with (x,t) on [x'=1;]x>0" in {
    val s = sucSequent("[x'=1;]x>0".asFormula)
    helper.runTactic(globalAlphaRule("x", "t"), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[t:=x;][t'=1;]t>0".asFormula)
    ))
  }

  it should "be [t:=x;][t'=t+1;]t>0 with (x,t) on [x'=x+1;]x>0" in {
    val s = sucSequent("[x'=x+1;]x>0".asFormula)
    helper.runTactic(globalAlphaRule("x", "t"), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[t:=x;][t'=t+1;]t>0".asFormula)
    ))
  }

  it should "be [t:=x;][$$t'=t+1$$;]t>0 with (x,t) on [$$x'=x+1$$;]x>0" in {
    val s = sucSequent("[$$x'=x+1$$;]x>0".asFormula)
    helper.runTactic(globalAlphaRule("x", "t"), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[t:=x;][$$t'=t+1$$;]t>0".asFormula)
    ))
  }

  it should "be [t:=x;][$$t'=t+1,y'=t$$;]t>0 with (x,t) on [$$x'=x+1, y'=x$$;]x>0" in {
    val s = sucSequent("[$$x'=x+1,y'=x$$;]x>0".asFormula)
    helper.runTactic(globalAlphaRule("x", "t"), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[t:=x;][$$t'=t+1,y'=t$$;]t>0".asFormula)
    ))
  }

  it should "be [t:=x;][$$t'=t+1 & t>0,y'=t & y<t$$;]t>0 with (x,t) on [$$x'=x+1 & x>0, y'=x & y<x$$;]x>0" in {
    val s = sucSequent("[$$x'=x+1, y'=x $$ & x>0 & y<x;]x>0".asFormula)
    helper.runTactic(globalAlphaRule("x", "t"), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[t:=x;][$$t'=t+1 ,y'=t$$ & t>0 & y<t;]t>0".asFormula)
    ))
  }

  // (8) Modality(DiamondModality(DifferentialProgram | IncompleteSystem, _), phi)

  "Alpha-conversion rule on diamond ODE" should "be <t:=x;><t'=1;>t>0 with (x,t) on <x'=1;>x>0" in {
    val s = sucSequent("<x'=1;>x>0".asFormula)
    helper.runTactic(globalAlphaRule("x", "t"), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[t:=x;]<t'=1;>t>0".asFormula)
    ))
  }

  it should "be <t:=x;><t'=t+1;>t>0 with (x,t) on <x'=x+1;>x>0" in {
    val s = sucSequent("<x'=x+1;>x>0".asFormula)
    helper.runTactic(globalAlphaRule("x", "t"), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[t:=x;]<t'=t+1;>t>0".asFormula)
    ))
  }

  it should "be <t:=x;><$$t'=t+1$$;>t>0 with (x,t) on <$$x'=x+1$$;>x>0" in {
    val s = sucSequent("<$$x'=x+1$$;>x>0".asFormula)
    helper.runTactic(globalAlphaRule("x", "t"), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[t:=x;]<$$t'=t+1$$;>t>0".asFormula)
    ))
  }

  it should "be <t:=x;><$$t'=t+1,y'=t$$;>t>0 with (x,t) on <$$x'=x+1, y'=x$$;>x>0" in {
    val s = sucSequent("<$$x'=x+1,y'=x$$;>x>0".asFormula)
    helper.runTactic(globalAlphaRule("x", "t"), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[t:=x;]<$$t'=t+1,y'=t$$;>t>0".asFormula)
    ))
  }

  it should "be <t:=x;><$$t'=t+1 & t>0,y'=t & y<t$$;>t>0 with (x,t) on <$$x'=x+1 & x>0, y'=x & y<x$$;>x>0" in {
    val s = sucSequent("<$$x'=x+1, y'=x$$ & x>0 & y<x;>x>0".asFormula)
    helper.runTactic(globalAlphaRule("x", "t"), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[t:=x;]<$$t'=t+1,y'=t$$ & t>0 & y<t;>t>0".asFormula)
    ))
  }

  "Alpha-conversion rule on loops" should "be [t:=x;][{x:=1;}*;]x>0 with (x,t) on [{x:=1;}*;]x>0" in {
    val s = sucSequent("[{x:=1;}*;]x>0".asFormula)
    helper.runTactic(globalAlphaRule("x", "t"), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[t:=x;][{t:=1;}*;]t>0".asFormula)
    ))
  }

  it should "be [t:=x;][{x:=t+1;}*;]x>0 with (x,t) on [{x:=x+1;}*;]x>0" in {
    val s = sucSequent("[{x:=x+1;}*;]x>0".asFormula)
    helper.runTactic(globalAlphaRule("x", "t"), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[t:=x;][{t:=t+1;}*;]t>0".asFormula)
    ))
  }

  it should "be [{y:=t+1;}*;]t>0 with (x,t) on [{y:=x+1;}*;]x>0" in {
    val s = sucSequent("[{y:=x+1;}*;]x>0".asFormula)
    helper.runTactic(globalAlphaRule("x", "t"), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[t:=x;][{y:=t+1;}*;]t>0".asFormula)
    ))
  }

  it should "be [t:=x;][{x:=1 ++ x:=t+1}*;]x>0 with (x,t) on [{x:=1 ++ x:=x+1}*;]x>0" in {
    val s = sucSequent("[{x:=1 ++ x:=x+1}*;]x>0".asFormula)
    helper.runTactic(globalAlphaRule("x", "t"), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[t:=x;][{t:=1 ++ t:=t+1}*;]t>0".asFormula)
    ))
  }

  it should "not store initial value if variable to rename does not occur in loop" in {
    val s = sucSequent("[{y:=1;}*]true".asFormula)
    helper.runTactic(globalAlphaRule("x", "t"), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[t:=x;][{y:=1;}*]true".asFormula)
    ))
  }

  it should "not store initial value if variable to rename is bound outside and does not occur in loop" in {
    val s = sucSequent("\\forall x. [{y:=1;}*]true".asFormula)
    helper.runTactic(locateSucc(alphaRule("x", "t")), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("\\forall t. [{y:=1;}*]true".asFormula)))
    helper.runTactic(globalAlphaRule("x", "t"), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[t:=x;]\\forall t. [{y:=1;}*]true".asFormula)))
  }

  it should "not store initial value if variable to rename is free in loop" in {
    val s = sucSequent("\\forall x. [{y:=x+1;}*]true".asFormula)
    helper.runTactic(locateSucc(alphaRule("x", "t")), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("\\forall t. [{y:=t+1;}*]true".asFormula)
    ))
    helper.runTactic(globalAlphaRule("x", "t"), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[t:=x;]\\forall t. [{y:=t+1;}*]true".asFormula)
    ))
  }

  "Alpha-conversion rule on tests" should "be [?x>0;]x>0 with (x,t) on [?x>0;]x>0" in {
    val s = sucSequent("[?x>0;]x>0".asFormula)
    helper.runTactic(globalAlphaRule("x", "t"), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[t:=x;][?t>0;]t>0".asFormula)
    ))
  }

  it should "be forall t. [?t>0;]t>0 with (x,t) on forall x. [?x>0;]x>0" in {
    val s = sucSequent("\\forall x. [?x>0;]x>0".asFormula)
    helper.runTactic(locateSucc(alphaRule("x", "t")), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("\\forall t. [?t>0;]t>0".asFormula)
    ))
    helper.runTactic(globalAlphaRule("x", "t"), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[t:=x;]\\forall t. [?t>0;]t>0".asFormula)
    ))
  }

  "Alpha conversion of derivatives" should "be x'>0 with (x,t) on x'>0" in {
    val s = sucSequent("x'>0".asFormula)
    helper.runTactic(globalAlphaRule("x", "t"), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[t:=x;]t'>0".asFormula)
    ))
  }

  it should "be forall t. t'>0 with (x,t) on forall x. x'>0" in {
    val s = sucSequent("\\forall x. x'>0".asFormula)
    helper.runTactic(locateSucc(alphaRule("x", "t")), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("\\forall t. t'>0".asFormula)
    ))
    helper.runTactic(globalAlphaRule("x", "t"), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[t:=x;]\\forall t. t'>0".asFormula)
    ))
  }

  it should "be [t':=0;]t>0 with (x,t) on [x':=0;]x'>0" in {
    val s = sucSequent("[x':=0;]x'>0".asFormula)
    helper.runTactic(globalAlphaRule("x", "t"), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[t:=x;][t':=0;]t'>0".asFormula)
    ))
  }

  it should "rename in checked ODE fragments" in {
    val s = sucSequent("[$$x' ≚ x$$;]x>0".asFormula)
    helper.runTactic(globalAlphaRule("x", "t"), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[t:=x;][$$t' ≚ t$$;]t>0".asFormula)
    ))
  }

  "Global alpha conversion" should "store initial value and rename quantified variables" in {
    val s = sucSequent("[x:=0;]\\forall x. x>0".asFormula)
    helper.runTactic(globalAlphaRule("x", "t"), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[t:=x;][t:=0;]\\forall t. t>0".asFormula)
    ))
  }

  it should "store initial value" in {
    val s = sucSequent("[x:=x+1;x:=x+2]x>0".asFormula)
    helper.runTactic(globalAlphaRule("x", "t"), new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[t:=x;][t:=t+1;t:=t+2]t>0".asFormula)
    ))
  }

  /**
   * ==================================================
   * test cases for Alpha Conversion Tactic
   */

  "Alpha-conversion tactic" should "be [t:=x+1;][t_0:=t;][t_0'=1;]t_0>0 with (x,t) on [x:=x+1;][x'=1;]x>0" in {
    val s = sucSequent("[x:=x+1;][x'=1;]x>0".asFormula)
    val result = helper.runTactic(globalAlpha("x", "t"), new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "[t:=t+1;][t'=1;]t>0".asFormula
  }

  it should "be [t:=x+1;][t_0:=t;][{t_0:=t_0+1;}*]t_0>0 with (x,t) on [x:=x+1;][{x:=x+1;}*]x>0" in {
    val s = sucSequent("[x:=x+1;][{x:=x+1;}*]x>0".asFormula)
    val result = helper.runTactic(globalAlpha("x", "t"), new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "[t:=t+1;][{t:=t+1;}*]t>0".asFormula
  }

  /**
   * ==================================================
   * test cases for AlphaConversionHelper
   */


  "AlphaConversionHelper" should "rename free variables" in {
    val x = new Variable("x", None, Real)
    AlphaConversionHelper.replaceFree("x>0".asFormula)(x, CDot) should be (
      GreaterThan(Real, CDot, Number(0)))
  }

  it should "rename free variables in modality predicates" in {
    val x = new Variable("x", None, Real)
    val z = new Variable("z", None, Real)
    AlphaConversionHelper.replaceFree("[z:=2;](x>0 & z>0)".asFormula)(x, CDot) should be (
      BoxModality(Assign(z, Number(2)), And(GreaterThan(Real, CDot, Number(0)), GreaterThan(Real, z, Number(0)))))
    }

  it should "not rename bound variables" in {
    val x = new Variable("x", None, Real)
    AlphaConversionHelper.replaceFree("[x:=2;]x>0".asFormula)(x, CDot) should be (
      BoxModality(Assign(x, Number(2)), GreaterThan(Real, x, Number(0))))
  }

  it should "be enforceable to not rename bound variables" in {
    val x = new Variable("x", None, Real)
    AlphaConversionHelper.replaceFree("[x:=2;]x>0".asFormula)(x, CDot, None) should be (
      BoxModality(Assign(CDot, Number(2)), GreaterThan(Real, CDot, Number(0))))
  }

  it should "rename free variables but not variables bound by assignment" in {
    val x = new Variable("x", None, Real)
    AlphaConversionHelper.replaceFree("[x:=2+x;]x>0".asFormula)(x, CDot) should be (
      BoxModality(Assign(x, Add(Real, Number(2), CDot)), GreaterThan(Real, x, Number(0))))
  }

  it should "rename free variables but not variables bound by ODEs" in {
    val x = new Variable("x", None, Real)
    val z = new Variable("z", None, Real)
    AlphaConversionHelper.replaceFree("[z'=2+x;](x>0 & z>0)".asFormula)(x, CDot) should be (
      BoxModality(ODESystem(ODEProduct(AtomicODE(Derivative(Real, z), Add(Real, Number(2), CDot))), True),
        And(GreaterThan(Real, CDot, Number(0)), GreaterThan(Real, z, Number(0)))))
    AlphaConversionHelper.replaceFree("[z'=2+x;](x>0 & z>0)".asFormula)(z, CDot) should be (
      BoxModality(ODESystem(ODEProduct(AtomicODE(Derivative(Real, z), Add(Real, Number(2), x))), True),
        And(GreaterThan(Real, x, Number(0)), GreaterThan(Real, z, Number(0)))))
  }

  it should "rename free variables but not variables bound by marked ODEs" in {
    val x = new Variable("x", None, Real)
    val z = new Variable("z", None, Real)
    AlphaConversionHelper.replaceFree("[$$z'=2+x$$;](x>0 & z>0)".asFormula)(x, CDot) should be (
      BoxModality(ODESystem(IncompleteSystem(ODEProduct(AtomicODE(Derivative(Real, z),
        Add(Real, Number(2), CDot)))), True),
        And(GreaterThan(Real, CDot, Number(0)), GreaterThan(Real, z, Number(0)))))
    AlphaConversionHelper.replaceFree("[$$z'=2+x$$;](x>0 & z>0)".asFormula)(z, CDot) should be (
      BoxModality(ODESystem(IncompleteSystem(ODEProduct(AtomicODE(Derivative(Real, z),
        Add(Real, Number(2), x)))), True),
        And(GreaterThan(Real, x, Number(0)), GreaterThan(Real, z, Number(0)))))
  }

  it should "not rename variables bound by assignments in loops" in {
    val x = new Variable("x", None, Real)
    AlphaConversionHelper.replaceFree("[{x:=x+1;}*;]x>0".asFormula)(x, CDot) should be (
      BoxModality(Loop(Assign(x, Add(Real, x, Number(1)))),
        GreaterThan(Real, x, Number(0))))
  }

  it should "rename free variables but not bound variables in loops" in {
    val x = new Variable("x", None, Real)
    val z = new Variable("z", None, Real)
    AlphaConversionHelper.replaceFree("[{x:=x+1; ?z>5}*;](x>0 & z>4)".asFormula)(x, CDot) should be (
      BoxModality(Loop(Sequence(Assign(x, Add(Real, x, Number(1))), Test(GreaterThan(Real, z, Number(5))))),
        And(GreaterThan(Real, x, Number(0)), GreaterThan(Real, z, Number(4)))))
    AlphaConversionHelper.replaceFree("[{x:=x+1; ?z>5}*;](x>0 & z>4)".asFormula)(z, CDot) should be (
      BoxModality(Loop(Sequence(Assign(x, Add(Real, x, Number(1))), Test(GreaterThan(Real, CDot, Number(5))))),
        And(GreaterThan(Real, x, Number(0)), GreaterThan(Real, CDot, Number(4)))))
  }

  it should "rename free variables not mentioned in loops" in {
    val x = new Variable("x", None, Real)
    val z = new Variable("z", None, Real)
    AlphaConversionHelper.replaceFree("[{x:=x+1;}*;](x>0 & z>4)".asFormula)(x, CDot) should be (
      BoxModality(Loop(Assign(x, Add(Real, x, Number(1)))),
        And(GreaterThan(Real, x, Number(0)), GreaterThan(Real, z, Number(4)))))
    AlphaConversionHelper.replaceFree("[{x:=x+1;}*;](x>0 & z>4)".asFormula)(z, CDot) should be (
      BoxModality(Loop(Assign(x, Add(Real, x, Number(1)))),
        And(GreaterThan(Real, x, Number(0)), GreaterThan(Real, CDot, Number(4)))))
  }

  it should "only rename variables equal to old name even if free names is None" in {
    val x = new Variable("x", None, Real)
    val z = new Variable("z", None, Real)
    AlphaConversionHelper.replaceFree("[x:=z;]x>0".asFormula)(x, CDot, None) should be (
      BoxModality(Assign(CDot, z),
        GreaterThan(Real, CDot, Number(0))))
    AlphaConversionHelper.replaceFree("[x:=z;]x>0".asFormula)(z, CDot, None) should be (
      BoxModality(Assign(x, CDot),
        GreaterThan(Real, x, Number(0))))
  }

  it should "not rename bound occurrences" in {
    val x = new Variable("x", None, Real)
    val z = new Variable("z", None, Real)
    AlphaConversionHelper.replaceFree("[x:=x;]x>0".asFormula)(x, CDot) should be (
      BoxModality(Assign(x, CDot),
        GreaterThan(Real, x, Number(0))))
  }

  it should "only allow variables as new terms if replacing in universal quantifier" in {
    AlphaConversionHelper.replaceFree("\\forall x. x>0".asFormula)("x".asTerm, CDot) should be (
      "\\forall x. x>0".asFormula)
    AlphaConversionHelper.replaceFree("\\forall x. x>0".asFormula)("x".asTerm, "z".asTerm) should be (
      "\\forall z. z>0".asFormula)
  }

  it should "allow replacement with terms on right-hand side in assignments" in {
    AlphaConversionHelper.replaceFree("[x:=z;]x>0".asFormula)("z".asTerm, "1".asTerm) should be ("[x:=1;]x>0".asFormula)
  }

  it should "not allow replacement with terms on left-hand side in assignments" in {
    AlphaConversionHelper.replaceFree("[x:=z;]x>0".asFormula)("x".asTerm, "1".asTerm) should be ("[x:=z;]x>0".asFormula)
  }

  it should "replace terms if all their symbols are free" in {
    AlphaConversionHelper.replaceFree("x+1>0".asFormula)("x+1".asTerm, "y".asTerm) should be ("y>0".asFormula)
    AlphaConversionHelper.replaceFree("[x:=x+0;]x>0".asFormula)("0".asTerm, "y".asTerm) should be ("[x:=x+y;]x>y".asFormula)
  }

  it should "not replace terms if some of their symbols are bound" in {
    AlphaConversionHelper.replaceFree("[x:=2;]x+1>0".asFormula)("x+1".asTerm, "y".asTerm) should be (
      "[x:=2;]x+1>0".asFormula)
  }

  it should "replace terms if forced to, even if some of their symbols are bound" in {
    AlphaConversionHelper.replaceFree("[x:=2;]x+1>0".asFormula)("x+1".asTerm, "y".asTerm, None) should be (
      "[x:=2;]y>0".asFormula)
  }
}
