import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary._
import edu.cmu.cs.ls.keymaera.tactics.{AlphaConversionHelper, Tactics}
import edu.cmu.cs.ls.keymaera.tactics.Tactics.{ApplyRule, Tactic, PositionTactic}
import edu.cmu.cs.ls.keymaera.tests.ProvabilityTestHelper
import testHelper.StringConverter
import StringConverter._
import org.scalatest.{BeforeAndAfterEach, Matchers, FlatSpec}

/**
 * Created by smitsch on 1/13/15.
 * @author Stefan Mitsch
 */
class AlphaConversionTests extends FlatSpec with Matchers with BeforeAndAfterEach {
  val helper = new ProvabilityTestHelper((x) => println(x),
    new ToolBase("") { override def init(cfg: Map[String, String]) {} })

  override def beforeEach() = {
    Tactics.KeYmaeraScheduler.init(Map())
  }

  override def afterEach() = {
    Tactics.KeYmaeraScheduler.shutdown()
  }

  "Alpha conversion rule" should "rename in ODEs and store initial value" in {
    val sequent = new Sequent(Nil,
      scala.collection.immutable.IndexedSeq(),
      scala.collection.immutable.IndexedSeq("[y'=1;]true".asFormula)
    )

    def alpha(from: String, to: String): PositionTactic =
      new PositionTactic("Alpha Renaming") {
        override def applies(s: Sequent, p: Position): Boolean = true
        override def apply(p: Position): Tactic = new ApplyRule(new AlphaConversion(p, from, None, to, None)) {
          override def applicable(node: ProofNode): Boolean = true
        } & hideT(p.topLevel)
      }

    val tactic = locateSucc(alpha("y", "x"))
    helper.runTactic(tactic, new RootNode(sequent)).openGoals().foreach(_.sequent should be (
      new Sequent(Nil,
        scala.collection.immutable.IndexedSeq(),
        scala.collection.immutable.IndexedSeq("[x:=y;][x'=1;]true".asFormula)
      )
    ))
  }

  ignore /*"Alpha conversion tactic"*/ should "rename in ODEs, store initial value, and handle assignment" in {
    val sequent = new Sequent(Nil,
      scala.collection.immutable.IndexedSeq(),
      scala.collection.immutable.IndexedSeq("[y'=1;]true".asFormula)
    )

    val tactic = locateSucc(alphaRenamingT("y", None, "x", None))
    helper.runTactic(tactic, new RootNode(sequent)).openGoals().foreach(_.sequent should be (
      new Sequent(Nil,
        scala.collection.immutable.IndexedSeq(),
        scala.collection.immutable.IndexedSeq("[x'=1;]true".asFormula)
      )
    ))
  }

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
      BoxModality(ContEvolveProduct(NFContEvolve(Nil, Derivative(Real, z), Add(Real, Number(2), CDot), True)),
        And(GreaterThan(Real, CDot, Number(0)), GreaterThan(Real, z, Number(0)))))
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
}
