import org.scalatest.{Matchers, FlatSpec}
import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tests.ProvabilityTestHelper


/**
 * Created by nfulton on 12/31/14.
 */
class TraversalTests extends FlatSpec with Matchers {
  val helper = new ProvabilityTestHelper()

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Free Variables Traversal
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  "Free Variables Traversal" should "return x in [x:=1;]x=1" in {
    val expression = helper.parse("[x:=1;]x=1") match {
      case Some(e) => e
      case None => fail("Expected to project an expression.")
    }
    val variables = Traversals.freeVariables(expression)
    variables.length should be (1);
    variables.last should be (Variable("x", None, Real))
  }

  it should "handle sequences of assignments correctly" in {
    val programOption = helper.parseBareProgram("x := 1; y := 1; z := 1;")

    programOption match {
      case Some(p) => {
        val fvs = Traversals.freeVariables(p)

        fvs.length should be (3)
        (fvs.contains(Variable("x", None, Real)) &
          fvs.contains(Variable("y", None, Real)) &
          fvs.contains(Variable("z", None, Real))) should be (true)
      }
      case None => fail("Program didn't even parse correctly.")
    }
  }

  it should "handle more complicated programs correctly" in {
    val programOption = helper.parseBareProgram("{x := 1 ++ y := 2}*; z := 3; x := 45;")
    programOption match {
      case Some(p) => {
        val fvs = Traversals.freeVariables(p)
        fvs.length should be (3)
        (fvs.contains(Variable("x", None, Real)) &
          fvs.contains(Variable("y", None, Real)) &
          fvs.contains(Variable("z", None, Real))) should be (true)
      }
      case None => fail("program didn't even parse correctly.")
    }
  }

  it should "not include x in \\forall x . x=x" in {
    val x = Variable("x", None, Real)
    val expression = Forall(x :: Nil, Equals(Real, x, x))

    Traversals.freeVariables(expression).length should be (0)
  }

  it should "not include x in \\exists x . x=x" in {
    val x = Variable("x", None, Real)
    val expression = Exists(x :: Nil, Equals(Real, x, x))

    Traversals.freeVariables(expression).length should be (0)
  }

  it should "Include variables that are free before and after quantified expressions" in {
    val x = Variable("x", None, Real)
    val y = Variable("y", None, Real)
    val z = Variable("z", None, Real)

    val expression = helper.parseFormula("x > 0 & (\\forall y . y = y) | z < 0") //nonsense.
    val fvs = Traversals.freeVariables(expression)
    fvs.length should be (2)
    fvs.contains(x) should be (true)
    fvs.contains(y) should be (false)
    fvs.contains(z) should be (true)
  }
}
