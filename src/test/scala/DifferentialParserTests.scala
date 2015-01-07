import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tests.ProvabilityTestHelper
import org.scalatest.{Matchers, FlatSpec}

/**
 * Tests for ContEvolve -> NFContEvolve refactoring.
 * Created by nfulton on 1/2/15.
 */
class DifferentialParserTests extends FlatSpec with Matchers {
  val helper = new ProvabilityTestHelper()

  val x = Variable("x", None, Real)
  val y = Variable("y", None, Real)
  val one = Number(1)
  val zero = Number(0)

  "The parser" should "parse diff eqs in normal form into NFContEvolves" in {
    helper.parseBareProgram("x' = 1 & x > 0;") match {
      case Some(program) => program should be (NFContEvolve(Nil, x, Number(1), GreaterThan(Real, x, zero)))
      case None => fail("Parse failed.")
    }
  }

  it should "not confuse a portion of the diffeq with the domain constraint" in {
    helper.parseBareProgram("x'=y, y'=x & true;") match {
      case Some(program) =>
        program should be (NFContEvolveSystem(Nil, (Derivative(Real, x), y) :: (Derivative(Real, y), x) :: Nil, True))
      case None => fail("Failed to parse.")
    }
  }

  it should "not confuse a portion of the diffeq system with the evolution domain constraint" in {
    helper.parseBareProgram("x'=x, y'=y;") match {
      case Some(program) =>
        program should be (NFContEvolveSystem(Nil, (Derivative(Real, x), x) :: (Derivative(Real, y), y) :: Nil, True))
      case None => fail("Parse failed.")
    }
  }
}
