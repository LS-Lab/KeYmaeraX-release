import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tools.JLinkMathematicaLink
import org.scalatest.{BeforeAndAfterEach, Matchers, FlatSpec}

/**
 * Tests the JLink Mathematica implementation.
 * @author Stefan Mitsch
 */
class JLinkMathematicaLinkTests extends FlatSpec with Matchers with BeforeAndAfterEach {

  private var link: JLinkMathematicaLink = null

  private val x = Variable("x", None, Real)
  private val y = Variable("y", None, Real)
  private val z = Variable("z", None, Real)
  private val t = Variable("t", None, Real)
  private val x0 = Variable("x0", None, Real)
  private val y0 = Variable("y0", None, Real)
  private val one = Number(BigDecimal(1))
  private val two = Number(BigDecimal(2))

  override def beforeEach() = {
    link = new JLinkMathematicaLink
    link.init("/Applications/Mathematica.app/Contents/MacOS/MathKernel")
  }

  override def afterEach() = {
    link.shutdown()
    link = null
  }

  "x'=1" should "x=x0+t" in {
    val eq = ContEvolve(Equals(Real, Derivative(Real, x), one))
    val expected = Some(Equals(Real, x, Add(Real, Multiply(Real, one, t), x0)))
    link.diffSol(eq, t) should be (expected)
  }

  it should "x=x0+y*t with NFContEvolve" in {
    val eq = NFContEvolve(List(), Derivative(Real, x), one, True)
    val expected = Some(Equals(Real, x, Add(Real, Multiply(Real, one, t), x0)))
    link.diffSol(eq, t) should be (expected)
  }

  "x'=y" should "x=x0+y*t" in {
    val eq = ContEvolve(Equals(Real, Derivative(Real, x), y))
    val expected = Some(Equals(Real, x, Add(Real, x0, Multiply(Real, t, y))))
    link.diffSol(eq, t) should be (expected)
  }

  "x'=y, y'=z" should "y=y0+z*t and x=x0+y0*t+z/2*t^2 with ContEvolve" in {
    val eq = ContEvolve(And(Equals(Real, Derivative(Real, x), y), Equals(Real, Derivative(Real, y), z)))
    // x=1/2*(2*x0 + 2*t*y0 + t^2*z) and y=y0+t*z
    val expected = Some(And(
      Equals(Real, x, Multiply(Real, Divide(Real, one, two), Add(Real, Add(Real, Multiply(Real, two, x0), Multiply(Real, Multiply(Real, two, t), y0)), Multiply(Real, Exp(Real, t, two), z)))),
      Equals(Real, y, Add(Real, y0, Multiply(Real, t, z)))))
    link.diffSol(eq, t) should be (expected)
  }

  it should "y=y0+z*t and x=x0+y0*t+z/2*t^2 with ContProduct" in {
    val eq = ContEvolveProduct(
      NFContEvolve(Nil, Derivative(Real, x), y, True),
      NFContEvolve(Nil, Derivative(Real, y), z, True))
    // x=1/2*(2*x0 + 2*t*y0 + t^2*z) and y=y0+t*z
    val expected = Some(And(
      Equals(Real, x, Multiply(Real, Divide(Real, one, two), Add(Real, Add(Real, Multiply(Real, two, x0), Multiply(Real, Multiply(Real, two, t), y0)), Multiply(Real, Exp(Real, t, two), z)))),
      Equals(Real, y, Add(Real, y0, Multiply(Real, t, z)))))
    link.diffSol(eq, t) should be (expected)
  }

  "x'=y, t'=1" should "x=x0+y*t with ContEvolve" in {
    // special treatment of t for now
    val eq = ContEvolve(And(Equals(Real, Derivative(Real, x), y), Equals(Real, Derivative(Real, t), one)))
    val expected = Some(Equals(Real, x, Add(Real, x0, Multiply(Real, t, y))))
    link.diffSol(eq, t) should be (expected)
  }

  it should "x=x0+y*t with ContProduct" in {
    // special treatment of t for now
    val eq = ContEvolveProduct(
      NFContEvolve(Nil, Derivative(Real, x), y, True),
      NFContEvolve(Nil, Derivative(Real, t), one, True))
    val expected = Some(Equals(Real, x, Add(Real, x0, Multiply(Real, t, y))))
    link.diffSol(eq, t) should be (expected)
  }
}
