import edu.cmu.cs.ls.keymaera.core._
import org.scalatest.{Matchers, FlatSpec}
import testHelper.StringConverter._

/**
 * Created by smitsch on 1/13/15.
 * @author Stefan Mitsch
 */
class ExpressionTests extends FlatSpec with Matchers {
  "Equality of EmptyODE" should "consider a product of empty programs an empty program" in {
    EmptyODE() should be (ODEProduct(EmptyODE(), EmptyODE()))
  }

  "Equality of ODEProducts" should "consider a product of empty programs an empty program" in {
    ODEProduct(EmptyODE(), EmptyODE()) should be {
      EmptyODE()
    }
  }

  it should "ignore empty programs" in {
    def nf(x: String) = AtomicODE(Derivative(Real, x.asTerm), "1".asTerm)
    ODEProduct(ODEProduct(nf("x"), ODEProduct(nf("y"))),
      ODEProduct(EmptyODE(), ODEProduct(nf("z"), EmptyODE()))) should be (
      ODEProduct(nf("x"), ODEProduct(nf("y"), nf("z"))))
    ODEProduct(ODEProduct(EmptyODE(), ODEProduct(nf("x"), nf("y"))),
      ODEProduct(EmptyODE(), ODEProduct(nf("z")))) should be (
      ODEProduct(nf("x"), ODEProduct(nf("y"), nf("z"))))
  }

  "Normalization of ODEProducts" should "reduce two empty programs to one" in {
    ODEProduct(EmptyODE(), EmptyODE()).normalize() should be (
      EmptyODE())
  }

  it should "not change an already normalized product" in {
    def nf(x: String) = AtomicODE(Derivative(Real, x.asTerm), "1".asTerm)
    ODEProduct(nf("x"), EmptyODE()).normalize() should be (
      ODEProduct(nf("x"), EmptyODE()))
  }

  it should "always start with an atomic ODE" in {
    def nf(x: String) = AtomicODE(Derivative(Real, x.asTerm), "1".asTerm)
    ODEProduct(ODEProduct(nf("x"), ODEProduct(nf("y"))),
      ODEProduct(EmptyODE(), ODEProduct(nf("z")))).normalize() match {
      case ODEProduct(_: AtomicODE, _) =>
      case _ => fail("First element in normalized system of ODEs is not an atomic ODE")
    }
    ODEProduct(ODEProduct(EmptyODE(), ODEProduct(nf("x"), nf("y"))),
      ODEProduct(EmptyODE(), ODEProduct(nf("z")))).normalize() match {
      case ODEProduct(_: AtomicODE, _) =>
      case _ => fail("First element in normalized system of ODEs is not an atomic ODE")
    }
  }
}
