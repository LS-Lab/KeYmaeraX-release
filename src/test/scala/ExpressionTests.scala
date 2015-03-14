import edu.cmu.cs.ls.keymaera.core._
import org.scalatest.{Matchers, FlatSpec}
import testHelper.StringConverter._

/**
 * Created by smitsch on 1/13/15.
 * @author Stefan Mitsch
 */
class ExpressionTests extends FlatSpec with Matchers {
  "IncompleteSystem(c)" should "be equal to IncompleteSystem(c)" in {
    val c = AtomicContEvolve(Derivative(Real, Variable("x", None, Real)), Number(1))
    IncompleteSystem(c) should be (IncompleteSystem(c))
  }

  it should "not be equal to empty IncompleteSystem" in {
    val c = AtomicContEvolve(Derivative(Real, Variable("x", None, Real)), Number(1))
    IncompleteSystem(c) should not be IncompleteSystem()
  }

  it should "not be equal to empty IncompleteSystem(d)" in {
    val c = AtomicContEvolve(Derivative(Real, Variable("x", None, Real)), Number(1))
    val d = AtomicContEvolve(Derivative(Real, Variable("y", None, Real)), Number(1))
    IncompleteSystem(c) should not be IncompleteSystem(d)
  }

  it should "match IncompleteSystem(c) " in {
    val c = AtomicContEvolve(Derivative(Real, Variable("x", None, Real)), Number(1))
    IncompleteSystem(c) match {
      case IncompleteSystem(cc) => cc should be (c)
      case _ => fail()
    }
  }

  "Empty IncompleteSystem" should "be equal to other empty IncompleteSystem" in {
    IncompleteSystem() should be (IncompleteSystem())
  }

  it should "not be equal to IncompleteSystem(c)" in {
    val c = AtomicContEvolve(Derivative(Real, Variable("x", None, Real)), Number(1))
    IncompleteSystem() should not be IncompleteSystem(c)
  }

  it should "match IncompleteSystem(EmptyContEvolveProgram) " in {
    IncompleteSystem() match {
      case IncompleteSystem(c) => c should be (EmptyContEvolveProgram())
      case _ => fail()
    }
  }

  it should "not match IncompleteSystem(c)" in {
    IncompleteSystem() match {
      case IncompleteSystem(_: EmptyContEvolveProgram) => /* expected */
      case _ => fail()
    }
  }

  "Equality of EmptyContEvolveProgram" should "consider a product of empty programs an empty program" in {
    EmptyContEvolveProgram() should be (ContEvolveProduct(EmptyContEvolveProgram(), EmptyContEvolveProgram()))
  }

  "Equality of ContEvolveProducts" should "consider a product of empty programs an empty program" in {
    ContEvolveProduct(EmptyContEvolveProgram(), EmptyContEvolveProgram()) should be {
      EmptyContEvolveProgram()
    }
  }

  it should "ignore empty programs" in {
    def nf(x: String) = AtomicContEvolve(Derivative(Real, x.asTerm), "1".asTerm)
    ContEvolveProduct(ContEvolveProduct(nf("x"), ContEvolveProduct(nf("y"))),
      ContEvolveProduct(EmptyContEvolveProgram(), ContEvolveProduct(nf("z"), EmptyContEvolveProgram()))) should be (
      ContEvolveProduct(nf("x"), ContEvolveProduct(nf("y"), nf("z"))))
    ContEvolveProduct(ContEvolveProduct(EmptyContEvolveProgram(), ContEvolveProduct(nf("x"), nf("y"))),
      ContEvolveProduct(EmptyContEvolveProgram(), ContEvolveProduct(nf("z")))) should be (
      ContEvolveProduct(nf("x"), ContEvolveProduct(nf("y"), nf("z"))))
  }

  "Normalization of ContEvolveProducts" should "reduce two empty programs to one" in {
    ContEvolveProduct(EmptyContEvolveProgram(), EmptyContEvolveProgram()).normalize() should be (
      EmptyContEvolveProgram())
  }

  it should "not change an already normalized product" in {
    def nf(x: String) = AtomicContEvolve(Derivative(Real, x.asTerm), "1".asTerm)
    ContEvolveProduct(nf("x"), EmptyContEvolveProgram()).normalize() should be (
      ContEvolveProduct(nf("x"), EmptyContEvolveProgram()))
  }

  it should "always start with an atomic ODE" in {
    def nf(x: String) = AtomicContEvolve(Derivative(Real, x.asTerm), "1".asTerm)
    ContEvolveProduct(ContEvolveProduct(nf("x"), ContEvolveProduct(nf("y"))),
      ContEvolveProduct(EmptyContEvolveProgram(), ContEvolveProduct(nf("z")))).normalize() match {
      case ContEvolveProduct(_: AtomicContEvolve, _) =>
      case _ => fail("First element in normalized system of ODEs is not an atomic ODE")
    }
    ContEvolveProduct(ContEvolveProduct(EmptyContEvolveProgram(), ContEvolveProduct(nf("x"), nf("y"))),
      ContEvolveProduct(EmptyContEvolveProgram(), ContEvolveProduct(nf("z")))).normalize() match {
      case ContEvolveProduct(_: AtomicContEvolve, _) =>
      case _ => fail("First element in normalized system of ODEs is not an atomic ODE")
    }
  }
}
