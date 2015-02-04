import edu.cmu.cs.ls.keymaera.core._
import org.scalatest.{Matchers, FlatSpec}
import testHelper.StringConverter._

/**
 * Created by smitsch on 1/13/15.
 * @author Stefan Mitsch
 */
class ExpressionTests extends FlatSpec with Matchers {
  "IncompleteSystem(c)" should "be equal to IncompleteSystem(c)" in {
    val c = NFContEvolve(Nil, Derivative(Real, Variable("x", None, Real)), Number(1), True)
    IncompleteSystem(c) should be (IncompleteSystem(c))
  }

  it should "not be equal to empty IncompleteSystem" in {
    val c = NFContEvolve(Nil, Derivative(Real, Variable("x", None, Real)), Number(1), True)
    IncompleteSystem(c) should not be IncompleteSystem()
  }

  it should "not be equal to empty IncompleteSystem(d)" in {
    val c = NFContEvolve(Nil, Derivative(Real, Variable("x", None, Real)), Number(1), True)
    val d = NFContEvolve(Nil, Derivative(Real, Variable("y", None, Real)), Number(1), True)
    IncompleteSystem(c) should not be IncompleteSystem(d)
  }

  it should "match IncompleteSystem(c) " in {
    val c = NFContEvolve(Nil, Derivative(Real, Variable("x", None, Real)), Number(1), True)
    IncompleteSystem(c) match {
      case IncompleteSystem(cc) => cc should be (c)
      case _ => fail()
    }
  }

  "Empty IncompleteSystem" should "be equal to other empty IncompleteSystem" in {
    IncompleteSystem() should be (IncompleteSystem())
  }

  it should "not be equal to IncompleteSystem(c)" in {
    val c = NFContEvolve(Nil, Derivative(Real, Variable("x", None, Real)), Number(1), True)
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

  "Normalization of ContEvolveProducts" should "reduce two empty programs to one" in {
    ContEvolveProduct(EmptyContEvolveProgram(), EmptyContEvolveProgram()).normalize() should be (
      EmptyContEvolveProgram())
  }

  it should "not change an already normalized product" in {
    def nf(x: String) = NFContEvolve(Nil, Derivative(Real, x.asTerm), "1".asTerm, "true".asFormula)
    ContEvolveProduct(nf("x"), EmptyContEvolveProgram()).normalize() should be (
      ContEvolveProduct(nf("x"), EmptyContEvolveProgram()))
  }

  it should "have exactly one empty program at the end" in {
    def nf(x: String) = NFContEvolve(Nil, Derivative(Real, x.asTerm), "1".asTerm, "true".asFormula)
    ContEvolveProduct(ContEvolveProduct(nf("x"), ContEvolveProduct(nf("y"))),
      ContEvolveProduct(EmptyContEvolveProgram(), ContEvolveProduct(nf("z"), EmptyContEvolveProgram()))).
      normalize() should be (ContEvolveProduct(nf("x"), ContEvolveProduct(nf("y"), ContEvolveProduct(nf("z"), EmptyContEvolveProgram()))))
  }
}
