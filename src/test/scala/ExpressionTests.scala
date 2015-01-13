import edu.cmu.cs.ls.keymaera.core._
import org.scalatest.{Matchers, FlatSpec}

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
    IncompleteSystem(c) match {
      case s: IncompleteSystem => s.system shouldBe 'defined; s.system.get should be (c)
      case _ => fail()
    }
  }

  "Empty IncompleteSystem" should "be equal to other empty IncompleteSystem" in {
    IncompleteSystem should be (IncompleteSystem)
  }

  it should "not be equal to IncompleteSystem(c)" in {
    val c = NFContEvolve(Nil, Derivative(Real, Variable("x", None, Real)), Number(1), True)
    IncompleteSystem should not be IncompleteSystem(c)
  }

  it should "not match IncompleteSystem(c)" in {
    IncompleteSystem() match {
      case IncompleteSystem(c) => fail("Empty incomplete system should not match IncompleteSystem(c)")
      case s: IncompleteSystem => s.system should not be 'defined
      case _ => fail()
    }
  }
}
