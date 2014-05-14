import org.scalatest._
import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tools._
import java.io.File
import java.math.BigDecimal

class MathematicaConversionTests extends FlatSpec with Matchers {
  var ml : MathematicaLink = null //var so that we can instantiate within a test case.
  val x = Variable("x", None, Real)
  val y = Variable("y", None, Real)
  val A = Variable("A", None, Bool)
  val B = Variable("B", None, Bool)

  val zero = Number(new BigDecimal("0"))

  def num(n : Integer) = Number(new BigDecimal(n.toString()))
  def snum(n : String) = Number(new BigDecimal(n))

  "MathematicaLink" should "connect" in {
    ml = new JLinkMathematicaLink()
  }

  it should "convert numbers" in {
    ml.run("2+2")._2 should be (Number(4))
  }
  
   "Mathematica -> KeYmaera" should "convert simple quantifiers" in {
    val f = True //TODO handle true and false!
    ml.run("ForAll[{x}, x==x]")._2 should be (True)
    ml.run("Exists[{x}, x==0]")._2 should be (Exists(Seq(x), Equals(Real,x,zero)))
    ml.run("ForAll[x, x==0]")._2 should be (Forall(Seq(x), Equals(Real, x, zero)))
    //TODO-nrf polynomials?
    //TODO-nrf truth functions?
  }

  it should "convert equalities and inequalities" in {
    ml.run("x == y")._2 should be (Equals(Real, x, y))
    ml.run("x == 0")._2 should be (Equals(Real, x, zero))
    
    ml.run("x != y")._2 should be (NotEquals(Real, x, y))
    ml.run("x != 0")._2 should be (NotEquals(Real, x, zero))

    ml.run("x > y")._2 should be (GreaterThan(Real, x, y))
    ml.run("x > 0")._2 should be (GreaterThan(Real, x, zero))
    
    ml.run("x >= y")._2 should be (GreaterEquals(Real, x, y))
    ml.run("x >= 0")._2 should be (GreaterEquals(Real, x, zero))

    ml.run("x < y")._2 should be (LessThan(Real, x, y))
    ml.run("x < 0")._2 should be (LessThan(Real, x, zero))

    ml.run("x <= y")._2 should be (LessEquals(Real, x, y))
    ml.run("x <= 0")._2 should be (LessEquals(Real, x, zero))
  }

  it should "do math" in {
    ml.run("2+3")._2 should be (num(5))
    ml.run("2*3")._2 should be (num(6))
    ml.run("6/3")._2 should be (num(2))
    ml.run("10-5")._2 should be (num(5))
  }

  it should "not choke on rationals" in {
    ml.run("2/5")._2 should be (Divide(Real, num(2), num(5)))
  }

  //The second thing causes a choke.
  ignore should "not choke on other reasonable numbers" in {
    ml.run("Rationalize[0.5/10]")._2 should be (Divide(Real,num(1),num(20)))
    ml.run(".25/10")._2
  }

  ignore should "transcend" in {
    ml.run("Sin[x]")._2
  }

  it should "convert arithmetic expressions correctly" in {
    ml.run("x+y")._2 should be (Add(Real,x,y))
    ml.run("x*y")._2 should be (Multiply(Real,x,y))
    ml.run("x-1")._2 should be (Add(Real,Neg(Real,num(1)),x)) //TODO-nrf these two tests are nasty.
    ml.run("x/y")._2 should be (Multiply(Real, x, Exp(Real, y,num(-1))))
    ml.run("ForAll[{x}, x/4 == 4]")._2 should be 
    (
      Forall(Seq(x), 
        Equals(
          Real,
          Divide(
            Real, 
            x, 
            num(4)
          ),
          num(4)
        )
      )
    )
  }

  ignore should "convert inverse functions correctly" in {
    ???
  }

  ignore should "convert integrals correctly" in {
    ???
  }

  ignore should "Conbert rules correctly" in {
    ???
  }

  it should "convert Boolean Algebra correctly" in {
    ml.run("True")._2 should be (True)
    ml.run("False")._2 should be (False)
    //These test cases are fragile because they require Mathematica to not do
    //any reduction, but Mathematica's semantics are from from clear and in
    //future versions (or previous versions) these expressions might actually
    //evaluate
    ml.run("x==y && y==x")._2 should be (And(Equals(Real,x,y),Equals(Real, y,x))) //TODO-nrf what about sorts?!
    ml.run("x==y || y==x")._2 should be (Or(Equals(Real,x,y),Equals(Real,y,x)))
    ml.run("!(x==y && y==x)")._2 should be (Not(And(Equals(Real,x,y),Equals(Real,y,x))))

    //ml.run("x==y -> y==z") should be (Imply(Equals(Real,x,y),Equals(Real,y,z)))
    //ml.run("x==y <-> y==z") should be(Equiv(Equals(Real,x,y),Equals(Real,y,z)))
  }

  it should "not fail on a grab-bag of previous errors" in {
    ml.run("x^2 + 2x + 4")._2 should be 
    (
      Add(
        Real,
        num(4),
        Add(
          Real,
          Multiply(Real,num(2),x),
          Exp(Real,x,num(2))
        )
      )
    )
  }

  def roundTrip(e : edu.cmu.cs.ls.keymaera.core.Expr) = {
    val math = KeYmaeraToMathematica.fromKeYmaera(e)
    ml.run(math)._2
  }

  "Mathematica -> KeYmaera" should "convert inequalities" in {
    object round {
      def trip(e: Formula) = roundTrip(e) should be (e)
    }
    round trip Forall(Seq(x), GreaterThan(Real,x,y))
    round trip Forall(Seq(x), GreaterEquals(Real,x,y))
    round trip Forall(Seq(x), LessEquals(Real,x,y))
    round trip Forall(Seq(x), LessThan(Real,x,y))
  }

  "KeYmaera <-> Mathematica converters" should "commute" in {
    roundTrip(num(5)) should be (num(5))
  }
}
