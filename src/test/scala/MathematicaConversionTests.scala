import com.wolfram.jlink.Expr
import edu.cmu.cs.ls.keymaera.tactics.Tactics
import org.scalatest._
import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tools._
import java.io.File
import java.math.BigDecimal
import scala.collection.immutable._

class MathematicaConversionTests extends FlatSpec with Matchers with BeforeAndAfterEach {

  type MExpr = com.wolfram.jlink.Expr
  val mathematicaConfig : Map[String, String] = Map("linkName" -> "/Applications/Mathematica.app/Contents/MacOS/MathKernel")
  var ml : JLinkMathematicaLink = null //var so that we can instantiate within a test case.

  val x = Variable("x", None, Real)
  val y = Variable("y", None, Real)
  val A = Variable("A", None, Bool)
  val B = Variable("B", None, Bool)
  val xFn = Function("x", None, Real, Real)

  val zero = Number(new BigDecimal("0"))

  def num(n : Integer) = Number(new BigDecimal(n.toString()))
  def snum(n : String) = Number(new BigDecimal(n))

  override def beforeEach() = {
    ml = new JLinkMathematicaLink()
    ml.init(mathematicaConfig("linkName"), None) //@todo jlink
  }

  override def afterEach() = {
    ml.shutdown()
    ml = null
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

    ml.run("x >= y")._2 should be (GreaterEqual(Real, x, y))
    ml.run("x >= 0")._2 should be (GreaterEqual(Real, x, zero))

    ml.run("x < y")._2 should be (LessThan(Real, x, y))
    ml.run("x < 0")._2 should be (LessThan(Real, x, zero))

    ml.run("x <= y")._2 should be (LessEqual(Real, x, y))
    ml.run("x <= 0")._2 should be (LessEqual(Real, x, zero))
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

  it should "convert rules correctly" in {
    ml.run("Rule[x,y]")._2 should be (Equals(Real, x, y))
    ml.run("Rule[x[y],y]")._2 should be (Equals(Real, Apply(xFn, y), y))
    ml.run("{{Rule[x,y]}}")._2 should be (Equals(Real, x, y))
    ml.run("{{Rule[x,y], Rule[y,x]}}")._2 should be (And(Equals(Real, x, y), Equals(Real, y, x)))
    ml.run("{{Rule[x,y], Rule[y,x]}, {Rule[x[y],y]}}")._2 should be
      (Or(And(Equals(Real, x, y), Equals(Real, y, x)), Equals(Real, Apply(xFn, y), y)))
  }

  it should "convert names correctly" in {
    ml.run("x")._2 should be (x)
    ml.run("x[y]")._2 should be (Apply(Function("x", None, Real, Real), Variable("y", None, Real)))
    ml.run("x$underscore$0")._2 should be (Variable("x_0", None, Real))
    ml.run("x$underscore$0$underscore$1")._2 should be (Variable("x_0_1", None, Real))
    ml.run("x[y$underscore$0]")._2 should be (Apply(Function("x", None, Real, Real), Variable("y_0", None, Real)))
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


  object round {
    def trip(e: edu.cmu.cs.ls.keymaera.core.Expr) = roundTrip(e) should be (e)

    def roundTrip(e : edu.cmu.cs.ls.keymaera.core.Expr) = {
      val math = KeYmaeraToMathematica.fromKeYmaera(e)
      ml.run(math)._2
    }
  }

  "Mathematica -> KeYmaera" should "convert inequalities" in {
    round trip Forall(Seq(x), GreaterThan(Real,x,y))
    round trip Forall(Seq(x), GreaterEqual(Real,x,y))
    round trip Forall(Seq(x), LessEqual(Real,x,y))
    round trip Forall(Seq(x), LessThan(Real,x,y))
  }

  it should "convert parameterless Apply()" in {
    round trip Apply(Function("x", None, Unit, Real), Nothing)
  }

  it should "convert Apply()" in {
    round trip Apply(Function("x", None, Real, Real), Number(0))
    round trip Apply(Function("x", None, Real, Real), Variable("y", None, Real))
  }

  "KeYmaera <-> Mathematica converters" should "commute" in {
    round trip num(5)
    round trip x
    round trip Variable("x_0", None, Real)
    round trip Variable("x_", None, Real)
    round trip Variable("_", None, Real)
    round trip Variable("x_0_1", None, Real)
    round trip Variable("_x_0", None, Real)
    round trip Apply(Function("x", None, Real, Real), Variable("y_0", None, Real))
  }

  "KeYmaera -> Mathematica" should "convert Apply" in {
    val in = Apply(Function("y", None, Real, Real), Variable("x", None, Real))
    val expected = new MExpr(new MExpr(Expr.SYMBOL, "Apply"),
      Array[MExpr](
        new MExpr(Expr.SYMBOL, "KeYmaera`y"),
        new MExpr(Expr.SYM_LIST, Array[MExpr](new MExpr(Expr.SYMBOL, "KeYmaera`x")))))
    KeYmaeraToMathematica.fromKeYmaera(in) should be (expected)
  }

  it should "convert parameterless Apply()" in {
    val in = Apply(Function("y", None, Unit, Real), Nothing)
    val expected = new MExpr(new MExpr(Expr.SYMBOL, "Apply"),
      Array[MExpr](
        new MExpr(Expr.SYMBOL, "KeYmaera`y")))
    KeYmaeraToMathematica.fromKeYmaera(in) should be (expected)
  }
}
