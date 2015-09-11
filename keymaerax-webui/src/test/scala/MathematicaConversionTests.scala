/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
import com.wolfram.jlink.Expr
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter
import testHelper.ProvabilityTestHelper
import org.scalatest._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tools._
import java.math.BigDecimal
import scala.collection.immutable._

class MathematicaConversionTests extends FlatSpec with Matchers with BeforeAndAfterEach {

  type MExpr = com.wolfram.jlink.Expr
  val helper = new ProvabilityTestHelper((x) => println(x))
  val mathematicaConfig: Map[String, String] = helper.mathematicaConfig
  var ml : JLinkMathematicaLink = null //var so that we can instantiate within a test case.

  val x = Variable("x", None, Real)
  val y = Variable("y", None, Real)
  val A = Variable("A", None, Bool)
  val B = Variable("B", None, Bool)
  val xFn = Function("x", None, Real, Real)

  val zero = Number(new BigDecimal("0"))

  def num(n : Integer) = Number(new BigDecimal(n.toString))
  def snum(n : String) = Number(new BigDecimal(n))

  override def beforeEach() = {
    PrettyPrinter.setPrinter(edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter)
    ml = new JLinkMathematicaLink()
    ml.init(mathematicaConfig("linkName"), None) //@todo jlink
  }

  override def afterEach() = {
    ml.shutdown()
    ml = null
  }

  it should "convert numbers" in {
    ml.runUnchecked("2+2")._2 should be (Number(4))
  }

   "Mathematica -> KeYmaera" should "convert simple quantifiers" in {
    val f = True //TODO handle true and false!
    ml.runUnchecked("ForAll[{x}, x==x]")._2 should be (True)
    ml.runUnchecked("Exists[{x}, x==0]")._2 should be (Exists(Seq(x), Equal(x,zero)))
    ml.runUnchecked("ForAll[x, x==0]")._2 should be (Forall(Seq(x), Equal(x, zero)))
    //TODO-nrf polynomials?
    //TODO-nrf truth functions?
  }

  it should "convert equalities and inequalities" in {
    ml.runUnchecked("x == y")._2 should be (Equal(x, y))
    ml.runUnchecked("x == 0")._2 should be (Equal(x, zero))

    ml.runUnchecked("x != y")._2 should be (NotEqual(x, y))
    ml.runUnchecked("x != 0")._2 should be (NotEqual(x, zero))

    ml.runUnchecked("x > y")._2 should be (Greater(x, y))
    ml.runUnchecked("x > 0")._2 should be (Greater(x, zero))

    ml.runUnchecked("x >= y")._2 should be (GreaterEqual(x, y))
    ml.runUnchecked("x >= 0")._2 should be (GreaterEqual(x, zero))

    ml.runUnchecked("x < y")._2 should be (Less(x, y))
    ml.runUnchecked("x < 0")._2 should be (Less(x, zero))

    ml.runUnchecked("x <= y")._2 should be (LessEqual(x, y))
    ml.runUnchecked("x <= 0")._2 should be (LessEqual(x, zero))
  }

  it should "do math" in {
    ml.runUnchecked("2+3")._2 should be (num(5))
    ml.runUnchecked("2*3")._2 should be (num(6))
    ml.runUnchecked("6/3")._2 should be (num(2))
    ml.runUnchecked("10-5")._2 should be (num(5))
  }

  it should "not choke on rationals" in {
    ml.runUnchecked("2/5")._2 should be (Divide(num(2), num(5)))
  }

  //The second thing causes a choke.
  ignore should "not choke on other reasonable numbers" in {
    ml.runUnchecked("Rationalize[0.5/10]")._2 should be (Divide(num(1),num(20)))
    ml.runUnchecked(".25/10")._2
  }

  ignore should "transcend" in {
    ml.runUnchecked("Sin[x]")._2
  }

  it should "convert arithmetic expressions correctly" in {
    ml.runUnchecked("x+y")._2 should be (Plus(x,y))
    ml.runUnchecked("x*y")._2 should be (Times(x,y))
    ml.runUnchecked("x-1")._2 should be (Plus(Number(-1), x)) //TODO-nrf these three tests are nasty.
    ml.runUnchecked("x-y")._2 should be (Plus(x, Times(Number(-1), y)))
    ml.runUnchecked("x/y")._2 should be (Times(x, Power(y,num(-1))))
    ml.runUnchecked("ForAll[{x}, x/4 == 4]")._2 shouldBe
      Forall(Seq(x),
        Equal(
          Times(
            Divide(
              num(1),
              num(4)
            ),
            x),
          num(4)
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
    ml.runUnchecked("Rule[x,y]")._2 should be (Equal(x, y))
    ml.runUnchecked("Rule[x[y],y]")._2 should be (Equal(FuncOf(xFn, y), y))
    ml.runUnchecked("{{Rule[x,y]}}")._2 should be (Equal(x, y))
    ml.runUnchecked("{{Rule[x,y], Rule[y,x]}}")._2 should be (And(Equal(x, y), Equal(y, x)))
    ml.runUnchecked("{{Rule[x,y], Rule[y,x]}, {Rule[x[y],y]}}")._2 shouldBe
      Or(And(Equal(x, y), Equal(y, x)), Equal(FuncOf(xFn, y), y))
  }

  it should "convert names correctly" in {
    ml.runUnchecked("x")._2 should be (x)
    ml.runUnchecked("x[y]")._2 should be (FuncOf(Function("x", None, Real, Real), Variable("y", None, Real)))
    ml.runUnchecked("x[y0]")._2 should be (FuncOf(Function("x", None, Real, Real), Variable("y0", None, Real)))
  }

  ignore should "convert crazy names correctly" in {
    ml.runUnchecked("x$underscore$0")._2 should be (Variable("x_0", None, Real))
    ml.runUnchecked("x$underscore$0$underscore$1")._2 should be (Variable("x_0_1", None, Real))
    ml.runUnchecked("x[y$underscore$0]")._2 should be (FuncOf(Function("x", None, Real, Real), Variable("y_0", None, Real)))
  }

  it should "convert Boolean Algebra correctly" in {
    ml.runUnchecked("True")._2 should be (True)
    ml.runUnchecked("False")._2 should be (False)
    //These test cases are fragile because they require Mathematica to not do
    //any reduction, but Mathematica's semantics are from from clear and in
    //future versions (or previous versions) these expressions might actually
    //evaluate
    ml.runUnchecked("x==y && y==x")._2 should be (And(Equal(x,y),Equal(y,x)))
    ml.runUnchecked("x==y || y==x")._2 should be (Or(Equal(x,y),Equal(y,x)))
    ml.runUnchecked("!(x==y && y==x)")._2 should be (Not(And(Equal(x,y),Equal(y,x))))

    //ml.runUnchecked("x==y -> y==z") should be (Imply(Equals(Real,x,y),Equals(Real,y,z)))
    //ml.runUnchecked("x==y <-> y==z") should be(Equiv(Equals(Real,x,y),Equals(Real,y,z)))
  }

  it should "not fail on a grab-bag of previous errors" in {
    ml.runUnchecked("x^2 + 2x + 4")._2 shouldBe "4 + 2*x + x^2".asTerm
  }


  object round {
    def trip(e: edu.cmu.cs.ls.keymaerax.core.Expression) = roundTrip(e) should be (e)

    def roundTrip(e : edu.cmu.cs.ls.keymaerax.core.Expression) = {
      val math = KeYmaeraToMathematica.fromKeYmaera(e)
      ml.run(math)._2
    }
  }

  "Mathematica -> KeYmaera" should "convert inequalities" in {
    round trip "\\forall x x>y".asFormula
    round trip "\\forall x x>=y".asFormula
    round trip "\\forall x x<=y".asFormula
    round trip "\\forall x x<y".asFormula
  }

  it should "associate correctly" in {
    round trip "\\forall x ((x<=y & y<=z) & z<0)".asFormula
  }

  it should "convert parameterless Apply()" in {
    round trip FuncOf(Function("x", None, Unit, Real), Nothing)
  }

  it should "convert Apply()" in {
    round trip FuncOf(Function("x", None, Real, Real), Number(0))
    round trip FuncOf(Function("x", None, Real, Real), Variable("y", None, Real))
  }

  "KeYmaera <-> Mathematica converters" should "commute" in {
    round trip num(5)
    round trip x
    round trip Variable("y", None, Real)
    round trip Variable("xyzd", None, Real)
    round trip Variable("_", None, Real)
    round trip Variable("x_", None, Real)
    round trip Variable("x", Some(0), Real)
    round trip Variable("x", Some(5), Real)
    round trip Variable("x_", Some(0), Real)
    round trip Variable("x_", Some(2), Real)
    round trip FuncOf(Function("x", None, Real, Real), Variable("y0", None, Real))
  }

  ignore should "commute crazy names" in {
    round trip Variable("x_0", None, Real)
    round trip Variable("x_", None, Real)
    round trip Variable("_", None, Real)
    round trip Variable("x_0_1", None, Real)
    round trip Variable("_x_0", None, Real)
    round trip FuncOf(Function("x", None, Real, Real), Variable("y_0", None, Real))
  }

  "KeYmaera -> Mathematica" should "convert Apply" in {
    val in = FuncOf(Function("y", None, Real, Real), Variable("x", None, Real))
    val expected = new MExpr(new MExpr(Expr.SYMBOL, "Apply"),
      Array[MExpr](
        new MExpr(Expr.SYMBOL, "KeYmaera`y"),
        new MExpr(Expr.SYM_LIST, Array[MExpr](new MExpr(Expr.SYMBOL, "KeYmaera`x")))))
    KeYmaeraToMathematica.fromKeYmaera(in) should be (expected)
  }

  it should "convert parameterless Apply()" in {
    val in = FuncOf(Function("y", None, Unit, Real), Nothing)
    val expected = new MExpr(Expr.SYMBOL, "KeYmaera`constfn$y")
    KeYmaeraToMathematica.fromKeYmaera(in) should be (expected)
  }
}
