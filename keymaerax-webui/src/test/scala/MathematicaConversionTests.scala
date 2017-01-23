/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
import com.wolfram.jlink.Expr
import org.scalatest._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tools._
import java.math.BigDecimal

import edu.cmu.cs.ls.keymaerax.launcher.DefaultConfiguration
import edu.cmu.cs.ls.keymaerax.tools.MathematicaConversion.{KExpr, MExpr}

import scala.collection.immutable._

class MathematicaConversionTests extends FlatSpec with Matchers with BeforeAndAfterEach {

  val mathematicaConfig: Map[String, String] = DefaultConfiguration.defaultMathematicaConfig
  var link: JLinkMathematicaLink = _
  var ml : KeYmaeraMathematicaBridge[KExpr] = _ //var so that we can instantiate within a test case.

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
    link = new JLinkMathematicaLink()
    link.init(mathematicaConfig("linkName"), None) //@todo jlink
    ml = new BaseKeYmaeraMathematicaBridge[KExpr](link, KeYmaeraToMathematica, MathematicaToKeYmaera) {}
  }

  override def afterEach() = {
    link.shutdown()
    link = null
    ml = null
  }

  private object round {
    def trip(e: KExpr, k2m: K2MConverter[KExpr] = KeYmaeraToMathematica) = roundTrip(e, k2m) should be (e)

    def roundTrip(e: KExpr, k2m: K2MConverter[KExpr]) = {
      val math = k2m(e)
      ml.run(math)._2
    }
  }

  it should "convert numbers" in {
    ml.runUnchecked("2+2")._2 should be (Number(4))
  }

   "Mathematica -> KeYmaera" should "convert simple quantifiers" in {
    val f = True //TODO handle true and false!
    ml.runUnchecked("ForAll[{kyx`x}, kyx`x==kyx`x]")._2 should be (True)
    ml.runUnchecked("Exists[{kyx`x}, kyx`x==0]")._2 should be (Exists(Seq(x), Equal(x,zero)))
    ml.runUnchecked("ForAll[{kyx`x}, kyx`x==0]")._2 should be (Forall(Seq(x), Equal(x, zero)))
    //TODO-nrf polynomials?
    //TODO-nrf truth functions?
  }

  it should "convert equalities and inequalities" in {
    ml.runUnchecked("kyx`x == kyx`y")._2 should be (Equal(x, y))
    ml.runUnchecked("kyx`x == 0")._2 should be (Equal(x, zero))

    ml.runUnchecked("kyx`x != kyx`y")._2 should be (NotEqual(x, y))
    ml.runUnchecked("kyx`x != 0")._2 should be (NotEqual(x, zero))

    ml.runUnchecked("kyx`x > kyx`y")._2 should be (Greater(x, y))
    ml.runUnchecked("kyx`x > 0")._2 should be (Greater(x, zero))

    ml.runUnchecked("kyx`x >= kyx`y")._2 should be (GreaterEqual(x, y))
    ml.runUnchecked("kyx`x >= 0")._2 should be (GreaterEqual(x, zero))

    ml.runUnchecked("kyx`x < kyx`y")._2 should be (Less(x, y))
    ml.runUnchecked("kyx`x < 0")._2 should be (Less(x, zero))

    ml.runUnchecked("kyx`x <= kyx`y")._2 should be (LessEqual(x, y))
    ml.runUnchecked("kyx`x <= 0")._2 should be (LessEqual(x, zero))
  }

  it should "do math" in {
    ml.runUnchecked("2+3")._2 should be (num(5))
    ml.runUnchecked("2*3")._2 should be (num(6))
    ml.runUnchecked("6/3")._2 should be (num(2))
    ml.runUnchecked("10-5")._2 should be (num(5))
  }

  it should "not choke on rationals" in {
    ml.runUnchecked("2/5")._2 shouldBe Divide(num(2), num(5))
    ml.runUnchecked("Rational[2,5]")._2 shouldBe Divide(num(2), num(5))
  }

  it should "not choke on other reasonable numbers" in {
    ml.runUnchecked("Rationalize[0.5/10]")._2 should be (Divide(num(1),num(20)))
    ml.runUnchecked(".25/10")._2 shouldBe Number(0.025)
  }

  it should "convert arithmetic expressions correctly" in {
    ml.runUnchecked("kyx`x+kyx`y")._2 should be (Plus(x,y))
    ml.runUnchecked("kyx`x*kyx`y")._2 should be (Times(x,y))
    ml.runUnchecked("kyx`x-1")._2 should be (Plus(Number(-1), x)) //TODO-nrf these three tests are nasty.
    ml.runUnchecked("kyx`x-kyx`y")._2 should be (Plus(x, Times(Number(-1), y)))
    ml.runUnchecked("kyx`x/kyx`y")._2 should be (Times(x, Power(y,num(-1))))
    ml.runUnchecked("ForAll[{kyx`x}, kyx`x/4 == 4]")._2 shouldBe
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

  it should "convert rules correctly with the nonQEConverter" in {
    ml = new BaseKeYmaeraMathematicaBridge[KExpr](link, new  UncheckedK2MConverter(), new UncheckedM2KConverter()) {}
    ml.runUnchecked("Rule[kyx`x,kyx`y]")._2 shouldBe Equal(x, y)
    ml.runUnchecked("Rule[kyx`x[kyx`y],kyx`y]")._2 should be (Equal(FuncOf(xFn, y), y))
    ml.runUnchecked("{{Rule[kyx`x,kyx`y]}}")._2 should be (Equal(x, y))
    ml.runUnchecked("{{Rule[kyx`x,kyx`y], Rule[kyx`y,kyx`x]}}")._2 should be (And(Equal(x, y), Equal(y, x)))
    ml.runUnchecked("{{Rule[kyx`x,kyx`y], Rule[kyx`y,kyx`x]}, {Rule[kyx`x[kyx`y],kyx`y]}}")._2 shouldBe
      Or(And(Equal(x, y), Equal(y, x)), Equal(FuncOf(xFn, y), y))
  }

  it should "not convert rules with the default converter" in {
    a [ConversionException] should be thrownBy ml.runUnchecked("Rule[kyx`x,kyx`y]")
    a [ConversionException] should be thrownBy ml.runUnchecked("{{Rule[kyx`x,kyx`y]}}")
    a [ConversionException] should be thrownBy ml.runUnchecked("{{Rule[kyx`x,kyx`y], Rule[kyx`y,kyx`x]}}")
  }

  it should "convert names correctly" in {
    ml.runUnchecked("kyx`x")._2 should be (x)
    ml.runUnchecked("Apply[kyx`x, {kyx`y}]")._2 should be (FuncOf(Function("x", None, Real, Real), Variable("y", None, Real)))
    ml.runUnchecked("Apply[kyx`x, {kyx`y0}]")._2 should be (FuncOf(Function("x", None, Real, Real), Variable("y0", None, Real)))
  }

  it should "convert crazy names correctly" in {
    ml.runUnchecked("kyx`x$u$")._2 should be (Variable("x_", None, Real))
    ml.runUnchecked("kyx`x[kyx`y$u$]")._2 should be (FuncOf(Function("x", None, Real, Real), Variable("y_", None, Real)))
  }

  it should "convert Boolean Algebra correctly" in {
    ml.runUnchecked("True")._2 should be (True)
    ml.runUnchecked("False")._2 should be (False)
    //These test cases are fragile because they require Mathematica to not do
    //any reduction, but Mathematica's semantics are from from clear and in
    //future versions (or previous versions) these expressions might actually
    //evaluate
    ml.runUnchecked("kyx`x==kyx`y && kyx`y==kyx`x")._2 should be (And(Equal(x,y),Equal(y,x)))
    ml.runUnchecked("kyx`x==kyx`y || kyx`y==kyx`x")._2 should be (Or(Equal(x,y),Equal(y,x)))
    ml.runUnchecked("!(kyx`x==kyx`y && kyx`y==kyx`x)")._2 should be (Not(And(Equal(x,y),Equal(y,x))))

    //ml.runUnchecked("x==y -> y==z") should be (Imply(Equals(Real,x,y),Equals(Real,y,z)))
    //ml.runUnchecked("x==y <-> y==z") should be(Equiv(Equals(Real,x,y),Equals(Real,y,z)))
  }

  it should "not fail on a grab-bag of previous errors" in {
    ml.runUnchecked("kyx`x^2 + 2kyx`x + 4")._2 shouldBe "4 + 2*x + x^2".asTerm
  }

  it should "refuse to convert parameterless Apply()" in {
    a [MatchError] should be thrownBy KeYmaeraToMathematica(FuncOf(Function("x", None, Unit, Real), Nothing))
  }

  it should "convert inequalities" in {
    ml.runUnchecked("kyx`x < kyx`y == kyx`z < 0")._2 shouldBe "x<y & y=z & z<0".asFormula
  }

  it should "convert derivatives with the nonQEConverter" in {
    ml = new BaseKeYmaeraMathematicaBridge[KExpr](link, new  UncheckedK2MConverter(), new UncheckedM2KConverter()) {}
    ml.runUnchecked("Derivative[1][kyx`x]")._2 shouldBe DifferentialSymbol(Variable("x"))
  }

  "KeYmaera <-> Mathematica converters" should "commute" in {
    round trip num(5)
    round trip x
    round trip Variable("y", None, Real)
    round trip Variable("xyzd", None, Real)
    //round trip Variable("_", None, Real)
    round trip Variable("x_", None, Real)
    round trip Variable("x", Some(0), Real)
    round trip Variable("x", Some(5), Real)
    round trip Variable("x_", Some(0), Real)
    round trip Variable("x_", Some(2), Real)
    round trip FuncOf(Function("x", None, Real, Real), Variable("y0", None, Real))
  }

  it should "commute crazy names" in {
    round trip Variable("x_", None, Real)
    //round trip Variable("_", None, Real)
    round trip FuncOf(Function("x", None, Real, Real), Variable("y_", None, Real))
  }

  it should "convert inequalities" in {
    round trip "\\forall x x>y".asFormula
    round trip "\\forall x x>=y".asFormula
    round trip "\\forall x x<=y".asFormula
    round trip "\\forall x x<y".asFormula
  }

  it should "associate correctly" in {
    round trip "\\forall x ((x<=y & y<=z) & z<0)".asFormula
    KeYmaeraToMathematica("5--2".asTerm) shouldBe new MExpr(new MExpr(Expr.SYMBOL, "Subtract"),
      Array(new MExpr(5), new MExpr(-2)))
  }

  it should "convert Apply()" in {
    round trip FuncOf(Function("x", None, Real, Real), Number(0))
    round trip FuncOf(Function("x", None, Real, Real), Variable("y", None, Real))
  }

  it should "convert special functions" in {
    round trip "abs(x)".asTerm
    round trip "min(x,y)".asTerm
    round trip "max(x,y)".asTerm
  }

  it should "convert non-arg functions with nonQEConverter" in {
    ml = new BaseKeYmaeraMathematicaBridge[KExpr](link, new  UncheckedK2MConverter(), new UncheckedM2KConverter()) {}
    round trip("g()".asTerm, new UncheckedK2MConverter())
  }

  "KeYmaera -> Mathematica" should "convert Apply" in {
    val in = FuncOf(Function("y", None, Real, Real), Variable("x"))
    val expected = new MExpr(new MExpr(Expr.SYMBOL, "kyx`y"), Array[MExpr](new MExpr(Expr.SYMBOL, "kyx`x")))
    KeYmaeraToMathematica(in) should be (expected)
  }

  it should "refuse to convert parameterless Apply()" in {
    val in = FuncOf(Function("y", None, Unit, Real), Nothing)
    a [MatchError] should be thrownBy KeYmaeraToMathematica(in)
  }

  it should "convert multi-argument Apply to nested lists" in {
    val in = FuncOf(Function("f", None, Tuple(Real, Tuple(Real, Real)), Real), Pair(Variable("x"), Pair(Variable("y"), Variable("z"))))
    val expected = new MExpr(new MExpr(Expr.SYMBOL, "kyx`f"),
        Array[MExpr](new MExpr(Expr.SYMBOL, "kyx`x"), new MExpr(Expr.SYM_LIST, Array[MExpr](
            new MExpr(Expr.SYMBOL, "kyx`y"), new MExpr(Expr.SYMBOL, "kyx`z")))))
    println(expected.toString)
    KeYmaeraToMathematica(in) should be (expected)
  }

  it should "convert special functions correctly" in {
    KeYmaeraToMathematica("abs(x)".asTerm) shouldBe new MExpr(new MExpr(Expr.SYMBOL, "Abs"), Array[MExpr](new MExpr(Expr.SYMBOL, "kyx`x")))
    KeYmaeraToMathematica("min(x,y)".asTerm) shouldBe new MExpr(new MExpr(Expr.SYMBOL, "Min"), Array[MExpr](new MExpr(Expr.SYMBOL, "kyx`x"), new MExpr(Expr.SYMBOL, "kyx`y")))
    KeYmaeraToMathematica("max(x,y)".asTerm) shouldBe new MExpr(new MExpr(Expr.SYMBOL, "Max"), Array[MExpr](new MExpr(Expr.SYMBOL, "kyx`x"), new MExpr(Expr.SYMBOL, "kyx`y")))
  }

  it should "distinguish uninterpreted names from interpreted ones by namespace" in {
    KeYmaeraToMathematica(Variable("abs")) shouldBe new MExpr(Expr.SYMBOL, "kyx`abs")
    KeYmaeraToMathematica(Variable("Abs")) shouldBe new MExpr(Expr.SYMBOL, "kyx`Abs")
    a [CoreException] should be thrownBy KeYmaeraToMathematica("abs()".asTerm)
    KeYmaeraToMathematica("Abs(x)".asTerm) shouldBe new MExpr(new MExpr(Expr.SYMBOL, "kyx`Abs"), Array[MExpr](new MExpr(Expr.SYMBOL, "kyx`x")))
    KeYmaeraToMathematica("abs(x)".asTerm) shouldBe new MExpr(new MExpr(Expr.SYMBOL, "Abs"), Array[MExpr](new MExpr(Expr.SYMBOL, "kyx`x")))
    a [CoreException] should be thrownBy KeYmaeraToMathematica("abs(x,y)".asTerm)
    KeYmaeraToMathematica(Variable("min")) shouldBe new MExpr(Expr.SYMBOL, "kyx`min")
    KeYmaeraToMathematica(Variable("Min")) shouldBe new MExpr(Expr.SYMBOL, "kyx`Min")
    a [CoreException] should be thrownBy KeYmaeraToMathematica("min(x)".asTerm)
    KeYmaeraToMathematica("Min(x,y)".asTerm) shouldBe new MExpr(new MExpr(Expr.SYMBOL, "kyx`Min"), Array[MExpr](new MExpr(Expr.SYMBOL, "kyx`x"), new MExpr(Expr.SYMBOL, "kyx`y")))
    KeYmaeraToMathematica("min(x,y)".asTerm) shouldBe new MExpr(new MExpr(Expr.SYMBOL, "Min"), Array[MExpr](new MExpr(Expr.SYMBOL, "kyx`x"), new MExpr(Expr.SYMBOL, "kyx`y")))
    a [CoreException] should be thrownBy KeYmaeraToMathematica("min(x,y,z)".asTerm)
    KeYmaeraToMathematica(Variable("max")) shouldBe new MExpr(Expr.SYMBOL, "kyx`max")
    KeYmaeraToMathematica(Variable("Max")) shouldBe new MExpr(Expr.SYMBOL, "kyx`Max")
    a [CoreException] should be thrownBy KeYmaeraToMathematica("max(x)".asTerm)
    KeYmaeraToMathematica("Max(x,y)".asTerm) shouldBe new MExpr(new MExpr(Expr.SYMBOL, "kyx`Max"), Array[MExpr](new MExpr(Expr.SYMBOL, "kyx`x"), new MExpr(Expr.SYMBOL, "kyx`y")))
    KeYmaeraToMathematica("max(x,y)".asTerm) shouldBe new MExpr(new MExpr(Expr.SYMBOL, "Max"), Array[MExpr](new MExpr(Expr.SYMBOL, "kyx`x"), new MExpr(Expr.SYMBOL, "kyx`y")))
    a [CoreException] should be thrownBy KeYmaeraToMathematica("max(x,y,z)".asTerm)
  }
}
