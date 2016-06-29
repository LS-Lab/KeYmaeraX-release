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
  var link: JLinkMathematicaLink = null
  var ml : KeYmaeraMathematicaBridge[KExpr] = null //var so that we can instantiate within a test case.

  val x = Variable("x", None, Real)
  val y = Variable("y", None, Real)
  val A = Variable("A", None, Bool)
  val B = Variable("B", None, Bool)
  val xFn = Function("x", None, Real, Real)

  val zero = Number(new BigDecimal("0"))

  private val defaultK2MConverter = KeYmaeraToMathematica

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
    def trip(e: edu.cmu.cs.ls.keymaerax.core.Expression) = roundTrip(e) should be (e)

    def roundTrip(e : edu.cmu.cs.ls.keymaerax.core.Expression) = {
      val math = defaultK2MConverter(e)
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

  ignore should "convert inverse functions correctly" in {
    ???
  }

  ignore should "convert integrals correctly" in {
    ???
  }

  it should "convert rules correctly with the nonQEConverter" ignore {
    //@todo run(MExpr, executor, converter) is private, and so are executor and converter
    ml.runUnchecked("Rule[x,y]")._2 shouldBe Equal(x, y)
    ml.runUnchecked("Rule[x[y],y]")._2 should be (Equal(FuncOf(xFn, y), y))
    ml.runUnchecked("{{Rule[x,y]}}")._2 should be (Equal(x, y))
    ml.runUnchecked("{{Rule[x,y], Rule[y,x]}}")._2 should be (And(Equal(x, y), Equal(y, x)))
    ml.runUnchecked("{{Rule[x,y], Rule[y,x]}, {Rule[x[y],y]}}")._2 shouldBe
      Or(And(Equal(x, y), Equal(y, x)), Equal(FuncOf(xFn, y), y))
  }

  it should "not convert rules with the default converter" in {
    a [ConversionException] should be thrownBy ml.runUnchecked("Rule[x,y]")
    a [ConversionException] should be thrownBy ml.runUnchecked("{{Rule[x,y]}}")
    a [ConversionException] should be thrownBy ml.runUnchecked("{{Rule[x,y], Rule[y,x]}}")
  }

  it should "convert names correctly" in {
    ml.runUnchecked("kyx`x")._2 should be (x)
    ml.runUnchecked("Apply[kyx`x, {kyx`y}]")._2 should be (FuncOf(Function("x", None, Real, Real), Variable("y", None, Real)))
    ml.runUnchecked("Apply[kyx`x, {kyx`y0}]")._2 should be (FuncOf(Function("x", None, Real, Real), Variable("y0", None, Real)))
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
    a [MatchError] should be thrownBy defaultK2MConverter(FuncOf(Function("x", None, Unit, Real), Nothing))
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

  it should "convert inequalities" in {
    round trip "\\forall x x>y".asFormula
    round trip "\\forall x x>=y".asFormula
    round trip "\\forall x x<=y".asFormula
    round trip "\\forall x x<y".asFormula
  }

  it should "associate correctly" in {
    round trip "\\forall x ((x<=y & y<=z) & z<0)".asFormula
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

  "KeYmaera -> Mathematica" should "convert Apply" in {
    val in = FuncOf(Function("y", None, Real, Real), Variable("x"))
    val expected = new MExpr(new MExpr(Expr.SYMBOL, "kyx`y"), Array[MExpr](new MExpr(Expr.SYMBOL, "kyx`x")))
    defaultK2MConverter(in) should be (expected)
  }

  it should "refuse to convert parameterless Apply()" in {
    val in = FuncOf(Function("y", None, Unit, Real), Nothing)
    a [MatchError] should be thrownBy defaultK2MConverter(in)
  }

  it should "convert multi-argument Apply to nested lists" in {
    val in = FuncOf(Function("f", None, Tuple(Real, Tuple(Real, Real)), Real), Pair(Variable("x"), Pair(Variable("y"), Variable("z"))))
    val expected = new MExpr(new MExpr(Expr.SYMBOL, "kyx`f"),
        Array[MExpr](new MExpr(Expr.SYMBOL, "kyx`x"), new MExpr(Expr.SYM_LIST, Array[MExpr](
            new MExpr(Expr.SYMBOL, "kyx`y"), new MExpr(Expr.SYMBOL, "kyx`z")))))
    println(expected.toString)
    defaultK2MConverter(in) should be (expected)
  }

  it should "convert special functions correctly" in {
    defaultK2MConverter("abs(x)".asTerm) shouldBe new MExpr(new MExpr(Expr.SYMBOL, "Abs"), Array[MExpr](new MExpr(Expr.SYMBOL, "kyx`x")))
    defaultK2MConverter("min(x,y)".asTerm) shouldBe new MExpr(new MExpr(Expr.SYMBOL, "Min"), Array[MExpr](new MExpr(Expr.SYMBOL, "kyx`x"), new MExpr(Expr.SYMBOL, "kyx`y")))
    defaultK2MConverter("max(x,y)".asTerm) shouldBe new MExpr(new MExpr(Expr.SYMBOL, "Max"), Array[MExpr](new MExpr(Expr.SYMBOL, "kyx`x"), new MExpr(Expr.SYMBOL, "kyx`y")))
  }

  it should "insist on correct domain/sort of special functions" in {
    a [CoreException] should be thrownBy defaultK2MConverter(Variable("abs"))
    a [CoreException] should be thrownBy defaultK2MConverter(Variable("Abs"))
    a [CoreException] should be thrownBy defaultK2MConverter("abs()".asTerm)
    a [CoreException] should be thrownBy defaultK2MConverter("Abs(x)".asTerm)  // correct domain, but uppercase
    a [CoreException] should be thrownBy defaultK2MConverter("abs(x,y)".asTerm)
    a [CoreException] should be thrownBy defaultK2MConverter(Variable("min"))
    a [CoreException] should be thrownBy defaultK2MConverter(Variable("Min"))
    a [CoreException] should be thrownBy defaultK2MConverter("min(x)".asTerm)
    a [CoreException] should be thrownBy defaultK2MConverter("Min(x,y)".asTerm)  // correct domain, but uppercase
    a [CoreException] should be thrownBy defaultK2MConverter("min(x,y,z)".asTerm)
    a [CoreException] should be thrownBy defaultK2MConverter(Variable("max"))
    a [CoreException] should be thrownBy defaultK2MConverter(Variable("Max"))
    a [CoreException] should be thrownBy defaultK2MConverter("max(x)".asTerm)
    a [CoreException] should be thrownBy defaultK2MConverter("Max(x,y)".asTerm) // correct domain, but uppercase
    a [CoreException] should be thrownBy defaultK2MConverter("max(x,y,z)".asTerm)
  }
}
