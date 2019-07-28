package tools

import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tools.RingsAlgebraTool

/** Tests for RingsAlgebraTool
  */
class RingsAlgebraToolTests extends TacticTestBase  {

  "RingsAlgebraTool" should "compute groebner basis" in withMathematica { _ =>
    val x = "1+x*y^2+1+y^2+x*y+(x+y+3)^(2-1)".asTerm
    val y = "y+x*z*a+(a*b+1/3)^2".asTerm
    val tool = new RingsAlgebraTool()

    tool.groebnerBasis(List(x,y,Variable("z"))) shouldBe List("z", "1+9*y+6*a*b+9*a^2*b^2", "5+y+x+y^2+x*y+x*y^2").map(_.asTerm)
  }

  it should "compute groebner basis univariate" in withMathematica { _ =>
    val x1 = "x".asTerm
    val x2 = "(x^2+2*x+1)^(20-14)".asTerm
    val y = "x^2".asTerm
    val tool = new RingsAlgebraTool()

    tool.groebnerBasis(List(x1,y)) shouldBe List("x").map(_.asTerm)
    tool.groebnerBasis(List(x2,y)) shouldBe List("1").map(_.asTerm)
  }

  it should "compute polynomial remainder" in withMathematica { _ =>
    val x = "a*b()+e+f".asTerm
    val y = "a".asTerm
    val z = "e+f+b()".asTerm
    val tool = new RingsAlgebraTool()

    val res = tool.polynomialReduce(x,List(y,z))
    res._1 shouldBe List("b()","1").map(_.asTerm)
    res._2 shouldBe "-1*b()".asTerm
  }

  it should "compute univariate quotient remainder" in withMathematica { _ =>
    val x = "(x^2+x*y)^2+1/5*z*x^3+z*y+1".asTerm
    val y = "x".asVariable
    val tool = new RingsAlgebraTool()

    val res = tool.quotientRemainder(x,y,y)

    res._1 shouldBe "1/5*x^2*z+x*y^2+2*x^2*y+x^3".asTerm
    res._2 shouldBe "1+y*z".asTerm
  }

}