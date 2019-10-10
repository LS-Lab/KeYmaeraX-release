package tools

import edu.cmu.cs.ls.keymaerax.btactics.{TacticTestBase, TactixLibrary}
import edu.cmu.cs.ls.keymaerax.btactics.helpers.DifferentialHelper
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tools.{RingsAlgebraTool, RingsLibrary}

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

  it should "compute the Lie derivative" in withMathematica { _ =>
    val R = new RingsLibrary("t,x,y,z,i,j".split(',').map(_.asTerm))
    val t = "x*y*(x + z*x - 13)/4 + 4*z*z*(x + x^5)".asTerm
    val tR = R.toRing(t)
    val odemap = Map("x".asVariable -> "-y".asTerm, "y".asVariable -> "-x^2".asTerm, "z".asVariable -> "14*x*y*z".asTerm)
    val ringsLieDerivative = R.lieDerivative(odemap.mapValues(R.toRing).get)(t)
    val lieDerivative = DifferentialHelper.lieDerivative("{x'=-y,y'=-x^2,z'=14*x*y*z}".asDifferentialProgram, t)
    val res = proveBy(Equal(R.fromRing(ringsLieDerivative), lieDerivative), TactixLibrary.QE)
    res shouldBe 'proved
  }

  it should "compute Horner form" in {
    val R = new RingsLibrary("t,x,y,z,i,j".split(',').map(_.asTerm))
    val t = "x*y*(x + z*x - 13)/4 + 4*z*z*(x + x^5)".asTerm
    R.toHorner(R.toRing(t),"x^2,y^2,z^2,x,y,z".split(',').map(_.asTerm).map(R.toRing).toList) shouldBe
      "x*(y*(-13/4))+z^2*(x*4)+x^2*(y*(1/4+z*(1/4))+x^2*(z^2*(x*4)))".asTerm
  }

  it should "split high-order monomials and monomials containing unwanted terms" in {
    val R = new RingsLibrary("t,x,y,z,i,j".split(',').map(_.asTerm))
    val vars = "x,y,z".split(',').map(s => R.ring.index(R.mapper(s.asNamedSymbol)))
    val drop = "i,j".split(',').map(s => R.ring.index(R.mapper(s.asNamedSymbol)))
    val (p, r) = R.splitInternal(R.toRing("x*y + x*y*z + x*i + x".asTerm), 2, vars, drop)
    R.fromRing(p) shouldBe "x+x*y".asTerm
    R.fromRing(r) shouldBe "i*x+x*y*z".asTerm
  }

  it should "integrate" in {
    val R = new RingsLibrary("t,x,y,z,i,j".split(',').map(_.asTerm))
    val tI = R.ring.index(R.mapper("t".asVariable))
    R.fromRing(R.integrate(tI)(R.toRing("1 + x*y*t + 2*x*t^2".asTerm))) shouldBe "t+1/2*t^2*x*y+2/3*t^3*x".asTerm
  }

  it should "compute the Picard operation" in {
    val R = new RingsLibrary("t,x,y,z,i,j".split(',').map(_.asTerm))
    val ode = R.ODE("t".asVariable, "x,y".split(",").map(_.asVariable), "-y^2,x+y".split(',').map(_.asTerm))
    val x0R = "2*x+0.5*y,x+0.1*y".split(',').map(_.asTerm).map(R.toRing)
    val psR = "x*y*t + 2*x,x*t-y".split(',').map(t => R.toRing(t.asTerm))
    ode.PicardOperation(x0R, psR, 3).zipped.map{case (a, b) => (R.fromRing(a), R.fromRing(b))}.toList shouldBe
      ("1/2*y+2*x+-1*t*y^2".asTerm,"t^2*x*y+-1/3*t^3*x^2".asTerm)::
        ("1/10*y+x+-1*t*y+2*t*x+1/2*t^2*x".asTerm,"1/2*t^2*x*y".asTerm)::Nil
  }

  it should "compute the Picard iteration" in {
    val R = new RingsLibrary("t,x,y,z,i,j".split(',').map(_.asTerm))
    val ode = R.ODE("t".asVariable, "x,y".split(",").map(_.asVariable), "-y^2,x+y".split(',').map(_.asTerm))
    val x0R = "2*x+0.5*y,x+0.1*y".split(',').map(_.asTerm).map(R.toRing)
    ode.PicardIteration(x0R, 4).map(R.fromRing).toList shouldBe
      "1/2*y+2*x+-1/100*t*y^2+-1/5*t*x*y+-1*t*x^2+-3/50*t^2*y^2+-9/10*t^2*x*y+-3*t^2*x^2".asTerm ::
        "1/10*y+x+3/5*t*y+3*t*x+3/10*t^2*y+3/2*t^2*x+-1/200*t^2*y^2+-1/10*t^2*x*y+1/10*t^3*y+-1/2*t^2*x^2+1/2*t^3*x".asTerm ::
        Nil
  }

}