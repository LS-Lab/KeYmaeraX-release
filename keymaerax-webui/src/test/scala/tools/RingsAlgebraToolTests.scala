package tools

import edu.cmu.cs.ls.keymaerax.btactics.{TacticTestBase, TactixLibrary}
import edu.cmu.cs.ls.keymaerax.btactics.helpers.DifferentialHelper
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tools.ext.{RingsAlgebraTool, RingsLibrary}
import org.scalatest.LoneElement._

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
    res._2 shouldBe "-b()".asTerm
  }

  it should "compute univariate quotient remainder" in withMathematica { _ =>
    val x = "(x^2+x*y)^2+1/5*z*x^3+z*y+1".asTerm
    val y = "x".asVariable
    val tool = new RingsAlgebraTool()

    val res = tool.quotientRemainder(x,y,y)

    res._1 shouldBe "1/5*x^2*z+x*y^2+2*x^2*y+x^3".asTerm
    res._2 shouldBe "1+y*z".asTerm
  }

  it should "return a custom distributive representation" in withMathematica { _ =>
    val R = new RingsLibrary("t,x,y,z,a(),b(),i,j,r0(),r1(),r2()".split(',').map(_.asTerm))
    val mv = R.toRing("4.2*x*t*r1()*r2()^2 + 1.3*t*a()*r1()*r2()^2 + r1() + x*r1() + t*r1()".asTerm)
    R.distributive(mv, "t,r1(),r2()".split(',').map(_.asTerm).toList) shouldBe
      Map(List(0, 1, 0) -> "1+x".asTerm, List(1, 1, 0) -> "1".asTerm, List(1, 1, 2) -> "13/10*a()+21/5*x".asTerm)
  }

  it should "compute the Lie derivative" in withMathematica { _ =>
    val R = new RingsLibrary("t,x,y,z,i,j".split(',').map(_.asTerm))
    val t = "x*y*(x + z*x - 13)/4 + 4*z*z*(x + x^5)".asTerm
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
      "x*(y*((-13)/4))+z^2*(x*4)+x^2*(y*(1/4+z*(1/4))+x^2*(z^2*(x*4)))".asTerm
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
    val R = new RingsLibrary("t,x,y,z,i,j,r0(),r1(),r2()".split(',').map(_.asTerm))
    val ode = R.ODE("t".asVariable,
      "x,y".split(",").map(_.asVariable),
      "r0(),r1()".split(',').map(_.asTerm.asInstanceOf[FuncOf]),
      "-y^2,x+y".split(',').map(_.asTerm))
    val x0R = "2*r0()+0.5*r1(),r0()+0.1*r1()".split(',').map(_.asTerm).map(R.toRing)
    val psR = "r0()*r1()*t + 2*r0(),r0()*t-r1()".split(',').map(t => R.toRing(t.asTerm))
    ode.PicardOperation(x0R, psR, 3).zipped.map { case (a, b) => (R.fromRing(a), R.fromRing(b)) }.toList shouldBe
      ("1/2*r1()+2*r0()+(-t)*r1()^2".asTerm, "t^2*r0()*r1()+(-1)/3*t^3*r0()^2".asTerm) ::
        ("1/10*r1()+r0()+(-t)*r1()+2*t*r0()+1/2*t^2*r0()".asTerm, "1/2*t^2*r0()*r1()".asTerm) :: Nil
  }

  it should "compute the Picard iteration" in {
    val R = new RingsLibrary("t,x,y,z,i,j,r0(),r1(),r2()".split(',').map(_.asTerm))
    val ode = R.ODE("t".asVariable,
      "x,y".split(",").map(_.asVariable),
      "r0(),r1()".split(',').map(_.asTerm.asInstanceOf[FuncOf]),
      "-y^2,x+y".split(',').map(_.asTerm))
    val x0R = "2*r0()+0.5*r1(),r0()+0.1*r1()".split(',').map(_.asTerm).map(R.toRing)
    ode.PicardIteration(x0R, 4).map(R.fromRing).toList shouldBe
      "1/2*r1()+2*r0()+(-1)/100*t*r1()^2+(-1)/5*t*r0()*r1()+(-t)*r0()^2+(-3)/50*t^2*r1()^2+(-9)/10*t^2*r0()*r1()+(-3)*t^2*r0()^2".asTerm ::
        "1/10*r1()+r0()+3/5*t*r1()+3*t*r0()+3/10*t^2*r1()+3/2*t^2*r0()+(-1)/200*t^2*r1()^2+(-1)/10*t^2*r0()*r1()+1/10*t^3*r1()+(-1)/2*t^2*r0()^2+1/2*t^3*r0()".asTerm ::
        Nil
  }

  it should "normalize with Rings" in withMathematica { _ =>
    val R = new RingsLibrary("t,x,y,z,a(),b(),i,j,r0(),r1(),r2()".split(',').map(_.asTerm))
    val seq = "A(), B() ==> C(), (t + x)*(i^4+r1()) - 234 <= 234 + a(), D()".asSequent
    val res = proveBy(seq, R.normalizeLessEquals(TactixLibrary.QE)(2))
    res.subgoals.loneElement.ante shouldBe seq.ante
    res.subgoals.loneElement.succ shouldBe seq.succ.updated(1, "0<=468+a()+(-x)*r1()+(-t)*r1()+(-i^4)*x+(-i^4)*t".asFormula)
  }

}