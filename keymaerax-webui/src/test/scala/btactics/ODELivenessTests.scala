package btactics

import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core.Provable
import edu.cmu.cs.ls.keymaerax.infrastruct.PosInExpr
import edu.cmu.cs.ls.keymaerax.pt.ElidingProvable
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

class ODELivenessTests extends TacticTestBase {

  //todo: move
  "vdg" should "unify ODEs correctly" in withQE { _ =>
      val ax = ElidingProvable(Provable.vectorialDG(2))
      val pr = proveBy(
        ("[{x'=1,y'=z,z'=-y & x <= 5}](y*y+z*z)' <= x*(y*y+z*z) + x^2 ->" +
          "([{x'=1 & x <= 5}]x >= 5 <-> [{x'=1,y'=z,z'=-y & x <= 5}]x>=5)").asFormula,
        byUS(ax)
      )
    println(pr)
    pr shouldBe 'proved
  }

  it should "correctly prove affine norm bound" in withQE { _ =>
    val affnorm = (1 to 10).map(ODEInvariance.affine_norm_bound(_))
    affnorm.exists(_.isProved == false) shouldBe false
  }

  "GEx" should "identity affine form for an ODE" in withQE { _ =>
    val ode = "z'=v^2+g()*y+z,y'=f()*x*x+z".asDifferentialProgram

    val res = ODELiveness.affine_form(ode)

    res._1 shouldBe List(List("1", "g()").map(_.asTerm), List("1", "0").map(_.asTerm))
    res._2.head shouldBe "v^2".asTerm
    //Mathematica: res._2.tail.head shouldBe "f()*x^2".asTerm
    //Z3: res._2.tail.head shouldBe "f()*x*x".asTerm
    res._3 shouldBe List("z".asVariable,"y".asVariable)
  }

  it should "derive global existence axiom for nested linear system" in withQE { _ =>
    val ode = "y'= f()*x*x + z, z'= v^2+g() * y + z,x'=v,v'=a".asDifferentialProgram

    val res = ODELiveness.deriveGlobalExistence(ode)

    res.isDefined shouldBe true
    res.get.isProved shouldBe true
    res.get.conclusion.succ(0) shouldBe "<{gextimevar_'=1,y'=f()*x*x+z,z'=v^2+g()*y+z,x'=v,v'=a&true}>gextimevar_>p()".asFormula
  }

  it should "fail to derive global existence axiom for nonlinear system" in withQE { _ =>
    val ode = "y'= f()*x*x + z, z'= v^2+g() * y + z^2,x'=v,v'=a".asDifferentialProgram

    val res = ODELiveness.deriveGlobalExistence(ode)

    res shouldBe None
  }

  it should "derive global existence for large and badly structured system" in withQE { _ =>
    val ode = "ee'=ff, g'=aa^2*g+gg,gg'=g+b^2*g,f'=a,dd'=ee,a'=b,aa'=bb,cc'=dd,e'=f,bb'=cc,d'=e,c'=d,b'=c,ff'=aa".asDifferentialProgram
    //When sorted correctly, this is just two cyclic ODEs with an extra dependency:
    //f'=a,e'=f,d'=e,c'=d,b'=c,a'=b, ff'=aa,ee'=ff,dd'=ee,cc'=dd,bb'=cc,aa'=bb, g'=aa^2*g

    val res = ODELiveness.deriveGlobalExistence(ode)

    res.isDefined shouldBe true
    res.get.isProved shouldBe true
    res.get.conclusion.succ(0) shouldBe "<{gextimevar_'=1,ee'=ff,g'=aa^2*g+gg,gg'=g+b^2*g,f'=a,dd'=ee,a'=b,aa'=bb,cc'=dd,e'=f,bb'=cc,d'=e,c'=d,b'=c,ff'=aa&true}>gextimevar_>p()".asFormula
  }

}
