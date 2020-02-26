package btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.BelleThrowable
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core.Provable
import edu.cmu.cs.ls.keymaerax.infrastruct.PosInExpr
import edu.cmu.cs.ls.keymaerax.pt.ElidingProvable
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.btactics.ODELiveness._

class ODELivenessTests extends TacticTestBase {

  //todo: move
  "vdg" should "unify ODEs correctly" in withQE { _ =>
      val ax = ElidingProvable(Provable.vectorialDG(2)._1)
      val pr = proveBy(
        ("[{y'=z,z'=-y,x'=1 & x <= 5}](y*y+z*z)' <= x*(y*y+z*z) + x^2 ->" +
          "([{x'=1 & x <= 5}]x >= 5 <- [{y'=z,z'=-y,x'=1 & x <= 5}]x>=5)").asFormula,
        byUS(ax)
      )
    println(pr)
    pr shouldBe 'proved
  }

  it should "correctly prove affine norm bound" in withQE { _ =>
    val affnorm = (1 to 5).map(ODEInvariance.affine_norm_bound)
    affnorm.exists(_.isProved == false) shouldBe false
  }

  it should "vDG on left and right of sequent" in withQE { _ =>
    val seq = "[{z'=100}]z=1, <{a'=x+y+z}>a=1 ==> < {x'=1} > 1+1 = 3 , [{y'=2}] 1+1=0".asSequent

    val pr = proveBy(seq,
      // nonlinear ghosts can always be added to boxes on left and diamonds on right
      vDG("z'=z^100*y,y'=z*y^2".asDifferentialProgram)(1) &
      vDG("a'=a^2+b^3+x+y+100".asDifferentialProgram)(-1) &
      // only affine ones can be added to diamonds on left and boxes on right
      vDG("z'=y*a*z+a+b+w,w'=w+z".asDifferentialProgram)(2) &
      vDG("b'=a*b+b*a+1,c'=b+c".asDifferentialProgram)(-2)
    )

    pr.subgoals.length shouldBe 1
    pr.subgoals(0) shouldBe
    "[{a'=a^2+b^3+x+y+100,z'=100&true}]z=1, <{b'=a*b+b*a+1,c'=b+c,a'=x+y+z&true}>a=1 ==> <{z'=z^100*y,y'=z*y^2,x'=1&true}>1+1=3, [{z'=y*a*z+a+b+w,w'=w+z,y'=2&true}]1+1=0".asSequent
  }

  it should "get instantiated vdg" in withQE { _ =>
    val vdginst = getVDGinst("v'=v^2+z,z'=v*y+z".asDifferentialProgram)
    println(vdginst)

    //todo: parsing support
    //vdginst._1 shouldBe 'proved
    //vdginst._1.conclusion shouldBe "==> [{v'=v^2+z,z'=v*y+z,dummy_{|v,z|}&q(|v,z|)}]2*(v*(v^2+z)+z*(v*y+z))<=a_(|v,z|)*(v*v+z*z)+b_(|v,z|)->[{v'=v^2+z,z'=v*y+z,dummy_{|v,z|}&q(|v,z|)}]p(|v,z|)->[{dummy_{|v,z|}&q(|v,z|)}]p(|v,z|)".asSequent

    //vdginst._2 shouldBe 'proved
    //vdginst._2.conclusion shouldBe "==> [{dummy_{|v,z|}&q(|v,z|)}]p(|v,z|)->[{v'=v^2+z,z'=v*y+z,dummy_{|v,z|}&q(|v,z|)}]p(|v,z|)".asSequent
  }

  "GEx" should "identity affine form for an ODE" in withQE { _ =>
    val ode = "z'=v^2+g()*y+z,y'=f()*x*x+z".asDifferentialProgram

    val res = affine_form(ode)

    res._1 shouldBe List(List("1", "g()").map(_.asTerm), List("1", "0").map(_.asTerm))
    res._2.head shouldBe "v^2".asTerm
    //Mathematica: res._2.tail.head shouldBe "f()*x^2".asTerm
    //Z3: res._2.tail.head shouldBe "f()*x*x".asTerm
    res._3 shouldBe List("z".asVariable,"y".asVariable)
  }

  it should "derive global existence axiom for nested linear system" in withQE { _ =>
    val ode = "y'= f()*x*x + z, z'= v^2+g() * y + z,x'=v,v'=a".asDifferentialProgram

    val res = deriveGlobalExistence(ode)

    res.isDefined shouldBe true
    res.get.isProved shouldBe true
    res.get.conclusion.succ(0) shouldBe "<{gextimevar_'=1,y'=f()*x*x+z,z'=v^2+g()*y+z,x'=v,v'=a&true}>gextimevar_>p()".asFormula
  }

  it should "fail to derive global existence axiom for nonlinear system" in withQE { _ =>
    val ode = "y'= f()*x*x + z, z'= v^2+g() * y + z^2,x'=v,v'=a".asDifferentialProgram

    val res = deriveGlobalExistence(ode)

    res shouldBe None
  }

  it should "derive global existence for large and badly structured system" in withQE { _ =>
    val ode = "ee'=ff, g'=aa^2*g+gg,gg'=g+b^2*g,f'=a,dd'=ee,a'=b,aa'=bb,cc'=dd,e'=f,bb'=cc,d'=e,c'=d,b'=c,ff'=aa".asDifferentialProgram
    //When sorted correctly, this is just two cyclic ODEs with an extra dependency:
    //f'=a,e'=f,d'=e,c'=d,b'=c,a'=b, ff'=aa,ee'=ff,dd'=ee,cc'=dd,bb'=cc,aa'=bb, g'=aa^2*g

    val res = deriveGlobalExistence(ode)

    res.isDefined shouldBe true
    res.get.isProved shouldBe true
    res.get.conclusion.succ(0) shouldBe "<{gextimevar_'=1,ee'=ff,g'=aa^2*g+gg,gg'=g+b^2*g,f'=a,dd'=ee,a'=b,aa'=bb,cc'=dd,e'=f,bb'=cc,d'=e,c'=d,b'=c,ff'=aa&true}>gextimevar_>p()".asFormula
  }

  "odeReduce" should "automatically delete irrelevant ODEs and stabilize" in withQE { _ =>
    val seq = "d >0 , 1+1=2 ==> 1+1=3, <{a'=b+c+e*5, x'=x+1, v'=2, e' = a+e, b'=c+f(),c'=d+e() & c <= 5}> x+v<= 5, 2+2=1".asSequent

    val pr = proveBy(seq, odeReduce(2))

    pr.subgoals.length shouldBe 1
    pr.subgoals(0) shouldBe "d>0, 1+1=2  ==> 1+1=3, <{x'=x+1,c'=d+e(),v'=2&c<=5}>x+v<=5, 2+2=1".asSequent
  }

  it should "throw a helpful error when it gets stuck" in withQE { _ =>
    val seq = "==> <{a'=b,b'=c,c'=d,d'=d^2+f,f'=f,e'=5 & e <= 5}> e<= 5".asSequent

    // how to catch directly ??
    val res = try {
      proveBy(seq, odeReduce(1))
      true shouldBe false //bad
    } catch {
      case e:BelleThrowable =>
        println(e.getMessage)
        true
        // it should have this error:
        //"because odeReduce failed to autoremove: {d'=d^2+f}. Try to add an assumption of this form to the antecedents: [{d'=d^2+f,f'=f,e'=5&e<=5}]2*(d*(d^2+f))<=a_(|d|)*(d*d)+b_(|d|)"
    }
  }

  it should "continue using assms" in withQE { _ =>
    val seq = "[{d'=d^2+f,f'=f,e'=5&e<=5}] 2*(d*(d^2+f)) <= 1*(d*d)+5 ==> <{a'=b,b'=c,c'=d,d'=d^2+f,f'=f,e'=5 & e <= 5}> e<= 5".asSequent

    val pr = proveBy(seq, odeReduce(1))
    pr.subgoals.length shouldBe 1
    pr.subgoals(0) shouldBe "[{d'=d^2+f,f'=f,e'=5&e<=5}]2*(d*(d^2+f))<=1*(d*d)+5  ==>  <{e'=5&e<=5}>e<=5".asSequent
  }

  "kdomd" should "refine ODE postcondition (with auto DC of assumptions)" in withQE { _ =>
    val seq = "[{x'=x,v'=v}] v <= 100 , a > 0, [{x'=x,v'=v&x+v^2<=6}] x <= 1 , b < 0, [{x'=x,v'=v&x=1}] 1+1=2 ==> <{x'=x, v'=v}> x+v^2 > 5".asSequent

    val pr = proveBy(seq, kDomainDiamond("x > 5".asFormula)(1))

    println(pr)

    pr.subgoals.length shouldBe 2
    pr.subgoals(0) shouldBe "[{x'=x,v'=v&true}]v<=100, a>0, [{x'=x,v'=v&x+v^2<=6}]x<=1, b < 0, [{x'=x,v'=v&x=1}]1+1=2 ==> <{x'=x,v'=v&true}>x>5".asSequent
    pr.subgoals(1) shouldBe "[{x'=x,v'=v&true}]v<=100, a>0, [{x'=x,v'=v&x+v^2<=6}]x<=1, b < 0, [{x'=x,v'=v&x=1}]1+1=2 ==> [{x'=x,v'=v&((true&!x+v^2>5)&v<=100)&x<=1}](!x>5)".asSequent
  }

  "ddr" should "refine ODE domains (with auto DC of assumptions)" in withQE { _ =>
    val seq = "a() > 0, [{x'=x,v'=v}]v>=0 , v = 1 ==> <{x'=x, v'=v & v >= 0}> x+v^2 > 5".asSequent

    val pr = proveBy(seq, dDR("x > 100 & v <= 5".asFormula)(1))

    println(pr)

    pr.subgoals.length shouldBe 2
    pr.subgoals(0) shouldBe "a()>0, [{x'=x,v'=v&true}]v>=0, v=1  ==>  <{x'=x,v'=v&x>100&v<=5}>x+v^2>5".asSequent
    pr.subgoals(1) shouldBe "a()>0, [{x'=x,v'=v&true}]v>=0, v=1  ==>  [{x'=x,v'=v&(x>100&v<=5)&v>=0}]v>=0".asSequent
  }

  "liveness" should "support liveness proofs by hand (1)" in withMathematica { _ =>
    // FM'19 linear ODE example
    val fml = "u^2+v^2 = 1 -> <{u'=-v-u, v'=u-v}> (1/4 <= max(abs(u),abs(v)) & max(abs(u),abs(v)) <= 1/2)".asFormula

    val pr = proveBy(fml,
      implyR(1) &
        kDomainDiamond("u^2+v^2=1/4".asFormula)(1) <(
          skip,
          dW(1) & QE
        ) &
        kDomainDiamond("u^2+v^2<=1/4".asFormula)(1) <( //@todo: make axiomatic IVT
          skip,
          ODE(1) //@todo: Z3 simplifier broken
        ) &
        // Wrap into tactic
        cut("\\exists t t=0".asFormula) <( existsL(-2) , cohideR(2) & QE) &
        vDG("t'=1".asDifferentialProgram)(1) &
        // same, actually p = 1
        cut("\\exists p u^2+v^2=p".asFormula) <( existsL(-3) , cohideR(2) & QE) &

        // Not great
        kDomainDiamond("t > 2*p".asFormula)(1) <(
          skip,
          dC("p-1/2*t >= u^2+v^2-1/4".asFormula)(1) <( ODE(1), ODE(1) )
        ) &

        //Wrap into global existence tactic:
        odeReduce(1) &
        solve(1) & QE
    )

    pr shouldBe 'proved
  }

  it should "support liveness proofs by hand (2)" in withMathematica { _ =>
    // FM'19 nonlinear ODE example
    val fml = "u^2+v^2 = 1 -> <{u'=-v-u*(1/4-u^2-v^2), v'=u-v*(1/4-u^2-v^2)}> (u^2+v^2 >= 2)".asFormula

    val pr = proveBy(fml,
      implyR(1) &

        // Wrap into tactic
        cut("\\exists t t=0".asFormula) <( existsL(-2) , cohideR(2) & QE) &
        vDG("t'=1".asDifferentialProgram)(1) &
        // same, actually p = 1
        cut("\\exists p u^2+v^2=p".asFormula) <( existsL(-3) , cohideR(2) & QE) &


        //Keep compactness assumption around, wrap into tactic
        cut("[{t'=1, u'=-v-u*(1/4-u^2-v^2), v'=u-v*(1/4-u^2-v^2)}] !(u^2+v^2 >= 2)".asFormula) <(
          skip,
          useAt("<> diamond",PosInExpr(1::Nil))(1) & prop
        ) &

        // cut some extra information that will get auto DC-ed in K<&>
        cut("[{t'=1, u'=-v-u*(1/4-u^2-v^2), v'=u-v*(1/4-u^2-v^2)}] u^2+v^2>=1".asFormula) <(
          skip,
          hideL(-4) & cohideOnlyR(2) & ODE(1)
        ) &
        // Not great
        kDomainDiamond("t > 2/3*p".asFormula)(1)
          <(
          skip,
          dC("p-3/2*t >= 2- (u^2+v^2)".asFormula)(1) <( ODE(1), hideL(-5) & hideL(-4) & ODE(1)) //todo: ODE fix! ignore box stuff in antecedents
          )
        &

        // Not great either: nasty ODE order!
        cut("[{u'=-v-u*(1/4-u^2-v^2),v'=u-v*(1/4-u^2-v^2),t'=1&true}]2*(u*(-v-u*(1/4-u^2-v^2))+v*(u-v*(1/4-u^2-v^2)))<=0*(u*u+v*v)+8".asFormula) <(
          odeReduce(1) & cohideR(1) & solve(1) & QE,
          cohideOnlyR(2) & skip //todo: need to unify modulo ODE reorder here
        )

    )

    println(pr)
  }
}
