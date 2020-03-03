package btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.BelleThrowable
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.{AntePosition, PosInExpr, SuccPosition}
import edu.cmu.cs.ls.keymaerax.pt.ElidingProvable
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.btactics.ODELiveness._

import scala.collection.immutable.Nil

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
    val affnorm = (1 to 4).map(ODEInvariance.affine_norm_bound)
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

  "compatibility" should "automatically match by compatibility" in withQE { _ =>
    //The first and last assumptions are compatible and can be automatically added
    val seq = "[{x'=1 & x < 6}]x>1,[{x'=1 & x < 4}]x>4, [{v'=2,x'=1,a'=b}]v<=5, [{v'=2,x'=1}]x+z<=5 ==> a > 0, [{x'=1,v'=2,a'=a^2+x+v^2 & x < 5}]1+1=2".asSequent

    val pr = proveBy(seq, compatCuts(2))

    println(pr)

    pr.subgoals.length shouldBe 1
    pr.subgoals(0) shouldBe "[{x'=1&x < 6}]x>1, [{x'=1&x < 4}]x>4, [{v'=2,x'=1,a'=b&true}]v<=5, [{v'=2,x'=1&true}]x+z<=5  ==>  a > 0, [{x'=1,v'=2,a'=a^2+x+v^2&(x < 5&x>1)&x+z<=5}]1+1=2".asSequent
  }

  "odeReduce" should "automatically delete irrelevant ODEs and stabilize" in withQE { _ =>
    val seq = "d >0 , 1+1=2 ==> 1+1=3, <{a'=b+c+e*5, x'=x+1, v'=2, e' = a+e, b'=c+f(),c'=d+e() & c <= 5}> x+v<= 5, 2+2=1".asSequent

    val pr = proveBy(seq, odeReduce(strict = true)(2))

    pr.subgoals.length shouldBe 1
    pr.subgoals(0) shouldBe "d>0, 1+1=2  ==> 1+1=3, <{x'=x+1,c'=d+e(),v'=2&c<=5}>x+v<=5, 2+2=1".asSequent
  }

  it should "throw a helpful error when it gets stuck" in withQE { _ =>
    val seq = "==> <{a'=b,b'=c,c'=d,d'=d^2+f,f'=f,e'=5 & e <= 5}> e<= 5".asSequent

    //the [Exception] thrownBy ??? should have message ""
    // how to catch directly ??
    val res = try {
      proveBy(seq, odeReduce(strict = true)(1))
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

    val pr = proveBy(seq, odeReduce(strict = true)(1))
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

  "ddx" should "prove diamonds that are true in the beginning" in withQE { _ =>
    val fml = "<{x'=x^2,v'=v^3+x+v+v+a()+b+c & b*x^2<= v+c+a()}>x+v<=a()".asFormula

    val pr = proveBy(fml,
      dDX(1)
    )

    println(pr)
    pr.subgoals.length shouldBe 1
    pr.subgoals(0) shouldBe "==> b*x^2<=v+c+a()&x+v<=a()".asSequent
  }

  "liveness" should "support liveness proofs by hand (1)" in withMathematica { _ =>
    // FM'19 linear ODE example
    val fml = "u^2+v^2 = 1 -> <{u'=-v-u, v'=u-v}> (1/4 <= max(abs(u),abs(v)) & max(abs(u),abs(v)) <= 1/2)".asFormula

    val pr = proveBy(fml,
      implyR(1) &
        kDomainDiamond("u^2+v^2<=1/4".asFormula)(1) <(
          skip,
          ODE(1)
          // ODE is smart enough to do this in one step without an IVT argument (but that can be done too)
        ) &
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
        odeReduce(strict = true)(1) &
        solve(1) & QE
    )
    println(pr)

    pr shouldBe 'proved
  }

  it should "support liveness proofs by hand (2)" in withQE { _ =>
    // FM'19 nonlinear ODE example
    val fml = "u^2+v^2 = 1 -> <{u'=-v-u*(1/4-u^2-v^2), v'=u-v*(1/4-u^2-v^2)}> (u^2+v^2 >= 2)".asFormula

    val pr = proveBy(fml,
      implyR(1) &

        //Keep compactness assumption around, wrap into tactic
        cut("[{u'=-v-u*(1/4-u^2-v^2), v'=u-v*(1/4-u^2-v^2)}] !(u^2+v^2 >= 2)".asFormula) <(
          skip,
          useAt("<> diamond",PosInExpr(1::Nil))(1) & prop
        ) &

        // cut some extra information that will get auto DC-ed in K<&>
        cut("[{u'=-v-u*(1/4-u^2-v^2), v'=u-v*(1/4-u^2-v^2)}] u^2+v^2>=1".asFormula) <(
          skip,
          hideL(-2) & cohideOnlyR(2) & ODE(1)
        ) &

        // Wrap into tactic
        cut("\\exists t t=0".asFormula) <( existsL(-4) , cohideR(2) & QE) &
        vDG("t'=1".asDifferentialProgram)(1) &
        // same, actually p = 1
        cut("\\exists p u^2+v^2=p".asFormula) <( existsL(-5) , cohideR(2) & QE) &

        // Not great
        kDomainDiamond("t > 2/3*p".asFormula)(1)
          <(
          skip,
          dC("p-3/2*t >= 2- (u^2+v^2)".asFormula)(1) <( ODE(1), hideL(-3) & hideL(-2) & ODE(1)) //todo: ODE fix! ignore box stuff in antecedents
          )
        &

        // Not great either: nasty ODE order!
        cut("[{u'=-v-u*(1/4-u^2-v^2),v'=u-v*(1/4-u^2-v^2),t'=1&true}]2*(u*(-v-u*(1/4-u^2-v^2))+v*(u-v*(1/4-u^2-v^2)))<=0*(u*u+v*v)+8".asFormula) <(
          odeReduce(strict = true)(1) & cohideR(1) & solve(1) & QE,
          cohideOnlyR(2) &
          compatCuts(1) & dW(1) & QE
        )

    )

    println(pr)
    pr shouldBe 'proved
  }

  it should "add liveness support (1)" in withMathematica { _ =>
    // FM'19 linear ODE example
    val fml = "u^2+v^2 = 1 -> <{u'=-v-u, v'=u-v}> (1/4 <= max(abs(u),abs(v)) & max(abs(u),abs(v)) <= 1/2)".asFormula

    val pr = proveBy(fml,
      implyR(1) &
        // This rephrasing seems neessary
        kDomainDiamond("u^2+v^2<=1/4".asFormula)(1) <(
          skip,
          ODE(1)
        ) &
        dV("1/2".asTerm)(1)
    )
    println(pr)
    pr shouldBe 'proved
  }

  it should "add liveness support (2)" in withQE { _ =>
    // FM'19 nonlinear ODE example
    val fml = "u^2+v^2 = 1 -> <{u'=-v-u*(1/4-u^2-v^2), v'=u-v*(1/4-u^2-v^2)}> (u^2+v^2 >= 2)".asFormula

    val pr = proveBy(fml,
      implyR(1) &
        //Keep compactness assumption around
        saveBox(1) &
        // cut some extra information that will get auto DC-ed in K<&>
        cut("[{u'=-v-u*(1/4-u^2-v^2), v'=u-v*(1/4-u^2-v^2)}] u^2+v^2>=1".asFormula) <(
          skip,
          hideL(-2) & cohideOnlyR(2) & ODE(1)
        ) &
        dV("3/2".asTerm)(1) &
        cut("[{u'=-v-u*(1/4-u^2-v^2),v'=u-v*(1/4-u^2-v^2),timevar_'=1&true}]2*(u*(-v-u*(1/4-u^2-v^2))+v*(u-v*(1/4-u^2-v^2)))<=0*(u*u+v*v)+8".asFormula) <(
          odeReduce(strict = true)(1) & cohideR(1) & solve(1) & QE,
          cohideOnlyR(2) & compatCuts(1) & dW(1) & QE
        )
    )
    println(pr)
    pr shouldBe 'proved
  }

  it should "work on simple examples (1)" in withQE { _ =>
    val pr = proveBy("a>0 ==> <{x'=a}>x>=b()".asSequent,
      dV("a".asTerm)(1))

    val pr2 = proveBy("c=1 ==> a<=0 , <{x'=a+c}>x>=b()".asSequent,
      dV("a".asTerm)(2))

    println(pr)
    println(pr2)
    pr shouldBe 'proved
    pr2 shouldBe 'proved
  }

  it should "work on FM'15 Example 11" in withMathematica { _ =>
    val X0 = "x2 > 0 & x1 >= -1/4 & x1 <= 1/4 & (x1^2+x2^2-1)^2<=1/30".asFormula
    val XT = "x2 < 0 & x1 >= -1/4 & x1 <= 1/4 & (x1^2+x2^2-1)^2<=1/30".asFormula
    val ode = "{x1'=x2-x1*(x1^2+x2^2-1), x2'=-x1-x2*(x1^2+x2^2-1)}".asDifferentialProgram
    val dom = "x1<=2 & x1>=-2 & x2<=2 & x2>=-2".asFormula

    val S1 = And(Not(XT), "x1 >= -1/4 & (x1^2+x2^2-1)^2<=1/30".asFormula)
    val p1 = "-(x1 - 6/5)^2 + (x1 - x2 - 2)^2 +10".asTerm

    val S2 = And(Not(X0), "x1 <= 1/4 & (x1^2+x2^2-1)^2<=1/30".asFormula)
    val p2 = "-(-x1 - 6/5)^2 + (-x1 + x2 - 2)^2 +10".asTerm

    val pr1 = proveBy( Imply(X0, Diamond(ODESystem(ode,dom),XT)) ,
      implyR(1) &
        // This part is an invariant, so cut it as context
        cut(Box(ODESystem(ode,True),"(x1^2+x2^2-1)^2<=1/30".asFormula)) <(
          skip,
          cohideOnlyR(2) & ODE(1)
        ) &
        // Thanks to the invariant, the avoid constraint is trivial with compatible cuts
        dDR(True)(1) <(
          skip,
          dW(1) & QE //or: ODE(1)
        ) &
        // Use a staging set that cannot be left without reaching the target
        kDomainDiamond(Not(S1))(1) <(
          skip,
          dC("x1>=-1/4".asFormula)(1) <(
            ODE(1),
            ODE(1)
          )
        ) &
        // Save the staging set as context
        saveBox(1) &
        // Use a progress function
        kDomainDiamond(Less(p1, Number(0)))(1) <(
          dV("0.1".asTerm)(1), //0.1 arbitrarily chosen here...
          dW(1) & QE
        )
        &
        // compact domain bound on Lie derivative
        cut("[{x1'=x2-x1*(x1^2+x2^2-1),x2'=-x1-x2*(x1^2+x2^2-1),timevar_'=1&true}]2*(x1*(x2-x1*(x1^2+x2^2-1))+x2*(-x1-x2*(x1^2+x2^2-1)))<=0*(x1*x1+x2*x2)+10000".asFormula) <(
          odeReduce(strict = true)(1) & cohideR(1) & solve(1) & QE,
          cohideOnlyR(2) & compatCuts(1) & dW(1) & QE
        )
    )

    val pr2 = proveBy( Imply(XT, Diamond(ODESystem(ode,dom),X0)) ,
      implyR(1) &
        // This part is an invariant, so cut it as context
        cut(Box(ODESystem(ode,True),"(x1^2+x2^2-1)^2<=1/30".asFormula)) <(
          skip,
          cohideOnlyR(2) & ODE(1)
        ) &
        // Thanks to the invariant, the avoid constraint is trivial with compatible cuts
        dDR(True)(1) <(
          skip,
          dW(1) & QE //or: ODE(1)
        ) &
        // Use a staging set that cannot be left without reaching the target
        kDomainDiamond(Not(S2))(1) <(
          skip,
          dC("x1<=1/4".asFormula)(1) <(
            ODE(1),
            ODE(1)
          )
        ) &
        // Save the staging set as context
        saveBox(1) &
        // Use a progress function
        kDomainDiamond(Less(p2, Number(0)))(1) <(
          dV("0.1".asTerm)(1), //0.1 arbitrarily chosen here...
          dW(1) & QE
        ) &
        // compact domain bound on Lie derivative
        cut("[{x1'=x2-x1*(x1^2+x2^2-1),x2'=-x1-x2*(x1^2+x2^2-1),timevar_'=1&true}]2*(x1*(x2-x1*(x1^2+x2^2-1))+x2*(-x1-x2*(x1^2+x2^2-1)))<=0*(x1*x1+x2*x2)+10000".asFormula) <(
          odeReduce(strict = true)(1) & cohideR(1) & solve(1) & QE,
          cohideOnlyR(2) & compatCuts(1) & dW(1) & QE
        )
    )

    println(pr1)
    println(pr2)
    pr1 shouldBe 'proved
    pr2 shouldBe 'proved
  }

  it should "work on FM'15 Example 12" in withMathematica { _ =>
    val X0 = "x2 - x1 < 0".asFormula
    val XT = "x2 - x1 = 0".asFormula
    val ode = "{x1'=-1, x2'=(x2-x1)^2}".asDifferentialProgram
    val dom = "true".asFormula

    val pr = proveBy( Imply(X0, Diamond(ODESystem(ode,dom),XT)) ,
      implyR(1) &
      kDomainDiamond("x2 - x1 >=0".asFormula)(1) <(
        saveBox(1) &
        dV("1".asTerm)(1) &
        // Proving bound on derivative
        //todo: cut needs to support old(.) directly
        cut("\\exists oldv oldv = x2-x1".asFormula) <(
          existsL(-5),
          cohideR(2) & QE
        ) &
        cut("[{x1'=-1,x2'=(x2-x1)^2,timevar_'=1&true}](x2-x1>=oldv)".asFormula) <(
          skip,
          cohideOnlyR(2) & hideL(-2) & ODE(1)
        ) &
        cut("[{x2'=(x2-x1)^2,x1'=-1,timevar_'=1&true}]2*(x2*(x2-x1)^2)<= oldv^2*(x2*x2)+oldv^2".asFormula) <(
          odeReduce()(1) & cohideR(1) & solve(1) & QE,
          cohideOnlyR(2) & compatCuts(1) & dW(1) & QE
        )
        ,
        ODE(1)
      )
    )

    println(pr)
    pr shouldBe 'proved
  }

  it should "support higher derivatives" in withQE { _ =>
    // note: postcondition x > j fails because of a renaming bug
    val pr = proveBy("j > 0 ==> <{d'=c, x'=v, v'=a, a'=j, c'=-d}> x > 100".asSequent,
      // Should be old(x), etc.
      higherdV(List("x-100","v","a/2","j/6").map(_.asTerm))(1) &
      // This is manual by design, although this is probably the main way to do it
      dC("a>=2*coeff2+6*coeff3*timevar_".asFormula)(1) <( skip, dI('full)(1) ) &
      dC("v>=coeff1+2*coeff2*timevar_+3*coeff3*timevar_^2".asFormula)(1) <( dI('full)(1), dI('full)(1) )
    )

    println(pr)
    pr shouldBe 'proved
  }

  it should "support semialgebraic dV (FM'15, Ex 15)" in withMathematica { _ =>
    val pr = proveBy("<{x1'=-x1,x2'=-x2}> (x1<=1 & x1>=-1 & x2<=1 &x2>=-1)".asFormula,
      semialgdV("1".asTerm)(1)
    )

    println(pr)
    pr shouldBe 'proved
  }

  it should "support semialgebraic dV (disjunctive)" in withMathematica { _ =>
    val pr = proveBy("v!=0 -> <{x'=v}> (x>100 | x < 100)".asFormula,
      implyR(1) &
        //encode abs(v)
        cut("\\exists absv (absv = abs(v))".asFormula) < (
          existsL(-2),
          hideR(1) & QE
        ) &
        semialgdV("absv".asTerm)(1)
    )

    println(pr)
    pr shouldBe 'proved
  }

  it should "prove RAL goal reachability" in withQE { _ =>
    val seq = "v>0, vl<=v, v<=vh, a=0, eps>0, k*eps^2-2*eps < k*(x^2+y^2)-2*x, k*(x^2+y^2)-2*x < k*eps^2-2*eps, y>0 ==> <{x'=-v*k*y, y'=v*(k*x-1), v'=0 & v>=0}>( x^2+y^2<=eps^2 & (vl<=v & v<=vh) )".asSequent

    val pr = proveBy(seq,
      // todo: replace with old
      cut("\\exists oldv (oldv = v)".asFormula) < (
        existsL('Llast),
        hideR(1) & QE
      ) &
      // known invariants: v stays constant, and robot always on annulus
      cut("[{x'=-v*k*y, y'=v*(k*x-1), v'=0}]( v=oldv & k*eps^2-2*eps < k*(x^2+y^2)-2*x & k*(x^2+y^2)-2*x < k*eps^2-2*eps) ".asFormula) <(
        skip,
        hideR(1) & ODE(1)
      ) &
      // dDR gets rid of domain constraint easily thanks to builtin compatible cuts
      dDR(True)(1) <(
        skip,
        dW(1) & QE
      ) &
      // K<&> simplifies postcondition again thanks to builtin compatible cuts
      kDomainDiamond("x^2+y^2<=eps^2".asFormula)(1) <(
        skip,
        dW(1) & QE
      ) &
      // todo: replace with old
      cut("\\exists oldhalfy (oldhalfy = y/2)".asFormula) < (
        existsL('Llast),
        hideL('Llast) & hideR(1) & QE
      ) &
      // As long as the goal is not yet reached, y will stay positive
      cut("[{x'=-v*k*y,y'=v*(k*x-1),v'=0&!x^2+y^2<=eps^2}] y > oldhalfy".asFormula)<(
        skip,
        hideR(1) & compatCuts(1) & ODE(1) //compatCuts super useful here
      ) &
      dV("2*oldv*oldhalfy".asTerm)(1)
    )

    println(pr)
    pr shouldBe 'proved
  }

  it should "prove RAL velocity bounds" in withMathematica { _ =>
    // abridged proof
    val seq = "v>=0, 0<vl, vl<vh, A>0, B>0 ==> \\exists a ( (a <= A & -B <= a) & <{x'=-v*k*y, y'=v*(k*x-1), v'=a & v>=0}>( vl<=v & v<=vh ))".asSequent

    val pr = proveBy(seq,
      // Trichotomy
      cut("v < vl|vl<=v&v<=vh|vh < v".asFormula) <(
        skip,
        hideR(1) & QE
      ) &
      orL('Llast) <(
        // v < vl, pick a = A
        existsR("A".asTerm)(1) & andR(1) <( QE,
          kDomainDiamond("v >= vl".asFormula)(1) <(
            skip,
            ODE(1) //note the slightly tricky refinement here (using IVT)
          ) &
          dDR(True)(1) <(
            skip,
            ODE(1)
          ) &
          dV("A".asTerm)(1)
        ),
        orL('Llast) <(
          //a=0
          dDX(1, 0::1::Nil) & QE,
          // In this easy case, solve would do it after removing extra ODEs
          //existsR("0".asTerm)(1) & andR(1) <( QE,
          // odeReduce()(1) & solve(1) & QE
          //a=-B
          existsR("-B".asTerm)(1) & andR(1) <( QE,
            kDomainDiamond("v <= vh".asFormula)(1) <(
              skip,
              ODE(1) //note the slightly tricky refinement here (using IVT)
            ) &
            closedRef("true".asFormula)(1) <(
              dV("B".asTerm)(1),
              QE,
              ODE(1)
            )

            // This needs some topological refinement in order to do without solving
          )
        )
      )
    )

    println(pr)
    pr shouldBe 'proved
  }

}
