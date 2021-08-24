package btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.TacticStatistics
import edu.cmu.cs.ls.keymaerax.btactics.SwitchedSystems._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import testHelper.KeYmaeraXTestTags.TodoTest

class SwitchedSystemsTests extends TacticTestBase {

  "state switch" should "return arbitrary switching models" in withMathematica { _ =>
    val ode1 = ODESystem("x'=-x".asDifferentialProgram, True)
    val ode2 = ODESystem("x'=-x^3".asDifferentialProgram, True)
    val ode3 = ODESystem("x'=-x^5".asDifferentialProgram, True)

    val ss = stateSwitch(List(ode1, ode2, ode3))

    println(ss)
    ss shouldBe "{{{x'=-x}++{x'=-x^3}}++{x'=-x^5}}*".asProgram
  }

  it should "return arbitrary switching models with time" in withMathematica { _ =>
    val ode1 = ODESystem("x'=-x".asDifferentialProgram, True)
    val ode2 = ODESystem("x'=-x^3".asDifferentialProgram, True)
    val ode3 = ODESystem("x'=-x^5".asDifferentialProgram, True)

    val ss = stateSwitch(List(ode1, ode2, ode3), Some(Variable("t_")))

    println(ss)
    ss shouldBe "{{{t_'=1,x'=-x}++{t_'=1,x'=-x^3}}++{t_'=1,x'=-x^5}}*".asProgram
  }

  it should "return state-dependent switching models" in withMathematica { _ =>
    val ode1 = ODESystem("x'=-x".asDifferentialProgram, "x > 0".asFormula)
    val ode2 = ODESystem("x'=-x^3".asDifferentialProgram, "x > 0".asFormula)
    val ode3 = ODESystem("x'=-x^5".asDifferentialProgram, "x <= 0".asFormula)

    val ss = stateSwitch(List(ode1, ode2, ode3), Some(Variable("t_")))

    println(ss)
    ss shouldBe "{{{t_'=1,x'=-x & x > 0}++{t_'=1,x'=-x^3 & x > 0}}++{t_'=1,x'=-x^5 & x <= 0}}*".asProgram
  }

  it should "check ODE active in domain" in withMathematica { _ =>

    val ode1 = ODESystem("x'=-1".asDifferentialProgram, "x > 0".asFormula)
    val ode2 = ODESystem("x'=-1".asDifferentialProgram, "x >= 0".asFormula)
    val ode3 = ODESystem("x'=-1".asDifferentialProgram, "x > 0".asFormula)

    odeActive(ode1).isEmpty shouldBe false //Some((Unable to leave ODE {x'=(-1)&x>0},Map(x -> 0)))
    odeActive(ode2) shouldBe None
    odeActive(ode1, "x > 1".asFormula) shouldBe None //Bad point is excluded by global domain
  }

  it should "check activity for recitation 4 example" in withMathematica { _ =>

    val ode1 = "{x'=v & l <= x & x <= r}".asProgram.asInstanceOf[ODESystem]
    val ode2 = "{x'=v & !(l <= x & x <= r)}".asProgram.asInstanceOf[ODESystem]

    odeActive(ode1) shouldBe None
    //Bad event trigger domain separation:
    //Some((Unable to enter ODE {x'=v&!(l<=x&x<=r)},Map(l -> 0, r -> 1, v -> (-1), x -> 0)))
    odeActive(ode2).isEmpty shouldBe false
    //The other side is problematic too:
    //Some((Unable to enter ODE {x'=v&!(l<=x&x<=r)},Map(l -> 0, r -> 1, v -> 1, x -> 1)))
    odeActive(ode2, "v >= 0".asFormula).isEmpty shouldBe false
  }

  it should "check event triggering" in withMathematica { _ =>

    val ode1 = "{x'=v, v'=-g & x >= 0 & x <= 5}".asProgram.asInstanceOf[ODESystem]
    val ode2 = "{x'=v, v'=-g & x > 5}".asProgram.asInstanceOf[ODESystem]

    odeActive(ode1) shouldBe None
    // Bad event domain split when x=5
    // Some((Unable to enter ODE {x'=v,v'=-g&x>5},Map(g -> 0, v -> 1, x -> 5)))
    odeActive(ode2).isEmpty shouldBe false

    // Points without evolution
    // Some((System cannot evolve forwards,Map(g -> (-1), v -> 0, x -> 5)))
    stateSwitchActive(List(ode1)).isEmpty shouldBe false
    // Some((System cannot evolve forwards,Map(g -> 1, v -> 0, x -> 0)))
    stateSwitchActive(List(ode1),"g > 0".asFormula).isEmpty shouldBe false

    // "x=0" is somewhat a special case in this model so ignore it (ball bounces at x = 0)
    // Some((System cannot evolve forwards,Map(g -> 1, v -> 1, x -> 5)))
    stateSwitchActive(List(ode1),"g > 0 & x > 0".asFormula).isEmpty shouldBe false
    // Every point can locally evolve (if we fixed ode2's domain)
    stateSwitchActive(List(ode1, ode2),"g > 0 & x > 0".asFormula) shouldBe None
  }

  it should "try ADHS example" in withMathematica { _ =>

    // Some bad examples
    val ode1 = "{x1'=0,x2'=1 & x1 >= x2}".asProgram.asInstanceOf[ODESystem]
    val ode2 = "{x1'=-1,x2'=0 & x1 < x2}".asProgram.asInstanceOf[ODESystem]
    val ode22 = "{x1'=1,x2'=0 & x1 <= x2}".asProgram.asInstanceOf[ODESystem]

    odeActive(ode1) shouldBe None
    // Some((Unable to enter ODE {x1'=(-1),x2'=0&x1 < x2},Map(x1 -> 0, x2 -> 0)))
    odeActive(ode2).isEmpty shouldBe false
    odeActive(ode22) shouldBe None
    // Some((System cannot evolve forwards,Map(x1 -> 0, x2 -> 0)))
    stateSwitchActive(List(ode1, ode22)).isEmpty shouldBe false //missing sliding ,ode

    // Fixed with third ODE for sliding mode
    val ode3 = "{x1'=1/2,x2'=1/2 & x1 = x2}".asProgram.asInstanceOf[ODESystem]
    odeActive(ode3) shouldBe None
    stateSwitchActive(List(ode1, ode22, ode3)) shouldBe None

    // Fixed with hysteresis
    val ode1E = "{x1'=0,x2'=1 & x1 >= x2 - eps}".asProgram.asInstanceOf[ODESystem]
    val ode2E = "{x1'=1,x2'=0 & x1 <= x2 + eps}".asProgram.asInstanceOf[ODESystem]

    odeActive(ode1E) shouldBe None
    odeActive(ode2E) shouldBe None
    stateSwitchActive(List(ode1E, ode2E),"eps > 0".asFormula) shouldBe None
  }

  "stability" should "specify stability for ODEs" in withMathematica { _ =>
    val ode = "{x' = -x, y'= -y, z'= -z * a}".asProgram

    val stab1 = stableOrigin(ode)
    val stab2 = stableOrigin(ode, varsopt=Some(List("x","y","z").map(_.asVariable)))
    val stab3 = stableOrigin(ode, varsopt=None, restr=Some("a > 0".asFormula))
    println(stab1)
    println(stab2)
    println(stab3)

    stab1 shouldBe "\\forall eps (eps>0->\\exists del (del>0&\\forall z \\forall y \\forall x (z^2+y^2+x^2 < del^2->[{x'=-x,y'=-y,z'=-z*a}]z^2+y^2+x^2 < eps^2)))".asFormula
    stab2 shouldBe "\\forall eps (eps>0->\\exists del (del>0&\\forall x \\forall y \\forall z (x^2+y^2+z^2 < del^2->[{x'=-x,y'=-y,z'=-z*a}]x^2+y^2+z^2 < eps^2)))".asFormula
    stab3 shouldBe "\\forall eps (eps>0->\\exists del (del>0&\\forall z \\forall y \\forall x (a>0&z^2+y^2+x^2 < del^2->[{x'=-x,y'=-y,z'=-z*a}]z^2+y^2+x^2 < eps^2)))".asFormula
  }

  it should "be reusable for switched systems" in withMathematica { _ =>
    val ode1 = ODESystem("x'=-x".asDifferentialProgram, True)
    val ode2 = ODESystem("x'=-x^3".asDifferentialProgram, True)
    val ode3 = ODESystem("x'=-x^5".asDifferentialProgram, True)

    val ss = stateSwitch(List(ode1,ode2,ode3))

    val stab = stableOrigin(ss)
    println(stab)

    stab shouldBe "\\forall eps (eps>0->\\exists del (del>0&\\forall x (x^2 < del^2->[{{{x'=-x}++{x'=-x^3}}++{x'=-x^5}}*]x^2 < eps^2)))".asFormula
  }

  it should "prove ODE stable" in withMathematica { _ =>
    val ode = "{x' = -x, y'= -y, z'= -z * a}".asProgram
    val stab1 = stableOrigin(ode)

    val pr = proveBy(Imply("a > 0".asFormula,stab1),
      implyR(1) &
        proveStable("x^2 + y^2 + z^2".asTerm,ode)(1)
    )

    println(pr)
    pr shouldBe 'proved
  }

  it should "prove system stable" in withMathematica { _ =>
    val ode1 = ODESystem("x'=-x".asDifferentialProgram, True)
    val ode2 = ODESystem("x'=-x^3".asDifferentialProgram, True)
    val ode3 = ODESystem("x'=-x^5".asDifferentialProgram, True)

    val ss = stateSwitch(List(ode1,ode2,ode3))
    val stab = stableOrigin(ss)

    val pr = proveBy(stab,
      proveStable("x^4+x^2".asTerm,ss)(1)
    )

    println(pr)
    pr shouldBe 'proved
  }

  it should "prove system stable 2" in withMathematica { _ =>
    val ode1 = ODESystem("x1'=-x1+x2^3, x2'=-x1-x2".asDifferentialProgram, True)
    val ode2 = ODESystem("x1'=-x1, x2'=-x2".asDifferentialProgram, True)

    val ss = stateSwitch(List(ode1,ode2))
    val stab = stableOrigin(ss)

    val pr = proveBy(stab,
      proveStable("x1 ^ 2 / 2 + x2 ^ 4 / 4".asTerm,ss)(1)
    )

    println(pr)
    pr shouldBe 'proved
  }

  it should "prove system stable 3" in withMathematica { _ =>
    val ode1 = "{x1'=-x1/8-x2,x2'=2*x1-x2/8 & x1*x2 <= 0}".asProgram.asInstanceOf[ODESystem]
    val ode2 = "{x1'=-x1/8-2*x2,x2'=x1-x2/8 & x1*x2 >= 0}".asProgram.asInstanceOf[ODESystem]

    val ss = stateSwitch(List(ode1,ode2))
    val stab = stableOrigin(ss)

    val pr = proveBy(stab,
      proveStable("x1 ^ 2 + x2 ^2".asTerm,ss)(1)
    )

    println(pr)
    pr shouldBe 'proved
  }

  // todo: need to handle arithmetic much better here (very slow)
  it should "prove ODE example stable" taggedAs TodoTest ignore withMathematica { _ =>
    val ode = "{x1' = -x1 + x2^3 - 3*x3*x4,x2' = -x1 - x2^3,x3' = x1*x4 - x3,x4' = x1*x3 - x4^3}".asProgram
    val stab1 = stableOrigin(ode)

    val pr = proveBy(stab1,
      proveStable("2*x1^2 + x2^4 + 3201/1024*x3^2 + 2943/1024*x4^2".asTerm,ode)(1)
    )

    println(pr)
    pr shouldBe 'proved
  }

  // todo: need to handle arithmetic much better here (too slow / doesn't prove)
  it should "prove large ODE stable" taggedAs TodoTest ignore withMathematica { _ =>
    val ode = "{x1' = -x1^3+4*x2^3-6*x3*x4,x2' = -x1-x2+x5^3,x3' = x1*x4-x3+x4*x6,x4' = x1*x3+x3*x6-x4^3,x5' = -2*x2^3-x5+x6,x6' = -3*x3*x4-x5^3-x6}".asProgram
    val stab1 = stableOrigin(ode)

    val pr = proveBy(stab1,
        proveStable("2*x1^2 + 4*x2^4 + x3^2 + 11*x4^2 + 2*x5^4 + 4*x6^2".asTerm,ode)(1)
    )

    println(pr)
  }

  "time dependent" should "model time dependency" in withMathematica { _ =>
    val ode1 = "{x'=x}".asProgram.asInstanceOf[ODESystem]
    val ode2 = "{x'=-x}".asProgram.asInstanceOf[ODESystem]

    val tt = timeSwitch(List( (ode1,Some(Number(5))), (ode2, None)),
      List(List((1,Number(5))),List((0,Number(5)))), topt = Some(Variable("t_")))

    println(tt)
    tt shouldBe (
      "{s_:=0;{u_:=0;++u_:=1;}}" +
      "{" +
      " {?u_=0;{{?s_>=5;u_:=1;}s_:=0;++u_:=0;}++" +
      "  ?u_=1;{{?s_>=5;u_:=0;}s_:=0;++u_:=1;}" +
      " }" +
      " {?u_=0;{t_'=1,s_'=1,x'=x&true&s_<=5}++" +
      "  ?u_=1;{t_'=1,s_'=1,x'=-x}" +
      " }" +
      "}*").asProgram
  }

  it should "model slow switching" in withMathematica { _ =>
    val ode1 = "{x'=x}".asProgram.asInstanceOf[ODESystem]
    val ode2 = "{x'=-x}".asProgram.asInstanceOf[ODESystem]

    val tt = slowSwitch( List(ode1,ode2), Number(5))

    println(tt)

    tt shouldBe (
      ("{s_:=0;{u_:=0;++u_:=1;}}" +
        "{" +
        "   {?u_=0;{{?s_>=5;u_:=1;}s_:=0;++u_:=0;}++" +
        "    ?u_=1;{{?s_>=5;u_:=0;}s_:=0;++u_:=1;}}" +
        "   {?u_=0;{s_'=1,x'=x}++" +
        "    ?u_=1;{s_'=1,x'=-x}}" +
        "}*").asProgram
    )
  }

  it should "do a manual slow stability proof" in withMathematica { _ =>
    val ode1 = "{x1'=-x1/8-x2,x2'=2*x1-x2/8}".asProgram.asInstanceOf[ODESystem]
    val ode2 = "{x1'=-x1/8-2*x2,x2'=x1-x2/8}".asProgram.asInstanceOf[ODESystem]

    val lyap1 = "2*x1^2+x2^2".asTerm
    val lyap2 = "x1^2+2*x2^2".asTerm
    val lyaps = List(lyap1,lyap2)

    val tt = slowSwitch (List(ode1,ode2), Number(3))
    val stab = stableOrigin(tt)

    val vars = List("x1","x2").map(_.asVariable)
    val normsq = vars.map(e => Power(e, Number(2))).reduceLeft(Plus) // ||x||^2

    val eps = Variable("eps")
    val del = Variable("del")
    val epssq = Power(eps, Number(2))
    val delsq = Power(del, Number(2))

    val w = Variable("w_")

    val epsgeq = lyaps.map( t => GreaterEqual(t,w)).reduceLeft(And)

    val epsbound =
      vars.foldRight(Imply(Equal(normsq, epssq), epsgeq): Formula)((v, f) => Forall(v :: Nil, f))
    val epsw = Exists(w :: Nil,
      And(Greater(w, Number(0)),
        epsbound
      ))

    val delless = lyaps.map( t => Less(t,w)).reduceLeft(And)
    val delw = And(And(Greater(del, Number(0)), Less(del, eps)),
      vars.foldRight(Imply(Less(normsq, delsq), delless): Formula)((v, f) => Forall(v :: Nil, f))
    )

    val exp = "1 + (s_*1/4) + (s_*1/4)^2/2 + (s_*1/4)^3/6".asTerm

    val u = Variable("u_")

    val lexp = lyaps.zipWithIndex.map( fi =>
      And(Equal(u,Number(fi._2)), Less(Times(fi._1,exp), w))
    ).reduceLeft(Or)

    val invariant = And(And("s_>=0".asFormula, Less(normsq,epssq)),lexp)

    val pr = proveBy(stab,
      allR(1) & implyR(1) &
      cutR(epsw)(1) <(
        //Automation should prove these bounds separately and then pick the smallest
        QE,
        implyR(1) & existsL(-2) & andL(-2) &
        existsRmon(delw)(1) <(
          hideL(-3) & QE,
          andL(-4) & andL(-4) & andR(1) <(
            id,
            (allR(1)*2) & implyR(1) &
            (allL(-4)*2) & implyL(-4) <(
              id,
              composeb(1) &
              hideL(-1) &
              hideL(-1) &
              generalize(invariant)(1) <(
                chase(1) & hideL(-3) & QE ,
                andL(-1) & hideL('Llast) &
                throughout(invariant)(1) <(
                  prop,
                  prop,
                  cohideOnlyL(-1) & andL(-1) & chase(1) & orL(-2) <(
                    andR(1) <(
                      QE, // can do more simplification
                      implyR(1) & hideR(1) & QE
                    ),
                    andR(1) <(
                      implyR(1) & hideR(1) & QE,
                      QE // can do more simplification
                    )
                  ),
                  andL(-1) & hideL(-2) &
                  andL(-1) & chase(1) & orL(-3) <(
                    andR(1) <(
                      implyR(1) &
                      exhaustiveEqL2R('Llast) &
                      // this sequence of cuts sets things up in the right order
                      dC("s_>=0".asFormula)(1) <(
                        dC(Less(Times(lyap1,exp), w))(1) <(
                          dC(Less(normsq,epssq))(1) <(
                            DW(1) & G(1) & QE, // can be simplified
                            ODEInvariance.dCClosure(1) <(
                              hideL(-1) & QE,
                              dC(Imply(Equal(normsq, epssq), epsgeq))(1) <(
                                DW(1) & G(1) & QE,
                                dW(1) & andL(-1) & andL(-2) &
                                allL(-2) & allL(-2) & id
                              )
                            )
                          ),
                          hideL(-1) & ODE(1)
                        ),
                        hideL(-1) & ODE(1)
                      )
                      ,
                      implyR(1) & hideR(1) & QE
                    ),
                    andR(1) <(
                      implyR(1) & hideR(1) & QE,
                      implyR(1) &
                        exhaustiveEqL2R('Llast) &
                        dC("s_>=0".asFormula)(1) <(
                          dC(Less(Times(lyap2,exp), w))(1) <(
                            dC(Less(normsq,epssq))(1) <(
                              DW(1) & G(1) & QE, // can be simplified
                              ODEInvariance.dCClosure(1) <(
                                hideL(-1) & QE,
                                dC(Imply(Equal(normsq, epssq), epsgeq))(1) <(
                                  DW(1) & G(1) & QE,
                                  dW(1) & andL(-1) & andL(-2) &
                                    allL(-2) & allL(-2) & id
                                )
                              )
                            ),
                            hideL(-1) & ODE(1)
                          ),
                          hideL(-1) & ODE(1)
                        )
                    )
                  )
                )
              )

            )
          )
        )
      )
    )

    println(pr)
    pr shouldBe 'proved
  }


}
