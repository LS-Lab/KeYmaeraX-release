package btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.TacticStatistics
import edu.cmu.cs.ls.keymaerax.btactics.SwitchedSystems._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

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

}
