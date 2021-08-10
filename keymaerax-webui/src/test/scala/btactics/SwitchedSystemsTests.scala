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

    odeActive(ode1) shouldBe false //Bad at x=0 (cannot leave)
    odeActive(ode2) shouldBe true
    odeActive(ode1, "x > 1".asFormula) shouldBe true //Bad point is excluded by global domain
  }

  it should "check activity for recitation 4 example" in withMathematica { _ =>

    val ode1 = "{x'=v & l <= x & x <= r}".asProgram.asInstanceOf[ODESystem]
    val ode2 = "{x'=v & !(l <= x & x <= r)}".asProgram.asInstanceOf[ODESystem]

    odeActive(ode1) shouldBe true
    odeActive(ode2) shouldBe false // Bad event trigger (cannot enter/leave)
    //Bad even if we restricted the set of states to look for violations
    odeActive(ode2, "l <= x & x <= r & v >= 0".asFormula) shouldBe false
  }

  it should "check event triggering" in withMathematica { _ =>

    val ode1 = "{x'=v, v'=-g & x <= 5}".asProgram.asInstanceOf[ODESystem]
    val ode2 = "{x'=v, v'=-g & x > 5}".asProgram.asInstanceOf[ODESystem]
    val ode3 = "{x'=v, v'=-g & x >= 6}".asProgram.asInstanceOf[ODESystem]

    stateSwitchActive(List(ode1)) shouldBe false
    stateSwitchActive(List(ode1, ode2)) shouldBe true
    stateSwitchActive(List(ode1, ode3)) shouldBe false
    odeActive(ode1) shouldBe true
    odeActive(ode2) shouldBe false
  }

  it should "try ADHS example" in withMathematica { _ =>

    // Some bad examples
    val ode1 = "{x1'=0,x2'=1 & x1 >= x2}".asProgram.asInstanceOf[ODESystem]
    val ode2 = "{x1'=-1,x2'=0 & x1 < x2}".asProgram.asInstanceOf[ODESystem]
    val ode22 = "{x1'=1,x2'=0 & x1 <= x2}".asProgram.asInstanceOf[ODESystem]

    odeActive(ode1) shouldBe true
    odeActive(ode2) shouldBe false
    odeActive(ode22) shouldBe true
    stateSwitchActive(List(ode1, ode22)) shouldBe false //missing sliding ,ode

    // Fixed with third ODE for sliding mode
    val ode3 = "{x1'=1/2,x2'=1/2 & x1 = x2}".asProgram.asInstanceOf[ODESystem]
    odeActive(ode3) shouldBe true
    stateSwitchActive(List(ode1, ode22, ode3)) shouldBe true

    // Fixed with hysteresis
    val ode1E = "{x1'=0,x2'=1 & x1 >= x2 - eps}".asProgram.asInstanceOf[ODESystem]
    val ode2E = "{x1'=1,x2'=0 & x1 <= x2 + eps}".asProgram.asInstanceOf[ODESystem]

    odeActive(ode1E) shouldBe true
    odeActive(ode2E) shouldBe true
    stateSwitchActive(List(ode1E, ode2E),"eps > 0".asFormula) shouldBe true
  }
}
