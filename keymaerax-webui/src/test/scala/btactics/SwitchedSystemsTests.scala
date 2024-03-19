/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package btactics

import edu.cmu.cs.ls.keymaerax.btactics.SwitchedSystems._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tagobjects.TodoTest

class SwitchedSystemsTests extends TacticTestBase {

  "ADT" should "parse and print state-dependent system" in withMathematica { _ =>
    val ode1 = ODESystem("x'=-x+y,z'=a+b".asDifferentialProgram, True)
    val ode2 = ODESystem("x'=-x^3".asDifferentialProgram, True)
    val ode3 = ODESystem("x'=-x^5".asDifferentialProgram, True)
    val ss = StateDependent(List(ode1, ode2, ode3))

    ss.cvars shouldBe List(Variable("x"), Variable("z"))
    ss.vars shouldBe List(Variable("z"), Variable("y"), Variable("x"), Variable("a"), Variable("b"))

    println(ss)
    println(ss.asProgram)
    println(ss.asClockedProgram(Variable("t_")))
    ss.asProgram shouldBe "{{x'=-x+y,z'=a+b}++{x'=-x^3}++{x'=-x^5}}*".asProgram
    ss.asClockedProgram(Variable("t_")) shouldBe "{{t_'=1,x'=-x+y,z'=a+b}++{t_'=1,x'=-x^3}++{t_'=1,x'=-x^5}}*".asProgram

    stateDependentFromProgram(ss.asProgram, None) shouldBe ss
    stateDependentFromProgram(ss.asClockedProgram(Variable("t_")), Some(Variable("t_"))) shouldBe ss

    // requirement fail: StateDependent(List())
    // freshness error: ss.asProgram(Variable("x"))
  }

  it should "parse and print controlled switching system" in withMathematica { _ =>
    val ode1 = ODESystem("x'=-x".asDifferentialProgram, True)
    val ode2 = ODESystem("x'=-x^3".asDifferentialProgram, True)
    val ode3 = ODESystem("x'=-x^5".asDifferentialProgram, True)

    val mode1 = (
      "mode1",
      ode1,
      List(
        ("mode2", "?x>a ; x:=0; y:=0;".asProgram), // 1 -> 2
        ("mode2", "?x<=0;".asProgram), // 1 -> 2
        ("mode3", "?x=0; x:=0;".asProgram), // 1 -> 3
      ),
    )

    val mode2 = ("mode2", ode2, List())

    val mode3 = ("mode3", ode3, List(("mode2", "?x<=0; x:=0;".asProgram))) // 3 -> 2

    val cs = Controlled(None, List(mode1, mode2, mode3), Variable("u"))

    cs.cvars shouldBe List(Variable("x"))
    cs.vars shouldBe List(Variable("u"), Variable("x"), Variable("a"), Variable("y"))

    println(cs.asProgram)
    cs.asProgram shouldBe
      "{u:=mode1();++u:=mode2();++u:=mode3();}{{?u=mode1();{{?x>a;x:=0;y:=0;}u:=mode2();++?x<=0;u:=mode2();++{?x=0;x:=0;}u:=mode3();++u:=u;}++?u=mode2();u:=u;++?u=mode3();{{?x<=0;x:=0;}u:=mode2();++u:=u;}}{?u=mode1();{x'=-x}++?u=mode2();{x'=-x^3}++?u=mode3();{x'=-x^5}}}*"
        .asProgram

    controlledFromProgram(cs.asProgram, None) shouldBe cs
    controlledFromProgram(cs.asClockedProgram(Variable("t_")), Some(Variable("t_"))) shouldBe cs
  }

  it should "parse and print controlled switching system 2" in withMathematica { _ =>
    val ode1 = ODESystem("x'=-x, t'=1".asDifferentialProgram, True)
    val ode2 = ODESystem("x'=-x^3, t'=1".asDifferentialProgram, True)

    val mode1 = (
      "mode1",
      ode1,
      List(
        ("mode2", "?x>a ; x:=0; y:=0;".asProgram), // 1 -> 2
        ("mode2", "?x<=0;".asProgram), // 1 -> 2
      ),
    )

    val mode2 = ("mode2", ode2, List())

    val cs = Controlled(Some("t:=0;".asProgram), List(mode1, mode2), Variable("mode"))

    cs.cvars shouldBe List(Variable("x"), Variable("t"))
    cs.vars shouldBe List(Variable("mode"), Variable("t"), Variable("x"), Variable("a"), Variable("y"))

    println(cs.asProgram)
    cs.asProgram shouldBe
      "{{mode:=mode1();++mode:=mode2();}t:=0;}{{?mode=mode1();{{?x>a;x:=0;y:=0;}mode:=mode2();++?x<=0;mode:=mode2();++mode:=mode;}++?mode=mode2();mode:=mode;}{?mode=mode1();{x'=-x,t'=1}++?mode=mode2();{x'=-x^3,t'=1}}}*"
        .asProgram

    controlledFromProgram(cs.asProgram, None) shouldBe cs
    controlledFromProgram(cs.asClockedProgram(Variable("t_")), Some(Variable("t_"))) shouldBe cs
  }

  it should "parse and print guarded state-dependent switching system" in withMathematica { _ =>
    val ode1 = ODESystem("x'=-x".asDifferentialProgram, True)
    val ode2 = ODESystem("x'=-x^3".asDifferentialProgram, True)
    val ode3 = ODESystem("x'=-x^5".asDifferentialProgram, True)

    val mode1 = (
      "mode1",
      ode1,
      List(
        ("mode2", "x>a".asFormula), // 1 -> 2
        ("mode2", "x<=0".asFormula), // 1 -> 2
        ("mode3", "x=0".asFormula), // 1 -> 3
      ),
    )

    val mode2 = ("mode2", ode2, List())

    val mode3 = ("mode3", ode3, List(("mode2", "x<=0".asFormula))) // 3 -> 2

    val cs = Guarded(List(mode1, mode2, mode3), Variable("u"))

    cs.cvars shouldBe List(Variable("x"))
    cs.vars shouldBe List(Variable("u"), Variable("x"), Variable("a"))

    println(cs.asProgram)
    cs.asProgram shouldBe
      "{u:=mode1();++u:=mode2();++u:=mode3();}{{?u=mode1();{?x>a;u:=mode2();++?x<=0;u:=mode2();++?x=0;u:=mode3();++u:=u;}++?u=mode2();u:=u;++?u=mode3();{?x<=0;u:=mode2();++u:=u;}}{?u=mode1();{x'=-x}++?u=mode2();{x'=-x^3}++?u=mode3();{x'=-x^5}}}*"
        .asProgram

    guardedFromProgram(cs.asProgram, None) shouldBe cs
    guardedFromProgram(cs.asClockedProgram(Variable("t_")), Some(Variable("t_"))) shouldBe cs
  }

  it should "parse and print time-dependent switching system" in withMathematica { _ =>
    val ode1 = "x'=-x".asDifferentialProgram
    val ode2 = "x'=-x^3".asDifferentialProgram

    val mode1 = (
      "mode1",
      ode1,
      None,
      List(
        ("mode2", Some("1".asTerm)), // 1 -> 2
        ("mode2", None), // 1 -> 3
      ),
    )

    val mode2 = ("mode2", ode2, Some("5".asTerm), List())

    val cs = Timed(List(mode1, mode2), Variable("u"), Variable("timer"))

    cs.cvars shouldBe List(Variable("x"))
    cs.vars shouldBe List(Variable("u"), Variable("timer"), Variable("x"))

    println(cs.asProgram)
    cs.asProgram shouldBe
      "{{u:=mode1();++u:=mode2();}timer:=0;}{{?u=mode1();{{?timer>=1;timer:=0;}u:=mode2();++{?true;timer:=0;}u:=mode2();++u:=u;}++?u=mode2();u:=u;}{?u=mode1();{timer'=1,x'=-x}++?u=mode2();{timer'=1,x'=-x^3&timer<=5}}}*"
        .asProgram

    timedFromProgram(cs.asProgram, None) shouldBe cs
    timedFromProgram(cs.asClockedProgram(Variable("t_")), Some(Variable("t_"))) shouldBe cs
  }

  "specifications" should "generate specs (state-dependent)" in withMathematica { _ =>
    val ode1 = ODESystem("x'=-x+y,z'=a+b".asDifferentialProgram, True)
    val ode2 = ODESystem("x'=-x^3".asDifferentialProgram, True)
    val ode3 = ODESystem("x'=-x^5".asDifferentialProgram, True)
    val ss = StateDependent(List(ode1, ode2, ode3))

    val spec = stabilitySpec(ss)
    println(spec)
    spec shouldBe
      "\\forall eps (eps>0->\\exists del (del>0&\\forall x \\forall z (x^2+z^2 < del^2->[{{x'=-x+y,z'=a+b}++{x'=-x^3}++{x'=-x^5}}*]x^2+z^2 < eps^2)))"
        .asFormula

    val spec2 = attractivitySpec(ss)
    println(spec2)
    spec2 shouldBe
      "\\forall eps (eps>0->\\forall del (del>0 -> \\exists T_ (T_>=0&\\forall x \\forall z (x^2+z^2 < del^2->[t_:=0;{{t_'=1,x'=-x+y,z'=a+b}++{t_'=1,x'=-x^3}++{t_'=1,x'=-x^5}}*](t_>=T_->x^2+z^2 < eps^2)))))"
        .asFormula
  }

  it should "generate specs (controlled)" in withMathematica { _ =>
    val ode1 = ODESystem("x'=-x, t'=1".asDifferentialProgram, True)
    val ode2 = ODESystem("x'=-x^3, t'=1".asDifferentialProgram, True)

    val mode1 = (
      "mode1",
      ode1,
      List(
        ("mode2", "?x>a ; x:=0; y:=0;".asProgram), // 1 -> 2
        ("mode2", "?x<=0;".asProgram), // 1 -> 2
      ),
    )

    val mode2 = ("mode2", ode2, List())

    val cs = Controlled(Some("t:=0;".asProgram), List(mode1, mode2), Variable("mode"))

    val spec = stabilitySpec(cs)
    println(spec)
    spec shouldBe
      "\\forall eps (eps>0->\\exists del (del>0&\\forall x \\forall t (x^2+t^2 < del^2->[{{mode:=mode1();++mode:=mode2();}t:=0;}{{?mode=mode1();{{?x>a;x:=0;y:=0;}mode:=mode2();++?x<=0;mode:=mode2();++mode:=mode;}++?mode=mode2();mode:=mode;}{?mode=mode1();{x'=-x,t'=1}++?mode=mode2();{x'=-x^3,t'=1}}}*]x^2+t^2 < eps^2)))"
        .asFormula

    val spec2 = attractivitySpec(cs)
    println(spec2)
    spec2 shouldBe
      "\\forall eps (eps>0->\\forall del (del>0 -> \\exists T_ (T_>=0&\\forall x \\forall t (x^2+t^2 < del^2->[t_:=0;{{mode:=mode1();++mode:=mode2();}t:=0;}{{?mode=mode1();{{?x>a;x:=0;y:=0;}mode:=mode2();++?x<=0;mode:=mode2();++mode:=mode;}++?mode=mode2();mode:=mode;}{?mode=mode1();{t_'=1,x'=-x,t'=1}++?mode=mode2();{t_'=1,x'=-x^3,t'=1}}}*](t_>=T_->x^2+t^2 < eps^2)))))"
        .asFormula
  }

  "UGpAS CLF" should "prove system stable" in withMathematica { _ =>
    val ode1 = ODESystem("x'=-a*x".asDifferentialProgram, True)
    val ode2 = ODESystem("x'=-x^3".asDifferentialProgram, "x^2 >= 0".asFormula)
    val ode3 = ODESystem("x'=-x^5".asDifferentialProgram, True)
    val ode4 = ODESystem("x'=x".asDifferentialProgram, False) // unstable mode that is never entered

    val ss = StateDependent(List(ode1, ode2, ode3, ode4))
    val spec = stabilitySpec(ss)

    val pr = proveBy(
      Imply("100>b".asFormula, Or("a <= 0".asFormula, spec)),
      implyR(1) & orR(1) & proveStabilityCLF("x^4+x^2".asTerm)(2),
    )

    println(pr)
    pr shouldBe Symbol("proved")

    val spec2 = attractivitySpec(ss)

    val pr2 = proveBy(
      Imply("100>b".asFormula, Or("a <= 0".asFormula, spec2)),
      implyR(1) & orR(1) & proveAttractivityCLF("x^4+x^2".asTerm)(2),
    )

    println(pr2)
    pr2 shouldBe Symbol("proved")
  }

  it should "prove system stable automatically" in withMathematicaMatlab { _ =>
    val ode1 = ODESystem("x1'=-2*x1-x2-x3, x2'=-x2, x3'=-x1-x2-2*x3".asDifferentialProgram, True)
    val ode2 = ODESystem("x1'=2*x2, x2'=-2*x1-x2, x3'=x1-2*x2-x3".asDifferentialProgram, True)

    val ss = StateDependent(List(ode1, ode2))
    val spec = stabilitySpec(ss)

    proveBy(spec, proveStabilityCLF(None)(1)) shouldBe Symbol("proved")
  }

  it should "prove ODE stable" in withMathematica { _ =>
    val ode = "{x' = -x, y'= -y, z'= -z * a}".asProgram.asInstanceOf[ODESystem]

    val ss = StateDependent(List(ode))
    val spec = stabilitySpec(ss)

    val pr = proveBy(Imply("a > 0".asFormula, spec), implyR(1) & proveStabilityCLF("x^2 + y^2 + z^2".asTerm)(1))

    println(pr)
    pr shouldBe Symbol("proved")

    val spec2 = attractivitySpec(ss)

    val pr2 = proveBy(Imply("a > 0".asFormula, spec2), implyR(1) & proveAttractivityCLF("x^2 + y^2 + z^2".asTerm)(1))

    println(pr2)
    pr2 shouldBe Symbol("proved")
  }

  it should "prove controlled stable, ignoring switching mechanism" in withMathematica { _ =>
    val ode1 = ODESystem("x'=-x".asDifferentialProgram, True)
    val ode2 = ODESystem("x'=-a*x^3".asDifferentialProgram, True)

    val mode1 = (
      "mode1",
      ode1,
      List(
        ("mode2", "?x>a ; y:=0;".asProgram), // 1 -> 2
        ("mode2", "?x<=0;".asProgram), // 1 -> 2
      ),
    )

    val mode2 = ("mode2", ode2, List())

    val cs = Controlled(Some("t:=0;".asProgram), List(mode1, mode2), Variable("mode"))
    val spec = stabilitySpec(cs)

    val pr = proveBy(
      Imply("100>b".asFormula, Or("a <= 0".asFormula, spec)),
      implyR(1) & orR(1) & proveStabilityCLF("x^4+x^2".asTerm)(2),
    )

    println(pr)
    pr shouldBe Symbol("proved")

    val spec2 = attractivitySpec(cs)

    val pr2 = proveBy(
      Imply("100>b".asFormula, Or("a <= 0".asFormula, spec2)),
      implyR(1) & orR(1) & proveAttractivityCLF("x^4+x^2".asTerm)(2),
    )

    println(pr2)
    pr2 shouldBe Symbol("proved")
  }

  it should "prove timed stable, ignoring switching mechanism" in withMathematica { _ =>
    val ode1 = "x'=-x".asDifferentialProgram
    val ode2 = "x'=-a*x^3".asDifferentialProgram

    val mode1 = ("mode1", ode1, None, List(("mode2", Some("3".asTerm)))) // 1 -> 2

    val mode2 = ("mode2", ode2, None, List(("mode1", Some("3".asTerm)))) // 1 -> 2

    val cs = Timed(List(mode1, mode2), Variable("u"), Variable("timer"))

    val spec = stabilitySpec(cs)

    val pr = proveBy(
      Imply("100>b".asFormula, Or("a <= 0".asFormula, spec)),
      implyR(1) & orR(1) & proveStabilityCLF("x^4+x^2".asTerm)(2),
    )

    println(pr)
    pr shouldBe Symbol("proved")

    val spec2 = attractivitySpec(cs)

    val pr2 = proveBy(
      Imply("100>b".asFormula, Or("a <= 0".asFormula, spec2)),
      implyR(1) & orR(1) & proveAttractivityCLF("x^4+x^2".asTerm)(2),
    )

    println(pr2)
    pr2 shouldBe Symbol("proved")
  }

  it should "prove system stable 2" in withMathematica { _ =>
    val ode1 = ODESystem("x1'=-x1+x2^3, x2'=-x1-x2".asDifferentialProgram, True)
    val ode2 = ODESystem("x1'=-x1, x2'=-x2".asDifferentialProgram, True)

    val ss = StateDependent(List(ode1, ode2))
    val spec = stabilitySpec(ss)

    val pr = proveBy(spec, proveStabilityCLF("x1 ^ 2 / 2 + x2 ^ 4 / 4".asTerm)(1))

    println(pr)
    pr shouldBe Symbol("proved")

    val spec2 = attractivitySpec(ss)

    val pr2 = proveBy(spec2, proveAttractivityCLF("x1 ^ 2 / 2 + x2 ^ 4 / 4".asTerm)(1))

    println(pr2)
    pr2 shouldBe Symbol("proved")
  }

  it should "prove system stable 3" in withMathematica { _ =>
    val ode1 = "{x1'=-x1/8-x2,x2'=2*x1-x2/8 & x1*x2 <= 0}".asProgram.asInstanceOf[ODESystem]
    val ode2 = "{x1'=-x1/8-2*x2,x2'=x1-x2/8 & x1*x2 >= 0}".asProgram.asInstanceOf[ODESystem]

    val ss = StateDependent(List(ode1, ode2))
    val stab = stabilitySpec(ss)

    val pr = proveBy(stab, proveStabilityCLF("x1 ^ 2 + x2 ^2".asTerm)(1))

    println(pr)
    pr shouldBe Symbol("proved")

    val spec2 = attractivitySpec(ss)

    val pr2 = proveBy(spec2, proveAttractivityCLF("x1 ^ 2 + x2 ^2".asTerm)(1))

    println(pr2)
    pr2 shouldBe Symbol("proved")
  }

  "UGpAS MLF" should "prove state-dependent system stable" in withMathematica { _ =>
    val ode1 = ODESystem("x'=-a*x".asDifferentialProgram, True)
    val ode2 = ODESystem("x'=-x^3".asDifferentialProgram, "x^2 >= 0".asFormula)
    val ode3 = ODESystem("x'=-x^5".asDifferentialProgram, True)
    val ode4 = ODESystem("x'=x".asDifferentialProgram, False) // unstable mode that is never entered

    val ss = StateDependent(List(ode1, ode2, ode3, ode4))

    val spec = stabilitySpec(ss)

    val pr = proveBy(
      Imply("100>b".asFormula, Or("a <= 0".asFormula, spec)),
      implyR(1) & orR(1) & proveStabilityStateMLF(
        "x^4+x^2".asTerm :: "(2*x^4+2*x^2)/2".asTerm :: "(3*x^4+3*x^2)/3".asTerm :: "4*x^4+100*x^2".asTerm :: Nil
      )(2),
    )

    println(pr)
    pr shouldBe Symbol("proved")

    val spec2 = attractivitySpec(ss)

    val pr2 = proveBy(
      Imply("100>b".asFormula, Or("a <= 0".asFormula, spec2)),
      implyR(1) & orR(1) & proveAttractivityStateMLF(
        "x^4+x^2".asTerm :: "(2*x^4+2*x^2)/2".asTerm :: "(3*x^4+3*x^2)/3".asTerm :: "4*x^4+100*x^2".asTerm :: Nil
      )(2),
    )

    println(pr2)
    pr2 shouldBe Symbol("proved")
  }

  it should "prove state-dependent system stable 2" in withMathematica { _ =>
    val ode1 = ODESystem("x1'=-x1/8-x2,x2'=2*x1-x2/8".asDifferentialProgram, "x1>=0".asFormula)
    val ode2 = ODESystem("x1'=-x1/8-2*x2,x2'=x1-x2/8".asDifferentialProgram, "x1<=0".asFormula)
    val ss = StateDependent(List(ode1, ode2))
    val spec = stabilitySpec(ss)

    val pr = proveBy(
      spec,
      proveStabilityStateMLF(
        "0.0011587*x1^2+ 0.00062432*x2^2 ".asTerm :: "0.00032638*x1^2 + 0.00062432*x2^2".asTerm :: Nil
      )(1),
    )

    println(pr)
    pr shouldBe Symbol("proved")

    val spec2 = attractivitySpec(ss)

    val pr2 = proveBy(
      spec2,
      proveAttractivityStateMLF(
        "0.0011587*x1^2+ 0.00062432*x2^2 ".asTerm :: "0.00032638*x1^2 + 0.00062432*x2^2".asTerm :: Nil
      )(1),
    )

    println(pr2)
    pr2 shouldBe Symbol("proved")
  }

  it should "prove state-dependent system stable 3" in withMathematica { _ =>
    // Johansson and Rantzer motivating example
    val ode1 = ODESystem("x1' = -5*x1-4*x2, x2' =   -x1-2*x2".asDifferentialProgram, "x1<=0".asFormula)
    val ode2 = ODESystem("x1' = -2*x1-4*x2, x2' = 20*x1-2*x2".asDifferentialProgram, "x1>=0".asFormula)
    val ss = StateDependent(List(ode1, ode2))
    val spec = stabilitySpec(ss)

    val pr = proveBy(
      spec,
      proveStabilityStateMLF(
        "0.00038025*x1^2 + 0.00010669*x1*x2 + 0.00019159*x2^2".asTerm :: "0.00067908*x1^2 + 0.00019159*x2^2".asTerm ::
          Nil
      )(1),
    )

    println(pr)
    pr shouldBe Symbol("proved")

    val spec2 = attractivitySpec(ss)

    val pr2 = proveBy(
      spec2,
      proveAttractivityStateMLF(
        "0.00038025*x1^2 + 0.00010669*x1*x2 + 0.00019159*x2^2".asTerm :: "0.00067908*x1^2 + 0.00019159*x2^2".asTerm ::
          Nil
      )(1),
    )

    println(pr2)
    pr2 shouldBe Symbol("proved")
  }

  it should "prove state-dependent system stable 4" in withMathematica { _ =>
    // Johansson and Rantzer example 1
    val o13 = "x1' = -0.1*x1 + x2,   x2' = -5*x1 - 0.1*x2".asDifferentialProgram
    val o24 = "x1' = -0.1*x1 + 5*x2, x2' = -x1 - 0.1*x2".asDifferentialProgram
    val ode1 = ODESystem(o13, "-x1+x2>=0 & -x1-x2>=0".asFormula)
    val ode2 = ODESystem(o24, "-x1+x2>=0 & x1+x2>=0".asFormula)
    val ode3 = ODESystem(o13, "-x1+x2<=0 & -x1-x2<=0".asFormula)
    val ode4 = ODESystem(o24, "-x1+x2<=0 & x1+x2<=0".asFormula)
    val ss = StateDependent(List(ode1, ode2, ode3, ode4))
    val spec = stabilitySpec(ss)

    val v13 = "5*x1^2+x2^2".asTerm
    val v24 = "x1^2+5*x2^2".asTerm

    val pr = proveBy(spec, proveStabilityStateMLF(v13 :: v24 :: v13 :: v24 :: Nil)(1))

    println(pr)
    pr shouldBe Symbol("proved")

    val spec2 = attractivitySpec(ss)

    val pr2 = proveBy(spec2, proveAttractivityStateMLF(v13 :: v24 :: v13 :: v24 :: Nil)(1))

    println(pr2)
    pr2 shouldBe Symbol("proved")
  }

  it should "prove guarded system stable 1" in withMathematica { _ =>
    // Johansson and Rantzer example 2 & 3
    val o1 = "x1' = -x1 -100 *x2,   x2' = 10*x1-x2".asDifferentialProgram
    val o2 = "x1' = x1 + 10*x2, x2' = -100*x1 + x2".asDifferentialProgram
    val ode1 = ODESystem(o1, True)
    val ode2 = ODESystem(o2, "-10*x1-x2 >=0  & 2*x1-x2>=0".asFormula)

    val ss = Guarded(
      List(
        ("mode1", ode1, List(("mode2", "-10*x1-x2=0".asFormula))),
        ("mode2", ode2, List(("mode1", "2*x1-x2=0".asFormula))),
      ),
      Variable("mode"),
    )

    val v1 = "17.9*x1^2-2*0.89*x1*x2+179*x2^2".asTerm
    val v2 = "739*x1^2-2*38.1*x1*x2+91.8*x2^2".asTerm

    val spec = stabilitySpec(ss)
    val pr =
      proveBy(Imply("mode1()=1 & mode2()=2".asFormula, spec), implyR(1) & proveStabilityStateMLF(v1 :: v2 :: Nil)(1))

    println(pr)
    pr shouldBe Symbol("proved")

    val spec2 = attractivitySpec(ss)
    val pr2 = proveBy(
      Imply("mode1()=1 & mode2()=2".asFormula, spec2),
      implyR(1) & proveAttractivityStateMLF(v1 :: v2 :: Nil)(1),
    )

    println(pr2)
    pr2 shouldBe Symbol("proved")
  }

  it should "prove guarded system stable automatically" in withMathematica { _ =>
    // Johansson and Rantzer motivating example
    val ode1 = ODESystem("x1' = -5*x1-4*x2, x2' =   -x1-2*x2".asDifferentialProgram, "x1<=0".asFormula)
    val ode2 = ODESystem("x1' = -2*x1-4*x2, x2' = 20*x1-2*x2".asDifferentialProgram, "x1>=0".asFormula)
    // val ss = StateDependent(List(ode1,ode2))

    val ss = Guarded(
      List(("mode1", ode1, List(("mode2", "x1=0".asFormula))), ("mode2", ode2, List(("mode1", "x1=0".asFormula)))),
      Variable("mode"),
    )

    proveBy(Imply("mode1()!=mode2()".asFormula, stabilitySpec(ss)), implyR(1) & proveStabilityStateMLF(Nil)(1)) shouldBe
      Symbol("proved")
    proveBy(
      Imply("mode1()!=mode2()".asFormula, attractivitySpec(ss)),
      implyR(1) & proveAttractivityStateMLF(Nil)(1),
    ) shouldBe Symbol("proved")
  }

  it should "prove timed system stable 1" in withMathematica { _ =>
    val ode1 = "x1'=-x1/8-x2,x2'=2*x1-x2/8".asDifferentialProgram
    val ode2 = "x1'=-x1/8-2*x2,x2'=x1-x2/8".asDifferentialProgram

    // This is simply slow switching with minimum dwell time 2
    val mode1 = ("mode1", ode1, None, List(("mode2", Some("3".asTerm)))) // 1 -> 2
    val mode2 = ("mode2", ode2, None, List(("mode1", Some("3".asTerm)))) // 2 -> 1

    val cs = Timed(List(mode1, mode2), Variable("u"), Variable("timer"))

    val v1 = "2*x1^2+x2^2".asTerm
    val v2 = "x1^2+2*x2^2".asTerm

    val spec = stabilitySpec(cs)
    val pr = proveBy(
      Imply("mode1()=1 & mode2()=2".asFormula, spec),
      implyR(1) & proveStabilityTimeMLF(v1 :: v2 :: Nil, "1/4>0".asFormula :: "1/4>0".asFormula :: Nil)(1),
    )

    println(pr)
    pr shouldBe Symbol("proved")

    val spec2 = attractivitySpec(cs)
    val pr2 = proveBy(
      Imply("mode1()=1 & mode2()=2".asFormula, spec2),
      implyR(1) &
        proveAttractivityTimeMLF(v1 :: v2 :: Nil, "1/4>0".asFormula :: "1/4>0".asFormula :: Nil, "1/4-7/30".asTerm)(1),
    )

    println(pr2)
    pr2 shouldBe Symbol("proved")
  }

  it should "prove timed system stable 2" in withMathematica { _ =>
    // Zhai, Hu, Yasuda & Michel Example 1
    val ode1 = "x1'=x2,x2'=x1".asDifferentialProgram
    val ode2 = "x1'=-2*x1+x2,x2'=x1-2*x2".asDifferentialProgram

    val mode1 = ("mode1", ode1, Some("1/10".asTerm), List(("mode2", None))) // 1 -> 2
    val mode2 = ("mode2", ode2, None, List(("mode1", Some("3/10".asTerm)))) // 2 -> 1

    val cs = Timed(List(mode1, mode2), Variable("u"), Variable("timer"))

    val v1 = "x1^2+x2^2".asTerm
    val v2 = "x1^2+x2^2".asTerm

    val spec = stabilitySpec(cs)

    val pr = proveBy(
      Imply("mode1()=1 & mode2()=2".asFormula, spec),
      implyR(1) & proveStabilityTimeMLF(v1 :: v2 :: Nil, "-2 <= 0".asFormula :: "2 > 0".asFormula :: Nil)(1),
    )

    println(pr)
    pr shouldBe Symbol("proved")

    val spec2 = attractivitySpec(cs)

    val pr2 = proveBy(
      Imply("mode1()=1 & mode2()=2".asFormula, spec2),
      implyR(1) &
        proveAttractivityTimeMLF(v1 :: v2 :: Nil, "-2 <= 0".asFormula :: "2 > 0".asFormula :: Nil, "1/100".asTerm)(1),
    )

    println(pr2)
    pr2 shouldBe Symbol("proved")
  }

  // Works, but slow and requires configuring to degree 15 and factor 1.2 Taylor expansion
  it should "prove timed system stable 3" taggedAs TodoTest ignore withMathematica { _ =>
    // Zhai, Hu, Yasuda & Michel Example 2
    val ode1 = "x1'=2*x1+2*x2,x2'=x1+3*x2".asDifferentialProgram
    val ode2 = "x1'=-2*x1+x2,x2'=x1-2*x2".asDifferentialProgram

    val mode1 = ("mode1", ode1, Some("1/2".asTerm), List(("mode2", None))) // 1 -> 2
    val mode2 = ("mode2", ode2, None, List(("mode1", Some("9/2".asTerm)))) // 2 -> 1

    val cs = Timed(List(mode1, mode2), Variable("u"), Variable("timer"))

    val v1 = "2*x1^2+x2^2".asTerm
    val v2 = "x1^2+x2^2".asTerm

    val spec = stabilitySpec(cs)
    val pr = proveBy(
      Imply("mode1()=1 & mode2()=2".asFormula, spec),
      implyR(1) &
        // Works, but slow and requires configuring to degree 15 and factor 1.2 Taylor expansion
        proveStabilityTimeMLF(v1 :: v2 :: Nil, "-9 <= 0".asFormula :: "2 > 0".asFormula :: Nil)(1),
    )

    println(pr)
    pr shouldBe Symbol("proved")

    val spec2 = attractivitySpec(cs)
    val pr2 = proveBy(
      Imply("mode1()=1 & mode2()=2".asFormula, spec2),
      implyR(1) &
        proveAttractivityTimeMLF(v1 :: v2 :: Nil, "-9 <= 0".asFormula :: "2 > 0".asFormula :: Nil, "0.01".asTerm)(1),
    )

    println(pr2)
    pr2 shouldBe Symbol("proved")
  }

  it should "prove timed system stable 4" in withMathematica { _ =>
    // Cyclic slow switching
    val ode1 = "x1'=-x1/8-x2,x2'=2*x1-x2/8".asDifferentialProgram
    val ode2 = "x1'=-x1/8-2*x2,x2'=x1-x2/8".asDifferentialProgram
    val ode3 = "x1'=-x1,x2'=-x2".asDifferentialProgram

    val mode1 = ("mode1", ode1, None, List(("mode2", Some("3".asTerm)))) // 1 -> 2
    val mode2 = ("mode2", ode2, None, List(("mode3", None))) // 2 -> 3
    val mode3 = ("mode3", ode3, None, List(("mode1", Some("0.4".asTerm)))) // 3 -> 1

    val cs = Timed(List(mode1, mode2, mode3), Variable("u"), Variable("timer"))

    val spec = stabilitySpec(cs)

    val v1 = "2*x1^2+x2^2".asTerm
    val v2 = "x1^2+2*x2^2".asTerm
    val v3 = "x1^2+x2^2".asTerm

    val pr = proveBy(
      Imply("mode1()=1 & mode2()=2 & mode3()=3".asFormula, spec),
      implyR(1) & proveStabilityTimeMLF(
        v1 :: v2 :: v3 :: Nil,
        "1/4 > 0".asFormula :: "1/4 > 0".asFormula :: "2 > 0".asFormula :: Nil,
      )(1),
    )

    println(pr)
    pr shouldBe Symbol("proved")

    val spec2 = attractivitySpec(cs)

    val pr2 = proveBy(
      Imply("mode1()=1 & mode2()=2 & mode3()=3".asFormula, spec2),
      implyR(1) & proveAttractivityTimeMLF(
        v1 :: v2 :: v3 :: Nil,
        "1/4 > 0".asFormula :: "1/4 > 0".asFormula :: "2 > 0".asFormula :: Nil,
        "1/4-7/30".asTerm,
      )(1),
    )

    println(pr2)
    pr2 shouldBe Symbol("proved")
  }

  it should "be robust to mode expansion" in withMathematica { _ =>
    val v1 = "17.9*x1^2-2*0.89*x1*x2+179*x2^2".asTerm
    val v2 = "739*x1^2-2*38.1*x1*x2+91.8*x2^2".asTerm

    val pr = proveBy(
      " ==>  \\forall eps (eps>0->\\exists del (del>0&\\forall x1 \\forall x2 (x1^2+x2^2 < del^2->[{mode:=0;++mode:=1;}{{?mode=0;{?(-10)*x1-x2=0;mode:=1;++mode:=mode;}++?mode=1;{?2*x1-x2=0;mode:=0;++mode:=mode;}}{?mode=0;{x1'=-x1-100*x2,x2'=10*x1-x2}++?mode=1;{x1'=x1+10*x2,x2'=(-100)*x1+x2&(-10)*x1-x2>=0&2*x1-x2>=0}}}*]x1^2+x2^2 < eps^2)))"
        .asSequent,
      proveStabilityStateMLF(v1 :: v2 :: Nil)(1),
    )

    println(pr)
    pr shouldBe Symbol("proved")
  }

  "state switch" should "check ODE active in domain" in withMathematica { _ =>
    val ode1 = ODESystem("x'=-1".asDifferentialProgram, "x > 0".asFormula)
    val ode2 = ODESystem("x'=-1".asDifferentialProgram, "x >= 0".asFormula)

    odeActive(ode1, True).isEmpty shouldBe false // Some((Unable to leave ODE {x'=(-1)&x>0},Map(x -> 0)))
    odeActive(ode2, True) shouldBe None
    odeActive(ode1, "x > 1".asFormula) shouldBe None // Bad point is excluded by global domain
  }

  it should "check activity for recitation 4 example" in withMathematica { _ =>
    val ode1 = "{x'=v & l <= x & x <= r}".asProgram.asInstanceOf[ODESystem]
    val ode2 = "{x'=v & !(l <= x & x <= r)}".asProgram.asInstanceOf[ODESystem]

    odeActive(ode1, True) shouldBe None
    // Bad event trigger domain separation:
    // Some((Unable to enter ODE {x'=v&!(l<=x&x<=r)},Map(l -> 0, r -> 1, v -> (-1), x -> 0)))
    odeActive(ode2, True).isEmpty shouldBe false
    // The other side is problematic too:
    // Some((Unable to enter ODE {x'=v&!(l<=x&x<=r)},Map(l -> 0, r -> 1, v -> 1, x -> 1)))
    odeActive(ode2, "v >= 0".asFormula).isEmpty shouldBe false
  }

  it should "check event triggering" in withMathematica { _ =>
    val ode1 = "{x'=v, v'=-g & x >= 0 & x <= 5}".asProgram.asInstanceOf[ODESystem]
    val ode2 = "{x'=v, v'=-g & x > 5}".asProgram.asInstanceOf[ODESystem]

    odeActive(ode1, True) shouldBe None
    // Bad event domain split when x=5
    // Some((Unable to enter ODE {x'=v,v'=-g&x>5},Map(g -> 0, v -> 1, x -> 5)))
    odeActive(ode2, True).isEmpty shouldBe false

    // Points without evolution
    // Some((System cannot evolve forwards,Map(g -> (-1), v -> 0, x -> 5)))
    stateSwitchActive(List(ode1)).isEmpty shouldBe false
    // Some((System cannot evolve forwards,Map(g -> 1, v -> 0, x -> 0)))
    stateSwitchActive(List(ode1), "g > 0".asFormula).isEmpty shouldBe false

    // "x=0" is somewhat a special case in this model so ignore it (ball bounces at x = 0)
    // Some((System cannot evolve forwards,Map(g -> 1, v -> 1, x -> 5)))
    stateSwitchActive(List(ode1), "g > 0 & x > 0".asFormula).isEmpty shouldBe false
    // Every point can locally evolve (if we fixed ode2's domain)
    stateSwitchActive(List(ode1, ode2), "g > 0 & x > 0".asFormula) shouldBe None
  }

  it should "try ADHS example" in withMathematica { _ =>
    // Some bad examples
    val ode1 = "{x1'=0,x2'=1 & x1 >= x2}".asProgram.asInstanceOf[ODESystem]
    val ode2 = "{x1'=-1,x2'=0 & x1 < x2}".asProgram.asInstanceOf[ODESystem]
    val ode22 = "{x1'=1,x2'=0 & x1 <= x2}".asProgram.asInstanceOf[ODESystem]

    odeActive(ode1, True) shouldBe None
    // Some((Unable to enter ODE {x1'=(-1),x2'=0&x1 < x2},Map(x1 -> 0, x2 -> 0)))
    odeActive(ode2, True).isEmpty shouldBe false
    odeActive(ode22, True) shouldBe None
    // Some((System cannot evolve forwards,Map(x1 -> 0, x2 -> 0)))
    stateSwitchActive(List(ode1, ode22)).isEmpty shouldBe false // missing sliding ,ode

    // Fixed with third ODE for sliding mode
    val ode3 = "{x1'=1/2,x2'=1/2 & x1 = x2}".asProgram.asInstanceOf[ODESystem]
    odeActive(ode3, True) shouldBe None
    stateSwitchActive(List(ode1, ode22, ode3)) shouldBe None

    // Fixed with hysteresis
    val ode1E = "{x1'=0,x2'=1 & x1 >= x2 - eps}".asProgram.asInstanceOf[ODESystem]
    val ode2E = "{x1'=1,x2'=0 & x1 <= x2 + eps}".asProgram.asInstanceOf[ODESystem]

    odeActive(ode1E, True) shouldBe None
    odeActive(ode2E, True) shouldBe None
    stateSwitchActive(List(ode1E, ode2E), "eps > 0".asFormula) shouldBe None
  }

  it should "check nonholonomic integrator" in withMathematica { _ =>
    val ode1 = "{x' = -x+a*y, y' = -y-a*x, z'= x*(-y-a*x) - y*(-x+a*y) & z>=0}".asProgram.asInstanceOf[ODESystem]
    val ode2 = "{x' = -x-a*y, y' = -y+a*x, z'= x*(-y+a*x) - y*(-x-a*y) & z<=0}".asProgram.asInstanceOf[ODESystem]
    val ode3 = "{x' = -x, y' = -y, z'= x*(-y) - y*(-x) & z=0}".asProgram.asInstanceOf[ODESystem]

    odeActive(ode1, True) shouldBe None
    odeActive(ode2, True) shouldBe None
    odeActive(ode3, True) shouldBe None
    stateSwitchActive(List(ode1, ode2, ode3)) shouldBe None
  }

  "stability" should "specify stability for ODEs" in withMathematica { _ =>
    val ode = "{x' = -x, y'= -y, z'= -z * a}".asProgram

    val stab1 = stableOrigin(ode)
    val stab2 = stableOrigin(ode, varsopt = Some(List("x", "y", "z").map(s => (s.asVariable, Number(0)))))
    val stab3 = stableOrigin(ode, varsopt = None, restr = Some("a > 0".asFormula))
    println(stab1)
    println(stab2)
    println(stab3)

    stab1 shouldBe
      "\\forall eps (eps>0->\\exists del (del>0&\\forall z \\forall y \\forall x (z^2+y^2+x^2 < del^2->[{x'=-x,y'=-y,z'=-z*a}]z^2+y^2+x^2 < eps^2)))"
        .asFormula
    stab2 shouldBe
      "\\forall eps (eps>0->\\exists del (del>0&\\forall x \\forall y \\forall z ((x-0)^2+(y-0)^2+(z-0)^2 < del^2->[{x'=-x,y'=-y,z'=-z*a}](x-0)^2+(y-0)^2+(z-0)^2 < eps^2)))"
        .asFormula
    stab3 shouldBe
      "\\forall eps (eps>0->\\exists del (del>0&\\forall z \\forall y \\forall x (a>0&z^2+y^2+x^2 < del^2->[{x'=-x,y'=-y,z'=-z*a}]z^2+y^2+x^2 < eps^2)))"
        .asFormula
  }

//  it should "be reusable for switched systems" in withMathematica { _ =>
//    val ode1 = ODESystem("x'=-x".asDifferentialProgram, True)
//    val ode2 = ODESystem("x'=-x^3".asDifferentialProgram, True)
//    val ode3 = ODESystem("x'=-x^5".asDifferentialProgram, True)
//
//    val ss = stateSwitch(List(ode1,ode2,ode3))
//
//    val stab = stableOrigin(ss)
//    println(stab)
//
//    stab shouldBe "\\forall eps (eps>0->\\exists del (del>0&\\forall x (x^2 < del^2->[{{{x'=-x}++{x'=-x^3}}++{x'=-x^5}}*]x^2 < eps^2)))".asFormula
//  }

  // todo: need to handle arithmetic much better here (very slow)
  it should "prove ODE example stable" taggedAs TodoTest ignore withMathematica { _ =>
    val ode = "{x1' = -x1 + x2^3 - 3*x3*x4,x2' = -x1 - x2^3,x3' = x1*x4 - x3,x4' = x1*x3 - x4^3}".asProgram
    val stab1 = stableOrigin(ode)

    val pr = proveBy(stab1, proveStable("2*x1^2 + x2^4 + 3201/1024*x3^2 + 2943/1024*x4^2".asTerm, ode)(1))

    println(pr)
    pr shouldBe Symbol("proved")
  }
  // todo: need to handle arithmetic much better here (too slow / doesn't prove)
  it should "prove large ODE stable" taggedAs TodoTest ignore withMathematica { _ =>
    val ode =
      "{x1' = -x1^3+4*x2^3-6*x3*x4,x2' = -x1-x2+x5^3,x3' = x1*x4-x3+x4*x6,x4' = x1*x3+x3*x6-x4^3,x5' = -2*x2^3-x5+x6,x6' = -3*x3*x4-x5^3-x6}"
        .asProgram
    val stab1 = stableOrigin(ode)

    val pr = proveBy(stab1, proveStable("2*x1^2 + 4*x2^4 + x3^2 + 11*x4^2 + 2*x5^4 + 4*x6^2".asTerm, ode)(1))

    println(pr)
  }

  "time dependent" should "model time dependency" in withMathematica { _ =>
    val ode1 = "{x'=x}".asProgram.asInstanceOf[ODESystem]
    val ode2 = "{x'=-x}".asProgram.asInstanceOf[ODESystem]

    val tt = timeSwitch(
      List((ode1, Some(Number(5))), (ode2, None)),
      List(List((1, Number(5))), List((0, Number(5)))),
      topt = Some(Variable("t_")),
    )

    println(tt)
    tt shouldBe
      ("{s_:=0;{u_:=0;++u_:=1;}}" + "{" + " {?u_=0;{{?s_>=5;u_:=1;}s_:=0;++u_:=0;}++" +
        "  ?u_=1;{{?s_>=5;u_:=0;}s_:=0;++u_:=1;}" + " }" + " {?u_=0;{t_'=1,s_'=1,x'=x&true&s_<=5}++" +
        "  ?u_=1;{t_'=1,s_'=1,x'=-x}" + " }" + "}*").asProgram
  }

  it should "model slow switching" in withMathematica { _ =>
    val ode1 = "{x'=x}".asProgram.asInstanceOf[ODESystem]
    val ode2 = "{x'=-x}".asProgram.asInstanceOf[ODESystem]

    val tt = slowSwitch(List(ode1, ode2), Number(5))

    println(tt)

    tt shouldBe
      ("{s_:=0;{u_:=0;++u_:=1;}}" + "{" + "   {?u_=0;{{?s_>=5;u_:=1;}s_:=0;++u_:=0;}++" +
        "    ?u_=1;{{?s_>=5;u_:=0;}s_:=0;++u_:=1;}}" + "   {?u_=0;{s_'=1,x'=x}++" + "    ?u_=1;{s_'=1,x'=-x}}" + "}*")
        .asProgram
  }

  it should "do a manual slow stability proof" in withMathematica { _ =>
    val ode1 = "{x1'=-x1/8-x2,x2'=2*x1-x2/8}".asProgram.asInstanceOf[ODESystem]
    val ode2 = "{x1'=-x1/8-2*x2,x2'=x1-x2/8}".asProgram.asInstanceOf[ODESystem]

    val lyap1 = "2*x1^2+x2^2".asTerm
    val lyap2 = "x1^2+2*x2^2".asTerm
    val lyaps = List(lyap1, lyap2)

    val tt = slowSwitch(List(ode1, ode2), Number(3))
    val stab = stableOrigin(tt)

    val vars = List("x1", "x2").map(_.asVariable)
    val normsq = vars.map(e => Power(e, Number(2))).reduceLeft(Plus) // ||x||^2

    val eps = Variable("eps")
    val del = Variable("del")
    val epssq = Power(eps, Number(2))
    val delsq = Power(del, Number(2))

    val w = Variable("w_")

    val epsgeq = lyaps.map(t => GreaterEqual(t, w)).reduceLeft(And)

    val epsbound = vars.foldRight(Imply(Equal(normsq, epssq), epsgeq): Formula)((v, f) => Forall(v :: Nil, f))
    val epsw = Exists(w :: Nil, And(Greater(w, Number(0)), epsbound))

    val delless = lyaps.map(t => Less(t, w)).reduceLeft(And)
    val delw = And(
      And(Greater(del, Number(0)), Less(del, eps)),
      vars.foldRight(Imply(Less(normsq, delsq), delless): Formula)((v, f) => Forall(v :: Nil, f)),
    )

    val exp = "1 + (s_*1/4) + (s_*1/4)^2/2 + (s_*1/4)^3/6".asTerm

    val u = Variable("u_")

    val lexp = lyaps.zipWithIndex.map(fi => And(Equal(u, Number(fi._2)), Less(Times(fi._1, exp), w))).reduceLeft(Or)

    val invariant = And(And("s_>=0".asFormula, Less(normsq, epssq)), lexp)

    val pr = proveBy(
      stab,
      allR(1) & implyR(1) &
        cutR(epsw)(1) <
        (
          // Automation should prove these bounds separately and then pick the smallest
          QE,
          implyR(1) & existsL(-2) & andL(-2) &
            existsRmon(delw)(1) <
            (
              hideL(-3) & QE,
              andL(-4) & andL(-4) &
                andR(1) <
                (
                  id,
                  (allR(1) * 2) & implyR(1) & (allL(-4) * 2) &
                    implyL(-4) <
                    (
                      id,
                      composeb(1) & hideL(-1) & hideL(-1) &
                        generalize(invariant)(1) <
                        (
                          chase(1) & hideL(-3) & QE,
                          andL(-1) & hideL(Symbol("Llast")) &
                            throughout(invariant)(1) <
                            (
                              prop,
                              prop,
                              cohideOnlyL(-1) & andL(-1) & chase(1) &
                                orL(-2) <
                                (
                                  andR(1) <
                                    (
                                      QE, // can do more simplification
                                      implyR(1) & hideR(1) & QE,
                                    ),
                                  andR(1) <
                                    (
                                      implyR(1) & hideR(1) & QE,
                                      QE, // can do more simplification
                                    ),
                                ),
                              andL(-1) & hideL(-2) & andL(-1) & chase(1) &
                                orL(-3) <
                                (
                                  andR(1) <
                                    (
                                      implyR(1) & exhaustiveEqL2R(Symbol("Llast")) &
                                        // this sequence of cuts sets things up in the right order
                                        dC("s_>=0".asFormula)(1) <
                                        (
                                          dC(Less(Times(lyap1, exp), w))(1) <
                                            (
                                              dC(Less(normsq, epssq))(1) <
                                                (
                                                  DW(1) & G(1) & QE, // can be simplified
                                                  ODEInvariance.dCClosure(1) <
                                                    (
                                                      hideL(-1) & QE,
                                                      dC(Imply(Equal(normsq, epssq), epsgeq))(1) <
                                                        (
                                                          DW(1) & G(1) & QE,
                                                          dW(1) & andL(-1) & andL(-2) & allL(-2) & allL(-2) & id,
                                                        ),
                                                    ),
                                                ),
                                              hideL(-1) & ODE(1),
                                            ),
                                          hideL(-1) & ODE(1),
                                        ),
                                      implyR(1) & hideR(1) & QE,
                                    ),
                                  andR(1) <
                                    (
                                      implyR(1) & hideR(1) & QE,
                                      implyR(1) & exhaustiveEqL2R(Symbol("Llast")) &
                                        dC("s_>=0".asFormula)(1) <
                                        (
                                          dC(Less(Times(lyap2, exp), w))(1) <
                                            (
                                              dC(Less(normsq, epssq))(1) <
                                                (
                                                  DW(1) & G(1) & QE, // can be simplified
                                                  ODEInvariance.dCClosure(1) <
                                                    (
                                                      hideL(-1) & QE,
                                                      dC(Imply(Equal(normsq, epssq), epsgeq))(1) <
                                                        (
                                                          DW(1) & G(1) & QE,
                                                          dW(1) & andL(-1) & andL(-2) & allL(-2) & allL(-2) & id,
                                                        ),
                                                    ),
                                                ),
                                              hideL(-1) & ODE(1),
                                            ),
                                          hideL(-1) & ODE(1),
                                        ),
                                    ),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    )

    println(pr)
    pr shouldBe Symbol("proved")
  }

}
