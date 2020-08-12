package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import edu.cmu.cs.ls.keymaerax.btactics.{Integrator, RandomFormula, TacticTestBase}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.RandomParserTests
import edu.cmu.cs.ls.keymaerax.tags._
import fastparse.Parsed.{Failure, Success}
import fastparse._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.ProofChecker.ProofCheckException

class EndToEndTests extends TacticTestBase {
  val check: String => Formula = Kaisar.apply

  "full proof checker" should "check box loop" in withMathematica { _ =>
      val pfStr = "?xZero:(x >= 1); {{x := x + 1; !IS:(x >= 1) using x xZero by auto;}*} !xFin:(x>=0) using xZero by auto;"
      val ff = check(pfStr)
      ff shouldBe "[?x>=1;x_0:=x;{x_1:=x_0+1; {?x_1>=1;}^@ x_0:=x_1;}*{?x_0>=0;}^@]true".asFormula
  }

  it should "resolve simple backward state labels:" in withMathematica { _ =>
    val pfStr =
        "init: ?xZero:(x >= 1);" +
        "  !IH: (x >= x@init) by auto;" +
        "  {loop: x:=x+1;" +
        "  !step:(x >= x@loop) by auto; " +
        "  !IS:(x >= x@init) using step IH by auto;" +
        "}*" +
        "!final:(x >= 0) using xZero IH by auto;"
    val ff = check(pfStr)
    ff shouldBe "[?x>=1;{?x>=x;}^@ x_0:=x;{x_1:=x_0+1;  {?x_1>=x_0;}^@ {?x_1>=x;}^@ x_0:=x_1;}*{?x_0>=0;}^@]true".asFormula
  }

  it should "support straight-line forward label" in withMathematica { _ =>
    val pfStr =
      "!xLater:(x@final = 4) by auto;" +
      "x := 0;" +
      "x := x + 1;" +
      "x := x + 3;" +
      "final: !result:(x > 3) using xLater by auto;"
    val ff = check(pfStr)
    ff shouldBe "[{?(0 + 1 + 3 = 4);}^@ x_0:= 0; x_1 := x_0 + 1; x_2 := x_1 + 3; {?(x_2>3);}^@]true".asFormula
  }

  it should "support straight-line nondeterministic forward label" in withMathematica { _ =>
    val pfStr =
      "?zInit:(z := 5);" +
      "!xLater:(x@final(z) = 10) using zInit by auto;" +
      "y := *;" +
      "x := z + y;" +
      "final(y):" +
      "!last:(y = z -> x = 10) using xLater by auto;"
    val ff = check(pfStr)
    ff shouldBe "[{z_0:=5; {?(z_0 + z_0 = 10);}^@ y_0 :=*; x_0 := z_0 + y_0; {?(y_0=z_0-> x_0=10);}^@}]true".asFormula
  }

  it should "support forward label separated by irrelevant choice " in withMathematica { _ =>
    val pfStr =
      "?zInit:(z := 5);" +
        "!xLater:(x@final(z) = 10) using zInit by auto;" +
        "y := *;" +
        "{k := 0; ++ k := 1;}" +
        "x := z + y;" +
        "final(y):" +
        "!last:(y = z -> x = 10) using xLater by auto;"
    val ff = check(pfStr)
    ff shouldBe "[{z_0:=5; {?(z_0 + z_0 = 10);}^@ y_0 :=*; {k_0 := 0; ++ k_0 := 1;} x_0 := z_0 + y_0; {?(y_0=z_0-> x_0=10);}^@}]true".asFormula
  }

  it should "support forward label separated by irrelevant choice inside of loop " in withMathematica { _ =>
    val pfStr =
      "?zInit:(z := 5);" +
      "!base:(true) by auto;" +
      "{!xLater:(x@final(z) = 10) using zInit by auto;" +
      "y := *;" +
      "{k := 0; ++ k := 1;}" +
      "x := z + y;" +
      "final(y):" +
      "!last:(y = z -> x = 10) using xLater by auto;" +
      "!istep:(true) by auto;" +
      "}*"
    val ff = check(pfStr)
    ff shouldBe ("[z_0:=5; " +
      "{?(true);}^@ " +
      "{y_0 := y; k_0 := k; x_0 := x;}" +
      "{" +
      "  {?(z_0 + z_0 = 10);}^@ " +
      "  y_1 :=*; " +
      "  {k_1 := 0; ++ k_1 := 1;} " +
      "  x_1 := z_0 + y_1; " +
      "  {?(y_1=z_0-> x_1=10);}^@ " +
      "  {?(true);}^@" +
      "  {y_0 := y_1; k_0 := k_1; x_0 := x_1;}" +
      "}*]true").asFormula
  }

  it should "support forward label separated by irrelevant loop " in withMathematica { _ =>
    val pfStr =
      "?zInit:(z := 5);" +
        "!xLater:(x@final(z) = 10) using zInit by auto;" +
        "y := *;" +
        "!base:(true) by auto;" +
        "{{k := 0; ++ k := 1;} !is:(true) by auto;}*" +
        "x := z + y;" +
        "final(y):" +
        "!last:(y = z -> x = 10) using xLater by auto;"
    val ff = check(pfStr)
    ff shouldBe "[{z_0:=5; {?(z_0 + z_0 = 10);}^@ y_0 :=*; {?(true);}^@ k_0:=k; {{k_1 := 0; ++ k_1 := 1;}{?(true);}^@k_0:=k_1;}* x_0 := z_0 + y_0; {?(y_0=z_0-> x_0=10);}^@}]true".asFormula
  }

  it should "support forward label going outside box choice" in withMathematica { _ =>
    val pfStr = "x:=0; {!foo:(x@final > 0) by auto; ++ x:=1;} x:=1; final:"
    val ff = check(pfStr)
    ff shouldBe "[x_0:=0; {{{?(1 > 0);}^@x_1:=x_0; } ++ x_1 := 1;} x_2:=1;]true".asFormula
  }

  it should "prove solution cut that requires domain constraint assumption" in withMathematica { _ =>
    val pfStr = "?tInit:(t:= 0); ?xInit:(x:= 1);  {t' = 1, x' = -1 & xRange:(x >=0) & !tRange:(t <= 1) using xInit tInit xRange by solution};"
    val ff = check(pfStr)
    ff shouldBe "[t_0:=0; x_0:= 1; {t_1 := t_0;x_1:=x_0;}{t_1' = 1, x_1' = -1 & x_1>=0}]true".asFormula
  }

  it should "prove diffcut" in withMathematica { _ =>
    val pfStr = "?yZero:(y:=0); ?xZero:(x:=1); x' = y & !dc:(x > 0) using xZero yZero by solution;"
    val ff = check(pfStr)
    ff shouldBe "[y_0:=0; x_0:=1;x_1:=x_0;{x_1' = y_0}]true".asFormula
  }

  it should "catch bad diffcut" in withMathematica { _ =>
    val pfStr = "?xZero:(x:=1); x' = -1 & !dc:(x > 0) using xZero by induction;"
    a[ProofCheckException] shouldBe thrownBy(check(pfStr))
  }

  it should "prove dc-assign" in withMathematica { _ =>
    val pfStr = "t:= 0; {t' = 1, x' = y & t := T};"
    val ff = check(pfStr)
    ff shouldBe "[t_0:= 0; {t_1 := t_0; x_0 := x;}{{t_1' = 1, x_0' = y}; ?(t_1= T);}^@]true".asFormula
  }


  // @TODO: Write tests that make sure to actually prove T >= 0
  // @TODO: elaborator should catch unbound references
  // @TODO: consider annotations on modifiers because cuts are too awkward
  it should "prove and then use dc-assign" in withMathematica { _ =>
    val pfStr = "t := 0; x:= 0; {t' = 1, x' = 2 & t := T & !max:t<=T by solution}; !final:(x = 2*T) using max ... by auto;"
    val ff = check(pfStr)
    ff shouldBe "[t_0:= 0; x_0 := 0; {t_1:=t_0;x_1:=x_0;}{{t_1' = 1, x_1' = 2 & t_1<=T}; ?(t_1=T);}^@{?(x_1=2*T);}^@]true".asFormula
  }

  it should "prove renamed dc-assign" in withMathematica { _ =>
    val pfStr = "timer:= 0; {timer' = 1, x' = y & timer := T};"
    val ff = check(pfStr)
    ff shouldBe "[timer_0:= 0; {timer_1:=timer_0;x_0:=x;}{{timer_1' = 1, x_0' = y}; ?(timer_1 = T);}^@]true".asFormula
  }

  it should "prove diamond assertion " in withMathematica { _ =>
    val pfStr = "t:= 0; {t' = 1, x' = y & t := T & !dc:(t >= 0) by induction};"
    val ff = check(pfStr)
    ff shouldBe "[t_0:=0; {t_1:=t_0;x_0:=x;}{{t_1'=1, x_0'=y & t_1>=0}; ?(t_1=T);}^@]true".asFormula
  }

  it should "prove triple induction " in withMathematica { _ =>
    val pfStr = "?xInit:(x:=0); ?yInit:(y:=0); ?zInit:(z:=0); " +
      "{x'=z, y' = 1, z' = y " +
      "& !yInv:(y >= 0) using yInit  by induction" +
      "& !zInv:(z >= 0) using zInit yInv by induction" +
      "& !xInv:(x >= 0) using xInit zInv by induction" +
      "};"
    val ff = check(pfStr)
    ff shouldBe "[x_0:=0; y_0:=0;z_0:=0;{x_1:=x_0;y_1:=y_0;z_1:=z_0;}{x_1'=z_1, y_1'=1, z_1'=y_1}]true".asFormula
  }

  it should "catch invalid dc-assign 3: wrong clock" in withMathematica { _ =>
    val pfStr = "t:= 0; {t' = 2, x' = y & t := T};"
    a[ProofCheckException] shouldBe thrownBy(check(pfStr))
  }

  // @TODO: Write a test that gives a name to an ODE solution equation
  // @TODO: Write a test that exercises ODE ghost scope escaping
  // @TODO: Write a test that uses an alternative ?x:P syntax for domain constraints
  // @TODO: Write a test that expects initial values to be automatically found in dI
  // @TODO: Write tests that exercise pattern match statements, let statements, pattern selectors,

  /* @TODO: This test would be prettier and faster if (1) ODE solution assignments can be annotated and
   * (2) Context fact lookup was fully precise when looking up multiple facts, each on multiple branches.
   */
  it should "Prove 1d car safety" in withMathematica { _ =>
    val pfStr =
      "?xInit:(x:=0); ?vInit:(v:=0); ?acc:(A > 0); ?brk:(B > 0); ?tstep:(T > 0); ?separate: (x < d);" +
      "!inv:(v^2/(2*B) <= (d - x) & v >= 0) using xInit vInit brk separate by auto;" +
      "{{switch {" +
        "case accel: ((v + T*A)^2/(2*B) <= (d - (x + v*T + (A*T^2)/2))) =>" +
        "  ?accA:(a := A);" +
        "  !safe1:((v + T*a)^2/(2*B) <= (d - (x + v*T + (a*T^2)/2))) using accel acc accA inv brk tstep ... by auto;" +
        "  note safeAcc = andI(safe1, accA);" +
        "case brake: ((v + T*A)^2/(2*B)  + 1 >= (d - (x + v*T + (A*T^2)/2))) =>" +
        "  ?accB:(a := -B);" +
        "  ?fast:(v >= B*T);" +
        "  !safe2:((v + T*a)^2/(2*B) <= (d - (x + v*T + (a*T^2)/2))) using brake acc accB brk inv tstep fast ... by auto;" +
        "  note safeAcc = andI(safe2, andI(accB, fast));" +
        "}}" +
        "t:= 0;" +
        "{x' = v, v' = a, t' = 1 & dc: (t <= T & v>=0)};" +
        "!invStep: (v^2/(2*B) <= (d - x) & v>= 0) using safeAcc inv dc acc brk tstep ... by auto;" +
      "}*" +
       "!safe:(x <= d & v >= 0) using inv brk  by auto;"
    val ff = check(pfStr)
    val discreteFml =
      ("[x_0:=0;v_0:=0;?A>0;?B>0;?T>0;?x_0 < d;" +
        "{?v_0^2/(2*B)<=d-x_0&v_0>=0;}^@" +
        "{x_1:=x_0;v_1:=v_0;a_0:=a;t_0:=t;}" +
        "{{{?(v_1+T*A)^2/(2*B)+1>=d-(x_1+v_1*T+A*T^2/2);" +
          "a_1:=-B;?v_1>=B*T;" +
          "{?(v_1+T*a_1)^2/(2*B)<=d-(x_1+v_1*T+a_1*T^2/2);}^@" +
          "{?(v_1+T*a_1)^2/(2*B)<=d-(x_1+v_1*T+a_1*T^2/2)&a_1=-B&v_1>=B*T;}^@}" +
        "^@++" +
        "{?(v_1+T*A)^2/(2*B)<=d-(x_1+v_1*T+A*T^2/2);" +
        "  a_1:=A;" +
        "  {?(v_1+T*a_1)^2/(2*B)<=d-(x_1+v_1*T+a_1*T^2/2);}^@" +
        "  {?(v_1+T*a_1)^2/(2*B)<=d-(x_1+v_1*T+a_1*T^2/2)&a_1=A;}^@}^@}^@" +
        "t_1:=0;" +
        "{x_2:=x_1;v_2:=v_1;t_2:=t_1;}" +
        "{x_2'=v_2,v_2'=a_1,t_2'=1&t_2<=T&v_2>=0}" +
        "{?v_2^2/(2*B)<=d-x_2&v_2>=0;}^@" +
        "x_1:=x_2;v_1:=v_2;a_0:=a_1;t_0:=t_2;}*" +
      "{?x_1<=d&v_1>=0;}^@]true").asFormula
    ff shouldBe discreteFml
  }

  it should "Prove 1d car safety with forward labels" in withMathematica { _ =>
    val pfStr =
      "?xInit:(x:=0); ?vInit:(v:=0); ?acc:(A > 0); ?brk:(B > 0); ?tstep:(T > 0); ?separate: (x < d);" +
        "!inv:(v^2/(2*B) <= (d - x) & v >= 0) using xInit vInit brk separate by auto;" +
        "{{switch {" +
        "case accel: ((v^2/(2*B))@ode(A, T) <= (d-x)@ode(A, T)) =>" +
        "  ?accA:(a := A);" +
        "  !safe1:((v^2/(2*B))@ode(a, T) <= (d-x)@ode(a, T)) using accel acc accA inv brk tstep ... by auto;" +
        "  note safeAcc = andI(safe1, accA);" +
        "case brake: ((v^2/(2*B))@ode(A, T) + 1 >= (d-x)@ode(A, T)) =>" +
        "  ?accB:(a := -B);" +
        "  ?fast:(v >= B*T);" +
        "  !safe2:((v^2/(2*B))@ode(a, T) <= (d-x)@ode(a, T)) using brake acc accB brk inv tstep fast ... by auto;" +
        "  note safeAcc = andI(safe2, andI(accB, fast));" +
        "}}" +
        "t:= 0;" +
        "{x' = v, v' = a, t' = 1 & dc: (t <= T & v>=0)};" +
        "ode(a, t):" +
        "!invStep: (v^2/(2*B) <= (d - x) & v>= 0) using safeAcc inv dc acc brk tstep ... by auto;" +
        "}*" +
        "!safe:(x <= d & v >= 0) using inv brk  by auto;"
    val ff = check(pfStr)

    val discreteFml =
      ("[x_0:=0;v_0:=0;?A>0;?B>0;?T>0;?x_0 < d;" +
        "{?v_0^2/(2*B)<=d-x_0&v_0>=0;}^@" +
        "{x_1:=x_0;v_1:=v_0;a_0:=a;t_0:=t;}" +
        "{{{?(A*T+v_1)^2/(2*B)+1>=d-(A*(T^2/2)+v_1*T+x_1);" +
        "a_1:=-B;?v_1>=B*T;" +
        "{?(a_1*T+v_1)^2/(2*B)<=d-(a_1*(T^2/2)+v_1*T+x_1);}^@" +
        "{?(a_1*T+v_1)^2/(2*B)<=d-(a_1*(T^2/2)+v_1*T+x_1)&a_1=-B&v_1>=B*T;}^@}" +
        "^@++" +
        "{?(A*T+v_1)^2/(2*B)<=d-(A*(T^2/2)+v_1*T+x_1);" +
        "  a_1:=A;" +
        "  {?(a_1*T+v_1)^2/(2*B)<=d-(a_1*(T^2/2)+v_1*T+x_1);}^@" +
        "  {?(a_1*T+v_1)^2/(2*B)<=d-(a_1*(T^2/2)+v_1*T+x_1)&a_1=A;}^@}^@}^@" +
        "t_1:=0;" +
        "{x_2:=x_1;v_2:=v_1;t_2:=t_1;}" +
        "{x_2'=v_2,v_2'=a_1,t_2'=1&t_2<=T&v_2>=0}" +
        "{?v_2^2/(2*B)<=d-x_2&v_2>=0;}^@" +
        "x_1:=x_2;v_1:=v_2;a_0:=a_1;t_0:=t_2;}*" +
        "{?x_1<=d&v_1>=0;}^@]true").asFormula
    ff shouldBe discreteFml
  }

  "Error message printer" should "nicely print missing semicolon;" in withMathematica { _ =>
    val pfStr =
      """?xInit:(x:=0); ?vInit:(v:=0); ?acc:(A > 0); ?brk:(B > 0); ?tstep:(T > 0); ?separate: (x < d)
        |!inv:(v^2/2*B <= (d - x) & v >= 0) using xInit vInit brk separate by auto;
        |{{switch {
        |case accel: ((v + T*A)^2/2*B <= (d - (x + v*T + (A*T^2)/2)) + 1) =>
        |  a := A;
        |  !safeAcc:((v + T*a)^2/2*B <= (d - (x + v*T + (a*T^2)/2))) using accel acc brk tstep by auto;
        |case brake: ((v + T*A)^2/2*B >= (d - (x + v*T + (A*T^2)/2))) =>
        |  a := -B;
        |  !safeAcc:((v + T*a)^2/2*B <= (d - (x + v*T + (a*T^2)/2))) using brake acc brk inv tstep by auto;
        |}}
        |t:= 0;
        |invStep: (v^2/2*B <= (d - x)) using safeAcc by auto;
        |}*
        |!safe:(x <= d & v >= 0) using inv by auto;""".stripMargin
    a[Exception] shouldBe thrownBy(check(pfStr))
  }

}
