/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

/**
 * Test Kaisar proofs, applying all passes of Kaisar end-to-end
 * @author
 *   Brandon Bohrer
 */
package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase
import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.KaisarProof._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tagobjects.TodoTest
import fastparse.Parsed.{Failure, Success}
import fastparse._

// @TODO: Decide how useful pattern selectors and match statements are. (match statements might be kind of useless)
// @TODO: Test end-to-end angelic loop proofs with nominals etc
// @TODO: Smart-QE for efficiency
// @TODO: Proper file format with "conclusion" and "proves" statements and refiner and "synthesize" maybe, declare rigids, detect wrong or undefined rigid names
// @TODO: Optimize loop checking case to fail early if loop body doesn't assert or note inductive statement as final step
// @TODO: ODE proof checking should include past cuts by default
// @TODO: Elaboration of abs, min, max should use intuitive auto-generated names, recover high-level messages if possible
// @TODO: Double-check abs, min, max elaboration to avoid needless branching
// @TODO: Use new contexts for all-around smart QE, which substitutes variables wherever possible (may need dependency analysis)
//   and which hides old irrelevant max, min, abs to reduce branching factor.
// @TODO: Discuss whether any compelling need for domain constraints at times other than initial and final

class EndToEndTests extends TacticTestBase {
  val check: String => Formula = Kaisar.single(_)._2

  "full proof checker" should "check box loop" in withMathematica { _ =>
    val pfStr =
      "?xZero:(x >= 1); {{x := x + 1; !IS:(x >= 1) using x xZero by auto;}*} !xFin:(x>=0) using xZero by auto;"
    val ff = check(pfStr)
    ff shouldBe "[?x_0>=1;x_1:=x_0;{x_2:=x_1+1; {?x_2>=1;}^@ x_1:=x_2;}*{?x_1>=0;}^@]true".asFormula
  }

  it should "handle reassignment after loop" in withMathematica { _ =>
    val pfStr =
      "?xZero:(x >= 1); {{x := x + 1; !IS:(x >= 1) using x xZero by auto;}*} !xFin:(x>=0) using xZero by auto; x:= x + 3;"
    val ff = check(pfStr)
    ff shouldBe "[?x_0>=1;x_1:=x_0;{x_2:=x_1+1; {?x_2>=1;}^@ x_1:=x_2;}*{?x_1>=0;}^@ x_2:=x_1+3;]true".asFormula

  }

  it should "resolve lets in assertions" in withMathematica { _ =>
    val pfStr = "let square(x) = x*x; !fact:(square(2) = 4) by auto;  !also:(square(2) >= 2) using fact by auto;"
    val ff = check(pfStr)
    ff shouldBe "[{?(2*2 = 4);}^@ {?(2*2 >= 2);}^@]true".asFormula
  }

  it should "expand let's free var at use site, not def" in withMathematica { _ =>
    val pfStr = SharedModels.letEvalAtUse
    val ff = check(pfStr)
    ff shouldBe "[x_1 := 0; x_2:=1; {?(x_2=1);}^@]true".asFormula
  }

  it should "support let inside @" in withMathematica { _ =>
    val pfStr = "let square(x) = x*x; !eq:(square(x)@last = 4) by auto; x:= 1; x:=3; x:=2; last:"
    val ff = check(pfStr)
    ff shouldBe "[{?(2 * 2 = 4);}^@ x_1 := 1; x_2 := 3; x_3 := 2;]true".asFormula
  }

  it should "support @ inside of let" in withMathematica { _ =>
    val pfStr = "let square(x) = (x*x)@last; !eq:(square(x) = 4) by auto; x:= 1; x:=3; x:=2; last:"
    val ff = check(pfStr)
    ff shouldBe "[{?(2 * 2 = 4);}^@ x_1 := 1; x_2 := 3; x_3 := 2;]true".asFormula
  }

  it should "resolve simple backward state labels:" in withMathematica { _ =>
    val pfStr = "init: ?xZero:(x >= 1);" + "  !IH: (x >= x@init) by auto;" + "  {loop: x:=x+1;" +
      "  !step:(x >= x@loop) by auto; " + "  !IS:(x >= x@init) using step IH by auto;" + "}*" +
      "!final:(x >= 0) using xZero IH by auto;"
    val ff = check(pfStr)
    ff shouldBe
      "[?x_0>=1;{?x_0>=x_0;}^@ x_1:=x_0;{x_2:=x_1+1;  {?x_2>=x_1;}^@ {?x_2>=x_0;}^@ x_1:=x_2;}*{?x_1>=0;}^@]true"
        .asFormula
  }

  it should "support straight-line forward label" in withMathematica { _ =>
    val pfStr = "!xLater:(x@final = 4) by auto;" + "x := 0;" + "x := x + 1;" + "x := x + 3;" +
      "final: !result:(x > 3) using xLater by auto;"
    val ff = check(pfStr)
    ff shouldBe "[{?(0 + 1 + 3 = 4);}^@ x_1:= 0; x_2 := x_1 + 1; x_3 := x_2 + 3; {?(x_3>3);}^@]true".asFormula
  }

  it should "support straight-line nondeterministic forward label" in withMathematica { _ =>
    val pfStr = "?zInit:(z := 5);" + "!xLater:(x@final(z) = 10) using zInit by auto;" + "y := *;" + "x := z + y;" +
      "final(y):" + "!last:(y = z -> x = 10) using xLater by auto;"
    val ff = check(pfStr)
    ff shouldBe "[{z_1:=5; {?(z_1 + z_1 = 10);}^@ y_1 :=*; x_1 := z_1 + y_1; {?(y_1=z_1-> x_1=10);}^@}]true".asFormula
  }

  it should "support forward label separated by irrelevant choice " in withMathematica { _ =>
    val pfStr = "?zInit:(z := 5);" + "!xLater:(x@final(z) = 10) using zInit by auto;" + "y := *;" +
      "{k := 0; ++ k := 1;}" + "x := z + y;" + "final(y):" + "!last:(y = z -> x = 10) using xLater by auto;"
    val ff = check(pfStr)
    ff shouldBe
      "[{z_1:=5; {?(z_1 + z_1 = 10);}^@ y_1 :=*; {k_1 := 0; ++ k_1 := 1;} x_1 := z_1 + y_1; {?(y_1=z_1-> x_1=10);}^@}]true"
        .asFormula
  }

  it should "support forward label separated by irrelevant choice inside of loop " in withMathematica { _ =>
    val pfStr = "?zInit:(z := 5);" + "!base:(true) by auto;" + "{!xLater:(x@final(z) = 10) using zInit by auto;" +
      "y := *;" + "{k := 0; ++ k := 1;}" + "x := z + y;" + "final(y):" +
      "!last:(y = z -> x = 10) using xLater by auto;" + "!istep:(true) by auto;" + "}*"
    val ff = check(pfStr)
    ff shouldBe
      ("[z_1:=5; " + "{?(true);}^@ " + "{x_1 := x_0; y_1 := y_0; k_1 := k_0;}" + "{" + "  {?(z_1 + z_1 = 10);}^@ " +
        "  y_2 :=*; " + "  {k_2 := 0; ++ k_2 := 1;} " + "  x_2 := z_1 + y_2; " + "  {?(y_2=z_1-> x_2=10);}^@ " +
        "  {?(true);}^@" + "  {x_1 := x_2; y_1 := y_2; k_1 := k_2;}" + "}*]true").asFormula
  }

  it should "support forward label separated by irrelevant loop " in withMathematica { _ =>
    val pfStr = "?zInit:(z := 5);" + "!xLater:(x@final(z) = 10) using zInit by auto;" + "y := *;" +
      "!base:(true) by auto;" + "{{k := 0; ++ k := 1;} !is:(true) by auto;}*" + "x := z + y;" + "final(y):" +
      "!last:(y = z -> x = 10) using xLater by auto;"
    val ff = check(pfStr)
    ff shouldBe
      "[{z_1:=5; {?(z_1 + z_1 = 10);}^@ y_1 :=*; {?(true);}^@ k_1:=k_0; {{k_2 := 0; ++ k_2 := 1;}{?(true);}^@k_1:=k_2;}* x_1 := z_1 + y_1; {?(y_1=z_1-> x_1=10);}^@}]true"
        .asFormula
  }

  it should "support forward label going outside box choice" in withMathematica { _ =>
    val pfStr = "x:=0; {!foo:(x@final > 0) by auto; ++ x:=1;} x:=1; final:"
    val ff = check(pfStr)
    ff shouldBe "[x_1:=0; {{{?(1 > 0);}^@x_2:=x_1; } ++ x_2 := 1;} x_3:=1;]true".asFormula
  }

  it should "prove solution cut that requires  domain constraint assumption" in withMathematica { _ =>
    val pfStr =
      "?tInit:(t:= 0); ?xInit:(x:= 1);  {t' = 1, x' = (-1) & ?xRange:(x >=0); & !tRange:(t <= 1) using xInit tInit xRange by solution;};"
    val ff = check(pfStr)
    ff shouldBe "[t_1:=0; x_1:= 1; {t_2 := t_1;x_2:=x_1;}{t_2' = 1, x_2' = (-1) & x_2>=0}]true".asFormula
  }

  it should "automatically find base case assumption in diffcut" in withMathematica { _ =>
    val pfStr = "?(y>=0); {y' = 1 & !dc:(y >= 0) by induction;};"
    val ff = check(pfStr)
    ff shouldBe "[?(y_0>=0); y_1:=y_0;{y_1' = 1}]true".asFormula
  }

  it should "allow solution to be looked up later as assumption" in withMathematica { _ =>
    val pfStr = "?xInit:(x:=0); ?tInit:(t:=0); {t' = 1, xSol: x' = 2}; !xFin:(x = 2*t) using xInit tInit xSol by auto;"
    val ff = check(pfStr)
    ff shouldBe "[x_1 := 0; t_1:=0; {x_2 := x_1; t_2 := t_1;};{t_2' = 1, x_2' = 2}; {?(x_2 = 2*t_2);}^@]true".asFormula
  }

  it should "include duration info when looking any solution" in withMathematica { _ =>
    val pfStr = "?xInit:(x:=0); ?tInit:(t:=0); {t' = 1, xSol: x' = 2}; !xFin:(x >= 0) using xInit tInit xSol by auto;"
    val ff = check(pfStr)
    ff shouldBe "[x_1 := 0; t_1:=0; {x_2 := x_1; t_2 := t_1;};{t_2' = 1, x_2' = 2}; {?(x_2 >= 0);}^@]true".asFormula
  }

  it should "prove diffcut" in withMathematica { _ =>
    val pfStr = "?yZero:(y:=0); ?xZero:(x:=1); x' = y & !dc:(x > 0) using xZero yZero by solution;"
    val ff = check(pfStr)
    ff shouldBe "[y_1:=0; x_1:=1;x_2:=x_1;{x_2' = y_1}]true".asFormula
  }

  it should "catch bad diffcut" in withMathematica { _ =>
    val pfStr = "?xZero:(x:=1); x' = -1 & !dc:(x > 0) using xZero by induction;"
    a[ProofCheckException] shouldBe thrownBy(check(pfStr))
  }

  it should "prove dc-assign" in withMathematica { _ =>
    val pfStr = "?(T >= 0); t:= 0; {t' = 1, x' = y & ?(t := T);};"
    val ff = check(pfStr)
    ff shouldBe "[?(T_0>=0); t_1:= 0; {x_1 := x_0; t_2 := t_1;}{{t_2' = 1, x_1' = y_0}; ?(t_2= T_0);}^@]true".asFormula
  }

  it should "catch unbound fact reference in provable proof" in withMathematica { _ =>
    val pfStr = "!xFact:(true) using yFact by auto;"
    a[ElaborationException] shouldBe thrownBy(check(pfStr))
  }

  it should "prove and then use dc-assign" in withMathematica { _ =>
    val pfStr =
      "?(T>=0);t := 0; x:= 0; {t' = 1, x' = 2 & ?(t := T); & !max:(t<=T) by solution;}; !final:(x = 2*T) using max ... by auto;"
    val ff = check(pfStr)
    ff shouldBe
      "[?(T_0>=0); t_1:= 0; x_1 := 0; {t_2:=t_1;x_2:=x_1;}{{t_2' = 1, x_2' = 2 & t_2<=T_0}; ?(t_2=T_0);}^@{?(x_2=2*T_0);}^@]true"
        .asFormula
  }

  it should "prove renamed dc-assign" in withMathematica { _ =>
    val pfStr = "?(T>=0); timer:= 0; {timer' = 1, x' = y & ?(timer := T);};"
    val ff = check(pfStr)
    ff shouldBe
      "[?(T_0>=0); timer_1:= 0; {x_1:=x_0;timer_2:=timer_1;}{{timer_2' = 1, x_1' = y_0}; ?(timer_2 = T_0);}^@]true"
        .asFormula
  }

  it should "prove diamond assertion " in withMathematica { _ =>
    val pfStr = "?(T>=0); t:= 0; {t' = 1, x' = y & ?(t := T); & !dc:(t >= 0) by induction;};"
    val ff = check(pfStr)
    ff shouldBe "[?(T_0>=0);t_1:=0; {x_1:=x_0;t_2:=t_1;}{{t_2'=1, x_1'=y_0 & t_2>=0}; ?(t_2=T_0);}^@]true".asFormula
  }

  it should "prove triple induction " in withMathematica { _ =>
    val pfStr = "?xInit:(x:=0); ?yInit:(y:=0); ?zInit:(z:=0); " + "{x'=z, y' = 1, z' = y " +
      "& !yInv:(y >= 0) using yInit  by induction;" + "& !zInv:(z >= 0) using zInit yInv by induction;" +
      "& !xInv:(x >= 0) using xInit zInv by induction;" + "};"
    val ff = check(pfStr)
    ff shouldBe "[x_1:=0; y_1:=0;z_1:=0;{x_2:=x_1;y_2:=y_1;z_2:=z_1;}{x_2'=z_2, y_2'=1, z_2'=y_2}]true".asFormula
  }

  it should "catch unsound dI variable scoping " in withMathematica { _ =>
    val pfStr = "?xInit:(x:=0); ?yInit:(y:=0); ?zInit:(z:=0); " + "{x'=z, y' = 1, z' = y " +
      "& !yInv:(y >= 0) using yInit  by induction;" + "& !zInv:(z = 0) using zInit yInit y by induction;" +
      "& !xInv:(x = 0) using xInit zInit z by induction;" + "};"
    a[ProofCheckException] shouldBe thrownBy(check(pfStr))
  }

  it should "catch invalid dc-assign 3: wrong clock" in withMathematica { _ =>
    val pfStr = "t:= 0; {t' = 2, x' = y & ?(t := T);};"
    a[ProofCheckException] shouldBe thrownBy(check(pfStr))
  }

  it should "catch invalid dc-assign 4: negative duration" in withMathematica { _ =>
    val pfStr = "t:= 0; {t' = 1, x' = y & ?(t := T);};"
    a[ProofCheckException] shouldBe thrownBy(check(pfStr))
  }

  it should "prove another simple diffghost" in withMathematica { _ =>
    val pfStr = "/++ x:= 0; ++/ y' = y^2, /++ x' = y ++/;"
    val ff = check(pfStr)
    ff shouldBe "[{y_1:=y_0;x_2:=x_1;} {y_1'=y_1^2&true}]true".asFormula
  }

  it should "prove simple ghost ODE" in withMathematica { _ =>
    val pfStr = "" + "x := 1;" + "/++  y := (1/x)^(1/2); " + "!inv:(x*y^2 = 1) by auto; ++/" +
      "{x' = -x, /++ y' = y * (1/2) ++/ & !inv:(x*y^2 = 1) by induction;}" + "!nonZero:(x > 0) using inv by auto;"
    val ff = check(pfStr)
    ff shouldBe "[x_1:=1; {x_2:=x_1;y_2:=y_1;}{x_2' = -x_2};{?(x_2>0);}^@]true".asFormula
  }

  it should "catch ODE ghost scope escaping" in withMathematica { _ =>
    val pfStr = "" + "x := 1;" + "/++ y := (1/x)^(1/2); ++/" + "!base: (x*y^2 = 1) by auto;" +
      "{x' = -x, /++ y' = y * (1/2) ++/ & !inv:(x*y^2 = 1) by induction;}" + "!nonZero:(x*y^2 = 1) using inv by auto;"
    a[ProofCheckException] shouldBe thrownBy(check(pfStr))
  }

  it should "allow ghost references in later ghosts" in withMathematica { _ =>
    val pfStr = "/++ x := 1; ++/ y := 2; /++ x := x + 2; !xVal:(x=3) by auto; ++/"
    check(pfStr) shouldBe "[y_1:= 2;]true".asFormula
  }

  it should "Prove 1d car safety" in withMathematica { _ =>
    val pfStr = SharedModels.essentialsSafeCar1D
    val ff = check(pfStr)
    val discreteFml =
      ("[x_1:=0;v_1:=0;?(A_0>0&B_0>0&T_0>0&x_1 < d_0);" + "{?v_1^2/(2*B_0)<=d_0-x_1&v_1>=0;}^@" +
        "{x_2:=x_1;t_1:=t_0;a_1:=a_0;v_2:=v_1;}" + "{{" + "{?(v_2+T_0*A_0)^2/(2*B_0)<=d_0-(x_2+v_2*T_0+A_0*T_0^2/2);" +
        "  a_2:=A_0;" + "  {?(v_2+T_0*a_2)^2/(2*B_0)<=d_0-(x_2+v_2*T_0+a_2*T_0^2/2);}^@" + " }^@" + "++" +
        "{?(v_2+T_0*A_0)^2/(2*B_0)+1>=d_0-(x_2+v_2*T_0+A_0*T_0^2/2);" + "a_2:=-B_0;?v_2>=B_0*T_0;" +
        "{?(v_2+T_0*a_2)^2/(2*B_0)<=d_0-(x_2+v_2*T_0+a_2*T_0^2/2);}^@}^@" + "}^@" + "t_2:=0;" +
        "{x_3:=x_2;t_3:=t_2;v_3:=v_2;}" + "{x_3'=v_3,v_3'=a_2,t_3'=1&t_3<=T_0&v_3>=0}" +
        "{?v_3^2/(2*B_0)<=d_0-x_3&v_3>=0;}^@" + "x_2:=x_3;t_1:=t_3;a_1:=a_2;v_2:=v_3;}*" + "{?x_2<=d_0&v_2>=0;}^@]true")
        .asFormula
    ff shouldBe discreteFml
  }

  it should "support tuple patterns" in withMathematica { _ =>
    val pfStr = "?(xInit, vInit):(x := 0; v := 0;); ?(acc, brk, tstep, separate):(A > 0 & B > 0 & T > 0 & x < d);"
    val ff = check(pfStr)
    ff shouldBe "[x_1:= 0; v_1 := 0; ?(A_0 > 0& B_0 > 0 & T_0 > 0 & x_1 < d_0);]true".asFormula
  }

  it should "Prove 1d car safety with forward labels" in withMathematica { _ =>
    val pfStr = "let SB() = (v^2/(2*B)); " +
      "?xInit:(x:=0); ?vInit:(v:=0); ?acc:(A > 0); ?brk:(B > 0); ?tstep:(T > 0); ?separate: (x < d);" +
      "!inv:(SB() <= (d - x) & v >= 0) using xInit vInit brk separate by auto;" + "{{switch {" +
      "case accel: ((SB())@ode(A, T) <= (d-x)@ode(A, T)) =>" + "  ?accA:(a := A);" +
      "  !safe1:((SB())@ode(a, T) <= (d-x)@ode(a, T)) using accel acc accA inv brk tstep ... by auto;" +
      "  note safeAcc = andI(safe1, accA);" + "case brake: ((SB())@ode(A, T) + 1 >= (d-x)@ode(A, T)) =>" +
      "  ?accB:(a := -B);" + "  ?fast:(v >= B*T);" +
      "  !safe2:((SB())@ode(a, T) <= (d-x)@ode(a, T)) using brake acc accB brk inv tstep fast ... by auto;" +
      "  note safeAcc = andI(safe2, andI(accB, fast));" + "}}" + "t:= 0;" +
      "{xSol: x' = v, vSol: v' = a, tSol: t' = 1 & ?dc: (t <= T & v>=0);};" + "ode(a, t):" +
      "!invStep: (SB() <= (d - x) & v>= 0) using safeAcc inv dc acc brk tstep xSol vSol tSol by auto;" + "}*" +
      "!safe:(x <= d & v >= 0) using inv brk  by auto;"
    val ff = check(pfStr)

    val discreteFml =
      ("[x_1:=0;v_1:=0;?A_0>0;?B_0>0;?T_0>0;?x_1 < d_0;" + "{?v_1^2/(2*B_0)<=d_0-x_1&v_1>=0;}^@" +
        "{x_2:=x_1;t_1:=t_0;a_1:=a_0;v_2:=v_1;}" + "{{" +
        "{?(A_0*T_0+v_2)^2/(2*B_0)<=d_0-(A_0*(T_0^2/2)+v_2*T_0+x_2);" + "  a_2:=A_0;" +
        "  {?(a_2*T_0+v_2)^2/(2*B_0)<=d_0-(a_2*(T_0^2/2)+v_2*T_0+x_2);}^@" +
        "  {?(a_2*T_0+v_2)^2/(2*B_0)<=d_0-(a_2*(T_0^2/2)+v_2*T_0+x_2)&a_2=A_0;}^@" + "}^@" + "++" +
        "{?(A_0*T_0+v_2)^2/(2*B_0)+1>=d_0-(A_0*(T_0^2/2)+v_2*T_0+x_2);" + "a_2:=-B_0;?v_2>=B_0*T_0;" +
        "{?(a_2*T_0+v_2)^2/(2*B_0)<=d_0-(a_2*(T_0^2/2)+v_2*T_0+x_2);}^@" +
        "{?(a_2*T_0+v_2)^2/(2*B_0)<=d_0-(a_2*(T_0^2/2)+v_2*T_0+x_2)&a_2=-B_0&v_2>=B_0*T_0;}^@" + "}^@}^@" + "t_2:=0;" +
        "{x_3:=x_2;t_3:=t_2;v_3:=v_2;}" + "{x_3'=v_3,v_3'=a_2,t_3'=1&t_3<=T_0&v_3>=0}" +
        "{?v_3^2/(2*B_0)<=d_0-x_3&v_3>=0;}^@" + "x_2:=x_3;t_1:=t_3;a_1:=a_2;v_2:=v_3;}*" + "{?x_2<=d_0&v_2>=0;}^@]true")
        .asFormula
    ff shouldBe discreteFml
  }

  val pp = ProofParser
  val kp = KaisarKeywordParser

  def p[T](s: String, parser: P[_] => P[T]): T = parse(s, parser) match {
    case x: Success[T] => x.value
    case x: Failure => throw new Exception(x.trace().toString)
  }

  private def testExampleSet(examples: List[String]): Unit = {
    val STOP_AFTER_FIRST = true
    var parseErrors: List[(String, Throwable)] = Nil
    var checkErrors: List[(String, Throwable)] = Nil
    examples.foreach(s =>
      try { KaisarProgramParser.parseSingle(s) }
      catch {
        case t: Throwable =>
          parseErrors = (s, t) :: parseErrors
          if (STOP_AFTER_FIRST) {
            println("Could not parse: " + s)
            throw t
          }
      }
    )
    val provedConclusions = examples.flatMap(s =>
      try { List((s, check(s))) }
      catch {
        case t: Throwable =>
          checkErrors = (s, t) :: checkErrors;
          if (STOP_AFTER_FIRST) {
            println("\n\nFailed while checking proof: " + s)
            throw t
          }
          Nil
      }
    )
    val short = false
    println("\n\n\n")
    if (parseErrors.nonEmpty) {
      if (short) println(s"${parseErrors.length} EXAMPLES FAIL TO PARSE")
      else println("The following examples failed to parse: " + parseErrors.mkString("\n\n"))
    }
    if (checkErrors.nonEmpty) {
      if (short) println(s"${checkErrors.length} EXAMPLES FAIL TO CHECK")
      else println("The following examples failed to prove: " + checkErrors.mkString("\n\n"))
    }
    if (short) println(s"${provedConclusions.length} PROOFS SUCCEED")
    else println("The conclusions of each successful proof are as follows: " + provedConclusions.mkString("\n\n"))
    (parseErrors ++ checkErrors).isEmpty shouldBe true
  }

  // @TODO: Improve language so examples work
  it should "FEATURE_REQUEST: parse and prove all thesis examples" taggedAs TodoTest in withMathematica { _ =>
    testExampleSet(SharedModels.thesisExamples)
  }

  it should "parse and prove all PLDI studies" in withMathematica { _ => testExampleSet(SharedModels.pldiExamples) }

  it should "parse and prove PLDI streamlined versions too" in withMathematica { _ =>
    testExampleSet(List(SharedModels.pldiStreamlined, SharedModels.pldiStreamlinedSandbox))
  }

  it should "parse and prove all RSS studies" in withMathematica { _ => testExampleSet(SharedModels.rssExamples) }

  it should "parse and prove all IJRR studies" in withMathematica { _ => testExampleSet(SharedModels.ijrrModels) }

  it should "FEATURE_REQUEST: parse and prove specific examples" taggedAs TodoTest in withMathematica { _ =>
    testExampleSet(SharedModels.forwardHypothetical :: Nil) // @note works
    testExampleSet(SharedModels.sandboxExample :: Nil) // @note fails
    // disturbReachAvoiddurationODE  solAgain
    // .labelOldEq .demonicLoopConst    .inverseGhostODECircle
    /*switchLiteralArgAlternate forwardHypotheticalUnsolvable*/
    // SharedModels.basicForConv :: SharedModels.revisedReachAvoidFor :: SharedModels.basicForNoConv
    // SharedModels.basicForConv forwardHypothetical
    // basicForConv revisedReachAvoidFor basicForNoConv

  }

  it should "allow ghosts of invariants in loop induction proofs " in withMathematica { _ =>
    testExampleSet(SharedModels.demonicLoopGhostly :: Nil)
  }

  "QE" should "prove some formulas" in withMathematica { _ =>
    val fmlStr = "true"
    val fml = fmlStr.asFormula
    val res = edu.cmu.cs.ls.keymaerax.cdgl.ProofChecker.qeValid(fml)
    println("QE complete")
    res shouldBe true
  }

  "Error message printer" should "nicely print missing semicolon;" in withMathematica { _ =>
    val pfStr = """?xInit:(x:=0); ?vInit:(v:=0); ?acc:(A > 0); ?brk:(B > 0); ?tstep:(T > 0); ?separate: (x < d)
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
