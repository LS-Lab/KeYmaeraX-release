package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import edu.cmu.cs.ls.keymaerax.btactics.{RandomFormula, TacticTestBase}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.RandomParserTests
import edu.cmu.cs.ls.keymaerax.tags._
import fastparse.Parsed.{Failure, Success}
import fastparse._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

class EndToEndTests extends TacticTestBase {

  val check: String => Formula = Kaisar.apply

  // @TODO: limit set of programVar equalities after BoxLoop...
  "full proof checker" should "check box loop" in withMathematica { _ =>
      val pfStr = "?xZero:(x >= 1); {{x := x + 1; !IS:(x >= 1) using x xZero by auto;}*} !xFin:(x>=0) using xZero by auto;"
      val ff = check(pfStr)
     /*           :[?x>=1;x_0:=x;{x_1:=x_0+1; {?x_0>=1;}^@{?x_1=x_0+1&x_0=x;}^@{?x_1>=1;}^@x_0:=x_1;}*{?x_0>=1;}^@{?x_0=x_1&x_0=x;}^@{?x_0>=0;}^@]true */
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

  it should "prove solution cut that requires domain constraint assumption" in withMathematica { _ =>
    val pfStr = "?tInit:(t:= 0); ?xInit:(x:= 1);  {t' = 1, x' = -1 & xRange:(x >=0) & !tRange:(t <= 1) using xInit tInit xRange by solution};"
    val ff = check(pfStr)
    ff shouldBe "[t_0:=0; x_0:= 1; {t_1 := t_0;x_1:=x_0;}{t_1' = 1, x_1' = -1 & x_1>=0}]true".asFormula
  }

}
