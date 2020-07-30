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

  // @TODO: After SSA, Loop cannot tell what final statement was for purposes of inductive step checking
  "full proof checker" should "check box loop" in withMathematica { _ =>
      val pfStr = "?xZero:(x >= 1); {{x := x + 1; !IS:(x >= 1) by auto;}*} ?xFin:(x>=0);"
      val ff = check(pfStr)
      ff shouldBe "[?(x>=1); x_0 := x; {x_1:=x_0+1;{?(x_1>=1);}^@ x_0:=x_1;}*;?(x_0>=0);]true".asFormula
  }
}
