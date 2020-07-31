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

  // @TODO: Need ghost feature to hide auxilliary notes in final formula
  // @TODO: Need to apply proper renaming in lookups of fact variables
  "full proof checker" should "check box loop" in withMathematica { _ =>
      // todo: should be !xFin instead of ?xFin
      val pfStr = "?xZero:(x >= 1); {{x := x + 1; !IS:(x >= 1) using x xZero by auto;}*} ?xFin:(x>=0);"
      val ff = check(pfStr)
      ff shouldBe "[?x>=1;x_0:=x;{x_1:=x_0+1; {?x_1>=1;}^@ x_0:=x_1;}*?x_0>=0;]true".asFormula
  }
}
