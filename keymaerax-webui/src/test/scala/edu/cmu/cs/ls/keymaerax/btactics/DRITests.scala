/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.SequentialInterpreter
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.{BelleParser, BellePrettyPrinter}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.UsualTest

/**
  * Tests of the Differential Radical Invariance checking proof rule, implemented in terms of the DRIStep axiom.
  * @author Nathan Fulton
  */
@UsualTest
class DRITests extends TacticTestBase {

  "DRIStep" should "step" in {
    val f1 = "x=0 -> [{x' = 1 & 2=2}]x=0".asFormula
    //h(x) ~> x, f(x) ~> 1, q(x) ~> 2=2 Sic. just so things are different.
    val f2 = "(x = 0 & 2=2 -> [x' := 1;](x)'=0) & ([x' := 1;](x)'=0 -> [{x'=1 & 2=2 & x=0}][x' := 1;](x)'=0)".asFormula
    val t = DifferentialTactics.DRIStep(1)
    loneSucc(proveBy(f1, t)) shouldBe f2
  }

  it should "parse/print round trip" in {
    BelleParser("DRIStep(1)") shouldBe DifferentialTactics.DRIStep(1)
    BellePrettyPrinter(BelleParser("DRIStep(1)")) shouldBe "DRIStep(1)"
    BelleParser(BellePrettyPrinter(DifferentialTactics.DRIStep(1))) shouldBe DifferentialTactics.DRIStep(1)
  }

  "DRI" should "close simple example" in withZ3(qeTool => {
    val f = "x=0 -> [{x' = 0 & 2=2}]x=0".asFormula
    val t = DifferentialTactics.DRI(1)
    proveBy(f,t) shouldBe 'proved
  })
}
