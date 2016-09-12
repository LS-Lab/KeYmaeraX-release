/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

/**
  * @author Nathan Fulton
  */
class KeYmaeraI extends TacticTestBase {
  "KeYmaeraI" should "prove hw 5.3" in {
    val f = "A() & ( (A() -> B()) | (A() -> C()) ) -> B() | C()".asFormula
    val t = BelleParser(
      """
        |implyR(1) & andL(-1) & orL(-2) <(
        |  implyL(-2) <(
        |    close,
        |    orR1(1) & close
        |  ),
        |  implyL(-2) <(
        |    close,
        |    orR2(1) & close
        |  )
        |)
      """.stripMargin
    )
    proveBy(f, t) shouldBe 'proved
  }

  it should "prove true" in {
    val f = "true".asFormula
    val t = BelleParser("close")
    proveBy(f,t) shouldBe 'proved
  }

  it should "prove false" in {
    val f = "false -> false".asFormula
    val t = BelleParser("implyR(1) & close")
    proveBy(f,t) shouldBe 'proved
  }

  it should "prove by id" in {
    val f = "P() -> P()".asFormula
    val t = BelleParser("implyR(1) & close")
    proveBy(f,t) shouldBe 'proved
  }
}
