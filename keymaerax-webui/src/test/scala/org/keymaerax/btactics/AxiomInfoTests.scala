/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics

import org.keymaerax.btactics.macros._
import org.keymaerax.pt.ProvableSig
import org.keymaerax.tags.{SummaryTest, UsualTest}
import org.scalatest.BeforeAndAfterEach
import org.scalatest.matchers.should.Matchers

/** Created by bbohrer on 12/28/15. */
@SummaryTest @UsualTest
class AxiomInfoTests extends TacticTestBase with Matchers with BeforeAndAfterEach {
  "Axiom Info" should "exist for all axioms" in withZ3 { _ =>
    try {
      DerivationInfoRegistry.init()
      ProvableSig.axiom.keys.forall({ case axiomName => AxiomInfo(axiomName); true }) shouldBe true
    } catch {
      case e: AxiomNotFoundException =>
        println("Test failed: Axiom not implemented: " + e.axiomName)
        throw e
    }
  }
}
