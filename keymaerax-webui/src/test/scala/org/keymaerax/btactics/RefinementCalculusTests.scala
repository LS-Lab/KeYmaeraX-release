/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics

import org.keymaerax.btactics.RefinementCalculus.*
import org.keymaerax.btactics.macros.DerivationInfoAugmentors.ProvableInfoAugmentor

class RefinementCalculusTests extends TacticTestBase {
  "Auxiliary axioms" should "prove" in {
    val axioms = List(refDiamond.provable, hideChoiceL.provable, hideChoiceR.provable, refEq, prgEqSym)
    axioms.map(axiom => axiom.isProved shouldBe true)
  }
}
