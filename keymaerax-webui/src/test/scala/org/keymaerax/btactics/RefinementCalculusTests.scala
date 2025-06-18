/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics

import org.keymaerax.bellerophon.TacticInapplicableFailure
import org.keymaerax.btactics.RefinementCalculus.*
import org.keymaerax.btactics.macros.DerivationInfoAugmentors.ProvableInfoAugmentor
import org.keymaerax.parser.StringConverter.StringToStringConverter

class RefinementCalculusTests extends TacticTestBase {
  "Auxiliary axioms" should "prove" in {
    val axioms = List(refDiamond.provable, hideChoiceL.provable, hideChoiceR.provable, refEq, prgEqSym)
    axioms.map(axiom => axiom.isProved shouldBe true)
  }

  "refOde" should "apply to one-dimensional odes" in {
    val pr = TactixLibrary.proveBy("{x'=y & x>=0} == {x'=y+0 & x>=0}".asFormula, refOde(1))
    pr.subgoals.head shouldBe " ==> [{x'=y & x>=0}](y = y+0)".asSequent
  }

  it should "extend to two-dimensional odes" in {
    val pr = TactixLibrary.proveBy("{x'=y, y'=-x & x>=0} == {x'=y+0, y'=-1*x & x>=0}".asFormula, refOde(1))
    pr.subgoals.head shouldBe " ==> [{x'=y, y'=-x & x>=0}](y = y+0 & -x = -1*x)".asSequent
  }

  it should "extend to three-dimensional odes" in {
    val pr = TactixLibrary
      .proveBy("{x'=y, y'=-x, t'=1 & x>=0} == {x'=y+0, y'=-1*x, t'=(-1)^2 & x>=0}".asFormula, refOde(1))
    pr.subgoals.head shouldBe " ==> [{x'=y, y'=-x, t'=1 & x>=0}](y = y+0 & -x = -1*x & 1 = (-1)^2)".asSequent
  }

  it should "fail if the dimensions do not match" in {
    val e = the[TacticInapplicableFailure] thrownBy
      TactixLibrary.proveBy("{x'=y, y'=-x & x>=0} == {x'=y+0, y'=-1*x, t'=(-1)^2 & x>=0}".asFormula, refOde(1))
    e.getMessage shouldBe "ODEs do not have compatible shape: {x'=y,y'=-x} and {x'=y+0,y'=-1*x,t'=(-1)^2}"
  }

  it should "fail if the variables do not match" in {
    val e = the[TacticInapplicableFailure] thrownBy
      TactixLibrary.proveBy("{x'=y, y'=-x, v'=1 & x>=0} == {x'=y+0, y'=-1*x, t'=(-1)^2 & x>=0}".asFormula, refOde(1))
    e.getMessage shouldBe "ODEs do not have compatible variables: v' and t'"
  }
}
