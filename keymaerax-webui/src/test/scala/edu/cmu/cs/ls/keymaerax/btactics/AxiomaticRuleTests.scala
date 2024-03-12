/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.core.Sequent
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.SummaryTest

import scala.collection.immutable

/**
 * Tests [[edu.cmu.cs.ls.keymaerax.btactics.DLBySubst.monb]], [[edu.cmu.cs.ls.keymaerax.btactics.DLBySubst.mond]],
 * [[edu.cmu.cs.ls.keymaerax.btactics.DLBySubst.G]]
 */
@SummaryTest
class AxiomaticRuleTests extends TacticTestBase {

  "[] monotone" should "work" in withTactics {
    val result = proveBy(
      Sequent(immutable.IndexedSeq("[x:=1;]x>0".asFormula), immutable.IndexedSeq("[x:=1;]x>-1".asFormula)),
      TactixLibrary.monb,
    )

    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x>0".asFormula
    result.subgoals.head.succ should contain only "x>-1".asFormula
  }

  "<> monotone" should "work" in withTactics {
    val result = proveBy(
      Sequent(immutable.IndexedSeq("<x:=1;>x>0".asFormula), immutable.IndexedSeq("<x:=1;>x>-1".asFormula)),
      TactixLibrary.mond,
    )

    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x>0".asFormula
    result.subgoals.head.succ should contain only "x>-1".asFormula
  }

  "G" should "work" in withTactics {
    val result = proveBy("[x:=1;]x>0".asFormula, TactixLibrary.G(1))

    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "x>0".asFormula
  }
}
