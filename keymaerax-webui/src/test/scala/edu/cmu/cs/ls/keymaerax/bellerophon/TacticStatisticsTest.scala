/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.bellerophon.parser.{BelleParser, BellePrettyPrinter}
import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase
import edu.cmu.cs.ls.keymaerax.tags.{SummaryTest, UsualTest}

import scala.collection.immutable.StringOps

/**
  * Tests tactic statistics.
  * @author Stefan Mitsch
  */
@SummaryTest
@UsualTest
class TacticStatisticsTest extends TacticTestBase {

  "Tactic statistics" should "count an atomic step as 1" in withTactics {
    val t = BelleParser("hideR(1)")
    TacticStatistics.size(t) shouldBe 1
    TacticStatistics.lines(t) shouldBe (BellePrettyPrinter(t): StringOps).lines.size
  }

  it should "count the tactics in a sequence" in withTactics {
    val t = BelleParser("hideR(1);hideL(-2);id")
    TacticStatistics.size(t) shouldBe 3
    TacticStatistics.lines(t) shouldBe (BellePrettyPrinter(t): StringOps).lines.size
  }

  it should "count the steps in a saturate/repeat tactic, plus 1 for the operator" in withTactics {
    val t = BelleParser("hideR(1)*;hideL(-2)*3")
    TacticStatistics.size(t) shouldBe 4
    TacticStatistics.lines(t) shouldBe (BellePrettyPrinter(t): StringOps).lines.size
  }

  it should "count the steps in a defined tactic, plus 1 for every use" in withTactics {
    val t = BelleParser("tactic t as (hideR(1);hideL(-2)); implyR(1); t; t; t")
    TacticStatistics.size(t) shouldBe 6
    TacticStatistics.lines(t) shouldBe (BellePrettyPrinter(t): StringOps).lines.size
  }

  it should "count the tactic steps on branches, plus 1 for the branch operator" in withTactics {
    val t = BelleParser("andR(1); <(hideL(-2), hideR(1))")
    TacticStatistics.size(t) shouldBe 4
    TacticStatistics.lines(t) shouldBe (BellePrettyPrinter(t): StringOps).lines.size
  }

}
