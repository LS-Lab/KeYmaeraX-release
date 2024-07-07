/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.tools

import org.keymaerax.btactics.{TacticTestBase, TactixLibrary}
import org.keymaerax.btactics.helpers.QELogger
import org.keymaerax.core.Number
import org.keymaerax.tags.{IgnoreInBuildTest, SlowTest}
import org.scalatest.prop.TableDrivenPropertyChecks._

/** Runs recorded benchmark QE problems with Z3. Created by smitsch on 8/30/17. */
@IgnoreInBuildTest @SlowTest
class Z3BenchmarkTests extends TacticTestBase {

  private val qeTimeout = Some(Number(60))

  private val haveQeLogPath = qeLogPath + "haveqe.txt"

  "Z3" should "prove all recorded actual QE calls" in withZ3 { tool =>
    val logEntries = QELogger.parseLog(haveQeLogPath).map({ case (name, sequents) => name -> sequents.head._2 }).toList
    val examples = Table(("Name", "Sequent"), logEntries: _*)
    forEvery(examples) { (name, seq) =>
      whenever(tool.isInitialized) {
        println(s"Proving $name with Z3 ${seq.prettyString}")
        proveBy(seq, TactixLibrary.QEX(None, qeTimeout)) shouldBe Symbol("proved")
      }
    }
  }

}
