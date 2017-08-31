/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.tools

import edu.cmu.cs.ls.keymaerax.btactics.{TacticTestBase, TactixLibrary}
import edu.cmu.cs.ls.keymaerax.btactics.helpers.QELogger
import edu.cmu.cs.ls.keymaerax.tags.{IgnoreInBuildTest, SlowTest}
import org.scalatest.prop.TableDrivenPropertyChecks._

/**
  * Runs recorded benchmark QE problems with Z3.
  * Created by smitsch on 8/30/17.
  */
@IgnoreInBuildTest
@SlowTest
class Z3BenchmarkTests extends TacticTestBase {

  private val qeTimeout = Some(60)

  private val haveQeLogPath = qeLogPath + "haveqe.txt"

  "Z3" should "prove all recorded actual QE calls" in withZ3 { _ =>
    val logEntries = QELogger.parseLog(haveQeLogPath).map({case (name, sequents) => name -> sequents.head._2}).toList
    val examples = Table(("Name", "Sequent"), logEntries:_*)
    forEvery(examples) { (name, seq) =>
      println(s"Proving $name with Z3 ${seq.prettyString}")
      proveBy(seq, TactixLibrary.QE(Nil, None, qeTimeout)) shouldBe 'proved
    }
  }

}
