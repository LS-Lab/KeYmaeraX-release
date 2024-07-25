/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra

import org.keymaerax.bellerophon.parser.BellePrettyPrinter
import org.keymaerax.btactics.TacticTestBase
import org.keymaerax.parser.ArchiveParser
import org.scalatest.prop.TableDrivenPropertyChecks._

import scala.io.Source

/**
 * Tests the database implementation.
 *
 * Created by smitsch on 3/06/18.
 */
class DBTests extends TacticTestBase {

  "Stored tactics" should "be reparseable" in withTactics {
    withDatabase { db =>
      val entries =
        ("/examples/tutorials/sttt/sttt.kyx" :: "/examples/tutorials/cpsweek/cpsweek.kyx" ::
          "/examples/tutorials/fm/fm.kyx" :: "/examples/tutorials/basic/basictutorial.kyx" :: Nil)
          .map(getClass.getResourceAsStream(_))
          .flatMap(i => ArchiveParser.parse(Source.fromInputStream(i).mkString))
          .flatMap(e => e.tactics.zipWithIndex.map(t => (e.name + " " + t._2, e.fileContent, t._1._3)))

      val tactics = Table(("name", "fileContent", "tactic"), entries: _*)
      forEvery(tactics) { (name, fileContent, tactic) =>
        val tacticString = BellePrettyPrinter(tactic)
        val modelId = db.db.createModel(db.user.userName, name, fileContent, "", None, None, None, Some(tacticString))
        modelId shouldBe Symbol("defined")
        val modelEntry = db.db.getModel(modelId.get)
        val storedTactic = modelEntry.tactic
        storedTactic shouldBe Symbol("defined")
        // @note compare pretty printed because text locations differ when tactic is read from a file vs. from stored tactic
        BellePrettyPrinter(ArchiveParser.tacticParser(storedTactic.get)) shouldBe BellePrettyPrinter(tactic)

        val proofId = db.db.createProofForModel(modelId.get, name, "", "", Some(tacticString))
        val storedProofTactic = db.db.getProofInfo(proofId).tactic
        storedProofTactic shouldBe Symbol("defined")
        BellePrettyPrinter(ArchiveParser.tacticParser(storedProofTactic.get)) shouldBe BellePrettyPrinter(tactic)
      }

    }
  }

}
