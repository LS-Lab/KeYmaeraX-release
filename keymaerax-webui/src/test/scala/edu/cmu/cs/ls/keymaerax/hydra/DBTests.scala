/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.hydra

import edu.cmu.cs.ls.keymaerax.bellerophon.{AppliedDependentPositionTactic, AppliedDependentPositionTacticWithAppliedInput, AppliedPositionTactic, BelleExpr, BranchTactic, CaseTactic, EitherTactic, Find, SaturateTactic, SeqTactic}
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.{BelleParser, BellePrettyPrinter}
import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase
import edu.cmu.cs.ls.keymaerax.parser.{ArchiveParser, Declaration, UnknownLocation}
import org.scalactic.Uniformity
import org.scalatest.prop.TableDrivenPropertyChecks._

/**
  * Tests the database implementation.
  * Created by smitsch on 3/06/18.
  */
class DBTests extends TacticTestBase {

  "Stored tactics" should "be reparseable" in withTactics { withDatabase { db =>
    val entries = (
      "/examples/tutorials/sttt/sttt.kyx" ::
      "/examples/tutorials/cpsweek/cpsweek.kyx" ::
      "/examples/tutorials/fm/fm.kyx" ::
      "/examples/tutorials/basic/basictutorial.kyx" :: Nil).
      map(getClass.getResourceAsStream(_)).
      flatMap(i => ArchiveParser.parse(io.Source.fromInputStream(i).mkString)).
      flatMap(e => e.tactics.zipWithIndex.map(t => (e.name + " " + t._2, e.fileContent, t._1._3)))

    val tactics = Table(("name", "fileContent", "tactic"), entries:_*)
    forEvery(tactics) { (name, fileContent, tactic) =>
      val tacticString = BellePrettyPrinter(tactic)
      val modelId = db.db.createModel(db.user.userName, name, fileContent, "", None, None, None, Some(tacticString))
      modelId shouldBe 'defined
      val modelEntry = db.db.getModel(modelId.get)
      val storedTactic = modelEntry.tactic
      storedTactic shouldBe 'defined
      //@note compare pretty printed because text locations differ when tactic is read from a file vs. from stored tactic
      BellePrettyPrinter(ArchiveParser.tacticParser(storedTactic.get)) shouldBe BellePrettyPrinter(tactic)

      val proofId = db.db.createProofForModel(modelId.get, name, "", "", Some(tacticString))
      val storedProofTactic = db.db.getProofInfo(proofId).tactic
      storedProofTactic shouldBe 'defined
      BellePrettyPrinter(ArchiveParser.tacticParser(storedProofTactic.get)) shouldBe BellePrettyPrinter(tactic)
    }

  }}

}
