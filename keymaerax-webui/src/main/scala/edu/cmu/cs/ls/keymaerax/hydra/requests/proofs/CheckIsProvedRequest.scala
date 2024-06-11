/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.proofs

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.core.{Formula, FuncOf, NamedSymbol, PredOf, Sequent, StaticSemantics, USubst}
import edu.cmu.cs.ls.keymaerax.hydra.responses.proofs.{GetTacticResponse, ProofVerificationResponse}
import edu.cmu.cs.ls.keymaerax.hydra.{
  ArchiveEntryPrinter,
  DBAbstraction,
  DbProofTree,
  ErrorResponse,
  ModelPOJO,
  ProofPOJO,
  ProofSession,
  ReadRequest,
  Response,
  UserProofRequest,
  VerboseTraceToTacticConverter,
}
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors.ExpressionAugmentor
import edu.cmu.cs.ls.keymaerax.lemma.{Lemma, LemmaDBFactory}
import edu.cmu.cs.ls.keymaerax.parser.ArchiveParser
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tools.ToolEvidence

import java.io.File
import java.nio.file.{Files, Paths}
import java.text.SimpleDateFormat
import java.util.Calendar
import scala.collection.immutable.{IndexedSeq, List, Nil}

class CheckIsProvedRequest(db: DBAbstraction, userId: String, proofId: String)
    extends UserProofRequest(db, userId, proofId) with ReadRequest {
  private def exportLemma(lemmaName: String, model: ModelPOJO, provable: ProvableSig, tactic: String) = {
    val evidence = Lemma.requiredEvidence(
      provable,
      ToolEvidence(List("tool" -> "KeYmaera X", "model" -> model.keyFile, "tactic" -> tactic)) :: Nil,
    )
    val lemma = new Lemma(provable, evidence, Some(lemmaName))
    if (LemmaDBFactory.lemmaDB.contains(lemmaName)) LemmaDBFactory.lemmaDB.remove(lemmaName)
    LemmaDBFactory.lemmaDB.add(lemma)
  }
  private def backupProof(model: ModelPOJO, tactic: String) = {
    val proofbackupPath = Paths.get(Configuration.KEYMAERAX_HOME_PATH + File.separator + "proofbackup")
    if (!Files.exists(proofbackupPath)) Files.createDirectories(proofbackupPath)

    val sanitizedModelName = model.name.replaceAll("\\W", "_")
    val proofName = sanitizedModelName + "_" + new SimpleDateFormat("yyyy-MM-dd_HH-mm-ss")
      .format(Calendar.getInstance().getTime)
    var i = 0
    var uniqueProofName = proofName
    while (Files.exists(proofbackupPath.resolve(uniqueProofName))) {
      i = i + 1
      uniqueProofName = proofName + "_" + i
    }

    val archiveContent = ArchiveEntryPrinter.archiveEntry(model, (proofName, tactic) :: Nil, withComments = false)
    Files.write(proofbackupPath.resolve(uniqueProofName), archiveContent.getBytes())
  }

  override protected def doResultingResponse(): Response = {
    val tree = DbProofTree(db, proofId)
    tree.load()
    val model = db.getModel(tree.info.modelId.get)
    val entry = ArchiveParser.parse(model.keyFile, parseTactics = false).head

    // proof may have expanded some definitions itself and used lemmas that expanded some definitions
    val provable = tree.root.provable
    val conclusionSignature = StaticSemantics.signature(provable.conclusion)

    val proofSession = session(proofId).asInstanceOf[ProofSession]
    // find expanded definitions (including delayed model assumptions)
    val substs = (entry.defs.substs ++ proofSession.defs.substs ++ tree.proofSubsts)
      .distinct
      .filter(_.what match {
        case FuncOf(n, _) => !conclusionSignature.contains(n)
        case PredOf(n, _) => !conclusionSignature.contains(n)
        case n: NamedSymbol => !conclusionSignature.contains(n)
        case _ => false
      })

    val conclusionFormula = entry.model.exhaustiveSubst(USubst(substs)).asInstanceOf[Formula]
    val conclusion = Sequent(IndexedSeq(), IndexedSeq(conclusionFormula))

    if (!provable.isProved) new ErrorResponse(
      "Proof verification failed: proof " + proofId +
        " is not closed.\n Expected a provable without subgoals, but result provable is\n" + provable.prettyString
    )
    else if (provable.conclusion != conclusion) new ErrorResponse(
      "Proof verification failed: proof " + proofId + " does not conclude the associated model.\n Expected " +
        conclusion.prettyString + "\nBut got\n" + provable.conclusion.prettyString
    )
    else {
      assert(provable.isProved, "Provable " + provable + " must be proved")
      assert(
        provable.conclusion == conclusion,
        "Conclusion of provable " + provable + " must match problem " + conclusion,
      )
      val (tactic, proofStateInfo) = tree.tacticString(new VerboseTraceToTacticConverter(tree.info.defs(db)))
      // remember tactic string and mapping to proof tree
      val newInfo = ProofPOJO(
        tree.info.proofId,
        tree.info.modelId,
        tree.info.name,
        tree.info.description,
        tree.info.date,
        tree.info.stepCount,
        tree.info.closed,
        tree.info.provableId,
        tree.info.temporary,
        Some(GetTacticResponse(tactic, proofStateInfo.map({ case (k, v) => (k, v.id.toString) })).getJson.compactPrint),
      )
      db.updateProofInfo(newInfo)
      // remember lemma
      exportLemma("user" + File.separator + model.name, model, provable, tactic)
      // backup proof to prevent data loss
      backupProof(model, tactic)
      new ProofVerificationResponse(proofId, provable, tactic)
    }
  }
}
