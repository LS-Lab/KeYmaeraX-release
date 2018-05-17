/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.hydra

import java.io.File

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.{BelleParser, BellePrettyPrinter}
import edu.cmu.cs.ls.keymaerax.core.{BaseVariable, Bool, Formula, Function, Real, Sequent, Sort, StaticSemantics, Tuple, Unit}
import edu.cmu.cs.ls.keymaerax.hydra.SQLite.SQLiteDB
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXPrettyPrinter, KeYmaeraXProblemParser}
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tacticsinterface.TraceRecordingListener

import scala.collection.immutable.{IndexedSeq, Nil, Seq}

/** Create models and record proofs in a temporary database. */
class TempDBTools(additionalListeners: Seq[IOListener]) {
  lazy val user: UserPOJO = db.getUser(Configuration(Configuration.Keys.GUEST_USER)).get

  val db: SQLiteDB = {
    val testLocation = File.createTempFile("testdb", ".sqlite")
    val db = new SQLiteDB(testLocation.getAbsolutePath)
    db.cleanup(testLocation.getAbsolutePath)
    db
  }

  /** Turns a formula into a model problem with mandatory declarations. */
  def makeModel(content: String): String = {
    def printDomain(d: Sort): String = d match {
      case Real => "R"
      case Bool => "B"
      case Unit => ""
      case Tuple(l, r) => printDomain(l) + "," + printDomain(r)
    }

    def augmentDeclarations(content: String, parsedContent: Formula): String =
      if (content.contains("Problem.")) content //@note determine by mandatory "Problem." block of KeYmaeraXProblemParser
      else {
        val symbols = StaticSemantics.symbols(parsedContent)
        val fnDecls = symbols.filter(_.isInstanceOf[Function]).map(_.asInstanceOf[Function]).map(fn =>
          if (fn.sort == Real) s"R ${fn.asString}(${printDomain(fn.domain)})."
          else if (fn.sort == Bool) s"B ${fn.asString}(${printDomain(fn.domain)})."
          else throw new Exception("Unknown sort: " + fn.sort)
        ).mkString("\n  ")
        val varDecls = symbols.filter(_.isInstanceOf[BaseVariable]).map(v => s"R ${v.prettyString}.").mkString("\n  ")
        s"""Functions.
           |  $fnDecls
           |End.
           |ProgramVariables.
           |  $varDecls
           |End.
           |Problem.
           |  $content
           |End.""".stripMargin
      }

    augmentDeclarations(content, KeYmaeraXProblemParser.parseAsProblemOrFormula(content))
  }

  /** Creates a new proof entry in the database for a model parsed from `modelContent`. */
  def createProof(modelContent: String, modelName: String = "", proofName: String = "Proof"): Int = {
    db.getModelList(user.userName).find(_.name == modelName) match {
      case Some(m) => db.deleteModel(m.modelId)
      case None => // nothing to do
    }
    db.createModel(user.userName, modelName, makeModel(modelContent), "", None, None, None, None) match {
      case Some(modelId) => db.createProofForModel(modelId, modelName + proofName, "", "", None)
      case None => throw new Exception("Unable to create temporary model in DB")
    }
  }

  /** Prove model `modelContent` using tactic  `t`. Record the proof in the database and check that the recorded
    * tactic is the provided tactic. Returns the proof ID and resulting provable. */
  def proveByWithProofId(modelContent: String, t: BelleExpr,
                         interpreter: Seq[IOListener] => Interpreter = ExhaustiveSequentialInterpreter,
                         proofId: Option[Int] = None,
                         modelName: String = ""): (Int, ProvableSig) = {
    val s: Sequent = KeYmaeraXProblemParser.parseAsProblemOrFormula(modelContent) match {
      case fml: Formula => Sequent(IndexedSeq(), IndexedSeq(fml))
      case _ => throw new Exception("Model content " + modelContent + " cannot be parsed")
    }
    val pId = proofId match {
      case Some(id) => id
      case None => createProof(modelContent, modelName)
    }
    val globalProvable = ProvableSig.startProof(s)
    val listener = new TraceRecordingListener(db, pId, None,
      globalProvable, 0 /* start from single provable */, recursive = false, "custom")
    val listeners = listener::Nil ++ additionalListeners
    BelleInterpreter.setInterpreter(interpreter(listeners))
    BelleInterpreter(t, BelleProvable(ProvableSig.startProof(s))) match {
      case BelleProvable(provable, _) =>
        assert(provable.conclusion == s, "The proved conclusion must match the input model")
        //extractTactic(proofId) shouldBe t //@todo trim trailing branching nil
        if (provable.isProved) {
          // check that database thinks so too
          val finalTree = DbProofTree(db, pId.toString)
          finalTree.load()
          //finalTree.leaves shouldBe empty
          finalTree.nodes.foreach(n => n.parent match {
            case None => assert(n.conclusion == s, "The proved conclusion of an intermediate node must match the input model")
            case Some(parent) =>
            //@todo throughout tactic records goal index and parent provables wrong
            //assert(n.conclusion == parent.localProvable.subgoals(n.goalIdx), "The proved conclusion of an intermediate node must match the parent's subgoal")
          })
        }
        (pId, provable)
      case r => throw new Exception("Unexpected tactic result " + r)
    }
  }

  /** Prove model `modelContent` using tactic  `t`. Record the proof in the database and check that the recorded
    * tactic is the provided tactic. Returns the resulting provable. */
  def proveBy(modelContent: String, t: BelleExpr, interpreter: Seq[IOListener] => Interpreter = ExhaustiveSequentialInterpreter,
              modelName: String = ""): ProvableSig =
    proveByWithProofId(modelContent, t, interpreter, None, modelName)._2

  /** Returns the tactic recorded for the proof `proofId`. */
  def extractTactic(proofId: Int): BelleExpr = DbProofTree(db, proofId.toString).tactic

  /** Extracts the internal steps taken by proof step `stepId` at level `level` (0: original tactic, 1: direct internal steps, etc.)  */
  def extractStepDetails(proofId: Int, stepId: String, level: Int = 1): BelleExpr = {
    DbProofTree(db, proofId.toString).locate(stepId) match {
      case Some(node) => node.maker match {
        case Some(tactic) =>
          val localProofId = db.createProof(node.localProvable)
          val interpreter = SpoonFeedingInterpreter(localProofId, -1, db.createProof, DBTools.listener(db),
            ExhaustiveSequentialInterpreter, level, strict=false)
          interpreter(BelleParser(tactic), BelleProvable(ProvableSig.startProof(node.localProvable.conclusion)))
          extractTactic(localProofId)
      }
    }
  }

  /** Expands anonymous tactics into their steps. */
  def extractSerializableTactic(fml: Formula, tactic: BelleExpr): BelleExpr = {
    try {
      val printed = BellePrettyPrinter(tactic)
      val reparsed = BelleParser(printed)
      assert(reparsed == tactic && BellePrettyPrinter(reparsed) == printed, "Print of parse of print must be equal")
      tactic
    } catch {
      case _: Throwable =>
        val modelContent = KeYmaeraXPrettyPrinter(fml)
        val proofId = createProof(modelContent)
        val currInterpreter = BelleInterpreter.interpreter
        val theInterpreter = SpoonFeedingInterpreter(proofId, -1, db.createProof, DBTools.listener(db),
          ExhaustiveSequentialInterpreter)
        def interpreter(listeners: Seq[IOListener]): Interpreter = {
          //@note ignore listeners provided by db.proveByWithProofId, use own trace recording listener
          theInterpreter
        }
        val (_, proof) = proveByWithProofId(modelContent, tactic, interpreter, Some(proofId))
        theInterpreter.kill()
        assert(proof.isProved, "Sandbox proof must be closed, but has open goals " + proof.subgoals.mkString("\n"))
        BelleInterpreter.setInterpreter(currInterpreter)
        extractTactic(proofId)
    }
  }
}
