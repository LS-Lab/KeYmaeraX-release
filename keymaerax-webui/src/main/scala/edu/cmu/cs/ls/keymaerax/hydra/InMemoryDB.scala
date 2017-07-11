/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.hydra

import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXProblemParser
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BellePrettyPrinter
import edu.cmu.cs.ls.keymaerax.bellerophon.BelleExpr
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig

import scala.collection.immutable.Nil

/**
  * In-memory database, e.g., for stepping into tactics.
  * @author Stefan Mitsch
  */
class InMemoryDB extends DBAbstraction {

  private val models: scala.collection.mutable.Map[Int, ModelPOJO] = scala.collection.mutable.Map()
  private val proofs: scala.collection.mutable.Map[Int, (ProvableSig, ProofPOJO)] = scala.collection.mutable.Map()
  //@note proofId == executionId
  private val executionSteps: scala.collection.mutable.Map[Int, ExecutionStepPOJO] = scala.collection.mutable.Map()
  private val executables: scala.collection.mutable.Map[Int, ExecutablePOJO] = scala.collection.mutable.Map()
  private val provables: scala.collection.mutable.Map[Int, ProvableSig] = scala.collection.mutable.Map()
  private val agendaItems: scala.collection.mutable.Map[Int, AgendaItemPOJO] = scala.collection.mutable.Map()

  private val configs: scala.collection.mutable.Map[String, ConfigurationPOJO] = scala.collection.mutable.Map(
    "version" -> new ConfigurationPOJO("version", Map("version" -> VERSION)),
    "tool" -> new ConfigurationPOJO("tool", Map("qe" -> "mathematica")),
    "mathematica" -> new ConfigurationPOJO("mathematica", Map(
      "linkName" -> "/Applications/Mathematica.app/Contents/MacOS/MathKernel",
      "jlinkLibDir" -> "/Applications/Mathematica.app/Contents/SystemFiles/Links/JLink/SystemFiles/Libraries/MacOSX-x86-64"
    ))
  )


  // Configuration and database setup and initialization and all DB communication

  override def getAllConfigurations: Set[ConfigurationPOJO] = configs.values.toSet

  override def getModelList(userId: String): List[ModelPOJO] = models.values.toList

  override def createUser(username: String, password: String, mode: String): Unit = {}

  override def getUser(username: String): Option[UserPOJO] = Some(new UserPOJO(username, 1))

  override def updateConfiguration(config: ConfigurationPOJO): Unit = { configs(config.name) = config }

  //Proofs and Proof Nodes
  override def getProofInfo(proofId: Int): ProofPOJO = synchronized { proofs(proofId)._2 }

  // Users
  override def userExists(username: String): Boolean = true

  override def getProofsForUser(userId: String): List[(ProofPOJO, String)] = {
    proofs.values.map({ case (_, p) => (p, models(p.modelId.get).name)}).toList
  }

  override def userOwnsProof(userId: String, proofId: String): Boolean =
    getProofsForUser(userId).exists(_._1.proofId == proofId.toInt)

  override def checkPassword(username: String, password: String): Boolean = true

  override def updateProofInfo(proof: ProofPOJO): Unit = {
    val (provable, _) = proofs(proof.proofId)
    proofs(proof.proofId) = (provable, proof)
  }

  //returns id of create object
  override def getProofsForModel(modelId: Int): List[ProofPOJO] = synchronized {
    proofs.values.map(_._2).filter(_.modelId == modelId).toList
  }

  def deleteExecution(executionId: Int): Boolean = synchronized {
    executionSteps.filter(_._2.executionId == executionId).foreach(s => executionSteps.remove(s._1))
    true
  }

  override def deleteProof(proofId: Int): Boolean = synchronized {
    deleteExecution(proofId)
    proofs.remove(proofId).isDefined
  }

  //Models
  override def getUniqueModelName(userId: String, modelName: String): String = modelName + models.size

  override def createModel(userId: String, name: String, fileContents: String, date: String,
                           description: Option[String] = None, publink: Option[String] = None,
                           title: Option[String] = None, tactic: Option[String] = None): Option[Int] =
  synchronized {
    if (!models.values.exists(_.name == name)) {
      val modelId = models.keys.size
      models(modelId) = new ModelPOJO(modelId, userId, name, date, fileContents, description.getOrElse(""),
        publink.getOrElse(""), title.getOrElse(""), tactic, 0, temporary=false)
      Some(modelId)
    } else None
  }

  override def updateModel(modelId: Int, name: String, title: Option[String], description: Option[String]): Unit = {
    val model = models(modelId)
    val nm = new ModelPOJO(modelId, model.userId, name, model.date, model.keyFile, description.get, model.pubLink,
      title.get, model.tactic, model.numProofs, model.temporary)
    models(modelId) = nm
  }

  override def addModelTactic(modelId: String, fileContents: String): Option[Int] = {
    val mId = modelId.toInt
    val model = models(mId)
    if (model.tactic.isEmpty) {
      val nm = new ModelPOJO(mId, model.userId, model.name, model.date, model.keyFile, model.description, model.pubLink,
        model.title, Some(fileContents), model.numProofs, model.temporary)
      models(mId) = nm
      Some(1)
    } else None
  }

  override def createProofForModel(modelId: Int, name: String, description: String, date: String,
                                   tactic: Option[String]): Int = synchronized {
    val proofId = proofs.keys.size
    val provableId = provables.keys.size
    val model = KeYmaeraXProblemParser(models(modelId).keyFile)
    val provable = ProvableSig.startProof(model)
    provables(provableId) = provable
    proofs(proofId) = (provable, new ProofPOJO(proofId, Some(modelId), name, description, date, 0, closed=false,
      Some(provableId), temporary=false, tactic))
    proofId
  }

  override def createProof(provable: ProvableSig): Int = synchronized {
    val proofId = proofs.keys.size
    val provableId = provables.keys.size
    provables(provableId) = provable
    proofs(proofId) = (provable, new ProofPOJO(proofId, None, "", "", "", 0, closed=false, Some(provableId),
      temporary=true, None))
    proofId
  }

  override def getModel(modelId: Int): ModelPOJO = synchronized { models(modelId) }

  override def deleteModel(modelId: Int): Boolean = synchronized {
    proofs.filter({case (_, (_, p)) => p.modelId == Some(modelId)}).foreach({case (_, (_, p)) => deleteProof(p.proofId)})
    models.remove(modelId).isDefined
  }

  override def getConfiguration(configName: String): ConfigurationPOJO = configs(configName)

  /**
    * Initializes a new database.
    */
  override def cleanup (): Unit = {}
  def cleanup(which: String): Unit = {}

  /** Deletes a provable and all associated sequents / formulas */
  override def deleteProvable(provableId: Int): Boolean = true

  /**
    * Adds an execution step to an existing execution
    *
    * @note Implementations should enforce additional invarants -- never insert when branches or alt orderings overlap.
    */
  override def addExecutionStep(step: ExecutionStepPOJO): Int = synchronized {
    val stepId = executionSteps.keys.size
    executionSteps(stepId) = step
    stepId
  }

  override def addAlternative(alternativeTo: Int, inputProvable: ProvableSig, trace:ExecutionTrace): Unit = {}

  /** Adds a Bellerophon expression as an executable and returns the new executableId */
  override def addBelleExpr(expr: BelleExpr): Int = synchronized {
    val executableId = executables.keys.size
    executables(executableId) = ExecutablePOJO(executableId, BellePrettyPrinter(expr))
    executableId
  }

  /** Stores a Provable in the database and returns its ID */
  override def createProvable(p: ProvableSig): Int = synchronized {
    val provableId = provables.keys.size
    provables(provableId) = p
    provableId
  }

  /** Returns the executable with ID executableId */
  override def getExecutable(executableId: Int): ExecutablePOJO = {
    getExecutables(List(executableId)).head
  }

  /** Allow retrieving executables in bulk to reduce the number of database queries. */
  def getExecutables(executableIds: List[Int]): List[ExecutablePOJO] = synchronized {
    executables.filterKeys(executableIds.contains).values.toList.sortBy(_.executableId)
  }

  /** Use escape hatch in prover core to create a new Provable */
  override def getProvable(lemmaId: Int): ProvablePOJO = {
    loadProvables(List(lemmaId)).head
  }

  def loadProvables(lemmaIds: List[Int]): List[ProvablePOJO] = provables.filterKeys(lemmaIds.contains).
    map({ case (k, v) => ProvablePOJO(k, v)}).toList.sortBy(_.provableId)

  override def addAgendaItem(proofId: Int, initialProofNode: ProofTreeNodeId, displayName: String): Int = {
    val item = AgendaItemPOJO(agendaItems.size, proofId, initialProofNode, displayName)
    agendaItems(item.itemId) = item
    item.itemId
  }

  override def updateAgendaItem(item: AgendaItemPOJO): Unit = agendaItems(item.itemId) = item

  override def agendaItemsForProof(proofId: Int): List[AgendaItemPOJO] = agendaItems.values.filter(_.proofId == proofId).toList

  override def getAgendaItem(proofId: Int, initialProofNode: ProofTreeNodeId): Option[AgendaItemPOJO] =
    agendaItems.values.find(i => i.proofId == proofId && i.initialProofNode == initialProofNode)

  /** Updates an executable step */
  override def updateExecutionStep(executionStepId: Int, step: ExecutionStepPOJO): Unit = synchronized {
    executionSteps(executionStepId) = step
  }

  /** Deletes execution steps. */
  override def deleteExecutionStep(proofId: Int, stepId: Int): Unit = executionSteps.remove(stepId)

  def printStats(): Unit = {}

  def proofSteps(executionId: Int): List[ExecutionStepPOJO] = synchronized {
    executionSteps.values.filter(v =>
      v.executionId == executionId && v.status == ExecutionStepStatus.Finished).toList.
      sortBy(_.stepId)
  }

  private def zipTrace(executionSteps: List[ExecutionStepPOJO], executables: List[ExecutablePOJO], localProvables: List[ProvableSig]): List[ExecutionStep] = {
    (executionSteps, executables, localProvables) match {
      case (step::steps, _::exes, localProvable::moreProvables) =>
        val successorIds = steps.filter(_.previousStep == step.stepId).flatMap(_.stepId)
        ExecutionStep(step.stepId.get, step.previousStep, step.executionId, () => localProvable,
          step.branchOrder, step.numSubgoals, step.numOpenSubgoals, successorIds, step.ruleName, step.executableId,
          step.userExecuted)  :: zipTrace(steps, exes, moreProvables)
      case (Nil, Nil, Nil) => Nil
      case _ => throw new ProverException("Bug in zipTrace")
    }
  }

  override def getExecutionSteps(executionId: Int): List[ExecutionStepPOJO] = proofSteps(executionId)

  override def getFirstExecutionStep(proofId: Int): Option[ExecutionStepPOJO] = proofSteps(proofId).headOption

  /** Returns a list of steps that do not have successors for each of their subgoals. */
  override def getPlainOpenSteps(proofId: Int): List[(ExecutionStepPOJO, List[Int])] = {
    val trace = proofSteps(proofId)
    trace.map(parent => (parent, trace.filter(s => parent.stepId == s.previousStep).map(_.branchOrder))).
      filter(e => e._2.length < e._1.numSubgoals)
  }

  override def getPlainExecutionStep(executionId: Int, stepId: Int): Option[ExecutionStepPOJO] =
    getExecutionSteps(executionId).find(_.stepId == Some(stepId))

  override def getPlainStepSuccessors(proofId: Int, prevStepId: Int, branchOrder: Int): List[ExecutionStepPOJO] = {
    proofSteps(proofId).filter(s => s.previousStep == Some(prevStepId) && s.branchOrder == branchOrder)
  }

  override def getExecutionStep(proofId: Int, stepId: Int): Option[ExecutionStep] = {
    val steps = proofSteps(proofId)
    steps.find(_.stepId == Some(stepId)) match {
      case None => None
      case Some(step) =>
        val successorIds = steps.filter(_.previousStep == step.stepId).flatMap(_.stepId)
        Some(ExecutionStep(step.stepId.get, step.previousStep, step.executionId, () => getProvable(step.localProvableId.get).provable,
          step.branchOrder, step.numSubgoals, step.numOpenSubgoals, successorIds, step.ruleName, step.executableId,
          step.userExecuted))
    }
  }


  override def getStepProvable(executionId: Int, stepId: Option[Int], subgoal: Option[Int]): Option[ProvableSig] =
    (stepId, subgoal) match {
      case (None, None) => Some(proofs(executionId)._1)
      case (Some(stId), None) => getPlainExecutionStep(executionId, stId) match {
        case Some(step) => step.localProvableId match {case None => None case Some(lpId) => Some(getProvable(lpId).provable)}
        case None => throw new IllegalArgumentException("Unknown step ID " + stId)
      }
      case (stId, Some(sgIdx)) => getStepProvable(executionId, stId, None) match {
        case None => None
        case Some(p) => Some(p.sub(sgIdx))
      }
    }

  override def getExecutionTrace(proofId: Int, withProvables: Boolean=true): ExecutionTrace = {
    /* This method has proven itself to be a resource hog, so this implementation attempts to minimize the number of
       DB calls. */
    val steps = proofSteps(proofId)
    if (steps.isEmpty) {
      ExecutionTrace(proofId.toString, proofId.toString, Nil)
    } else {
      val provableIds = steps.map(_.localProvableId.get)
      val executableIds = steps.map(_.executableId)
      val provables = loadProvables(provableIds).map(_.provable)
      val executables = getExecutables(executableIds)
      val traceSteps = zipTrace(steps, executables, provables)
      ExecutionTrace(proofId.toString, proofId.toString, traceSteps)
    }
  }

  override def getInvariants(modelId: Int): Map[Expression, Formula] = {
    //@todo
//    val model = getModel(modelId)
//    var invariants: Map[Expression, Formula] = Map.empty
//    KeYmaeraXParser.setAnnotationListener{case (program, formula) =>
//      invariants = invariants.+((program, formula))
//    }
//    KeYmaeraXProblemParser.parseAsProblemOrFormula(model.keyFile)
//    invariants
    Map.empty
  }

  /** Ensures any changes which might currently reside in auxilliary storage have been synced to main storage. */
  override def syncDatabase(): Unit = {}

  //Proofs and Proof Nodes
  override def isProofClosed(proofId: Int): Boolean = proofs(proofId)._2.closed
}