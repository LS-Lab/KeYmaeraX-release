/**
 * HyDRA API Requests
 * @author Nathan Fulton
 */
package edu.cmu.cs.ls.keymaera.hydra

import java.io.FileReader
import java.text.SimpleDateFormat
import java.util.Calendar

import com.github.fge.jackson.JsonLoader
import com.github.fge.jsonschema.main.JsonSchemaFactory
import edu.cmu.cs.ls.keymaera.api.KeYmaeraInterface
import edu.cmu.cs.ls.keymaera.api.KeYmaeraInterface.TaskManagement
import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.parser.KeYmaeraParser
import edu.cmu.cs.ls.keymaera.tacticsinterface.{CLParser, CLInterpreter}

/**
 * A Request should handle all expensive computation as well as all
 * possible side-effects of a request (e.g. updating the database), but should
 * not modify the internal state of the HyDRA server (e.g. do not update the 
 * event queue).
 * 
 * Requests objects should do work after getResultingUpdates is called, 
 * not during object construction.
 * 
 * Request.getResultingUpdates might be run from a new thread. 
 */
sealed trait Request {
  def getResultingResponses() : List[Response] //see Response.scala.

  def currentDate() : String = {
    val format = new SimpleDateFormat("d-M-y")
    format.format(Calendar.getInstance().getTime())
  }
}

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Users
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

class CreateUserRequest(db : DBAbstraction, username : String, password:String) extends Request {
  override def getResultingResponses() = {
    val userExists = db.userExists(username)
    if(!userExists) db.createUser(username,password)
    new BooleanResponse(!userExists) :: Nil
  }
}

class LoginRequest(db : DBAbstraction, username : String, password : String) extends Request {
  override def getResultingResponses(): List[Response] = {
    new LoginResponse(db.checkPassword(username, password), username) ::  Nil
  }
}

class ProofsForUserRequest(db : DBAbstraction, userId: String) extends Request {
  def getResultingResponses() = {
    val proofs = db.getProofsForUser(userId).map(proof =>
      (proof._1, KeYmaeraInterface.getTaskStatus(proof._1.proofId).toString))
    new ProofListResponse(proofs) :: Nil
  }
}

/**
 * Returns an object containing all information necessary to fill out the global template (e.g., the "new events" bubble)
 * @param db
 * @param userId
 */
class DashInfoRequest(db : DBAbstraction, userId : String) extends Request{
  override def getResultingResponses() : List[Response] = {
    val openProofCount : Int = db.openProofs(userId).length
    val allModelsCount: Int = db.getModelList(userId).length
    val provedModelsCount: Int = db.getModelList(userId).flatMap(m => db.getProofsForModel(m.modelId)).count(_.closed)

    new DashInfoResponse(openProofCount, allModelsCount, provedModelsCount) :: Nil
  }
}

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Models
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

class CreateModelRequest(db : DBAbstraction, userId : String, nameOfModel : String, keyFileContents : String) extends Request {
  def getResultingResponses() = {
    try {
      //Return the resulting response.
      var p = new KeYmaeraParser()
      p.runParser(keyFileContents) match {
        case f : Formula => {
          val result = db.createModel(userId, nameOfModel, keyFileContents, currentDate())
          new BooleanResponse(result) :: Nil
        }
        case a => new ErrorResponse(new Exception("TODO pass back the parse error.")) :: Nil //TODO-nrf pass back useful parser error messages.
      }


    }
    catch {
      case e:Exception => e.printStackTrace(); new ErrorResponse(e) :: Nil
    }
  }
}

class GetModelListRequest(db : DBAbstraction, userId : String) extends Request {
  def getResultingResponses() = {
    new ModelListResponse(db.getModelList(userId)) :: Nil
  }
}

class GetModelRequest(db : DBAbstraction, userId : String, modelId : String) extends Request {
  def getResultingResponses() = {
    val model = db.getModel(modelId)
    new GetModelResponse(model) :: Nil
  }
}

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Proofs of models
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

class CreateProofRequest(db : DBAbstraction, userId : String, modelId : String, name : String, description : String)
 extends Request {
  def getResultingResponses() = {
    val proofId = db.createProofForModel(modelId, name, description, currentDate())

    // Create a "task" for the model associated with this proof.
    val keyFile = db.getModel(modelId).keyFile
    KeYmaeraInterface.addTask(proofId, keyFile)

    new CreatedIdResponse(proofId) :: Nil
  }
}

class ProofsForModelRequest(db : DBAbstraction, modelId: String) extends Request {
  def getResultingResponses() = {
    val proofs = db.getProofsForModel(modelId).map(proof =>
      (proof, KeYmaeraInterface.getTaskStatus(proof.proofId).toString))
    new ProofListResponse(proofs) :: Nil
  }
}

class OpenProofRequest(db : DBAbstraction, userId : String, proofId : String) extends Request {
  def getResultingResponses() = {
    val proof = db.getProofInfo(proofId)

    if (!KeYmaeraInterface.containsTask(proof.proofId)) {
      val model = db.getModel(proof.modelId)
      KeYmaeraInterface.addTask(proof.proofId, model.keyFile)
      val steps : List[AbstractDispatchedPOJO] = db.getProofSteps(proof.proofId).map(step => db.getDispatchedTermOrTactic(step).getOrElse(throw new Exception("Expected to find tactic inst or term with id " + step)))
      if (steps.nonEmpty) {
          steps.head match {
          case firstStep : DispatchedTacticPOJO => {
            KeYmaeraInterface.runTactic(proof.proofId, firstStep.nodeId, firstStep.tacticsId, firstStep.formulaId,
              firstStep.id, Some(tacticCompleted(steps.toArray, 1)), firstStep.input, firstStep.auto)
          }
          case firstStep : DispatchedCLTermPOJO => {
            KeYmaeraInterface.runTerm(firstStep.clTerm, firstStep.proofId, firstStep.nodeId, firstStep.clTerm, Some(tacticCompleted(steps.toArray, 1)))
          }
        }
      } else {
        TaskManagement.finishedLoadingTask(proofId)
      }
    }

    val status = KeYmaeraInterface.getTaskStatus(proofId)

    new OpenProofResponse(proof, status.toString) :: Nil
  }

  //@todo To improve readability, move the once-unwinding above and this implementation into a single function.
  private def tacticCompleted(steps : Array[AbstractDispatchedPOJO], next : Int)(tId: String)(proofId: String, nId: Option[String],
                                                                               tacticId: String) {
    if (next < steps.length) {
      val nextStep = steps(next)
      steps(next) match {
        case nextStep : DispatchedTacticPOJO => {
          KeYmaeraInterface.runTactic(proofId, nextStep.nodeId, nextStep.tacticsId, nextStep.formulaId, nextStep.id,
            Some(tacticCompleted(steps, next + 1)), nextStep.input, nextStep.auto)
        }
        case nextStep : DispatchedCLTermPOJO => {
          KeYmaeraInterface.runTerm(nextStep.id, nextStep.proofId, nextStep.nodeId, nextStep.clTerm, Some(tacticCompleted(steps, next + 1)))
        }
      }
    } else {
      TaskManagement.finishedLoadingTask(proofId)
    }
  }
}

/**
 * Gets all tasks of the specified proof. A task is some work the user has to do. It is not a KeYmaera task!
 * @param db Access to the database.
 * @param userId Identifies the user.
 * @param proofId Identifies the proof.
 */
class GetProofAgendaRequest(db : DBAbstraction, userId : String, proofId : String) extends Request {
  def getResultingResponses() = {
    // TODO refactor into template method for all tasks that interact with the proof
    if (!KeYmaeraInterface.containsTask(proofId)) {
      if (!KeYmaeraInterface.isLoadingTask(proofId)) {
        new ProofNotLoadedResponse(proofId) :: Nil
      } else {
        new ProofIsLoadingResponse(proofId) :: Nil
      }
    } else {
      val proof = db.getProofInfo(proofId)
      val openGoalIds = KeYmaeraInterface.getOpenGoals(proofId)

      val result = openGoalIds.map(g => KeYmaeraInterface.getSubtree(proof.proofId, Some(g), 0, true) match {
        case Some(proofNode) => (proof, g, proofNode)
        case None => throw new IllegalStateException("No subtree for goal " + g + " in proof " + proof.proofId)
      })
      new ProofAgendaResponse(result) :: Nil
    }
  }
}

/**
 * Searches for tactics that are applicable to the specified formula. The sequent, which contains this formula, is
 * identified by the proof ID and the node ID.
 * @param db Access to the database.
 * @param userId Identifies the user.
 * @param proofId Identifies the proof.
 * @param nodeId Identifies the node. If None, request the tactics of the "root" node of the task.
 * @param formulaId Identifies the formula in the sequent on which to apply the tactic.
 */
class GetApplicableTacticsRequest(db : DBAbstraction, userId : String, proofId : String, nodeId : Option[String], formulaId : Option[String]) extends Request {
  def getResultingResponses() = {
    val applicableTactics = KeYmaeraInterface.getApplicableTactics(proofId, nodeId, formulaId)
      .map(tId => db.getTactic(tId) match {
        case Some(t) => t
        case None => throw new IllegalStateException("Tactic " + tId + " not in database")
    }).toList
    new ApplicableTacticsResponse(applicableTactics) :: Nil
  }
}

/**
 * Runs the specified tactic on the formula with the specified ID. The sequent, which contains this formula, is
 * identified by the proof ID and the node ID.
 * @param db Access to the database.
 * @param userId Identifies the user.
 * @param proofId Identifies the proof.
 * @param nodeId Identifies the node. If None, the tactic is run on the "root" node of the task.
 * @param formulaId Identifies the formula in the sequent on which to apply the tactic.
 * @param tacticName Identifies the tactic to run.
 * @param input The input to the tactic.
 * @param auto Indicates the degree of automation for position tactics. If formulaId != None, only SaturateCurrent is allowed.
 */
class RunTacticByNameRequest(db : DBAbstraction, userId : String, proofId : String, nodeId : Option[String],
                             formulaId : Option[String], tacticName : String, input : Map[Int,String],
                             auto: Option[String] = None) extends Request {
  def getResultingResponses() = {
    val tacticId = db.getTacticByName(tacticName) match {
      case Some(t) => t.tacticId
      case None => throw new IllegalArgumentException("Tactic name " + tacticName + " unknown")
    }
    new RunTacticRequest(db, userId, proofId, nodeId, formulaId, tacticId, input, auto).getResultingResponses()
  }
}

/**
 * Runs the specified tactic on the formula with the specified ID. The sequent, which contains this formula, is
 * identified by the proof ID and the node ID.
 * @param db Access to the database.
 * @param userId Identifies the user.
 * @param proofId Identifies the proof.
 * @param nodeId Identifies the node. If None, the tactic is run on the "root" node of the task.
 * @param formulaId Identifies the formula in the sequent on which to apply the tactic.
 * @param tacticId Identifies the tactic to run.
 * @param input The input to the tactic.
 * @param auto Indicates the degree of automation for position tactics. If formulaId != None, only SaturateCurrent is allowed.
 * @see KeYmaeraInterface.PositionTacticAutomation for valid values of auto
 */
class RunTacticRequest(db : DBAbstraction, userId : String, proofId : String, nodeId : Option[String],
                       formulaId : Option[String], tacticId : String, input : Map[Int,String],
                       auto: Option[String] = None) extends Request {
  def getResultingResponses() = {
    val automation = auto match {
      case Some(s) => Some(KeYmaeraInterface.PositionTacticAutomation.withName(s.toLowerCase))
      case _ => None
    }
    val tId = db.createDispatchedTactics(proofId, nodeId, formulaId, tacticId, input, automation, DispatchedTacticStatus.Prepared)
    db.updateDispatchedTactics(new DispatchedTacticPOJO(tId, proofId, nodeId, formulaId, tacticId, input, automation,
      DispatchedTacticStatus.Running))

    KeYmaeraInterface.runTactic(proofId, nodeId, tacticId, formulaId, tId,
      Some(tacticCompleted(db)), input, automation)

    new DispatchedTacticResponse(new DispatchedTacticPOJO(tId, proofId, nodeId, formulaId, tacticId, input, automation,
      DispatchedTacticStatus.Running)) :: Nil
  }

  private def tacticCompleted(db : DBAbstraction)(tId: String)(proofId: String, nId: Option[String], tacticId: String) {
    db.synchronized {
      db.updateProofOnTacticCompletion(proofId, tId)
    }
  }
}


class RunCLTermRequest(db : DBAbstraction, userId : String, proofId : String, nodeId : Option[String], clTerm : String) extends Request {
  def getResultingResponses() = {
    try {
      //Make sure that the tactic is going to construct and parse before updating the database.
      CLInterpreter.construct(CLParser(clTerm).getOrElse(throw new Exception("Failed to parse.")))

      val termId = db.createDispatchedCLTerm(proofId, nodeId, clTerm)
      //Update status to running.
      val dispatchedTerm = new DispatchedCLTermPOJO(termId, proofId, nodeId, clTerm, Some(DispatchedTacticStatus.Running))
      db.updateDispatchedCLTerm(dispatchedTerm)
      //Run the tactic.
      KeYmaeraInterface.runTerm(termId, proofId, nodeId, clTerm, Some(completionContinuation(db)))
      //Construct the response to this request.
      new DispatchedCLTermResponse(dispatchedTerm):: Nil
    }
    catch {
      case e:Exception => { e.printStackTrace(); new ErrorResponse(e) :: Nil }
    }
  }

  private def completionContinuation(db : DBAbstraction)(termId : String)(proodId : String, nodeId : Option[String], clTerm : String): Unit = {
    db.synchronized {
      db.updateProofOnCLTermCompletion(proofId, termId)
    }
  }
}

class GetDispatchedTacticRequest(db : DBAbstraction, userId : String, proofId : String, tId : String) extends Request {
  def getResultingResponses() = {
    db.getDispatchedTactics(tId) match {
      case Some(d) => new DispatchedTacticResponse(d) :: Nil
      case _ => new ErrorResponse(new IllegalArgumentException("Cannot find dispatched tactic with ID: " + tId)) :: Nil
    }
  }
}

class GetDispatchedTermRequest(db : DBAbstraction, userId : String, proofId : String, termId : String) extends Request {
  def getResultingResponses() = {
    db.getDispatchedCLTerm(termId) match {
      case Some(d) => new DispatchedCLTermResponse(d) :: Nil
      case _ => new ErrorResponse(new IllegalArgumentException("Cannot find dispatched term with ID: " + termId)) :: Nil
    }
  }
}


class GetProofTreeRequest(db : DBAbstraction, userId : String, proofId : String, nodeId : Option[String]) extends Request{
  override def getResultingResponses(): List[Response] = {
    // TODO fetch only one branch, need to refactor UI for this
    val node = KeYmaeraInterface.getSubtree(proofId, nodeId, 1000, false)
    node match {
      case Some(theNode) =>
        val schema = JsonSchemaFactory.byDefault().getJsonSchema(JsonLoader.fromReader(new FileReader("src/main/resources/js/schema/prooftree.js")))
        val report = schema.validate(JsonLoader.fromString(theNode))
        if (report.isSuccess)
          new AngularTreeViewResponse(theNode) :: Nil
        else {
          throw report.iterator().next().asException()
        }
      case None          => new ErrorResponse(new Exception("Could not find a node associated with these id's.")) :: Nil
    }
  }
}

class GetProofHistoryRequest(db : DBAbstraction, userId : String, proofId : String) extends Request {
  override def getResultingResponses(): List[Response] = {
    val steps = db.getProofSteps(proofId).map(step => db.getDispatchedTactics(step)).map(_.get).
      map(step => step -> db.getTactic(step.tacticsId).getOrElse(
        throw new IllegalStateException(s"Proof refers to unknown tactic ${step.tacticsId}")))
    if (steps.nonEmpty) {
      new ProofHistoryResponse(steps) :: Nil
    } else new ErrorResponse(new Exception("Could not find a proof history associated with these ids.")) :: Nil
  }
}

class GetProofNodeInfoRequest(db : DBAbstraction, userId : String, proofId : String, nodeId: Option[String]) extends Request {
  def getResultingResponses() = {
    // TODO refactor into template method for all tasks that interact with the proof
    if (!KeYmaeraInterface.containsTask(proofId)) {
      if (!KeYmaeraInterface.isLoadingTask(proofId)) {
        new ProofNotLoadedResponse(proofId) :: Nil
      } else {
        new ProofIsLoadingResponse(proofId) :: Nil
      }
    } else {
      val proofNode = KeYmaeraInterface.getSubtree(proofId, nodeId, 0, printSequent = true) match {
        case Some(pn) => pn
        case None => throw new IllegalStateException("No subtree for goal " + nodeId + " in proof " + proofId)
      }
      new ProofNodeInfoResponse(proofId, nodeId, proofNode) :: Nil
    }
  }
}

class GetProofStatusRequest(db : DBAbstraction, userId : String, proofId : String) extends Request {
  def getResultingResponses() = {
    if (!KeYmaeraInterface.containsTask(proofId)) {
      if (!KeYmaeraInterface.isLoadingTask(proofId)) {
        new ProofNotLoadedResponse(proofId) :: Nil
      } else {
        new ProofIsLoadingResponse(proofId) :: Nil
      }
    } else {
      if (!KeYmaeraInterface.isLoadingTask(proofId)) {
        new ProofIsLoadedResponse(proofId) :: Nil
      } else {
        new ProofIsLoadingResponse(proofId) :: Nil
      }
    }
  }
}


/**
 * like GetProofTreeRequest, but fetches 0 instead of 1000 subnodes.
 * @param db
 * @param proofId
 * @param nodeId
 */
class GetNodeRequest(db : DBAbstraction, proofId : String, nodeId : Option[String]) extends Request {
  override def getResultingResponses(): List[Response] = {
    // TODO fetch only one branch, need to refactor UI for this
    val node = KeYmaeraInterface.getSubtree(proofId, nodeId, 0, true)
    node match {
      case Some(theNode) => new NodeResponse(theNode) :: Nil
      case None => new ErrorResponse(new Exception("Could not find a node associated with these id's.")) :: Nil
    }
  }
}
