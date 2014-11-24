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
import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.parser.KeYmaeraParser

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
    val proofsWithNames = db.getProofsForUser(userId)
    val proofs = proofsWithNames.map(_._1).map(proof =>
      (proof, KeYmaeraInterface.getTaskStatus(proof.proofId).toString))
    val names  = proofsWithNames.map(_._2)
    new ProofListResponse(proofs,Some(names)) :: Nil
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

    new DashInfoResponse(openProofCount) :: Nil
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
      val steps = db.getProofSteps(proof.proofId).map(step => db.getDispatchedTactics(step)).map(_.get)
      if (steps.nonEmpty) {
        val firstStep = steps.head
        KeYmaeraInterface.runTactic(proof.proofId, firstStep.nodeId, firstStep.tacticsId, firstStep.formulaId,
          firstStep.id, Some(tacticCompleted(steps.toArray, 1)), firstStep.input)
      }
    }

    val status = KeYmaeraInterface.getTaskStatus(proofId)

    new OpenProofResponse(proof, status.toString) :: Nil
  }

  private def tacticCompleted(steps : Array[DispatchedTacticPOJO], next : Int)(tId: String)(proofId: String, nId: Option[String],
                                                                               tacticId: String) {
    if (next < steps.length) {
      val nextStep = steps(next)
      KeYmaeraInterface.runTactic(proofId, nextStep.nodeId, nextStep.tacticsId, nextStep.formulaId, nextStep.id,
        Some(tacticCompleted(steps, next + 1)), nextStep.input)
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

      val result = openGoalIds.map(g => KeYmaeraInterface.getSubtree(proof.proofId, Some(g), 0) match {
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
 */
class RunTacticByNameRequest(db : DBAbstraction, userId : String, proofId : String, nodeId : Option[String],
                             formulaId : Option[String], tacticName : String, input : Map[Int,String]) extends Request {
  def getResultingResponses() = {
    val tacticId = db.getTacticByName(tacticName) match {
      case Some(t) => t.tacticId
      case None => throw new IllegalArgumentException("Tactic name " + tacticName + " unknown")
    }
    new RunTacticRequest(db, userId, proofId, nodeId, formulaId, tacticId, input).getResultingResponses()
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
 */
class RunTacticRequest(db : DBAbstraction, userId : String, proofId : String, nodeId : Option[String],
                       formulaId : Option[String], tacticId : String, input : Map[Int,String]) extends Request {
  def getResultingResponses() = {
    val tId = db.createDispatchedTactics(proofId, nodeId, formulaId, tacticId, input, DispatchedTacticStatus.Prepared)
    KeYmaeraInterface.runTactic(proofId, nodeId, tacticId, formulaId, tId,
      Some(tacticCompleted(db)), input)
    db.updateDispatchedTactics(new DispatchedTacticPOJO(tId, proofId, nodeId, formulaId, tacticId, input,
      DispatchedTacticStatus.Running))
    new DispatchedTacticResponse(new DispatchedTacticPOJO(tId, proofId, nodeId, formulaId, tacticId, input,
      DispatchedTacticStatus.Running)) :: Nil
  }

  private def tacticCompleted(db : DBAbstraction)(tId: String)(proofId: String, nId: Option[String], tacticId: String) {
    val finishedTactic = db.getDispatchedTactics(tId) match {
      case Some(t) => t
      case _ => throw new IllegalStateException("Finished tactic not found in database: " + tId)
    }
    // TODO the following updates must be an atomic operation on the database
    db.addFinishedTactic(proofId, tId)
    db.updateDispatchedTactics(new DispatchedTacticPOJO(
      finishedTactic.id,
      finishedTactic.proofId,
      finishedTactic.nodeId,
      finishedTactic.formulaId,
      finishedTactic.tacticsId,
      finishedTactic.input,
      DispatchedTacticStatus.Finished
    ))
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


class GetProofTreeRequest(db : DBAbstraction, userId : String, proofId : String, nodeId : Option[String]) extends Request{
  override def getResultingResponses(): List[Response] = {
    // TODO fetch only one branch, need to refactor UI for this
    val node = KeYmaeraInterface.getSubtree(proofId, nodeId, 1000)
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

/**
 * like GetProofTreeRequest, but fetches 0 instead of 1000 subnodes.
 * @param db
 * @param proofId
 * @param nodeId
 */
class GetNodeRequest(db : DBAbstraction, proofId : String, nodeId : Option[String]) extends Request {
  override def getResultingResponses(): List[Response] = {
    // TODO fetch only one branch, need to refactor UI for this
    val node = KeYmaeraInterface.getSubtree(proofId, nodeId, 0)
    node match {
      case Some(theNode) => {
        //        val schema = JsonSchemaFactory.byDefault().getJsonSchema(JsonLoader.fromReader(new FileReader("src/main/resources/js/schema/prooftree.js")))
        //        val report = schema.validate(JsonLoader.fromString(theNode))
        //        if (report.isSuccess)
        new NodeResponse(theNode) :: Nil
        //        else {
        //          throw new Exception("json schema violation.")
        //        }
      }
      case None          => { new ErrorResponse(new Exception("Could not find a node associated with these id's.")) :: Nil }
    }
  }
}




//
//
//class GetProblemRequest(userid : String, proofid : String) extends Request {
//  def getResultingResponses() = {
//    try {
//      val node = ProverBusinessLogic.getModel(proofid)
//      new GetProblemResponse(proofid, node) :: Nil
//    } catch {
//      case e:Exception => e.printStackTrace(); new ErrorResponse(e) :: Nil
//    }
//  }
//}
//
//class RunTacticRequest(userid: String, tacticId: Int, proofId: String, nodeId: String, formulaId: Option[String] = None) extends Request {
//  def getResultingResponses() = {
//    try {
//      // TODO: use the userid
//      println("Running tactic " + tacticId + " on proof " + proofId + " on node " + nodeId + " on formula" + formulaId)
//      //val res = ProverBusinessLogic.runTactic(ProverBusinessLogic.getTactic(tacticId), proofId, nodeId, formulaId, s => ServerState.addUpdate(userid, s))
//      val res = ProverBusinessLogic.runTactic(ProverBusinessLogic.getTactic(tacticId), proofId, nodeId, formulaId, s => { val sub = ProverBusinessLogic.getSubtree(proofId); println("======= Retrieved a tree " + sub); ServerState.addUpdate(userid, sub)} )
//      res match {
//        case Some(s) => new TacticDispatchedResponse(proofId, nodeId, tacticId.toString, s.toString) :: Nil
//        // TODO think about exception
//        case None => throw new IllegalStateException("Tactic not applicable")
//      }
//    }
//    catch {
//      case e:Exception => new ErrorResponse(e) :: Nil
//    }
//  }
//
//}
