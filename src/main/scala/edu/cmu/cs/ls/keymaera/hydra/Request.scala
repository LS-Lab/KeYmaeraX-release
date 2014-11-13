/**
 * HyDRA API Requests
 * @author Nathan Fulton
 */
package edu.cmu.cs.ls.keymaera.hydra

import java.text.SimpleDateFormat
import java.util.Calendar

import edu.cmu.cs.ls.keymaera.api.{KeYmaeraInterface, KeYmaeraInterface2}
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

class CreateProofRequest(db : DBAbstraction, userId : String, modelId : String, name : String, description : String) extends Request {
  def getResultingResponses() = {
    val proofId = db.createProofForModel(modelId, name, description, currentDate())

    // Create a "task" for the model associated with this proof.
    val keyFile = db.getModel(modelId).keyFile
    val taskId = db.createTask(proofId)
    val taskJson = KeYmaeraInterface.addTask(taskId, keyFile)
    db.updateTask(new TaskPOJO(taskId, taskJson, taskId, proofId))

    new CreatedIdResponse(proofId) :: Nil
  }
}

class ProofsForModelRequest(db : DBAbstraction, modelId: String) extends Request {
  def getResultingResponses() = {
    new ProofListResponse(db.getProofsForModel(modelId)) :: Nil
  }
}

class ProofsForUserRequest(db : DBAbstraction, userId: String) extends Request {
  def getResultingResponses() = {
    val proofsWithNames = db.getProofsForUser(userId)
    val proofs = proofsWithNames.map(_._1)
    val names  = proofsWithNames.map(_._2)
    new ProofListResponse(proofs,Some(names)) :: Nil
  }
}

class GetProofInfoRequest(db : DBAbstraction, userId : String, proofId : String) extends Request {
  def getResultingResponses() = {
    val proof = db.getProofInfo(proofId)
    new GetProofInfoResponse(proof) :: Nil
  }
}

class GetProofTasksRequest(db : DBAbstraction, userId : String, proofId : String) extends Request {
  def getResultingResponses() = {
    val tasks = db.getProofTasks(proofId)
    new ProofTasksResponse(tasks) :: Nil
  }
}

class GetApplicableTacticsRequest(db : DBAbstraction, userId : String, proofId : String, taskId : String, nodeId : Option[String], formulaId : String) extends Request {
  def getResultingResponses() = {

    val tactics = new TacticPOJO("0", "keymaera.imply-left", "", TacticKind.PositionTactic) :: Nil// TODO implement
    new ApplicableTacticsResponse(tactics) :: Nil
  }
}

class RunTacticRequest(db : DBAbstraction, userId : String, proofId : String, taskId : String, nodeId : Option[String], formulaId : String, tacticId : String) extends Request {
  def getResultingResponses() = {
    val nid = nodeId match {
      case Some(nid) => nid
      case None => taskId // task is root node
    }
    val tId = db.createDispatchedTactics(taskId, nid, formulaId, tacticId)
    KeYmaeraInterface.runTactic(taskId, nodeId, tacticId, Some(formulaId), tId,
      Some(tacticCompleted(db, nid)))
    new TacticDispatchedResponse(proofId, taskId, nid, tacticId, tId) :: Nil
  }

  private def tacticCompleted(db : DBAbstraction, nodeId: String)(tId: String)(taskId: String, nId: Option[String], tacticId: String) {
    KeYmaeraInterface.getSubtree(taskId, nId, (p: ProofStepInfo) => { p.infos.get("tactic") == Some(tId) }) match {
      case Some(s) =>
        // s is JSON representation of the subtree
        if (db.getSubtree(nodeId) == null) {
          db.createSubtree(nodeId, s)
        } else {
          db.updateSubtree(nodeId, s)
        }
      case None => ???/* log */
    }
  }
}


class GetProofTreeRequest(db : DBAbstraction, userId : String, taskId : String, nodeId : Option[String]) extends Request{
  override def getResultingResponses(): List[Response] = {
    val node = KeYmaeraInterface.getActualNode(taskId, nodeId)
    throw new Exception("blah")
    node match {
      case Some(theNode) => { new AngularTreeViewResponse(theNode) :: Nil }
      case None          => { new ErrorResponse(new Exception("Could not find a node associated with these id's.")) :: Nil }
    }
  }
}

class DashInfoRequest(db : DBAbstraction, userId : String) extends Request{
  override def getResultingResponses() : List[Response] = {
    val openProofCount : Int = db.openProofs(userId).length

    new DashInfoResponse(openProofCount) :: Nil
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
