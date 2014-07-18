/**
 * HyDRA API Requests
 * @author Nathan Fulton
 */
package edu.cmu.cs.ls.keymaera.hydra

/**
 * A Request should handle all expensive computation as well as all
 * possible side-effects of a request (e.g. updating the database), but shold
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
}

class CreateProblemRequest(userid : String, keyFileContents : String) extends Request {
  def getResultingResponses() = {
    try {
      // TODO: use the userid
      val res = ProverBusinessLogic.addModel(keyFileContents)
      //Return the resulting response.
      new CreateProblemResponse(res) :: Nil
    }
    catch {
      case e:Exception => e.printStackTrace(); new ErrorResponse(e) :: Nil
    }
  }
}

class GetProblemRequest(userid : String, proofid : String) extends Request {
  def getResultingResponses() = {
    try {
      val node = ProverBusinessLogic.getModel(proofid)
      new GetProblemResponse(proofid, node) :: Nil
    } catch {
      case e:Exception => e.printStackTrace(); new ErrorResponse(e) :: Nil
    }
  }
}

class RunTacticRequest(userid: String, tacticId: Int, proofId: String, nodeId: String, formulaId: Option[String] = None) extends Request {
  def getResultingResponses() = {
    try {
      // TODO: use the userid
      println("Running tactic " + tacticId + " on proof " + proofId + " on node " + nodeId + " on formula" + formulaId)
      //val res = ProverBusinessLogic.runTactic(ProverBusinessLogic.getTactic(tacticId), proofId, nodeId, formulaId, s => ServerState.addUpdate(userid, s))
      val res = ProverBusinessLogic.runTactic(ProverBusinessLogic.getTactic(tacticId), proofId, nodeId, formulaId, s => { val sub = ProverBusinessLogic.getSubtree(proofId); println("======= Retrieved a tree " + sub); ServerState.addUpdate(userid, sub)} )
      new UnimplementedResponse("running tactic " + res) :: Nil
    }
    catch {
      case e:Exception => new ErrorResponse(e) :: Nil
    }
  }

}
