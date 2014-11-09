/**
 * HyDRA API Responses
 *  @author Nathan Fulton
 */
package edu.cmu.cs.ls.keymaera.hydra

import spray.json._
import edu.cmu.cs.ls.keymaera.core.{ProofStep, ProofNode, Expr, Sequent}

/**
 * Responses are like views -- they shouldn't do anything except produce appropriately
 * formatted JSON from their parameters.
 */
sealed trait Response {
  val json : JsValue
}

class BooleanResponse(flag : Boolean) extends Response {
  val json = JsObject(
    "success" -> (if(flag) JsTrue else JsFalse),
    "type" -> JsNull
  )
}

class ModelListResponse(models : List[ModelPOJO]) extends Response {
  val objects = models.map(modelpojo => JsObject(
    "id" -> JsString(modelpojo.modelId),
    "name" -> JsString(modelpojo.name),
    "date" -> JsString(modelpojo.date),
    "keyFile" -> JsString(modelpojo.keyFile)
  ))

  val json = JsArray(objects)
}

class ProofListResponse(proofs : List[ProofPOJO]) extends Response {
  val objects = proofs.map(proof => JsObject(
    "id" -> JsString(proof.proofId),
    "name" -> JsString(proof.name),
    "description" -> JsString(proof.description),
    "date" -> JsString(proof.date),
    "modelId" -> JsString(proof.modelId),
    "stepCount" -> JsNumber(proof.stepCount),
    "status" -> JsBoolean(proof.closed)
  ))

  val json = JsArray(objects)
}

class GetModelResponse(model : ModelPOJO) extends Response {
  val json = JsObject(
    "id" -> JsString(model.modelId),
    "name" -> JsString(model.name),
    "date" -> JsString(model.date),
    "keyFile" -> JsString(model.keyFile)
  )
}

class LoginResponse(flag:Boolean, userId:String) extends Response {
  val json = JsObject(
    "success" -> (if(flag) JsTrue else JsFalse),
    "key" -> JsString("userId"),
    "value" -> JsString(userId),
    "type" -> JsString("LoginResponse")
  )
}

class CreatedIdResponse(id : String) extends Response {
  val json = JsObject("id" -> JsString(id))
}

class ErrorResponse(exn : Exception) extends Response {
  val json = JsObject(
        "textStatus" -> JsString(exn.getMessage()),
        "errorThrown" -> JsString(exn.getStackTrace().toString()),
        "type" -> JsString("error")
      )
}

class UnimplementedResponse(callUrl : String) extends Response {
  val json = JsObject(
      "textStatus" -> JsString("Call unimplemented: " + callUrl),
      "errorThrown" -> JsString("unimplemented"),
      "type" -> JsString("error")
  )
}

class GetProblemResponse(proofid:String, tree:String) extends Response {
  val json = JsObject(
    "proofid" -> JsString(proofid),
    "proofTree" -> JsonParser(tree)
  )
}

class TacticDispatchedResponse(taskId: String, nodeId: String, tacticId: String, tacticInstId: String) extends Response {
  val json = JsObject(
    "taskId" -> JsString(taskId),
    "nodeId" -> JsString(nodeId),
    "tacticId" -> JsString(tacticId),
    "tacticInstId" -> JsString(tacticInstId)
  )
}

class UpdateResponse(update: String) extends Response {
  val json = JsObject(
    "type" -> JsString("update"),
    "events" -> JsonParser(update)
  )
}

class ProofTreeResponse(tree: String) extends Response {
  val json = JsObject(
    "type" -> JsString("proof"),
    "tree" -> JsonParser(tree)
  )
}

class GetProofInfoResponse(proof : ProofPOJO) extends Response {
  val json = JsObject(
    "id" -> JsString(proof.proofId),
    "name" -> JsString(proof.name),
    "date" -> JsString(proof.date),
    "model" -> JsString(proof.modelId),
    "closed" -> JsBoolean(proof.closed),
    "stepCount" -> JsNumber(proof.stepCount)
  )
}

class ProofTasksResponse(tasks : List[TaskPOJO]) extends Response {
  val objects = tasks.map(taskpojo => JsObject(
    "id" -> JsString(taskpojo.taskId),
    "task" -> JsString(taskpojo.task),
    "rootTaskId" -> JsString(taskpojo.rootTaskId),
    "proofId" -> JsString(taskpojo.proofId)
  ))

  val json = JsArray(objects)
}

class ApplicableTacticsResponse(tactics : List[TacticsPOJO]) extends Response {
  val objects = tactics.map(tactic => JsObject(
    "id" -> JsString(tactic.tacticsId)
  ))

  val json = JsArray(objects)
}

/**
 * @return JSON that is directly usable by angular.treeview
 */
class AngularTreeViewResponse(root : ProofNode) extends Response {
  val json = nodeToJson(root)

  private def nodeToJson(p : ProofNode) : JsValue = {
    assert(p.children.length == 1) // when we allow for or-branching, this becomes false and the logic must change.
    val nodeLabel = p.children.last.rule.name
    val nodeId    = "" //not sure what should happen here... how do we refer to a node/step?
    val children = p.children.last.subgoals
    val childrenJson = JsArray( children.map(n => nodeToJson(n)) )

    val sequent = p.sequent.toString() //TODO pass in actual json

    JsObject("id" -> JsString(nodeId),
      "label" -> JsString(nodeLabel),
      "children" -> childrenJson)
  }
}