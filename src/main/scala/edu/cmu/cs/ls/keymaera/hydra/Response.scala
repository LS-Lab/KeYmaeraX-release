/**
 * HyDRA API Responses
 *  @author Nathan Fulton
 */
package edu.cmu.cs.ls.keymaera.hydra

import com.github.fge.jackson.JsonLoader
import com.github.fge.jsonschema.main.JsonSchemaFactory
import spray.json._
import edu.cmu.cs.ls.keymaera.core.{ProofStep, ProofNode, Expr, Sequent}
import java.io.File

/**
 * Responses are like views -- they shouldn't do anything except produce appropriately
 * formatted JSON from their parameters.
 *
 * To create a new response:
 * <ol>
 *   <li>Create a new object extending Response (perhaps with constructor arguments)</li>
 *   <li>override the json value with the json to be generated.</li>
 *   <li>override the schema value with Some(File(...)) containing the schema.</li>
 * </ol>
 *
 * See BooleanResponse for the simplest example.
 */
sealed trait Response {
  protected val SCHEMA_DIRECTORY = "src/main/resources/js/schema/"

  protected val json: JsValue
  val schema: Option[java.io.File] = None

  def getJson() = {
    validate();
    json
  }

  def validate() = {
    schema match {
      case None => true //OK.
      case Some(file) => {
        val schema = JsonSchemaFactory.byDefault().getJsonSchema(
          JsonLoader.fromFile(file)
        )
        val report = schema.validate(JsonLoader.fromString(json.prettyPrint))
        if (report.isSuccess())
          true
        else {
          throw new Exception("json schema violation.")
        }
      }
    }
  }
}

class BooleanResponse(flag : Boolean) extends Response {
  override val schema = Some(new File(SCHEMA_DIRECTORY + "BooleanResponse.js"))

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

class DispatchedTacticResponse(t : DispatchedTacticPOJO) extends Response {
  val nid = t.nodeId match {
    case Some(nodeId) => nodeId
    case None => t.proofId
  }
  val json = JsObject(
    "proofId" -> JsString(t.proofId),
    "nodeId" -> JsString(nid),
    "tacticId" -> JsString(t.tacticsId),
    "tacticInstId" -> JsString(t.id),
    "tacticInstStatus" -> JsString(t.status.toString)
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

class OpenProofResponse(proof : ProofPOJO) extends Response {
  val json = JsObject(
    "id" -> JsString(proof.proofId),
    "name" -> JsString(proof.name),
    "date" -> JsString(proof.date),
    "model" -> JsString(proof.modelId),
    "closed" -> JsBoolean(proof.closed),
    "stepCount" -> JsNumber(proof.stepCount)
  )
}

class ProofTasksResponse(tasks : List[(ProofPOJO, String)]) extends Response {
  val objects = tasks.map({ case (proofpojo, proofnodeJson) => JsObject(
    "proofId" -> JsString(proofpojo.proofId),
    "nodeId" -> JsString(proofpojo.proofId), /* TODO */
    "proofNode" -> JsonParser(proofnodeJson)
  )})

  val json = JsArray(objects)
}

class ApplicableTacticsResponse(tactics : List[TacticPOJO]) extends Response {
  val objects = tactics.map(tactic => JsObject(
    "id" -> JsString(tactic.tacticId),
    "name" -> JsString(tactic.name)
  ))

  val json = JsArray(objects)
}

/**
 * @return JSON that is directly usable by angular.treeview
 */
class AngularTreeViewResponse(root : ProofNode) extends Response {
  override val schema = Some(new File(SCHEMA_DIRECTORY + "angular.treeview.js"))

  val json = JsArray( nodeToJson(root) )

  private def nodeToJson(p : ProofNode) : JsValue = {
    val step = p.children.last

    JsObject("id"       -> JsString(""),
             "label"    -> JsString(step.rule.name),
             "children" -> JsArray(step.subgoals.map(n => nodeToJson(n))))

  }
}