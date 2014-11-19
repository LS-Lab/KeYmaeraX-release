/**
 * HyDRA API Responses
 *  @author Nathan Fulton
 *  @author Stefan Mitsch
 */
package edu.cmu.cs.ls.keymaera.hydra

import com.github.fge.jackson.JsonLoader
import com.github.fge.jsonschema.main.JsonSchemaFactory
import spray.json._
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

  def getJson = {
    validate()
    json
  }

  def validate() = {
    schema match {
      case None => true //OK.
      case Some(file) =>
        val schema = JsonSchemaFactory.byDefault().getJsonSchema(
          JsonLoader.fromFile(file)
        )
        val report = schema.validate(JsonLoader.fromString(json.prettyPrint))
        if (report.isSuccess) true
        else throw report.iterator().next().asException()
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

/**
 *
 * @param proofs The list of proofs with their status in KeYmaera (proof, loadStatus).
 * @param models -- optionally, a list of model names associated with each of the proofs in <em>proofs</em>
 */
class ProofListResponse(proofs : List[(ProofPOJO, String)], models : Option[List[String]] = None) extends Response {
  override val schema = Some(new File(SCHEMA_DIRECTORY + "prooflist.js"))

  val objects : List[JsObject] = models match {
    case None => proofs.map({case (proof, loadStatus) => JsObject(
      "id" -> JsString(proof.proofId),
      "name" -> JsString(proof.name),
      "description" -> JsString(proof.description),
      "date" -> JsString(proof.date),
      "modelId" -> JsString(proof.modelId),
      "stepCount" -> JsNumber(proof.stepCount),
      "status" -> JsBoolean(proof.closed),
      "loadStatus" -> JsString(loadStatus)
    )})
    case Some(modelNames) =>
      (proofs zip modelNames).map({case (p,loadStatus) =>
        val proof = p._1
        val modelName = p._2

        JsObject(
          "id" -> JsString(proof.proofId),
          "name" -> JsString(proof.name),
          "description" -> JsString(proof.description),
          "date" -> JsString(proof.date),
          "modelId" -> JsString(proof.modelId),
          "stepCount" -> JsNumber(proof.stepCount),
          "status" -> JsBoolean(proof.closed),
          "loadStatus" -> JsString(loadStatus),
          "modelName" -> JsString(modelName)
        )
      })
  }

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
        "textStatus" -> JsString(exn.getMessage),
        "errorThrown" -> JsString(exn.getStackTrace.toString),
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

class ProofStatusResponse(proofId : String, error : String) extends Response {
  override val schema = Some(new File(SCHEMA_DIRECTORY + "proofstatus.js"))
  val json = JsObject(
    "textStatus" -> JsString(error + ": " + proofId),
    "errorThrown" -> JsString(error),
    "proofId" -> JsString(proofId),
    "type" -> JsString("error")
  )
}
class ProofIsLoadingResponse(proofId : String) extends ProofStatusResponse(proofId, "proof is loading")
class ProofNotLoadedResponse(proofId : String) extends ProofStatusResponse(proofId, "proof not loaded")


class GetProblemResponse(proofid:String, tree:String) extends Response {
  val json = JsObject(
    "proofid" -> JsString(proofid),
    "proofTree" -> JsonParser(tree)
  )
}

//class TacticDispatchedResponse(proofId: String, taskId: String, nodeId: String, tacticId: String, tacticInstId: String) extends Response {
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

class OpenProofResponse(proof : ProofPOJO, loadStatus : String) extends Response {
  override val schema = Some(new File(SCHEMA_DIRECTORY + "proof.js"))
  val json = JsObject(
    "id" -> JsString(proof.proofId),
    "name" -> JsString(proof.name),
    "description" -> JsString(proof.description),
    "date" -> JsString(proof.date),
    "modelId" -> JsString(proof.modelId),
    "stepCount" -> JsNumber(proof.stepCount),
    "status" -> JsBoolean(proof.closed),
    "loadStatus" -> JsString(loadStatus)
  )
}

class ProofAgendaResponse(tasks : List[(ProofPOJO, String, String)]) extends Response {
  override val schema = Some(new File(SCHEMA_DIRECTORY + "proofagenda.js"))
  val objects = tasks.map({ case (proofPojo, nodeId, nodeJson) => JsObject(
    "proofId" -> JsString(proofPojo.proofId),
    "nodeId" -> JsString(nodeId),
    "proofNode" -> JsonParser(nodeJson)
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
class AngularTreeViewResponse(tree : String) extends Response {
  override val schema = Some(new File(SCHEMA_DIRECTORY + "angular.treeview.js"))
  
  val json = JsArray( convert(JsonParser(tree).asJsObject) )

  private def convert(node : JsObject) : JsValue = {
    //TODO implement that label of bare proof nodes correctly.
    //TODO switch to Jolt (https://github.com/bazaarvoice/jolt) once they can handle trees
    val children = (node.fields.get("children") match {
      case Some(c) => c
      case None => throw new IllegalArgumentException("Schema violation")
    }) match {
      case JsArray(c) => c
      case _ => throw new IllegalArgumentException("Schema violation")
    }

    val id = node.fields.get("id") match { case Some(i) => i case None => throw new IllegalArgumentException("Schema violation") }
    if (children.length > 0) {
      val step = children.head.asJsObject
      val rule = step.fields.get("rule") match {
        case Some(r) => r.asInstanceOf[JsString]
        case None => throw new IllegalArgumentException("Schema violation")
      }
      val subgoals = step.fields.get("children") match {
        case Some(gl) => gl.asInstanceOf[JsArray].elements.map(g => convert(g.asJsObject()))
        case None => throw new IllegalArgumentException("Schema violation")
      }
      JsObject(
        "id" -> id,
        "label" -> rule,
        "children" -> JsArray(subgoals)
      )
    } else {
      JsObject(
        "id" -> id,
        "label" -> JsString("Open Goal"), // TODO only if the goal is closed, which is not yet represented in JSON
        "children" -> JsArray()
      )
    }
  }
}

class DashInfoResponse(openProofs:Int) extends Response {
  override val schema = Some(new File(SCHEMA_DIRECTORY + "DashInfoResponse.js"))
  val json = JsObject(
    "open_proof_count" -> JsNumber(openProofs)
  )
}


class NodeResponse(tree : String) extends Response {
  //todo add schema.
  val node = JsonParser(tree).asJsObject
  val json = node
}
