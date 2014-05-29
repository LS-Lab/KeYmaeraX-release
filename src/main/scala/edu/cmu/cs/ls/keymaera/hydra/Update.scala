package edu.cmu.cs.ls.keymaera.hydra

import spray.json._
import edu.cmu.cs.ls.keymaera.core.Sequent

/**
 * Updates sent to clients.
 * 
 * Updates might be Responses, which are return values for specific calls.
 */
sealed trait Update {  
  /**
   * @return a comma-delimited list of KVP's, but should NOT add surrounding curly brackets.
   */
  val json : JsValue
}

case class CreateRootNode(sessionName : String, sequent : Sequent) extends Update {
  val json = JsObject("eventType" -> JsString("CreateRootNode"),
      "nodeId" -> JsString("0"),
      "parentId" -> JsNull,
      "sequent" -> KeYmaeraClientPrinter.getSequent(sessionName, "0", sequent)
      )
}

case class ErrorResponse(sessionName : String, exn : Exception) extends Update {
  val json = JsObject(
      "eventType" -> JsString("ErrorResponse"),
      "exnType" -> JsString(exn.getClass().getName()),
      "message"   -> JsString(exn.getMessage()),
      "stacktrace" -> JsString(exn.getStackTraceString)
      )
}

case class FormulaToStringResponse(sessionName : String, prettyString : String) extends Update {
  val json = JsObject(
      "eventType" -> JsString("FormulaToStringResponse"),
      "string" -> JsString(prettyString)    
  )
}

case class FormulaToInteractiveStringResponse(sessionName : String, prettyString : String) extends Update {
  val json = JsObject(
      "eventType" -> JsString("formulaToInteractiveStringResponse"),
      "html" -> JsString(prettyString)
  )
}

case class FormulaFromUidResponse(sessionName : String, fjson : JsValue) extends Update {
  val json = JsObject(
      "eventType" -> JsString("FormulaFromUid"),
      "formula" -> fjson
  )
}

case class RuleApplied(sessionName : String, parentId : JsString, ruleIdentifier : JsString, childNodes : JsValue) extends Update {
  val json = ???
}

/**
 * @deprecated use RuleApplied
 * @param node Needs feilds sequent and id.
 */
case class AddNodeResponse(sessionName : String, parentId : JsString, node: JsValue) extends Update {
  val json = JsObject(
    "eventType" -> JsString("AddNode"),
    "parentId"  -> parentId,
    "node"       -> node
  )
}

case class TacticFinished(sessionName : String, tacticName : String, uid : String) extends Update {
  val json = JsObject(
      "eventType" -> JsString("TacticFinished"),
      "tacticName" -> JsString(tacticName),
      "uid" -> JsString(uid)
  )
}