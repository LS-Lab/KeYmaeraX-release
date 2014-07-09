package edu.cmu.cs.ls.keymaera.hydra

import edu.cmu.cs.ls.keymaera.core.Sequent
import edu.cmu.cs.ls.keymaera.core.Expr
import spray.json.JsObject
import spray.json.JsValue
import scala.util.parsing.json.JSONArray

object ServerState {
  //updates : userid * proofid -> Response list
  val updates = new java.util.HashMap[String, List[Response]]()
  
  type KeyType = String

  def createNewKey(userid : String, i : Int = 0) : KeyType = {
    userid
    /*val key = (userid, "key" + i.toString())
    if(updates.containsKey(key)) {
      createNewKey(userid, i+1)
    }
    else {
      key 
    }*/
  }
  
  /**
   * @return the newly created proofid.
   */
  def createSession(userid : String) : KeyType = {
    val key = createNewKey(userid)
    if(updates.get(userid) == null)
      updates.put(key,Nil)
    key
  }
  
  def getUpdates(userid : String, count: Int) : String = {
    val sessionUpdates = updates.get(userid)
    val newUpdates = if(sessionUpdates != null) sessionUpdates.slice(count, sessionUpdates.size) else Nil
    val size = if(sessionUpdates != null) sessionUpdates.size else 0
    val result = spray.json.JsArray(newUpdates.map(_.json))
    JsObject(
      "events" -> result,
      "newCount" -> spray.json.JsNumber(size)
    ).prettyPrint
  }
  
  def addUpdate(userid : String, update : String) = {
    val key = userid
    val in = new ProofTreeResponse(update)
    updates.put(key, updates.get(key) :+ in)
  }
}
