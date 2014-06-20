package edu.cmu.cs.ls.keymaera.hydra

import edu.cmu.cs.ls.keymaera.core.Sequent
import edu.cmu.cs.ls.keymaera.core.Expr
import spray.json.JsObject
import spray.json.JsValue

object ServerState {
  //updates : userid * proofid -> Response list
  var updates = new java.util.HashMap[(String, String), List[Response]]()
  
  type KeyType = (String,String)
  
  //Note: this implementation of the keys is exposed.
  var sequents = new java.util.HashMap[KeyType, Sequent]()
  var expressions = new java.util.HashMap[KeyType, Expr]()
  
  def createNewKey(userid : String, i : Int = 0) : KeyType = {
    val key = (userid, "key" + i.toString())
    if(updates.containsKey(key)) {
      createNewKey(userid, i+1)
    }
    else {
      key 
    }
  }
  
  /**
   * @return the newly created proofid.
   */
  def createSession(userid : String) : KeyType = {
    val key = createNewKey(userid)
    updates.put(key,Nil)
    key
  }
  
  def getUpdates(userid : String, proofid : String, countStr : String) : String = {
    val count = Integer.parseInt(countStr)
    val sessionUpdates = updates.get((userid,proofid))
    val newUpdates = sessionUpdates.slice(count, sessionUpdates.size)
    val result = spray.json.JsArray(newUpdates.map(_.json))
    JsObject(
        "events" -> result,
        "newCount"  -> spray.json.JsNumber(sessionUpdates.size)
    ).prettyPrint
  }
  
  def addUpdate(userid : String, proofid:String, update : Response) = {
    val key = (userid, proofid)
    updates.put(key, updates.get(key) ++ List(update))
  }
  
  def addSequent(sessionName : String, uid : String, sequent : Sequent) = {
    sequents.put((sessionName,uid), sequent)
  }
  def getSequent(sessionName : String, uid : String) = sequents.get((sessionName,uid))
  
  def addExpression(sessionName : String, uid : String, e : Expr) = {
    expressions.put((sessionName, uid), e)
  }
  def getExpression(sessionName : String, uid : String) = expressions.get((sessionName,uid))
}
