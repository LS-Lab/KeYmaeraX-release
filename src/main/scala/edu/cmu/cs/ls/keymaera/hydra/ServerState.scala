package edu.cmu.cs.ls.keymaera.hydra

import edu.cmu.cs.ls.keymaera.core.Sequent
import edu.cmu.cs.ls.keymaera.core.Expr

/**
 * Pretty certain that we need to do something better for global session
 * state. In partuclar, the whole "queue updates and send down when ready"
 * thing is pretty essentially not RESTy. At the very list use locks.
 */
object ServerState {
  var updates = new java.util.HashMap[String, List[spray.json.JsValue]]()
  updates.put("default", Nil)
  
  type SessionNameCrossUid = (String,String)
  
  var sequents = new java.util.HashMap[SessionNameCrossUid, Sequent]()
  var expressions = new java.util.HashMap[SessionNameCrossUid, Expr]()
  
  def createNewKey(i : Int = 0) : String = {
    if(updates.containsKey("key" + i.toString())) {
      createNewKey(i+1)
    }
    else {
      "key" + i.toString()
    }
  }
  def createSession() : String = {
    val key = createNewKey()
    updates.put(key, Nil)
    key
  }
  
  def getUpdates(sessionName : String) : String = {
    val result = spray.json.JsArray(updates.get(sessionName))
    updates.put(sessionName, Nil)
    result.prettyPrint
  }
  
  def addUpdate(sessionName : String, update : spray.json.JsValue) = {
    val list = updates.remove(sessionName)
    updates.put(sessionName, list ++ List(update))
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
