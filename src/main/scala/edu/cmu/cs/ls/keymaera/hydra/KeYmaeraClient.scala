package edu.cmu.cs.ls.keymaera.hydra

import edu.cmu.cs.ls.keymaera.parser.{KeYmaeraParser, KeYmaeraPrettyPrinter}
import edu.cmu.cs.ls.keymaera.core._
import spray.json._

/**
 * Note: pretty-printing something to JSON with this printer has the side-effect
 * of sending a declaration to the server indicating the presence of a new 
 * expression, sequent or node.
 */
object KeYmaeraClientPrinter {    
  def getSequent(sessionName : String, uid : String, sequent : Sequent) = { 
    KeYmaeraClient.sendSequent(sessionName, uid, sequent);
    
    JsObject("uid"  -> JsString(uid),
    		 "pref" -> getExprList(sessionName, sequent.pref, uid + "p", 0),
    		 "ante" -> getExprList(sessionName, sequent.ante, uid + "a", 0),
    		 "succ" -> getExprList(sessionName, sequent.ante, uid + "s", 0))
  }

  def getExprList(sessionName : String, l : Seq[Expr], uidPrefix : String, uidOffset : Int) = {
    var result : List[JsValue] = Nil
    for(index <- 0 to l.length-1) {
      val expr = l.lift(index).get
      val uid = uidPrefix + (uidOffset+index).toString()
      result = result ++ List(getExpr(sessionName, uid, expr))
    }  
    JsArray(result)
  }
  
  def getExpr(sessionName : String, uid : String, e : Expr) : JsValue = {
    KeYmaeraClient.sendExpression(sessionName, uid, e);
    JsString("") //TODO!
  }
}

/**
 * KeYmaera Hydra server-side API implementation.
 */
object KeYmaeraClient {
  //For now, we just tightly couple to the server running in this jvm.
//  val server = "localhost"
//  val port = 8080 
  
  def serviceRequest(sessionName : String, request : Request) = {
    val updates = request.getResultingUpdates()
    for(update <- updates) {
      ServerState.addUpdate(sessionName, update.json)
    }
  }
  
  def sendSequent(sessionName : String, uid : String, s:Sequent) = {
    ServerState.addSequent(sessionName,uid,s)
  }
  
  def sendExpression(sessionName : String, uid : String, e:Expr) = {
    ServerState.addExpression(sessionName, uid, e)
  }
}

////////////////////////////////////////////////////////////////////////////////

/**
 * Requests from clients
 */
sealed trait Request {
  def getResultingUpdates() : List[Update]
}
case class Problem(sessionName : String, contents : String) extends Request {
  def getResultingUpdates() : List[Update] = {
    try {
      val expression  = new KeYmaeraParser().runParser(contents);
      val rootSequent = new Sequent(List(), IndexedSeq(), IndexedSeq(expression.asInstanceOf[Formula]));
      (new CreateRootNode(sessionName, rootSequent)) :: Nil
    }
    catch {
      case e : Exception => (new ErrorResponse(sessionName, e.getMessage())) :: Nil
    }
  }
}

////////////////////////////////////////////////////////////////////////////////

/**
 * Updates sent to clients
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

case class ErrorResponse(sessionName : String, message : String) extends Update {
  val json = JsObject("eventType" -> JsString("ErrorResponse"),
      "message" -> JsString(message))
}