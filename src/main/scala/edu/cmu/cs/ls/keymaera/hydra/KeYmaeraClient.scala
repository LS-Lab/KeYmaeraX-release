package edu.cmu.cs.ls.keymaera.hydra

import edu.cmu.cs.ls.keymaera.parser.{KeYmaeraParser, KeYmaeraPrettyPrinter}
import edu.cmu.cs.ls.keymaera.core._
import spray.json._
import edu.cmu.cs.ls.keymaera.core.Number.NumberObj

/**
 * Pretty-prints each subexpression, storing a unique identifier based upon the
 * positions in the sequent. The server is notified of all newly created identifiers.
 * 
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
    		 "succ" -> getExprList(sessionName, sequent.succ, uid + "s", 0))
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
    import edu.cmu.cs.ls.keymaera.parser.HTMLSymbols._;
    e match {
      case e : Binary => {
        JsObject(
            "uid" -> JsString(uid),
            "left" -> getExpr(sessionName, uid+"0", e.left),
            "connective" -> JsString(e match {
              case e : Add => PLUS
              case e : Assign => ASSIGN
              case e: And => AND
              case e: Equiv => EQUIV
              case e : Imply => "->"
              case e : Or => OR
              case e : BinaryGame => ???
              case e : Choice => CHOICE
              case e : Parallel => PARALLEL
              case e : Sequence => SCOLON
              case e : Equals => "="
              case e : GreaterEquals => GEQ
              case e : GreaterThan => GT
              case e: LessEquals => LEQ
              case e : LessThan => LT
              case e : NotEquals => NEQ
              case e : ProgramEquals => ???
              case e : ProgramNotEquals => ???
              case e : Divide => DIVIDE
              case e : Exp => EXP
              case e : Modality => ???
              case e : Multiply => MULTIPLY
              case e : Pair => ","
              case e : Subtract => MINUS
            }),
            "right" -> getExpr(sessionName, uid+"1", e.right))
      }
      case e : Ternary => {
        JsObject(
            "uid" -> JsString(uid),
            "fst" -> getExpr(sessionName, uid+"0", e.fst),
            "snd" -> getExpr(sessionName, uid+"1", e.snd),
            "thd" -> getExpr(sessionName, uid+"2", e.thd),
            "pre" -> JsString("if"),
            "in" -> JsString("then"),
            "else" -> JsString("else"))
      }
      case e : NamedSymbol => {JsObject(
          "uid" -> JsString(uid),
          "str" -> JsString(e.prettyString())
      )}
      //TODO very odd, using edu.cmu.cs.ls.keymaera.core.Number here fails....
      case e : Number.NumberObj => JsObject("uid" -> JsString(uid), "str" -> JsString(e.prettyString()))
      case e: NFContEvolve => JsString("unimplemented")
      case e : ContEvolve => JsString("unimplemented")
//      case e : True => JsObject("uid" -> JsString(uid),"str" -> JsString(TRUE))
//      case e : False => JsObject("uid" -> JsString(uid),"str" -> JsString(FALSE))
      case _ => JsString("unimmplemented: unary and quantifiers." + e.prettyString() + e.getClass().getName())
    }
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