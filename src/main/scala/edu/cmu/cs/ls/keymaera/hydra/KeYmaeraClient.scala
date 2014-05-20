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
              case e : Imply => ARROW
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
              case e : ProgramEquals => EQ //or equiv?
              case e : ProgramNotEquals => NEQ
              case e : Divide => DIVIDE
              case e : Exp => EXP
              case e : Modality => ??? //not sure why this is binary.
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
      
      case e : Unary => e match {
        case e : Apply => ???
        case e : ApplyPredicate => ???
        case e : BoxModality => JsObject(
            "uid" -> JsString(uid),
            "inner" -> getExpr(sessionName, uid+"0", e.child),
            "left_symbol" -> JsString(BOX_OPEN),
            "right_symbol" -> JsString(BOX_CLOSE))
        case e : ContEvolve => JsObject(
            "uid" -> JsString(uid),
            "inner" -> getExpr(sessionName, uid+"0", e.child),
            "left_symbol" -> JsString("{"),
            "right_symbol" -> JsString("}"))
        case e : Derivative => JsObject(
            "uid" -> JsString(uid),
            "child" -> getExpr(sessionName, uid+"0", e.child),
            "post_symbol" -> JsString(PRIME))
        case e : DiamondModality => JsObject(
            "uid" -> JsString(uid),
            "inner" -> getExpr(sessionName, uid+"0", e.child),
            "left_symbol" -> JsString(DIA_OPEN),
            "right_symbol" -> JsString(DIA_CLOSE))
        case e : Left => ???
        case e : Right => ???
        case e : NDetAssign => JsObject(
            "uid" -> JsString(uid),
            "child" -> getExpr(sessionName, uid+"0", e.child),
            "post_symbol" -> JsString(ASSIGN + KSTAR)
        )
        case e : Neg => JsObject(
            "uid" -> JsString(uid),
            "child" -> getExpr(sessionName, uid+"0", e.child),
            "pre_symbol" -> JsString(NEGATIVE)
        )
        case e : Test => JsObject(
            "uid" -> JsString(uid),
            "child" -> getExpr(sessionName, uid+"0", e.child),
            "pre_symbol" -> JsString(TEST)
        )
        case e : UnaryFormula => e match {
          case e : Finally => ???
          case e : FormulaDerivative => JsObject(
            "uid" -> JsString(uid),
            "child" -> getExpr(sessionName, uid+"0", e.child),
            "post_symbol" -> JsString(PRIME))
          case e : Globally => ???
          case e : Not => JsObject(
            "uid" -> JsString(uid),
            "child" -> getExpr(sessionName, uid+"0", e.child),
            "pre_symbol" -> JsString(NEGATE)
        )
          case e : Quantifier => e match {
            case Forall(variables, child) => JsObject(
                "uid" -> JsString(uid),
                "bind_symbol" -> JsString(FORALL),
                "variables" -> JsArray(getExprList(sessionName, uid+"v", variables)),
                "child" -> getExpr(sessionName, uid+"c", child)
            )
            case Exists(variables, child) => JsObject(
                "uid" -> JsString(uid),
                "bind_symbol" -> JsString(FORALL),
                "variables" -> JsArray(getExprList(sessionName, uid+"v", variables)),
                "child" -> getExpr(sessionName, uid+"c", child)
            )
          }
        }
        case e : UnaryGame => ???
        case e : UnaryProgram => e match {
          case e : Loop => JsObject( 
              "uid" -> JsString(uid),
              "child" -> getExpr(sessionName, uid+"c", e.child),
              "post_symbol" -> JsString(KSTAR)
          )
        }
      }
      
      case e : NamedSymbol => {JsObject(
          "uid" -> JsString(uid),
          "str" -> JsString(e.prettyString())
      )}
      case e : Number.NumberObj => JsObject("uid" -> JsString(uid), "str" -> JsString(e.prettyString()))
      case True() => JsObject("uid" -> JsString(uid),"str" -> JsString(TRUE))
      case False() => JsObject("uid" -> JsString(uid),"str" -> JsString(FALSE))
      case _ => JsString("unimmplemented: unary and quantifiers." + e.prettyString() + e.getClass().getName())
    }
  }
  
  def getExprList(sessionName:String,uid:String,variables:Seq[NamedSymbol]) = {
    (variables zip Seq.range(0, variables.size-1)).map( pair => {
      getExpr(sessionName, uid + pair._2.toString(), pair._1)
    }).toList
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
    updates
  }
  
  def hasExpression(sessionName:String, uid:String) = {
    ServerState.expressions.containsKey((sessionName, uid))
  }
  def getExpression(sessionName:String, uid:String) = {
    ServerState.getExpression(sessionName, uid)
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
      case e : Exception => (new ErrorResponse(sessionName, e)) :: Nil
    }
  }
}
case class FormulaToStringRequest(sessionName : String, uid : String) extends Request {
  def getResultingUpdates() : List[Update] = try {
    if(ServerState.expressions == null) {
      new ErrorResponse(sessionName, new NullPointerException()) :: Nil
    }
    else if(!KeYmaeraClient.hasExpression(sessionName,uid)) {
      new ErrorResponse(sessionName, new Exception("UID not found for uid: " + sessionName + "," + uid + " in " + ServerState.expressions.keySet().toArray().mkString(","))) :: Nil
    }
    else {
      val prettyString= KeYmaeraClient.getExpression(sessionName,uid).prettyString()
      (new FormulaToStringResponse(sessionName,prettyString))::Nil
    }
  }
  catch {
    case e : Exception => (new ErrorResponse(sessionName, e))::Nil
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
      "formula" -> JsString(prettyString)    
  )
}