/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
//package edu.cmu.cs.ls.keymaera.hydra
//
//import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraParser, KeYmaeraPrettyPrinter}
//import edu.cmu.cs.ls.keymaerax.core._
//import spray.json._
//import edu.cmu.cs.ls.keymaerax.core.Number.NumberObj
//import edu.cmu.cs.ls.keymaerax.tactics.Tactics
//import edu.cmu.cs.ls.keymaerax.tactics._
///**
// * Pretty-prints each subexpression, storing a unique identifier based upon the
// * positions in the sequent. The server is notified of all newly created identifiers.
// * 
// * Note: pretty-printing something to JSON with this printer has the side-effect
// * of sending a declaration to the server indicating the presence of a new 
// * expression, sequent or node.
// */
//object KeYmaeraClientPrinter {    
//  def printPos(p: PosInExpr): Any = p.pos.mkString("")
//  
//  def getSequent(sessionName : String, uid : String, sequent : Sequent) = { 
//    KeYmaeraClient.sendSequent(sessionName, uid, sequent);
//    
//    JsObject("uid"  -> JsString(uid),
//    		 "pref" -> getExprList(sessionName, sequent.pref, uid + "p", 0),
//    		 "ante" -> getExprList(sessionName, sequent.ante, uid + "a", 0),
//    		 "succ" -> getExprList(sessionName, sequent.succ, uid + "s", 0))
//  }
//
//  def getExprList(sessionName : String, l : Seq[Expr], uidPrefix : String, uidOffset : Int) = {
//    var result : List[JsValue] = Nil
//    for(index <- 0 to l.length-1) {
//      val expr = l.lift(index).get
//      val uid = uidPrefix + (uidOffset+index).toString()
//      result = result ++ List(exprToJson(sessionName, uid, expr))
//    }  
//    JsArray(result)
//  }
//  
//  def exprToJson(sessionName : String, uid : String, e : Expr) : JsValue = {
//    KeYmaeraClient.sendExpression(sessionName, uid, e);
//    import edu.cmu.cs.ls.keymaerax.parser.HTMLSymbols._;
//    e match {
//      case DiamondModality(ep) => {
//        val (program:Program, formula:Formula) = ep
//        JsObject(
//          "uid" -> JsString(uid),
//          "program" -> exprToJson(sessionName, uid+"0", program),
//          "formula" -> exprToJson(sessionName, uid+"0", formula),
//          "open" -> JsString(DIA_OPEN),
//          "close" -> JsString(DIA_CLOSE)
//        )
//      }
//      case BoxModality(ep) => {
//        val (program:Program, formula:Formula) = ep
//        JsObject(
//            "WTF" -> JsString(program.prettyString),
//          "uid" -> JsString(uid),
//          "program" -> exprToJson(sessionName, uid+"0", program),
//          "formula" -> exprToJson(sessionName, uid+"0", formula),
//          "open" -> JsString(BOX_OPEN),
//          "close" -> JsString(BOX_CLOSE)
//        )
//      }
//
//      case e : Binary => e match {
//        case _ => JsObject(
//            "uid" -> JsString(uid),
//            "left" -> exprToJson(sessionName, uid+"0", e.left),
//            "right" -> exprToJson(sessionName, uid+"1", e.right),
//            "connective" -> JsString(e match {
//              case e : Modality => throw new Exception("found modality!")
//              case e : Add => PLUS
//              case e : Assign => ASSIGN
//              case e: And => AND
//              case e: Equiv => EQUIV
//              case e : Imply => ARROW
//              case e : Or => OR
//              case e : BinaryGame => throw new Exception("Games not implemented.")
//              case e : Choice => CHOICE
//              case e : Parallel => PARALLEL
//              case e : Sequence => SCOLON
//              case e : Equals => "="
//              case e : GreaterEqual => GEQ
//              case e : GreaterThan => GT
//              case e: LessEqual => LEQ
//              case e : LessThan => LT
//              case e : NotEquals => NEQ
//              case e : ProgramEquals => EQ //or equiv?
//              case e : ProgramNotEquals => NEQ
//              case e : Divide => DIVIDE
//              case e : Exp => EXP
//              case e : Multiply => MULTIPLY
//              case e : Pair => ","
//              case e : Subtract => MINUS
//              case _ => ???
//            }))
//      }
//      
//      case e : Ternary => {
//        JsObject(
//            "uid" -> JsString(uid),
//            "fst" -> exprToJson(sessionName, uid+"0", e.fst),
//            "snd" -> exprToJson(sessionName, uid+"1", e.snd),
//            "thd" -> exprToJson(sessionName, uid+"2", e.thd),
//            "pre" -> JsString("if"),
//            "in" -> JsString("then"),
//            "else" -> JsString("else"))
//      }
//      case e : Unary => e match {
//        case e : Apply => JsObject(
//            "fn" -> exprToJson(sessionName, uid+"0", e.function),
//            "child" -> exprToJson(sessionName, uid+"1", e.child))
//        case e : ApplyPredicate => JsObject(
//            "fn" -> exprToJson(sessionName, uid+"0", e.function),
//            "child" -> exprToJson(sessionName, uid+"1", e.child))
//
//        case e : ContEvolve => JsObject(
//            "uid" -> JsString(uid),
//            "inner" -> exprToJson(sessionName, uid+"0", e.child),
//            "left_symbol" -> JsString("{"),
//            "right_symbol" -> JsString("}"))
//        case e : Derivative => JsObject(
//            "uid" -> JsString(uid),
//            "child" -> exprToJson(sessionName, uid+"0", e.child),
//            "post_symbol" -> JsString(PRIME))
//        case e : Left => ???
//        case e : Right => ???
//        case e : NDetAssign => JsObject(
//            "uid" -> JsString(uid),
//            "child" -> exprToJson(sessionName, uid+"0", e.child),
//            "post_symbol" -> JsString(ASSIGN + KSTAR)
//        )
//        case e : Neg => JsObject(
//            "uid" -> JsString(uid),
//            "child" -> exprToJson(sessionName, uid+"0", e.child),
//            "pre_symbol" -> JsString(NEGATIVE)
//        )
//        case e : Test => JsObject(
//            "uid" -> JsString(uid),
//            "child" -> exprToJson(sessionName, uid+"0", e.child),
//            "pre_symbol" -> JsString(TEST)
//        )
//        case e : UnaryFormula => e match {
//          case e : Finally => ???
//          case e : FormulaDerivative => JsObject(
//            "uid" -> JsString(uid),
//            "child" -> exprToJson(sessionName, uid+"0", e.child),
//            "post_symbol" -> JsString(PRIME))
//          case e : Globally => ???
//          case e : Not => JsObject(
//            "uid" -> JsString(uid),
//            "child" -> exprToJson(sessionName, uid+"0", e.child),
//            "pre_symbol" -> JsString(NEGATE)
//        )
//          case e : Quantifier => e match {
//            case Forall(variables, child) => JsObject(
//                "uid" -> JsString(uid),
//                "bind_symbol" -> JsString(FORALL),
//                "variables" -> JsArray(getNSList(sessionName, uid+"v", variables)),
//                "child" -> exprToJson(sessionName, uid+"c", child)
//            )
//            case Exists(variables, child) => JsObject(
//                "uid" -> JsString(uid),
//                "bind_symbol" -> JsString(FORALL),
//                "variables" -> JsArray(getNSList(sessionName, uid+"v", variables)),
//                "child" -> exprToJson(sessionName, uid+"c", child)
//            )
//          }
//        }
//        case e : UnaryGame => ???
//        case e : UnaryProgram => e match {
//          case e : Loop => JsObject( 
//              "uid" -> JsString(uid),
//              "child" -> exprToJson(sessionName, uid+"c", e.child),
//              "post_symbol" -> JsString(KSTAR)
//          )
//        }
//        case _ => ???
//      }
//      
//      case e : NamedSymbol => {JsObject(
//          "uid" -> JsString(uid),
//          "str" -> JsString(e.prettyString+(e.index match { case Some(j) => "_" + j case _ => "" }))
//      )}
//      case e : Number.NumberObj => JsObject("uid" -> JsString(uid), "str" -> JsString(e.prettyString))
//      case True() => JsObject("uid" -> JsString(uid),"str" -> JsString(TRUE))
//      case False() => JsObject("uid" -> JsString(uid),"str" -> JsString(FALSE))
//      case _ => JsString("unimmplemented: unary and quantifiers." + e.prettyString + e.getClass().getName())
//    }
//  }
//  
//  def getNSList(sessionName:String,uid:String,variables:Seq[NamedSymbol]) = {
//    var retVal : List[JsValue] = List()
//    var count = 0;
//    for(v <- variables) {
//      val newExpr = exprToJson(sessionName, uid + count.toString(), v)
//      retVal = retVal ++ List(newExpr)
//      count += 1;
//    }
//    retVal
//    /*
//    (variables zip Seq.range(0, variables.size-1)).map( pair => {
//      JsString(pair._1 + pair._2.toString())
////      exprToJson(sessionName, uid + pair._2.toString(), pair._1)
//    }).toList*/
//  }
//}
//
///**
// * KeYmaera Hydra server-side API implementation.
// */
//object KeYmaeraClient {
//  //For now, we just tightly couple to the server running in this jvm.
////  val server = "localhost"
////  val port = 8080 
//  
//
//  /**
//   * @return the sequent containing the expression or sequent with id ``uid"
//   */
//  def getContainingSequent(sessionName : String, uid : String) = {
//    if(this.hasSequent(sessionName, uid)) this.getSequent(sessionName, uid)
//    else if(this.hasExpression(sessionName, uid)) {
//      val expr = this.getExpression(sessionName, uid)
//      val sequentUid = {
//        if(uid.contains("a")) {
//	      val parts = uid.split("a")
//          if(parts.size > 2) throw new Exception("bad uid")
//	      parts.head
//	    }
//	    else if(uid.contains("p")) {
//	      val parts = uid.split("p")
//	      if(parts.size > 2) throw new Exception("bad uid")
//	      parts.head        
//	    }
//	    else if(uid.contains("s")) {
//	      val parts = uid.split("s")
//	      if(parts.size > 2) throw new Exception("bad uid")
//	      parts.head
//	    }
//	    else {
//	      throw new Exception("bad uid")
//	    }
//      }
//      this.getSequent(sessionName, sequentUid)      
//    }
//    else {
//      throw new Exception("Formula not found.")
//    }
//  }
//  
//  def serviceRequest(sessionName : String, request : Request) = {
//    val updates = request.getResultingUpdates()
//    for(update <- updates) {
//      ServerState.addUpdate(sessionName, update.json)
//    }
//    updates
//  }
//  
//  def hasSequent(sessionName : String, uid : String) = {
//    ServerState.sequents.containsKey((sessionName, uid))
//  }
//  
//  def getSequent(sessionName : String, uid : String) = {
//    ServerState.getSequent(sessionName, uid)
//  }
//  
//  def hasExpression(sessionName:String, uid:String) = {
//    ServerState.expressions.containsKey((sessionName, uid))
//  }
//  def getExpression(sessionName:String, uid:String) = {
//    ServerState.getExpression(sessionName, uid)
//  }
//  def sendSequent(sessionName : String, uid : String, s:Sequent) = {
//    ServerState.addSequent(sessionName,uid,s)
//  }
//  
//  def sendExpression(sessionName : String, uid : String, e:Expr) = {
//    ServerState.addExpression(sessionName, uid, e)
//  }
//}
//
