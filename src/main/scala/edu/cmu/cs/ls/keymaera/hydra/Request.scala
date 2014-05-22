package edu.cmu.cs.ls.keymaera.hydra

import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary
import edu.cmu.cs.ls.keymaera.parser.KeYmaeraParser
import edu.cmu.cs.ls.keymaera.core.{Sequent, Formula, RootNode}
import edu.cmu.cs.ls.keymaera.tactics.{Tactics, TacticWrapper}
import spray.json.JsString

////////////////////////////////////////////////////////////////////////////////
// Request types
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

case class FormulaFromUidRequest(sessionName : String, uid : String)  extends Request {
  def getResultingUpdates() : List[Update] = {
    try {
      val expr = KeYmaeraClient.getExpression(sessionName, uid)
      val json = KeYmaeraClientPrinter.exprToJson(sessionName, uid, expr)
      new FormulaFromUidResponse(sessionName, json) :: Nil
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

case class FormulaToInteractiveStringRequest(sessionName : String, uid : String) extends Request {
  def getResultingUpdates() : List[Update] = 
    try {
      if(ServerState.expressions == null) {
        new ErrorResponse(sessionName, new NullPointerException()) :: Nil
      }
      else if(!KeYmaeraClient.hasExpression(sessionName,uid)) {
        new ErrorResponse(sessionName, new Exception("UID not found for uid: " + sessionName + "," + uid + " in " + ServerState.expressions.keySet().toArray().mkString(","))) :: Nil
      }
      else {
        ???
//        val expr= KeYmaeraClient.getExpression(sessionName,uid)
//        val prettyString = new KeYmaeraClientInteractivePrinter(sessionName).makeInteractive(expr.asInstanceOf[Formula])
//        (new FormulaToStringResponse(sessionName,prettyString))::Nil
      }
    }
    catch {
      case e : Exception => (new ErrorResponse(sessionName, e))::Nil
    }
}

case class RunTacticRequest(sessionName : String, tacticName : String, uid : String) extends Request {
  def getResultingUpdates() : List[Update] = 
    try {
      if(tacticName.equals("default")) {
//        val sequent = ServerState.getSequent(sessionName, uid)
//        val tactic = TacticLibrary.default
//        val r = new RootNode(sequent)
//        Tactics.KeYmaeraScheduler.dispatch(new TacticWrapper(tactic, r))
//        while(!(Tactics.KeYmaeraScheduler.blocked == Tactics.KeYmaeraScheduler.maxThreads
//          && Tactics.KeYmaeraScheduler.prioList.isEmpty
//          && Tactics.MathematicaScheduler.blocked == Tactics.MathematicaScheduler.maxThreads
//          && Tactics.MathematicaScheduler.prioList.isEmpty)) 
//        {
//          Thread.sleep(100)
//        }
//        
//        val results = if(r.children.size == 0) {
//          Nil
//        }
//        else {
//          val sequents = r.children.map(_.subgoals.map(goal => goal.sequent)).flatten
//        
//          val results = (sequents zip Seq.range(0, sequents.size-1)).map(p => 
//            new AddNodeResponse(sessionName, JsString(uid + p._2.toString()), KeYmaeraClientPrinter.getSequent(sessionName, uid + p._2.toString(), p._1)))
//          if(results.size == 0) {
//            new ErrorResponse(sessionName, new Exception("Tactic ran but there was not result."))::Nil
//          }
//          else {
//            results
//          }
//        }
        val results = Nil
        //Add the "finished" result.
        results ++ List( new TacticFinished(sessionName, tacticName, uid) )
      }
      else {
        new ErrorResponse(sessionName, new Exception("tactic not supported by the runtactic request.")) :: Nil
      }
  }
  catch {
    case e : Exception => (new ErrorResponse(sessionName, e)) :: Nil
  }
}