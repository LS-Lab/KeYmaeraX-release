package edu.cmu.cs.ls.keymaera.hydra

import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary
import edu.cmu.cs.ls.keymaera.parser.KeYmaeraParser
import edu.cmu.cs.ls.keymaera.core.{Sequent, Formula, RootNode, ProofNode, ProofStep}
import edu.cmu.cs.ls.keymaera.tactics.{Tactics, TacticWrapper}
import spray.json.JsString
import spray.json.JsObject
import edu.cmu.cs.ls.keymaera.core.NamedSymbol

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
      val rootSequent = new Sequent(List(), scala.collection.immutable.IndexedSeq(), scala.collection.immutable.IndexedSeq(expression.asInstanceOf[Formula]));
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


case class RunTacticRequest(sessionName : String, tacticName : String, 
    uid : String, input : Option[List[String]], 
    parentNodeId : String) extends Request 
{
  ///Begin constructor logic.
  val sequent = ServerState.getSequent(sessionName, uid)
  
  val tactic = tacticName match {
    case "default" => TacticLibrary.default
    case "closeT"  => TacticLibrary.closeT
    case _ => {
      throw new Exception("Tactic not defined for the RunTactic Result: " + tacticName)
    }
  }
  ///End constructor logic.
  
  def getResultingUpdates() = {
    try {
      val root = runTactic()
      if(root.children.size == 0) {
        Nil
      }
      else {
        makeUpdates(root)
      }
    }
    catch {
      case e : Exception => {
        val errorResp = new ErrorResponse("Error while running tactic",e)
        errorResp :: Nil
      }
    }
  }
  
  def makeUpdates(root : RootNode) = {
    null
  }
  
  
  
  def runTactic() = {
    val r = new RootNode(sequent)
    Tactics.KeYmaeraScheduler.dispatch(new TacticWrapper(tactic, r))
    while(!(Tactics.KeYmaeraScheduler.blocked == Tactics.KeYmaeraScheduler.maxThreads
    && Tactics.KeYmaeraScheduler.prioList.isEmpty
    && Tactics.MathematicaScheduler.blocked == Tactics.MathematicaScheduler.maxThreads
    && Tactics.MathematicaScheduler.prioList.isEmpty)) 
    {
      Thread.sleep(100)
    }
    r
  }
}


//case class RunTacticRequest(sessionName : String, tacticName : String, uid : String, input : Option[List[String]], parentNodeId : String) extends Request {
//  private def proofNodeMap[T](l : List[ProofNode], fn : ProofNode => T) : List[T] = {
//    //System.err.println(l.size.toString() + l.map(_.toString()).mkString(","))
//    val thisLevel      = l.map(fn)
//    val nextLevelSteps = l.map(node => node.children).flatten
//    val nextLevelNodes = nextLevelSteps.map(step => step.subgoals).flatten
//    l.map(node => require(!nextLevelNodes.contains(node))) //guard against inf recursion
//    if(nextLevelNodes.isEmpty) thisLevel //base
//    else                       thisLevel ++ proofNodeMap(nextLevelNodes, fn)
//  }
//  
//  /**
//   * Runs ProofNodeMap on all nodes in a step.
//   */
//  private def proofStepMap[T](step : ProofStep, fn : ProofNode => T) : List[T] = {
//    val firstLevel = step.subgoals
//    proofNodeMap(firstLevel, fn)
//  }
//  
//  /**
//   * @return list of updates that results from the requested tactic.
//   */
//  def getResultingUpdates() : List[Update] = {
//    try { //Much can go wrong, so the entire request is wrapped in an error handler.
//      //tacticName -> tactic
//      val tactic = tacticName match {
//        case "default" => TacticLibrary.default
//        case "close"   => TacticLibrary.closeT
//        case _ => throw new Exception("tactic not supported: " + tacticName)
//      }
//      
//      val sequent = ServerState.getSequent(sessionName, uid)
//    
//      val r = new RootNode(sequent)
//      Tactics.KeYmaeraScheduler.dispatch(new TacticWrapper(tactic, r))
//      while(!(Tactics.KeYmaeraScheduler.blocked == Tactics.KeYmaeraScheduler.maxThreads
//      && Tactics.KeYmaeraScheduler.prioList.isEmpty
//      && Tactics.MathematicaScheduler.blocked == Tactics.MathematicaScheduler.maxThreads
//      && Tactics.MathematicaScheduler.prioList.isEmpty)) 
//      {
//        Thread.sleep(100)
//      }
//    
//      if(r.children.size == 0) { 
//        Nil 
//      }
//      else {
//        Nil
//      }
//    }
//    catch {
//      case e : Exception => (new ErrorResponse(sessionName, e)) :: Nil
//    }
//  }
//}