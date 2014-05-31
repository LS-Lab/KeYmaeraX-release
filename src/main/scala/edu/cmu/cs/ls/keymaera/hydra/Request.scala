package edu.cmu.cs.ls.keymaera.hydra

import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary
import edu.cmu.cs.ls.keymaera.parser.KeYmaeraParser
import edu.cmu.cs.ls.keymaera.core.{Sequent, Formula, RootNode}
import edu.cmu.cs.ls.keymaera.tactics.{Tactics, TacticWrapper}
import spray.json.JsString
import edu.cmu.cs.ls.keymaera.core.ProofNode
import spray.json.JsObject
import edu.cmu.cs.ls.keymaera.core.NamedSymbol
import edu.cmu.cs.ls.keymaera.hydra.ErrorResponse

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

case class RunTacticRequest(sessionName : String, tacticName : String, uid : String) extends Request {
  private def proofNodeMap[T](l : List[ProofNode], fn : ProofNode => T) : List[T] = {
    //System.err.println(l.size.toString() + l.map(_.toString()).mkString(","))
    val thisLevel      = l.map(fn)
    val nextLevelSteps = l.map(node => node.children).flatten
    val nextLevelNodes = nextLevelSteps.map(step => step.subgoals).flatten
    l.map(node => require(!nextLevelNodes.contains(node)))
    if(nextLevelNodes.isEmpty) thisLevel //base
    else                       thisLevel ++ proofNodeMap(nextLevelNodes, fn)
  }
  
  /**
   * @return uid for the subject w.r.t. the root, given that the uid of the root is rootUid.
   */
  private def nodeToUid(root : ProofNode, rootUid : String, subject : ProofNode) = {
    if(root.equals(subject)) {
      rootUid
    }
    else {
      rootUid + "0" //TODO correct this...
    }
  }
  
  /**
   * @return uid for the subject's parent w.r.t. the root, given that the uid of the root is rootUid.
   */
  private def nodeToParentUid(root : ProofNode, rootUid : String, subject : ProofNode) = {
    if(root.equals(subject)) {
      rootUid
    }
    else {
      rootUid //TODO correct this...
    }
  }
  
  def getResultingUpdates() : List[Update] = 
    try {
      val tactic = tacticName match {
        case "default" => TacticLibrary.default
        case "close"   => TacticLibrary.closeT
        case _ => throw new Exception("tactic not supported: " + tacticName)
      }
      
      val sequent = ServerState.getSequent(sessionName, uid)
    
      val r = new RootNode(sequent)
      Tactics.KeYmaeraScheduler.dispatch(new TacticWrapper(tactic, r))
      while(!(Tactics.KeYmaeraScheduler.blocked == Tactics.KeYmaeraScheduler.maxThreads
      && Tactics.KeYmaeraScheduler.prioList.isEmpty
      && Tactics.MathematicaScheduler.blocked == Tactics.MathematicaScheduler.maxThreads
      && Tactics.MathematicaScheduler.prioList.isEmpty)) 
      {
        Thread.sleep(100)
      }
    
      val results = {
        if(r.children.size == 0) { 
          Nil 
        }
        else {
          val mapFunction : ProofNode => AddNodeResponse = (x:ProofNode) => {
            val parentId = JsString(nodeToParentUid(r,uid,x))
            val newId = nodeToUid(r, uid, x)
            //TODO we should not be using newId as an id for nodes and sequents...
            val sequentString = KeYmaeraClientPrinter.getSequent(sessionName, newId, x.sequent)
            val nodeString = JsObject(
              "sequent" -> sequentString,
              "id" -> JsString(newId)
            )
            new AddNodeResponse(sessionName, parentId, nodeString)
          }
          val topLevel = r.children.map(step => step.subgoals).flatten
          proofNodeMap(topLevel, mapFunction)
        }
      }
    
      //Add the "tactic finished" result.
      results ++ List( new TacticFinished(sessionName, tacticName, uid) )
    }
    catch {
      case e : Exception => (new ErrorResponse(sessionName, e)) :: Nil
    }
}