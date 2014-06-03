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


case class RunTacticRequest(sessionName : String, tacticName : String, uid : String, input : Option[List[String]]) extends Request {
  private def proofNodeMap[T](l : List[ProofNode], fn : ProofNode => T) : List[T] = {
    //System.err.println(l.size.toString() + l.map(_.toString()).mkString(","))
    val thisLevel      = l.map(fn)
    val nextLevelSteps = l.map(node => node.children).flatten
    val nextLevelNodes = nextLevelSteps.map(step => step.subgoals).flatten
    l.map(node => require(!nextLevelNodes.contains(node))) //guard against inf recursion
    if(nextLevelNodes.isEmpty) thisLevel //base
    else                       thisLevel ++ proofNodeMap(nextLevelNodes, fn)
  }
  
  /**
   * Runs ProofNodeMap on all nodes in a step.
   */
  private def proofStepMap[T](step : ProofStep, fn : ProofNode => T) : List[T] = {
    val firstLevel = step.subgoals
    proofNodeMap(firstLevel, fn)
  }
  
  //////////////////////////////////////////////////////////////////////////////
  // If we do not need to cache/recover these proof steps/nodes, then this should
  // all be replaced with logic that loops through the proof steps and assigns
  // parentIds based on structure alone.
  
  /**
   * @return uid for the subject w.r.t. the root, given that the uid of the root is rootUid.
   * 
   * An uid for a proof node/step (different from uids for sequents and expressions... oy vey) 
   * is one of:
   * 	uid + "g" + integer + uid?
   *  	uid + "sg" + integer + gs + uid?
   * 
   */
  var total = 0
  private def nodeToUid(root : ProofNode, rootUid : String, subject : ProofNode) : String = {
    total += 1
    rootUid + total.toString()
//    nodeToUidHelper(root, rootUid, subject) match {
//      case Some(s) => s
//      case None => throw new Exception("could not get uid: " + root.toString() + "<br/>" + rootUid + "<br/>" + subject.toString())
//    }
  }
    
  private def nodeToUidHelper(root : ProofNode, rootUid : String, subject : ProofNode) : Option[String] = {
    if(root.equals(subject)) Some(rootUid)
    else {
      val children = root.children zip Range(0,root.children.size-1)
      val results = children.map(p => {
        uidFromStep(p._1, rootUid + p._2, subject)
      })
      if(results.size > 0) results.head
      else None
    }
  }
  
  def uidFromStep(step : ProofStep, stepUid : String, subject : ProofNode) : Option[String] = {
    val cs = step.goal.children zip Range(0, step.goal.children.size - 1)
    val goalResults = cs.map(c => {
      uidFromStep(c._1, stepUid + c._2, subject) match {
        case Some(id) => Some("g" + id)
        case None => None
      }
    }).filter(x => x.isDefined)
    if(!goalResults.isEmpty) goalResults.head
    else {
      val sgs = step.subgoals zip Range(0, step.subgoals.length - 1)
      val results = sgs.map(p => nodeToUidHelper(p._1, stepUid + "sg" + p._2 + "gs", subject)).filter(p => p.isDefined)
      if(results.length != 0) results.head 
      else None
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
  // End numbering block
  //////////////////////////////////////////////////////////////////////////////
  
  
  /**
   * @return list of updates that results from the requested tactic.
   */
  def getResultingUpdates() : List[Update] = 
    try { //Much can go wrong, so the entire request is wrapped in an error handler.
      //tacticName -> tactic
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
    
      val newProofNodes = {
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
          //Note: topLevel is necessary because we don't want the actual root added to the list
          //of added nodes.
          val topLevel = r.children.map(step => step.subgoals).flatten
          proofNodeMap(List(r), mapFunction)
        }
      }
      
      newProofNodes :+ new TacticFinished(sessionName, tacticName, uid)
    }
    catch {
      case e : Exception => (new ErrorResponse(sessionName, e)) :: Nil
    }
}