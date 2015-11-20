package edu.cmu.cs.ls.keymaerax.tacticsinterface

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleProvable, BelleValue, BelleExpr, IOListener}
import edu.cmu.cs.ls.keymaerax.core.Provable
import edu.cmu.cs.ls.keymaerax.hydra.{ExecutionStepPOJO, DBAbstraction, ExecutionStepStatus}
import edu.cmu.cs.ls.keymaerax.hydra.ExecutionStepStatus.ExecutionStepStatus

/**
  * Created by bbohrer on 11/20/15.
  */
object TacticDebugger {

  class DebuggerListener (db: DBAbstraction, executionId: String, executableId: String, userExecuted: Boolean,
                          alternativeOrder: Int, branch:Either[Int, String]) extends IOListener {
    class TraceNode (isFirstNode: Boolean){
      var id: Option[String] = None
      var parent: TraceNode = null
      var sibling: TraceNode = null
      var input: Provable = null
      var output: Provable = null
      var status: ExecutionStepStatus = null
      var reverseChildren: List[TraceNode] = Nil
      def children = reverseChildren.reverse
      var stepId: String = null
      val altOrder = if (isFirstNode) alternativeOrder else 0
      val branchLabel: String = branch match {case Right(label) => label case _ => null}
      val branchOrder: Int = branch match {case Left(order) => order case _ => -1}
      val userExe = if(userExecuted) isFirstNode else false

      var inputProvableId: String = null
      var outputProvableId: String = null

      def getInputProvableId:String = {
        if (inputProvableId == null)
          inputProvableId = db.serializeProvable(input)
        inputProvableId
      }

      def getOutputProvableId:String = {
        if (outputProvableId == null)
          outputProvableId = db.serializeProvable(output)
        outputProvableId
      }

      def asPOJO: ExecutionStepPOJO = {
        new ExecutionStepPOJO (stepId, executionId, sibling.stepId, parent.stepId, Option(branchOrder),
          Option(branchLabel), alternativeOrder,status, executableId, getInputProvableId, getOutputProvableId,
          userExecuted)
      }
    }

    var youngestSibling: TraceNode = null
    var node: TraceNode = null

    def begin(v: BelleValue, expr: BelleExpr) = {
      val parent = node
      node = new TraceNode(isFirstNode = parent == null)
      node.parent = parent
      node.sibling = youngestSibling
      node.input = v match {case BelleProvable(p) => p}
      node.status = ExecutionStepStatus.Running

      if(parent != null) {
        parent.status = ExecutionStepStatus.DependsOnChildren
        parent.reverseChildren = node :: parent.reverseChildren
        db.updateExecutionStatus(parent.stepId, parent.status)
      }
      node.stepId = db.addExecutionStep(node.asPOJO)
    }

    def end(v: BelleValue, expr: BelleExpr, result: BelleValue): Unit = {
      val current = node
      node = node.parent
      youngestSibling = current
      current.output = result match {case BelleProvable(p) => p}
      current.status = ExecutionStepStatus.Finished
      db.updateExecutionStatus(current.stepId, current.status)
    }
  }
}
