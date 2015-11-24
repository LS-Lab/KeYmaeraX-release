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
        if (input != null && inputProvableId == null)
          inputProvableId = db.serializeProvable(input)
        inputProvableId
      }

      def getOutputProvableId:String = {
        if (output != null && outputProvableId == null)
          outputProvableId = db.serializeProvable(output)
        outputProvableId
      }

      def asPOJO: ExecutionStepPOJO = {
        val siblingStep = if (sibling == null) null else sibling.stepId
        val parentStep = if (parent == null) null else parent.stepId
        new ExecutionStepPOJO (stepId, executionId, siblingStep, parentStep, Option(branchOrder),
          Option(branchLabel), alternativeOrder,status, executableId, getInputProvableId, getOutputProvableId,
          userExecuted)
      }
    }

    var youngestSibling: TraceNode = null
    var node: TraceNode = null
    var isDead: Boolean = false

    def begin(v: BelleValue, expr: BelleExpr): Unit = {
      synchronized {
        if(isDead) return
        val parent = node
        node = new TraceNode(isFirstNode = parent == null)
        node.parent = parent
        node.sibling = youngestSibling
        node.input = v match {
          case BelleProvable(p) => p
        }
        node.status = ExecutionStepStatus.Running

        if (parent != null) {
          parent.status = ExecutionStepStatus.DependsOnChildren
          parent.reverseChildren = node :: parent.reverseChildren
          db.updateExecutionStatus(parent.stepId, parent.status)
        }
        node.stepId = db.addExecutionStep(node.asPOJO)
      }
    }

    def end(v: BelleValue, expr: BelleExpr, result: BelleValue): Unit = {
      synchronized {
        if(isDead) return
        val current = node
        node = node.parent
        youngestSibling = current
        current.output = result match {
          case BelleProvable(p) => p
        }
        current.status = ExecutionStepStatus.Finished
        db.updateExecutionStatus(current.stepId, current.status)
      }
    }

    /** Called by HyDRA before killing the interpreter's thread. Updates the database to reflect that the computation
      * was interrupted. There are two race conditions to worry about here:
      * (1) kill() can race with a call to begin/end that was in progress when kill() started. This is resolved with
      * a mutex (synchronized{} blocks)
      * (2) An in-progress computation can race with a kill signal (sent externally after kill() is called). This is
      * resolved by setting a flag during kill() which turns future operations into a no-op. */
    def kill(): Unit = {
      synchronized {
        isDead = true
        db.updateExecutionStatus(node.stepId, ExecutionStepStatus.Aborted)
      }
    }
  }
}
