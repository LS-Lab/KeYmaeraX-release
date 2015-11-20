package edu.cmu.cs.ls.keymaerax.tacticsinterface

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleValue, BelleExpr, IOListener}
import edu.cmu.cs.ls.keymaerax.core.Provable
import edu.cmu.cs.ls.keymaerax.hydra.ExecutionStepStatus.ExecutionStepStatus

/**
  * Created by bbohrer on 11/20/15.
  */
object TacticDebugger {

  class DebuggerListener extends IOListener {
    class TraceNode {
      var id: Option[String] = None
      var parent: TraceNode = null
      var sibling: TraceNode = null
      var input: BelleValue = null
      var output: BelleValue = null
      var status: ExecutionStepStatus = null
      var reverseChildren: List[TraceNode] = Nil
    }

    var youngestSibling: TraceNode = null
    var node: TraceNode = null

    def begin(v: BelleValue, expr: BelleExpr) = {
      val parent = node
      node = new TraceNode()
      node.parent = parent
      node.sibling = youngestSibling
      node.input = v
    }

    def end(v: BelleValue, expr: BelleExpr, result: BelleValue): Unit = {
      val current = node
      node = node.parent
      youngestSibling = current
      current.output = result
      node.reverseChildren = current::node.reverseChildren
    }
  }
}
