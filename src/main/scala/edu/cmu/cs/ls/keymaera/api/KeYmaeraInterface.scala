package edu.cmu.cs.ls.keymaera.api

import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.parser.KeYmaeraParser
import edu.cmu.cs.ls.keymaera.tactics.Tactics.{PositionTactic, Tactic}
import edu.cmu.cs.ls.keymaera.tactics.{TacticWrapper, Tactics, TacticLibrary}
import edu.cmu.cs.ls.keymaera.core.Sequent
import scala.Some
import scala.Unit

/**
 * Open issues:
 * - How do we identify where changes came from?
 *   Consider the following case: A user starts a tactic on a node and then does some steps himself. If we now poll the node
 *   to find out about its children we might get a bunch of alternatives. Which one is it the user wants to see and how do we identify it?
 * - How can we attach meta information for the GUI?
 * - What information do we want to attach?
 *
 * Created by jdq on 6/12/14.
 */
object KeYmaeraInterface {

  object TaskManagement {
    @volatile var tasks: Map[String, (ProofNode, Map[String, ProofNode])] = Map()

    def addTask(r: ProofNode, taskId: String) = this.synchronized {
      assert(r.children.isEmpty)
      tasks += (taskId -> (r, Map()))
    }

    def addNode(tId: String, nId: String, p: ProofNode) = this.synchronized {
      tasks.get(tId) match {
        case Some(v) =>
          tasks += (tId -> (v._1, v._2 + (nId -> p)))
        case None => throw new IllegalArgumentException("Task not found " + tId)
      }
    }

    def containsTask(id: String) = tasks.contains(id)

    def getRoot(id: String): Option[ProofNode] = tasks.get(id).map(_._1)

    def getNode(tId: String, nId: String): Option[ProofNode] = tasks.get(tId).map(_._2.get(nId)).flatten
  }

  object TacticManagement {
    // TODO store tactics in DB, let DB issue IDs
    private var count = 0
    @volatile var tactics: Map[Int, () => Tactic] = Map()
    @volatile var positionTactics: Map[Int, () => PositionTactic] = Map()
    @volatile var inputTactics: Map[Int, (Formula) => Tactic] = Map()
    @volatile var inputPositionTactics: Map[Int, (Formula) => PositionTactic] = Map()

    addTactic(TacticLibrary.default)
    addPositionTactic(TacticLibrary.step)

    def addTactic(t: Tactic): Int = this.synchronized {
      val res = count
      tactics += (res -> (() => t))
      count = count + 1
      res
    }

    def addInputTactic(t: (Formula => Tactic)): Int = this.synchronized {
      val res = count
      inputTactics += (res -> t)
      count = count + 1
      res
    }

    def addPositionTactic(t: PositionTactic): Int = this.synchronized {
      val res = count
      positionTactics += (res -> (() => t))
      count = count + 1
      res
    }

    def addInputPositionTactic(t: (Formula => PositionTactic)): Int = this.synchronized {
      val res = count
      inputPositionTactics += (res -> t)
      count = count + 1
      res
    }

    def getTactic(id: Int): Option[Tactic] = tactics.get(id).map(_())

    def getPositionTactic(id: Int): Option[PositionTactic] = positionTactics.get(id).map(_())

    def getTactics: List[(Int, String)] = tactics.foldLeft(Nil: List[(Int, String)])((a, p) => a :+ (p._1, p._2().name))

    def getPositionTactics: List[(Int, String)] = positionTactics.foldLeft(Nil: List[(Int, String)])((a, p) => a :+ (p._1, p._2().name))

    // TODO implement getter for the other tactics
  }

  object RunningTactics {
    private var tactics: Map[String, Tactic] = Map()
    def add(t: Tactic, tId: String) = this.synchronized {
      tactics += (tId -> t)
    }

    def get(id: String): Option[Tactic] = tactics.get(id)
  }

  /**
   * Parse the problem and add it to the tasks management system
   *
   * @param taskId
   * @param content
   * @return JSON representation of the content
   */
  def addTask(taskId: String, content: String): String = {
    if (TaskManagement.containsTask(taskId)) throw new IllegalArgumentException("Duplicate task ID " + taskId)
    new KeYmaeraParser().runParser(content) match {
      case f: Formula =>
        val seq = Sequent(List(), collection.immutable.IndexedSeq[Formula](), collection.immutable.IndexedSeq[Formula](f) )
        val r = new RootNode(seq)
        TaskManagement.addTask(r, taskId)
        json(r, taskId, 0, taskId)
      case a => throw new IllegalStateException("Parsing the input did not result in a formula but in: " + a)
    }
  }

  def getNode(taskId: String, nodeId: Option[String]): Option[String] = nodeId match {
      case Some(id) => TaskManagement.getNode(taskId, id).map(json(_: ProofNode, id, 0, taskId))
      case None => TaskManagement.getRoot(taskId).map(json(_: ProofNode, taskId.toString, 0, taskId))
  }

  def getTactics: List[(Int, String)] = TacticManagement.getTactics

  def getPositionTactics: List[(Int, String)] = TacticManagement.getPositionTactics

  /**
   *
   * @param taskId the task for which this tactic is dispatched
   * @param nodeId the proof node on which to run the tactic (None to execute on the root node)
   * @param tacticId the tactic to dispatch
   * @param formulaId the formula (None to execute on the sequent)
   * @param tId the ID of the dispatched tactic
   * @param callBack callback executed when the tactic finishes
   */
  def runTactic(taskId: String, nodeId: Option[String], tacticId: Int, formulaId: Option[String], tId: String, callBack: Option[String => ((String, Option[String], Int) => Unit)] = None) = {
    (nodeId match {
      case Some(id) => TaskManagement.getNode(taskId, id)
      case None => TaskManagement.getRoot(taskId)
    }) match {
      case Some(n) =>
        (formulaId match {
          case Some(fid) =>
            val tail = Integer.parseInt(fid.split(":")(1))
            val pos = if(fid.startsWith("ante:")) new AntePosition(tail) else new SuccPosition(tail)
            TacticManagement.getPositionTactic(tacticId) match {
            case Some(t) => Some(t(pos))
            case None => None
          }
          case None =>
            TacticManagement.getTactic(tacticId)
        }) match {
        case Some(t) =>
          // attach a info transformation function which later on allows us to track then changes performed by this tactic
          // observe that since all nodes should be produced by tactics spawned off here, the nodes will all have a tactic label
          RunningTactics.add(t, tId)
          // register listener to react on tactic completion
          // this way the business logic can react to the completion if required
          t.registerCompletionEventListener(_ => callBack.foreach(_(tId)(taskId, nodeId, tacticId)))
          t.updateInfo = (p: ProofNodeInfo) => p.infos += ("tactic" -> tId.toString)
          t.updateStepInfo = (p: ProofStepInfo) => p.infos += ("tactic" -> tId.toString)
          println("Dispatching tactic")
          Tactics.KeYmaeraScheduler.dispatch(new TacticWrapper(t, n))
        case None => None
      }
      case None => println("Tasks are + " + TaskManagement.tasks); None
    }
  }

  def isRunning(tacticInstanceId: String): Boolean = {
    RunningTactics.get(tacticInstanceId) match {
      case Some(t) => !t.isComplete
      case None => false
    }
  }

  /**
   * This methods allows to poll for updates downwards from a given node
   *
   * @param taskId
   * @param nodeId
   * @param depth
   * @return
   */
  def getSubtree(taskId: String, nodeId: Option[String], depth: Int): Option[String] = {
    (nodeId match {
      case Some(id) => (id, TaskManagement.getNode(taskId, id))
      case None => ("", TaskManagement.getRoot(taskId))
    }) match {
      case (id, Some(n)) => Some(getSubtree(n, id, depth, taskId))
      case (_, None) => None
    }
  }

  def getSubtree(taskId: String, nodeId: Option[String], filter: (ProofStepInfo => Boolean)): Option[String] = {
    (nodeId match {
      case Some(id) => (id, TaskManagement.getNode(taskId, id))
      case None => ("", TaskManagement.getRoot(taskId))
    }) match {
      case (id, Some(n)) => Some(getSubtree(n, id, filter, taskId))
      case (_, None) => println("Not found " + taskId + " " + nodeId); None
    }

  }

  private def getSubtree(n: ProofNode, id: String, depth: Int, rootId: String): String = json(n, id, depth, rootId)

  private def getSubtree(n: ProofNode, id: String, filter: (ProofStepInfo => Boolean), rootId: String): String = json(n, id, filter, rootId)

  // TODO: maybe allow listeners to node change events

 // def json(p: ProofNode): String = JSONConverter(p)

  def json(p: ProofNode, id: String, l: Int, rootId: String): String = JSONConverter(p, id, l, (x: ProofNode, i: String) => TaskManagement.addNode(rootId, i, x))

  def json(p: ProofNode, id: String, filter: (ProofStepInfo => Boolean), rootId: String): String = JSONConverter(p, id, filter, (x: ProofNode, i: String) => TaskManagement.addNode(rootId, i, x))
}
