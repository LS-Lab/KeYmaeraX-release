/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra

import java.util.concurrent.{Callable, ExecutorService, Executors, FutureTask}

import edu.cmu.cs.ls.keymaerax.core.Ensures
import edu.cmu.cs.ls.keymaerax.bellerophon.{
  BelleExpr,
  BelleThrowable,
  BelleValue,
  Interpreter,
  UnsupportedTacticFeature,
}

/**
 * Scheduler for Bellerophon tactics
 * @author
 *   Nathan Fulton
 */
object BellerophonTacticExecutor {
  val defaultSize = 10
  val defaultExecutor = new BellerophonTacticExecutor(defaultSize)
}

case class InterpreterFuture[T](userId: String, interpreter: Interpreter, callable: Callable[T])
    extends FutureTask[T](callable) {
  override def cancel(mayInterruptIfRunning: Boolean): Boolean = {
    interpreter.kill()
    super.cancel(mayInterruptIfRunning)
  }
}

class BellerophonTacticExecutor(poolSize: Int) {
  require(poolSize > 0, "At least one thread is needed.")
  private val pool: ExecutorService = Executors.newFixedThreadPool(poolSize)

  /**
   * [[scheduledTactics]] could be at any state of execution, included finished. Tactics are never removed from the
   * [[scheduledTactics]] mapping unless explicitly via .remove()
   */
  private val scheduledTactics
      : scala.collection.mutable.Map[String, InterpreterFuture[Either[BelleValue, BelleThrowable]]] =
    scala.collection.mutable.Map()

  def tasksForUser(userId: String): List[String] = {
    scheduledTactics.flatMap { case (task, future) => if (userId == future.userId) List(task) else Nil }.toList
  }

  /**
   * Schedules a tactic for execution.
   * @param tactic
   *   The tactic to run
   * @param value
   *   The value to apply the tactic to.
   * @param interpreter
   *   The interpreter that actually runs the tactic.
   * @return
   *   The ID that [[BellerophonTacticExecutor]] uses to identify this tactic.
   */
  def schedule(userId: String, tactic: BelleExpr, value: BelleValue, interpreter: Interpreter): String = {
    val id = java.util.UUID.randomUUID().toString
    assert(!scheduledTactics.contains(id), "All running tactic IDs should be unique.")
    val future = makeFuture(userId, tactic, value, interpreter)
    pool.submit(future)
    scheduledTactics += ((id, future))
    id
  }

  /** True, if the task identified by `id` is done, false otherwise. */
  def isDone(id: String): Boolean = getTask(id) match {
    case Some(future) => future.isDone
    case None => throw new Exception("This tactic does not exist in the list.")
  }

  /** Tests whether the task identified by `id` exists. */
  def contains(id: String): Boolean = scheduledTactics.contains(id)

  /** Returns the task identified by `id`. */
  def getTask(id: String): Option[InterpreterFuture[Either[BelleValue, BelleThrowable]]] = scheduledTactics.get(id)

  /** Returns the result of the tactic, or None if the tactic is not done running. */
  def getResult(id: String): Option[Either[BelleValue, BelleThrowable]] =
    synchronized { if (isDone(id)) Some(scheduledTactics(id).get()) else None }

  /**
   * @param id
   *   The schedule id of the tactic to remove.
   * @param force
   *   If true, then the tactic can be removed even if it is currently running. In that case, the tactic execution is
   *   halted first. Defaults to false.
   */
  def tryRemove(id: String, force: Boolean = false): Unit = synchronized {
    if (scheduledTactics.contains(id)) {
      if (isDone(id)) { scheduledTactics.remove(id) }
      else if (force) {
        scheduledTactics.get(id).foreach(_.cancel(true))
        scheduledTactics.remove(id)
      } else {
        // @note if you want to remove a tactic even if it's still running, then call remove(id, true).
        throw new Exception(
          "Attempted to remove a tactic from scheduledTactics, but that tactic is not yet finished executing."
        )
      }
    }
  } ensures (!scheduledTactics.contains(id))

  /**
   * @param id
   *   The schedule id of the tactic to remove.
   * @param force
   *   If true, then the tactic can be removed even if it is currently running. In that case, the tactic execution is
   *   halted first. Defaults to false.
   */
  def remove(id: String, force: Boolean = false): Unit = {
    require(scheduledTactics.contains(id), "Cannot remove a tactic whose ID is not in the key set of scheduledTactics.")
    tryRemove(id, force)
  }

  /**
   * @param id
   *   The schedule id of the tactic to wait on
   * @param millis
   *   The duration in milliseconds to sleep between polling attempts
   */
  def wait(id: String, millis: Int = 10): Option[Either[BelleValue, BelleThrowable]] = {
    try {
      while (!isDone(id)) { Thread.sleep(millis) }
      getResult(id)
    } catch {
      // If the tactic execution is cancelled
      case _: Exception => None
    }
  }

  private def makeFuture(userId: String, tactic: BelleExpr, value: BelleValue, interpreter: Interpreter) = {
    new InterpreterFuture[Either[BelleValue, BelleThrowable]](
      userId,
      interpreter,
      new Callable[Either[BelleValue, BelleThrowable]]() {
        override def call(): Either[BelleValue, BelleThrowable] = {
          try { Left(interpreter(tactic, value)) }
          catch {
            case e: BelleThrowable => Right(e)
            case e: Throwable =>
              Right(new UnsupportedTacticFeature("Tactic " + tactic.prettyString + " reported:\n" + e.getMessage, e))
          }
        }
      },
    )
  }
}
