/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.tools.ext

import java.util.concurrent._

import org.keymaerax.Logging
import org.keymaerax.core.Ensures

import scala.collection.mutable

/** A tool executor executes commands concurrently on up to `poolSize` threads. */
class ToolExecutor(poolSize: Int) extends Logging {

  /** A task handle identifies the task with `id` and converts into the expected result type `T`. */
  case class TaskHandle[T](id: String) {

    /** Converts the task into the expected result type. */
    private[ToolExecutor] def convert(r: Either[Any, Throwable]): Either[T, Throwable] = r match {
      case Left(s) => Left(s.asInstanceOf[T])
      case Right(t) => Right(t)
    }
  }

  require(poolSize > 0, "At least one thread is needed.")

  /** The queue of scheduled tasks. */
  private val queue = new LinkedBlockingQueue[Runnable]()

  /** The thread pool. */
  private val pool: ExecutorService =
    new ThreadPoolExecutor(poolSize, poolSize, 0L, TimeUnit.MILLISECONDS, new LinkedBlockingQueue[Runnable])

  /** The tasks that have been scheduled and may or may not have completed yet. */
  private val scheduledTasks: mutable.Map[String, FutureTask[Either[Any, Throwable]]] = mutable.Map()

  /** Indicates the number of available worker threads. */
  def availableWorkers(): Int = poolSize - queue.size() - scheduledTasks.count(t => !t._2.isDone && !t._2.isCancelled)

  /**
   * Schedules a task; returns the task ID to query for status and result.
   * @param task
   *   The task to run
   * @return
   *   The task handle that [[ToolExecutor]] uses to identify this task.
   */
  def schedule[T](task: Unit => T): TaskHandle[T] = {
    val id = java.util.UUID.randomUUID().toString
    assert(!scheduledTasks.contains(id), "All running task IDs should be unique.")
    val future = makeFuture(task)
    pool.submit(future)
    scheduledTasks += ((id, future))
    TaskHandle(id)
  }

  /** Indicates whether or not the task is done. */
  def isDone[T](h: TaskHandle[T]): Boolean = scheduledTasks.get(h.id) match {
    case Some(future) => future.isDone
    case None => throw new Exception("The task " + h.id + " does not exist in the list.")
  }

  /** Returns the result of the task, or None if the task is not done running. */
  def getResult[T](h: TaskHandle[T]): Option[Either[T, Throwable]] =
    if (isDone(h)) Some(h.convert(scheduledTasks(h.id).get())) else None

  /**
   * Removes a task from the executor.
   * @param h
   *   The task handle of the task to remove.
   * @param force
   *   If true, then the task can be removed even if it is currently running. In that case, the task execution is halted
   *   first. Defaults to false.
   */
  def remove[T](h: TaskHandle[T], force: Boolean = false): Unit = {
    require(scheduledTasks.contains(h.id), "Cannot remove a task whose ID is not known")
    if (isDone(h)) { scheduledTasks.remove(h.id) }
    else if (force) {
      scheduledTasks.get(h.id).last.cancel(true)
      scheduledTasks.remove(h.id)
    } else {
      // @note if you want to remove a tactic even if it's still running, then call remove(id, true).
      throw new Exception(
        "Attempted to remove a tactic from scheduledTactics, but that tactic is not yet finished executing."
      )
    }
  } ensures (!scheduledTasks.contains(h.id))

  /**
   * Waits for task completion (polling).
   * @param h
   *   The task handle of the task to wait on
   * @param millis
   *   The duration in milliseconds to sleep between polling attempts
   */
  def wait[T](h: TaskHandle[T], millis: Int = 10): Option[Either[T, Throwable]] = {
    try {
      while (!isDone(h)) {
        Thread.sleep(millis)
        // indicates that tactic future in Hydra was cancelled
        if (Thread.currentThread().isInterrupted) return None
      }
      getResult(h)
    } catch {
      // If the task execution is cancelled in some other way
      case _: Throwable => None
    }
  }

  /** Terminates all running tasks in the pool. */
  def shutdown(): Unit = {
    pool.shutdownNow()
    if (!pool.awaitTermination(5, TimeUnit.SECONDS)) {
      // timeout before all tasks terminated
      logger.info("Tasks did not terminate while shutting down")
    }
  }

  /** Creates the future that ultimately executes the task. */
  private def makeFuture(task: Unit => Any): FutureTask[Either[Any, Throwable]] = new FutureTask(() =>
    try { Left(task(())) }
    catch { case e: Throwable => Right(e) }
  )
}
