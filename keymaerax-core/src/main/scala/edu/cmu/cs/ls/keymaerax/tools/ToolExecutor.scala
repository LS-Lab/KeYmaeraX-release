package edu.cmu.cs.ls.keymaerax.tools

import java.util.concurrent._

import scala.collection.mutable

class ToolExecutor[T](poolSize: Int) {
  require(poolSize > 0, "At least one thread is needed.")
  private val pool: ExecutorService = Executors.newFixedThreadPool(poolSize)

  private val scheduledTasks: mutable.Map[String, FutureTask[Either[T, Throwable]]] = mutable.Map()

  /**
   * Schedules a task; returns the task ID to query for status and result.
   * @param task The task to run
   * @return The ID that [[ToolExecutor]] uses to identify this task.
   */
  def schedule(task: Unit => T): String = {
    val id = java.util.UUID.randomUUID().toString
    assert(!scheduledTasks.contains(id), "All running task IDs should be unique.")
    val future = makeFuture(task)
    pool.submit(future)
    scheduledTasks += ((id, future))
    id
  }

  /** Indicates whether or not the task is done. */
  def isDone(id: String): Boolean = scheduledTasks.get(id) match {
    case Some(future) => future.isDone
    case None         => throw new Exception("This tactic does not exist in the list.")
  }

  /** Returns the result of the task, or None if the task is not done running. */
  def getResult(id: String) : Option[Either[T, Throwable]] =
    if(isDone(id)) Some(scheduledTasks(id).get()) else None

  /**
   * Removes a task from the executor.
   * @param id The schedule id of the task to remove.
   * @param force If true, then the task can be removed even if it is currently running.
   *              In that case, the task execution is halted first. Defaults to false.
   */
  def remove(id: String, force: Boolean = false): Unit = {
    require(scheduledTasks.contains(id), "Cannot remove a task whose ID is not known")
    if (isDone(id)) {
      scheduledTasks.remove(id)
    } else if (force) {
      scheduledTasks.get(id).last.cancel(true)
      scheduledTasks.remove(id)
    } else {
      //@note if you want to remove a tactic even if it's still running, then call remove(id, true).
      throw new Exception("Attempted to remove a tactic from scheduledTactics, but that tactic is not yet finished executing.")
    }
  } ensuring(!scheduledTasks.contains(id))

  /**
   * Waits for task completion (polling).
   * @param id The scheduled id of the task to wait on
   * @param millis The duration in milliseconds to sleep between polling attempts
   */
  def wait(id: String, millis: Int = 10): Option[Either[T, Throwable]] = {
    try {
      while(!isDone(id)) {
        Thread.sleep(millis)
        // indicates that tactic future in Hydra was cancelled
        if (Thread.currentThread().isInterrupted) return None
      }
      getResult(id)
    } catch {
      // If the task execution is cancelled in some other way
      case _: Throwable => None
    }
  }

  def shutdown(): Unit = {
    pool.shutdownNow()
    if (!pool.awaitTermination(5, TimeUnit.SECONDS)) {
      // timeout before all tasks terminated
      println("Tasks did not terminate while shutting down")
    }
  }

  /** Creates the future that ultimately executes the task. */
  private def makeFuture(task: Unit => T): FutureTask[Either[T, Throwable]] =
    new FutureTask(new Callable[Either[T, Throwable]]() {
      override def call(): Either[T, Throwable] = {
        try {
          Left(task())
        } catch {
          case e: Throwable => Right(e)
        }
      }
    })
}
