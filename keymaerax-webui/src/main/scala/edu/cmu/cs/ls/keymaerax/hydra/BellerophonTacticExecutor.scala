package edu.cmu.cs.ls.keymaerax.hydra

import java.util.concurrent.{Callable, FutureTask, ExecutorService, Executors}

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleError, BelleValue, BelleExpr, Interpreter}
import scala.collection.mutable.Map

/**
  * Scheduler for Bellerophon tactics
  * @author Nathan Fulton
  */
class BellerophonTacticExecutor(interpreter : Interpreter, poolSize: Int) {
  require(poolSize > 0, "At least one thread is needed.")
  private val pool : ExecutorService = Executors.newFixedThreadPool(poolSize)

  /**
    * [[scheduledTactics]] could be at any state of execution, included finished.
    * Tactics are never removed from the [[scheduledTactics]] mapping unless explicitly via .remove()
    */
  private val scheduledTactics : scala.collection.mutable.Map[String, FutureTask[Either[BelleValue, BelleError]]] = Map()

  /**
    *
    * @param tactic The tactic to run
    * @param value The value to apply the tactic to
    * @return The ID that [[BellerophonTacticExecutor]] uses to identify this tactic.
    */
  def schedule(tactic: BelleExpr, value: BelleValue) : String = {
    val id = java.util.UUID.randomUUID().toString
    assert(!scheduledTactics.contains(id), "All running tactic IDs should be unique.")
    val future = makeFuture(tactic, value)
    pool.submit(future)
    scheduledTactics += ((id, future))
    id
  }

  def isDone(id: String) = scheduledTactics.get(id) match {
    case Some(future) => future.isDone
    case None         => throw new Exception("This tactic does not exist in the list.")
  }

  /**
    *
    * @param id The schedule id of the tactic to remove.
    * @param force If true, then the tactic can be removed even if it is currently running.
    *              In that case, the tactic execution is halted first. Defaults to false.
    */
  def remove(id: String, force: Boolean = false) = {
    require(scheduledTactics.contains(id), "Cannot remove a tactic whose ID is not in the key set of scheduledTactics.")
    if (isDone(id)) {
      scheduledTactics.remove(id)
    }
    else if (force) {
      scheduledTactics.get(id).last.cancel(true)
      scheduledTactics.remove(id)
    }
    else {
      //@note if you want to remove a tactic even if it's still running, then call remove(id, true).
      throw new Exception("Attempted to remove a tactic from scheduledTactics, but that tactic is not yet finished executing.")
    }
  } ensuring(!scheduledTactics.contains(id))

  private def makeFuture(tactic: BelleExpr, value: BelleValue) = {
    new FutureTask[Either[BelleValue, BelleError]](new Callable[Either[BelleValue, BelleError]]() {
      override def call(): Either[BelleValue, BelleError] = {
        try {
          Left(interpreter(tactic, value))
        }
        catch {
          case e : BelleError     => Right(e)
          case thrown : Throwable => Right(new BelleError("Unknown throwable thrown during tactic execution", thrown))
        }
      }
    })
  }
}