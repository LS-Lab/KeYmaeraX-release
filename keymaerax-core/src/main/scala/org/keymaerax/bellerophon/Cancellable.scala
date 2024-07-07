/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.bellerophon

import java.util.concurrent.FutureTask

import scala.concurrent.{Future, Promise}
import scala.util.Try

/** Cancellable future, @see https://stackoverflow.com/questions/16009837/how-to-cancel-future-in-scala */
class Cancellable[T](executionContext: scala.concurrent.ExecutionContext, todo: => T) {
  private val promise = Promise[T]()

  def future: Future[T] = promise.future

  private val jf: FutureTask[T] = new FutureTask[T](() => todo) {
    override def done(): Unit = promise.complete(Try(get()))
  }

  def cancel(): Unit = jf.cancel(true)

  executionContext.execute(jf)
}
object Cancellable {
  def apply[T](todo: => T)(implicit executionContext: scala.concurrent.ExecutionContext): Cancellable[T] =
    new Cancellable[T](executionContext, todo)
}
