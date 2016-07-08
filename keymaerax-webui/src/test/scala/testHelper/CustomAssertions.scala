/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package testHelper

import org.scalatest.Assertions.{fail,withClue}

/** Custom test assertions.
  * Created by smitsch on 5/21/16.
  */
object CustomAssertions {
  /** withClue for code that throws RuntimeExceptions (assert etc.)
    * @see [[org.scalatest.Assertions.withClue]]
    * */
  def withSafeClue[T](clue: Any)(fun: => T): T = {
    try { fun } catch { case e: Any => withClue(clue) { fail(e) } }
  }
}
