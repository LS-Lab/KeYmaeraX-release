/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package testHelper

import edu.cmu.cs.ls.keymaerax.core.Provable
import org.scalatest.Assertions.{fail, withClue}
import org.scalatest.matchers.{MatchResult, Matcher}

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

  /** Turns exceptions into 'None', most useful with Matcher throwOrNoop
    * {{{theDeductionOf { proveBy(formula, tactic) } should throwOrNoop }}}*/
  def theDeductionOf[T <: Provable](f: => T): Option[T] = try { Some(f) } catch { case e: Throwable => None }

  /** Checks that a provable, if present, has a sole subgoal equal to its conclusion. */
  val throwOrNoop: Matcher[Option[Provable]] = throwOrNoop((p: Provable) => p.subgoals.size == 1 && p.subgoals.head == p.conclusion)
  def throwOrNoop(noopCond: (Provable => Boolean)): Matcher[Option[Provable]] = Matcher {
    (pr: Option[Provable]) => MatchResult(
      pr match {
        case Some(p) => noopCond(p)
        case None => true
      },
      pr + " is proved but shouldn't be",
      pr + " is rightfully not proved"
    )
  }
}
