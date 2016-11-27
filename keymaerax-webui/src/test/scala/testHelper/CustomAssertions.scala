/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package testHelper

import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
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
  def theDeductionOf[E <: Throwable](f: => ProvableSig): Either[ProvableSig, E] = try { Left(f) } catch { case e: E => Right(e) }

  /** Checks that a provable, if present, has a sole subgoal equal to its conclusion, so is equivalent to a single Provable.startProof. */
  val throwOrNoop: Matcher[Either[ProvableSig,Throwable]] = throwOrNoop[Throwable]((p: ProvableSig) => p.subgoals.size == 1 && p.subgoals.head == p.conclusion)
  /** Checks that a provable, if present, matches the specified noop condition. */
  def throwOrNoop[E <: AnyRef](noopCond: (ProvableSig => Boolean))(implicit manifest: Manifest[E]): Matcher[Either[ProvableSig,E]] = Matcher {
    (pr: Either[ProvableSig,E]) => MatchResult(
      pr match {
        case Left(p) => noopCond(p)
        case Right(e) =>
          val clazz = manifest.runtimeClass.asInstanceOf[Class[E]]
          clazz.isAssignableFrom(e.getClass)
      },
      if (pr.isLeft) pr + " is unexpectedly proved but shouldn't be"
      else /* pr.isRight */ pr + " resulted in unexpected exception, not in " + manifest.runtimeClass,
      pr + " is not proved, as expected"
    )
  }
}
