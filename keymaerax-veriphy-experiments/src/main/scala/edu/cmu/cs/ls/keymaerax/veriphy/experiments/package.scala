package edu.cmu.cs.ls.keymaerax.veriphy

import scala.annotation.elidable
import scala.collection.immutable

package object experiments {
  /*type USubstRen = USubstRenOne
  /** USubstRen factory method for standalone Renaming Uniform Substitution operation implementation, forwards to constructor. */
  def USubstRen(subsDefsInput: immutable.Seq[(Expression,Expression)]): USubstRen = USubstRenOne(subsDefsInput)

  /**
   * Copyright (c) Carnegie Mellon University.
   * See LICENSE.txt for the conditions of this license.
   */
  /**
   * Differential Dynamic Logic prover Microkernel.
   * @author Andre Platzer
   * @see Andre Platzer. [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 59(2), pp. 219-266, 2017.
   * @see Andre Platzer. [[https://doi.org/10.1145/2817824 Differential game logic]]. ACM Trans. Comput. Log. 17(1), 2015. [[http://arxiv.org/pdf/1408.1980 arXiv 1408.1980]]
   * @see Andre Platzer. [[https://doi.org/10.1109/LICS.2012.64 The complete proof theory of hybrid systems]]. ACM/IEEE Symposium on Logic in Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 541-550. IEEE 2012
   * @note Code Review: 2020-02-17
   */


    /** KeYmaera X core kernel version number */
    //val VERSION: String = Version.VERSION

    /** The uniform substitution type to use */
    type USubst = USubstOne
    /** USubst factory method, forwards to constructor. */
    def USubst(subsDefsInput: immutable.Seq[SubstitutionPair]): USubst = USubstOne(subsDefsInput)
    /** true if USubstChurch is used, false if USubstOne is used */
    private[keymaerax] val usubstChurch = (USubst(immutable.Seq()).getClass==USubstChurch.getClass)

    /** Insist on `requirement` being true, throwing a [[CoreException]] if false.
     *  This method is a `require` coming from the prover core that cannot be disabled.
     *  Blame is on the caller of the method
     *  for violating the contract.
     *
     *  @param requirement   the expression to test for being true
     *  @param message       a String explaining what is expected.
     *  @see [[scala.Predef.require()]]
     */
    @inline final def insist(requirement: Boolean, message: => Any): Unit = {
      if (!requirement)
        throw new CoreException("Core requirement failed: " + message)
    }

    /** Check that the given expression `e` does not throw an exception.
     * @return `true` if `e` completed without raising any exceptions or errors.
     *        `false` if `e` raised an exception or error.
     * @example {{{
     *  insist(noExeption(complicatedComputation), "The complicated computation should complete without throwing exceptions")
     * }}}
     */
    @inline final def noException[T](e: => T): Boolean =
      try { e; true } catch { case _: Throwable => false }

    /**
     * Java-style assertions, disabled by default, enabled with `java -ea`, disable with `java -da`.
     * Scala-style elidable at compile-time with `-Xdisable-assertions`
     *
     * Lazy evaluation of `condition` on `argument`, lazy evaluation of message.
     * @author Fabian Immler
     * */
    @elidable(elidable.ASSERTION) @inline
    def assertion[A](condition: A => Boolean, argument: A, message: => Any): A =
      Assertion.assertion((x: A) => condition(x) : java.lang.Boolean, argument, () => message.asInstanceOf[AnyRef])

    /** see [[assertion]] */
    @elidable(elidable.ASSERTION) @inline
    def assertion[A](condition: A => Boolean, argument: A): A =
      Assertion.assertion((x: A) => condition(x) : java.lang.Boolean, argument)

    /** see [[assertion]] */
    @elidable(elidable.ASSERTION) @inline
    def assertion(condition: => Boolean): Unit =
      Assertion.assertion(() => condition)

    /** see [[assertion]] */
    @elidable(elidable.ASSERTION) @inline
    def assertion(condition: =>Boolean, message: => Any): Unit =
      Assertion.assertion(() => condition : java.lang.Boolean, () => message.asInstanceOf[AnyRef])

    /** Contracts (like [[scala.Predef.Ensuring]]) implemented with Java-style assertions (see [[assertion]])
     * @author Fabian Immler
     */
    implicit final class Ensures[A](private val self: A) extends AnyVal {

      /** Java-style lazy-evaluation postcondition assertion that can be enabled with `java -ea`, disabled with `java -da`. */
      def ensures(cond: =>Boolean): A = { assertion(cond); self }

      /** Java-style lazy-evaluation postcondition assertion that can be enabled with `java -ea`, disabled with `java -da`. */
      def ensures(cond: =>Boolean, msg: => Any): A = { assertion(cond, msg);  self }

      /** Java-style lazy-evaluation postcondition assertion that can be enabled with `java -ea`, disabled with `java -da`. */
      def ensures(cond: A => Boolean): A = { assertion(cond, self); self }

      /** Java-style lazy-evaluation postcondition assertion that can be enabled with `java -ea`, disabled with `java -da`. */
      def ensures(cond: A => Boolean, msg: => Any): A = { assertion(cond, self, msg); self }

    }

*/
}
