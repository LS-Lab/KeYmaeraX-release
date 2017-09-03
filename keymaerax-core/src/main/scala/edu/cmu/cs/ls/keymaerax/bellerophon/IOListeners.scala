/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.helpers.QELogger
import edu.cmu.cs.ls.keymaerax.core.{Formula, Sequent}
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig

import scala.collection.immutable.IndexedSeq

/**
  * Some tactic listeners.
  * Created by smitsch on 9/3/17.
  */
object IOListeners {

  /** Interpreter listener that logs QE calls to `logPath` if condition `logCondition` is satisfied. */
  class QELogListener(logPath: String, logCondition: (ProvableSig, BelleExpr) => Boolean) extends IOListener() {
    private val logged: scala.collection.mutable.Set[Sequent] = scala.collection.mutable.Set()
    private def qeFml(s: Sequent): Formula =
      if (s.ante.isEmpty && s.succ.size == 1) s.succ.head.universalClosure
      else s.toFormula.universalClosure
    override def begin(input: BelleValue, expr: BelleExpr): Unit = input match {
      case BelleProvable(p, _) if logCondition(p, expr) =>
        val logSeq = Sequent(IndexedSeq(), IndexedSeq(qeFml(p.subgoals.head)))
        if (!logged.contains(logSeq)) {
          QELogger.logSequent(p.conclusion, logSeq, s"QE ${logged.size}", logPath)
          logged.add(logSeq)
        }
      case _ => // do nothing
    }
    override def end(input: BelleValue, expr: BelleExpr, output: Either[BelleValue, BelleThrowable]): Unit = {}
    override def kill(): Unit = {}
  }

  /** Interpreter listener that records the duration of tactics that satisfy condition `logCondition`. */
  class StopwatchListener(logCondition: (ProvableSig, BelleExpr) => Boolean) extends IOListener() {
    private var recordedDuration: Long = 0
    private var start: Option[((ProvableSig, BelleExpr), Long)] = None

    /** Returns the recorded duration. */
    def duration: Long = recordedDuration

    /** Resets the duration measurement. */
    def reset(): Unit = recordedDuration = 0

    override def begin(input: BelleValue, expr: BelleExpr): Unit = input match {
      case BelleProvable(p, _) if logCondition(p, expr) && start.isEmpty =>
        start = Some((p, expr), System.currentTimeMillis())
      case _ => // do nothing
    }
    override def end(input: BelleValue, expr: BelleExpr, output: Either[BelleValue, BelleThrowable]): Unit = (input, start) match {
      // do not record time in nested calls
      case (BelleProvable(p, _), Some((begin, startTime))) if logCondition(p, expr) && begin == (p, expr) =>
        recordedDuration += System.currentTimeMillis() - startTime
        start = None
      case _ => // do nothing
    }

    override def kill(): Unit = {}
  }

}
