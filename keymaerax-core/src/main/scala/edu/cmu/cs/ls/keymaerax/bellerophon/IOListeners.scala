/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.bellerophon

import java.io.PrintStream

import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BellePrettyPrinter
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.helpers.QELogger
import edu.cmu.cs.ls.keymaerax.core.{False, Formula, Sequent, StaticSemantics}
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig

import scala.collection.immutable.IndexedSeq
import scala.collection.mutable

/**
  * Some tactic listeners.
  * Created by smitsch on 9/3/17.
  */
object IOListeners {

  /** Interpreter listener that logs QE calls to `logger` if condition `logCondition` is satisfied. */
  class QELogListener(val logger: (Sequent, Sequent, String) => Unit,
                      val logCondition: (ProvableSig, BelleExpr) => Boolean) extends IOListener() {
    private val logged: scala.collection.mutable.Set[Sequent] = scala.collection.mutable.Set()
    private def qeFml(s: Sequent): Formula =
      if (s.ante.isEmpty && s.succ.size == 1) s.succ.head.universalClosure
      else s.toFormula.universalClosure
    override def begin(input: BelleValue, expr: BelleExpr): Unit = input match {
      case BelleProvable(p, _, _) if logCondition(p, expr) && !StaticSemantics.freeVars(p.subgoals.head).isInfinite =>
        val logSeq = Sequent(IndexedSeq(), IndexedSeq(qeFml(p.subgoals.head)))
        if (!logged.contains(logSeq)) {
          logger(p.conclusion, logSeq, s"QE ${logged.size}")
          logged.add(logSeq)
        }
      case _ => // do nothing
    }
    override def end(input: BelleValue, expr: BelleExpr, output: Either[BelleValue, Throwable]): Unit = {}
    override def kill(): Unit = {}
  }

  /** Interpreter listener that logs QE calls to `logPath` if condition `logCondition` is satisfied. */
  class QEFileLogListener(logPath: String, logCondition: (ProvableSig, BelleExpr) => Boolean)
    extends QELogListener((c: Sequent, g: Sequent, s: String) => QELogger.logSequent(c, g, s, logPath), logCondition)

  /** Interpreter listener that records the duration of tactics that satisfy condition `logCondition`. */
  class StopwatchListener(logCondition: (ProvableSig, BelleExpr) => Boolean) extends IOListener() {
    private var recordedDuration: Long = 0
    private var start: Option[((ProvableSig, BelleExpr), Long)] = None

    /** Returns the recorded duration. */
    def duration: Long = recordedDuration

    /** Resets the duration measurement. */
    def reset(): Unit = recordedDuration = 0

    override def begin(input: BelleValue, expr: BelleExpr): Unit = input match {
      case BelleProvable(p, _, _) if logCondition(p, expr) && start.isEmpty =>
        start = Some((p, expr), System.currentTimeMillis())
      case _ => // do nothing
    }
    override def end(input: BelleValue, expr: BelleExpr, output: Either[BelleValue, Throwable]): Unit = (input, start) match {
      // do not record time in nested calls
      case (BelleProvable(p, _, _), Some((begin, startTime))) if logCondition(p, expr) && begin == (p, expr) =>
        recordedDuration += System.currentTimeMillis() - startTime
        start = None
      case _ => // do nothing
    }

    override def kill(): Unit = {}
  }

  class InterpreterConsistencyListener extends IOListener() {
    private var stack: List[BelleExpr] = Nil
    override def begin(input: BelleValue, expr: BelleExpr): Unit = {
      //println("Begin " + expr.prettyString + "@" + expr.hashCode() + " on " + Thread.currentThread().hashCode())
      stack = expr +: stack
    }

    override def end(input: BelleValue, expr: BelleExpr, output: Either[BelleValue, Throwable]): Unit = {
      val expected = stack.head
      //println("End " + expr.prettyString + "@" + expr.hashCode() + " on " + Thread.currentThread().hashCode())
      assert(expr.eq(expected), "Popping unexpected " + expr.prettyString + "@" + expr.hashCode() + "; tail is " + expected.prettyString + "@" + expected.hashCode())
      stack = stack.tail
    }

    override def kill(): Unit = {}
  }

  /** Prints tactic progress to the console. */
  class PrintProgressListener(t: BelleExpr, stepInto: List[String] = Nil, printer: PrintStream = Console.out) extends IOListener() {
    private var executionStack = (t->0) :: Nil // branch index =0 except for BranchTactic
    private var start = System.currentTimeMillis()

    private def stepInto(e: BelleExpr): Boolean = stepInto.nonEmpty && (stepInto.head == "_ALL" || (e match {
      case n: NamedBelleExpr => n.isInternal || stepInto.contains(n.name)
      case _ => false
    }))

    override def begin(input: BelleValue, expr: BelleExpr): Unit = {
      //@todo recursive calls to same tactic may pop from stack prematurely (master? ODE?)
      if (stepInto(executionStack.head._1) && !expr.eq(executionStack.head._1)) executionStack = (expr->0) +: executionStack
      if (executionStack.nonEmpty && expr.eq(executionStack.head._1)) expr match {
        case SeqTactic(l :: _) => executionStack = (l->0) +: executionStack
        case BranchTactic(b) if b.nonEmpty =>
          executionStack = (b.head->0) +: executionStack
        case SaturateTactic(e) => executionStack = (e->0) +: executionStack
        case RepeatTactic(e, i) => executionStack = List.fill(i)(e->0) ++ executionStack
        case EitherTactic(l, _) => executionStack = (l->0) +: executionStack
        case ApplyDefTactic(DefTactic(name, e)) => printer.println(name); executionStack = (e->0) +: executionStack
        case e: AppliedPositionTactic => printer.print(BellePrettyPrinter(e) + "... ")
        case e: NamedBelleExpr if e.isInternal => // always step into internal tactics
        // avoid duplicate printing of DependentPositionTactic and AppliedDependentPositionTactic
        case _: DependentPositionTactic =>
        case e: NamedBelleExpr /*if e.getClass == executionStack.head._1.getClass*/ =>
          start = System.currentTimeMillis()
          printer.print(BellePrettyPrinter(e) + "... ")
          if (e.name == "QE" || e.name == "smartQE") printer.println("\n" + input.prettyString)
        case _ =>
      }
    }

    override def end(input: BelleValue, expr: BelleExpr, output: Either[BelleValue, Throwable]): Unit = {
      if (executionStack.nonEmpty && expr.eq(executionStack.head._1)) {
        executionStack = executionStack.tail

        def parent(stack: List[(BelleExpr, Int)]): List[NamedBelleExpr] = stack.filter({
          case (n: NamedBelleExpr, _) => !n.isInternal && n.name != "done"
          case _ => false
        }).map(_._1.asInstanceOf[NamedBelleExpr])

        val parentContinues: List[NamedBelleExpr] = executionStack.headOption match {
          case Some((SeqTactic(l :: r :: Nil), _)) if expr.eq(l) =>
            executionStack = (r->0) +: executionStack
            parent(executionStack.tail)
          case Some((SeqTactic(l :: r), _)) if expr.eq(l) =>
            executionStack = (SeqTactic(r)->0) +: executionStack
            parent(executionStack.tail)
          case Some((bt@BranchTactic(b), i)) if i+1 < b.size =>
            executionStack = (b(i+1)->0) +: (bt->(i+1)) +: executionStack.tail
            parent(executionStack.tail.tail)
          case Some((SaturateTactic(e), _)) => output match {
            // SaturateTactic always succeeds, but will noop if inner failed
            case Left(outValue) if outValue != input =>
              executionStack = (e->0) +: executionStack
              parent(executionStack.tail)
            case _ => Nil
          }
          case Some((EitherTactic(l, r), _)) if expr.eq(l) && output.isRight =>
            executionStack = (r->0) +: executionStack
            parent(executionStack.tail)
          case _ => Nil
        }

        val status = output match {
          case Left(BelleProvable(p, _, _)) =>
            if (p.isProved) "proved"
            else if (p.subgoals.head.succ.headOption.contains(False)) "disproved"
            else input match {
              case BelleProvable(q, _, _) =>
                if (p.subgoals == q.subgoals) "no progress"
                else {
                  val change = p.subgoals.diff(q.subgoals).size - q.subgoals.diff(p.subgoals).size
                  if (change > 0) "added " + change + " goal(s)"
                  else if (change == 0) "transformed goal(s)"
                  else "closed " + change + " goal(s)"
                }
              case _ => "Unexpected output provable from input error"
            }
          case _ => "failed"
        }

        expr match {
          case ApplyDefTactic(DefTactic(name, _)) => printer.println(name + " done (" + status + ")")
          case _: AppliedPositionTactic => printer.println("done (" + status + ")")
          case e: NamedBelleExpr if e.name == "QE" || e.name == "smartQE" =>
            printer.println(e.name + " done (" + status + ", " + (System.currentTimeMillis()-start) + "ms)")
          case n: NamedBelleExpr if !n.isInternal => printer.println(n.name + " done (" + status + ", " + (System.currentTimeMillis()-start) + "ms)")
          case _ =>
        }

        if (parentContinues.nonEmpty) println("continuing " + parentContinues.reverse.map(_.name).mkString(" > ") + "...")
      } else if (executionStack.nonEmpty && stepInto(executionStack.head._1)) {
        val popTo = executionStack.indexWhere(_._1.eq(expr))
        //@todo fix root cause of wrong stack
        if (popTo >= 0) {
          println("WARNING skipped end of: " + executionStack.take(popTo).map(_._1.prettyString).mkString(","))
          executionStack = executionStack.drop(popTo).tail
        } else {
          println("WARNING end of unrecorded beginning " + expr.prettyString)
        }
      }
    }

    override def kill(): Unit = {}
  }

  /** A progresss listener that collects the top-level tactic progress in a buffer. */
  case class CollectProgressListener(progress: mutable.Buffer[(BelleExpr, Either[BelleValue, Throwable])] = mutable.Buffer.empty) extends IOListener() {
    private var current: Option[(BelleExpr, Long)] = None
    override def begin(input: BelleValue, expr: BelleExpr): Unit = {
      if (current.isEmpty) {
        current = Some(expr, System.currentTimeMillis())
      }
    }
    override def end(input: BelleValue, expr: BelleExpr, output: Either[BelleValue, Throwable]): Unit = {
      if (current.map(_._1).contains(expr)) {
        progress.append((expr, output))
        current = None
      }
    }
    override def kill(): Unit = {}

    /** The currently executing tactic, including it's start time. */
    def getCurrentTactic: Option[(BelleExpr, Long)] = current
  }

}
