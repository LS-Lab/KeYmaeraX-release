/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

/** @note Code Review: 2016-08-02 */
package org.keymaerax.tools

import org.keymaerax.Configuration
import org.keymaerax.bellerophon.IOListeners.{QEFileLogListener, QELogListener, StopwatchListener}
import org.keymaerax.bellerophon._
import org.keymaerax.btactics._
import org.keymaerax.core.{Formula, PrettyPrinter, Program, Sequent}
import org.keymaerax.infrastruct.Augmentors.SequentAugmentor
import org.keymaerax.parser.Parser
import org.slf4j.LoggerFactory

import scala.annotation.tailrec

/**
 * The KeYmaera X tool, initializes the pretty printer.
 *
 * Created by smitsch on 4/27/15.
 * @author
 *   Stefan Mitsch
 */
object KeYmaeraXTool extends Tool {
  // TODO Convert to Scala 3 enum
  sealed trait InterpreterChoice
  object InterpreterChoice {
    object LazySequential extends InterpreterChoice
    object ExhaustiveSequential extends InterpreterChoice
  }

  /** Default timeout if not set in config */
  val DEFAULT_LEMMA_DERIVE_TIMEOUT = 120

  /** @inheritdoc */
  override val name: String = "KeYmaera"

  /** Indicates whether the tool is initialized. */
  private var initialized = false

  /**
   * Initialize KeYmaera X global state.
   *
   * @param initDerivationInfoRegistry
   *   whether to initialize the axiom and tactic library
   */
  def init(
      interpreter: InterpreterChoice = InterpreterChoice.LazySequential,
      initDerivationInfoRegistry: Boolean = true,
  ): Unit = {
    // @note allow re-initialization since we do not know how (Mathematica, Z3, not at all) the tactic registry was initialized
    if (initialized) shutdown()
    if (Configuration.getBoolean(Configuration.Keys.LAX).getOrElse(false))
      // @note Careful, this disables contract checking in printing!
      PrettyPrinter.setPrinter(org.keymaerax.parser.KeYmaeraXNoContractPrettyPrinter.pp)
    else PrettyPrinter.setPrinter(org.keymaerax.parser.KeYmaeraXPrettyPrinter.pp)

    val LOG_EARLIEST_QE = Configuration.getBoolean(Configuration.Keys.LOG_ALL_FO).getOrElse(false)
    val LOG_QE = Configuration.getBoolean(Configuration.Keys.LOG_QE).getOrElse(false)
    val LOG_QE_DURATION = Configuration.getBoolean(Configuration.Keys.LOG_QE_DURATION).getOrElse(false)
    val LOG_QE_STDOUT = Configuration.getBoolean(Configuration.Keys.LOG_QE_STDOUT).getOrElse(false)

    val qeLogPath: String = Configuration.path(Configuration.Keys.QE_LOG_PATH)
    lazy val allPotentialQEListener = new QEFileLogListener(
      qeLogPath + "wantqe.txt",
      (p, _) => { p.subgoals.size == 1 && p.subgoals.head.isPredicateFreeFOL },
    )
    lazy val qeListener = new QEFileLogListener(
      qeLogPath + "haveqe.txt",
      (_, t) =>
        t match {
          case DependentTactic("_rcf") => true
          case _ => false
        },
    )
    lazy val qeStdOutListener: QELogListener = new QELogListener(
      (_: Sequent, g: Sequent, s: String) => print(s"$s: ${g.prettyString}..."),
      (_, t) =>
        t match {
          case DependentTactic("_rcf") => true
          case _ => false
        },
    ) {
      private val stopwatchListener = new StopwatchListener(logCondition)

      override def begin(input: BelleValue, expr: BelleExpr): Unit = {
        stopwatchListener.reset()
        stopwatchListener.begin(input, expr)
        super.begin(input, expr)
      }

      override def end(input: BelleValue, expr: BelleExpr, output: Either[BelleValue, Throwable]): Unit = {
        stopwatchListener.end(input, expr, output)
        input match {
          case BelleProvable(p, _) if logCondition(p, expr) => println(s"${stopwatchListener.duration}ms")
          case _ => // nothing to do
        }
      }
    }
    lazy val qeDurationListener = new StopwatchListener((_, t) =>
      t match {
        case DependentTactic("_rcf") => true
        case _ => false
      }
    )

    val listeners = (if (LOG_QE) qeListener :: Nil else Nil) ++
      (if (LOG_EARLIEST_QE) allPotentialQEListener :: Nil else Nil) ++
      (if (LOG_QE_DURATION) qeDurationListener :: Nil else Nil) ++ (if (LOG_QE_STDOUT) qeStdOutListener :: Nil else Nil)

    BelleInterpreter.setInterpreter(interpreter match {
      case InterpreterChoice.LazySequential => LazySequentialInterpreter(listeners)
      case InterpreterChoice.ExhaustiveSequential => ExhaustiveSequentialInterpreter(listeners)
    })

    Configuration.withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) {
      // set timeout and return old for later restore
      val oldTimeout = ToolProvider.qeTool() match {
        case Some(tool: ToolOperationManagement) => {
          val ret = Some(tool.getOperationTimeout)

          val deriveTimeout = Configuration
            .getInt(Configuration.Keys.AXIOM_DERIVE_TIMEOUT)
            .getOrElse(DEFAULT_LEMMA_DERIVE_TIMEOUT)
          tool.setOperationTimeout(deriveTimeout)

          ret
        }
        case _ => None
      }

      try { DerivationInfoRegistry.init(initDerivationInfoRegistry) }
      catch {
        case t: Throwable =>
          /* During initialization, lemma derivation happens via reflective method access
           * (See Ax.scala #prepopulateDerivedLemmaDatabase).
           * Exceptions are thereby hidden behind an InvokationTargetException.
           * Since Java 1.4, the target of this exception is also returned by #getCause(),
           * so we can just walk up the cause chain and find the actual Exception. */
          val details = rootCause(t) match {
            case ex: MathematicaComputationTimedOutException =>
              s"""Timed out while trying to derive lemmas. Continuing with restricted functionality!
                 |HINT: Try to increase the timeout using the following key in your config file:
                 |
                 |   AXIOM_DERIVE_TIMEOUT = 120
                 |                      ^^^^^
                 |
                 |DETAILS: ${ex.getMessage}""".stripMargin
            case ex => s"""Timed out while trying to derive lemmas. Continuing with restricted functionality!
                          |DETAILS: ${ex.getMessage}""".stripMargin
          }

          // TODO: until logging is sorted out
          println(t.getMessage)
          println()
          println(details)

          LoggerFactory.getLogger(getClass).warn(details, t)

          if (Configuration.getBoolean(Configuration.Keys.DEBUG).contains(true)) { t.printStackTrace() }
          else { println("Run with -debug for more details.") }
      } finally {
        // Restore old timeout
        (oldTimeout, ToolProvider.qeTool()) match {
          case (Some(to), Some(t: ToolOperationManagement)) => t.setOperationTimeout(to)
          case _ => // nothing to do
        }
      }
    }

    val generator = new ConfigurableGenerator()
    Parser
      .parser
      .setAnnotationListener((p: Program, inv: Formula) =>
        generator.products +=
          (p ->
            (generator.products.getOrElse(p, Nil) :+ Invariant(inv, Some(InvariantHint.Annotation(tryHard = true)))))
      )
    TactixInit.invSupplier = generator

    initialized = true
  }

  @tailrec
  private def rootCause(it: Throwable): Throwable = {
    val cause = it.getCause
    if (cause == null || cause == it) it else rootCause(cause)
  }

  /** @inheritdoc */
  override def restart(): Unit = {}

  /** @inheritdoc */
  override def shutdown(): Unit = {
    PrettyPrinter.setPrinter(e => e.getClass.getName)
    TactixInit.invSupplier = FixedGenerator(Nil)
    initialized = false
  }

  /** @inheritdoc */
  override def isInitialized: Boolean = initialized

  /** @inheritdoc */
  override def cancel(): Boolean = true
}
