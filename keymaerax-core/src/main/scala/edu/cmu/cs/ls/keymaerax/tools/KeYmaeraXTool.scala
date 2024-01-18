/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

/**
  * @note Code Review: 2016-08-02
  */
package edu.cmu.cs.ls.keymaerax.tools

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.bellerophon.IOListeners.{QEFileLogListener, QELogListener, StopwatchListener}
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.{BellePrettyPrinter, DLBelleParser}
import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.InvariantGenerator.{AnnotationProofHint, GenProduct}
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.core.{Formula, PrettyPrinter, Program, Sequent}
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors.SequentAugmentor
import edu.cmu.cs.ls.keymaerax.parser.{ArchiveParser, DLArchiveParser, KeYmaeraXArchiveParser, Parser}
import org.slf4j.LoggerFactory

import scala.annotation.tailrec

/**
 * The KeYmaera X tool, initializes the pretty printer.
 *
 * Created by smitsch on 4/27/15.
 * @author Stefan Mitsch
 */
object KeYmaeraXTool extends Tool {
  /** Configuration option: whether or not to initialize the axiom and tactic library (default: true) */
  val INIT_DERIVATION_INFO_REGISTRY: String = "INIT_DERIVATION_INFO_REGISTRY"
  /** Interpreter, one of "LazySequentialInterpreter" | "ExhaustiveSequentialInterpreter" */
  val INTERPRETER: String = "INTERPRETER"

  /** Default timeout if not set in config */
  val DEFAULT_LEMMA_DERIVE_TIMEOUT = 120

  /** @inheritdoc */
  override val name: String = "KeYmaera"

  /** Indicates whether the tool is initialized. */
  private var initialized = false

  /** @inheritdoc */
  override def init(config: Map[String,String]): Unit = {
    //@note allow re-initialization since we do not know how (Mathematica, Z3, not at all) the tactic registry was initialized
    if (initialized) shutdown()
    if (Configuration.getBoolean(Configuration.Keys.LAX).getOrElse(false))
      //@note Careful, this disables contract checking in printing!
      PrettyPrinter.setPrinter(edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXNoContractPrettyPrinter.pp)
    else
      PrettyPrinter.setPrinter(edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter.pp)

    ArchiveParser.setParser(Configuration.getString(Configuration.Keys.PARSER) match {
      case Some("KeYmaeraXParser") | None => KeYmaeraXArchiveParser
      case Some("DLParser") =>
        new DLArchiveParser(new DLBelleParser(BellePrettyPrinter,
          ReflectiveExpressionBuilder(_, _, Some(TactixInit.invGenerator), _)))
      case Some(p) => throw new ProverSetupException("Unknown parser " + p + "; please use one of 'KeYmaeraXParser' or 'DLParser'")
    })

    val LOG_EARLIEST_QE = Configuration.getBoolean(Configuration.Keys.LOG_ALL_FO).getOrElse(false)
    val LOG_QE = Configuration.getBoolean(Configuration.Keys.LOG_QE).getOrElse(false)
    val LOG_QE_DURATION = Configuration.getBoolean(Configuration.Keys.LOG_QE_DURATION).getOrElse(false)
    val LOG_QE_STDOUT = Configuration.getBoolean(Configuration.Keys.LOG_QE_STDOUT).getOrElse(false)

    val qeLogPath: String = Configuration.path(Configuration.Keys.QE_LOG_PATH)
    lazy val allPotentialQEListener = new QEFileLogListener(qeLogPath + "wantqe.txt", (p, _) => { p.subgoals.size == 1 && p.subgoals.head.isPredicateFreeFOL })
    lazy val qeListener = new QEFileLogListener(qeLogPath + "haveqe.txt", (_, t) => t match { case DependentTactic("_rcf") => true case _ => false })
    lazy val qeStdOutListener: QELogListener = new QELogListener((_: Sequent, g: Sequent, s: String) => print(s"$s: ${g.prettyString}..."), (_, t) => t match { case DependentTactic("_rcf") => true case _ => false }) {
      private val stopwatchListener = new StopwatchListener(logCondition)

      override def begin(input: BelleValue, expr: BelleExpr): Unit = {
        stopwatchListener.reset()
        stopwatchListener.begin(input, expr)
        super.begin(input, expr)
      }

      override def end(input: BelleValue, expr: BelleExpr, output: Either[BelleValue, Throwable]): Unit = {
        stopwatchListener.end(input, expr, output)
        input match {
          case BelleProvable(p, _) if logCondition(p, expr) =>
            println(s"${stopwatchListener.duration}ms")
          case _ => // nothing to do
        }
      }
    }
    lazy val qeDurationListener = new StopwatchListener((_, t) => t match { case DependentTactic("_rcf") => true case _ => false })

    val listeners =
      (if (LOG_QE) qeListener::Nil else Nil) ++
      (if (LOG_EARLIEST_QE) allPotentialQEListener::Nil else Nil) ++
      (if (LOG_QE_DURATION) qeDurationListener::Nil else Nil) ++
      (if (LOG_QE_STDOUT) qeStdOutListener::Nil else Nil)

    val interpreter = config.getOrElse(INTERPRETER, LazySequentialInterpreter.getClass.getSimpleName)
    BelleInterpreter.setInterpreter(
      if (interpreter == LazySequentialInterpreter.getClass.getSimpleName) LazySequentialInterpreter(listeners)
      else if (interpreter == ExhaustiveSequentialInterpreter.getClass.getSimpleName) ExhaustiveSequentialInterpreter(listeners)
      else throw new IllegalArgumentException("Unknown interpreter: " + interpreter + "; please use one of " +
        LazySequentialInterpreter.getClass.getSimpleName + " | " + ExhaustiveSequentialInterpreter.getClass.getSimpleName)
    )
    val shouldInitLibrary = config.getOrElse(INIT_DERIVATION_INFO_REGISTRY, "true").toBoolean
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

      try {
        DerivationInfoRegistry.init(shouldInitLibrary)
      } catch {
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
            case ex =>
              s"""Timed out while trying to derive lemmas. Continuing with restricted functionality!
                 |DETAILS: ${ex.getMessage}""".stripMargin
          }

          // TODO: until logging is sorted out
          println(t.getMessage)
          println()
          println(details)

          LoggerFactory.getLogger(getClass)
            .warn(details, t)

          if (Configuration.getBoolean(Configuration.Keys.DEBUG).contains(true)) {
            t.printStackTrace()
          } else {
            println("Run with -debug for more details.")
          }
      } finally {
        // Restore old timeout
        (oldTimeout, ToolProvider.qeTool()) match {
          case (Some(to), Some(t: ToolOperationManagement)) => t.setOperationTimeout(to)
          case _ => // nothing to do
        }
      }
    }

    val generator = new ConfigurableGenerator[GenProduct]()
    Parser.parser.setAnnotationListener((p: Program, inv: Formula) =>
      generator.products += (p->(generator.products.getOrElse(p, Nil) :+ (inv, Some(AnnotationProofHint(tryHard=true))))))
    TactixInit.invSupplier = generator

    initialized = true
  }

  @tailrec private def rootCause(it: Throwable): Throwable = {
    val cause = it.getCause
    if (cause == null || cause == it) it
    else rootCause(cause)
  }

  /** @inheritdoc */
  override def restart(): Unit = { }

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
