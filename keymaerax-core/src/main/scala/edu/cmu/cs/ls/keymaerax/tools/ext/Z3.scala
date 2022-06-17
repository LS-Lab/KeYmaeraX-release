/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.tools.ext

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.lemma.Lemma
import edu.cmu.cs.ls.keymaerax.parser.Parser
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tools.qe.{DefaultSMTConverter, Z3QETool, Z3Solver}
import edu.cmu.cs.ls.keymaerax.tools.{ConversionException, Tool, ToolExecutionException, ToolOperationManagement}

import java.io.StringReader
import scala.collection.immutable.Map

/**
  * Z3 quantifier elimination tool for tactics.
  *
  * @see [[edu.cmu.cs.ls.keymaerax.btactics.Z3ToolProvider]] to obtain instances of Z3 that are properly initialized
  *      and installed/updated.
  * @author Stefan Mitsch
  */
final class Z3 extends Tool with QETacticTool with SimplificationTool with ToolOperationManagement {
  /** @inheritdoc */
  override val name: String = "Z3"

  /** The Z3 QE tool. */
  private val z3qe: Z3QETool = new Z3QETool()

  /** Untrusted access to Z3 directly. */
  private var z3: Z3Solver = _

  /** @inheritdoc */
  override def init(config: Map[String,String]): Unit = {
    z3 = new Z3Solver(config("z3Path"), DefaultSMTConverter)
    z3qe.init(config)
  }

  /** @inheritdoc */
  override def isInitialized: Boolean = z3qe.isInitialized && z3 != null

  /** @inheritdoc */
  override def restart(): Unit = z3qe.restart()

  /** @inheritdoc */
  override def shutdown(): Unit = {
    z3 = null
    z3qe.shutdown()
  }

  /** @inheritdoc */
  override def cancel(): Boolean = z3.cancel() && z3qe.cancel()

  /** @inheritdoc */
  override def qe(formula: Formula): Lemma = {
    require(isInitialized, "Z3 needs to be initialized before use")
    ProvableSig.proveArithmeticLemma(z3qe, formula)
  }

  /** @inheritdoc */
  override def qe(g: Goal, continueOnFalse: Boolean): (Goal, Formula) = g match {
    case Atom(fml) =>
      val Sequent(IndexedSeq(), IndexedSeq(Equiv(_, result))) = qe(fml).fact.conclusion
      g -> result
    case _ => throw ToolExecutionException("Z3 supports only atom goals")
  }

  /** @inheritdoc */
  override def simplify(expr: Expression, assumptions: List[Formula]): Expression = expr match {
    case f: Formula => simplify(f, assumptions)
    case t: Term => simplify(t, assumptions)
    case _ => throw ToolExecutionException("Z3 supports only simplifying terms and formulas, but not " + expr.kind)
  }

  /** @inheritdoc */
  override def simplify(expr: Formula, assumptions: List[Formula]): Formula = simplify(expr, assumptions,
    parser = (s: String) => SmtLibReader.readFml(s)
  )

  /** @inheritdoc */
  override def simplify(expr: Term, assumptions: List[Formula]): Term = simplify(expr, assumptions,
    parser = (s: String) => SmtLibReader.readTerm(s)
  )

  /** Simplifies expression `expr` accounting for `assumptions`, parses the result using `parser`. */
  private def simplify[T<:Expression](expr: T, assumptions: List[Formula], parser: String=>T): T = {
    val (varDec, smt) = DefaultSMTConverter.generateSMT(expr)
    val smtCode = varDec + "(simplify " + smt + ")"
    val z3Output = z3.runZ3Smt(smtCode, "z3simplify", getOperationTimeout)
    if (z3Output.contains("!")) expr
    else {
      try {
        parser(z3Output)
      } catch {
        case _: ConversionException => expr
      }
    }
  }

  /** @inheritdoc */
  override def setOperationTimeout(timeout: Int): Unit = z3qe.setOperationTimeout(timeout)

  /** @inheritdoc */
  override def getOperationTimeout: Int = z3qe.getOperationTimeout

  /** @inheritdoc */
  override def getAvailableWorkers: Int = 1
}
