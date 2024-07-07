/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

/** Mock Bellerophon tactic parser for JS compilation */
package org.keymaerax.bellerophon.parser

import org.keymaerax.bellerophon._
import org.keymaerax.parser.DLParser.parseException
import org.keymaerax.parser.{DLParser, Declaration, Parser}
import fastparse._

import scala.collection.immutable._

class DLMockBelleParser(
    override val printer: BelleExpr => String,
    tacticProvider: (String, List[Either[Seq[Any], PositionLocator]], Declaration) => BelleExpr,
) extends DLTacticParser {

  def tactic[$: P]: P[BelleExpr] = AnyChar.repX.map(t => ParallelTactic(Nil))

  /** Definitions, should be provided by the outer parser through [[setDefs]]. */
  private var defs: Declaration = Declaration(Map.empty)

  override val tacticParser: String => BelleExpr = this
  override val expressionParser: Parser = DLParser

  /** @inheritdoc */
  override def apply(input: String, defs: Declaration): BelleExpr = {
    setDefs(defs)
    belleParser(input)
  }

  /**
   * Sets the definitions to be used when parsing tactic expressions. Expected to be set before [[apply]] or [[tactic]]
   * are used.
   */
  override def setDefs(defs: Declaration): Unit = this.defs = defs

  /** @inheritdoc */
  override def setDefTactics(defs: Map[String, DefTactic]): Unit = {}

  /** Parse the input string in the concrete syntax as a differential dynamic logic expression */
  // @todo store the parser for speed
  val belleParser: String => BelleExpr = s =>
    fastparse.parse(s, tactic(_)) match {
      case Parsed.Success(value: BelleExpr, _) => value
      case f: Parsed.Failure => throw parseException(f)
    }

}
