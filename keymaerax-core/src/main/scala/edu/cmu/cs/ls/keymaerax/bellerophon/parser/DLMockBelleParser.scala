/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
/**
  * Mock Bellerophon tactic parser for JS compilation
  */
package edu.cmu.cs.ls.keymaerax.bellerophon.parser

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.parser.DLParser.parseException
import edu.cmu.cs.ls.keymaerax.parser.{DLParser, Declaration, ParseException, Parser}
import fastparse._

import scala.collection.immutable._

class DLMockBelleParser(override val printer: BelleExpr => String,
                        tacticProvider: (String, List[Either[Seq[Any], PositionLocator]], Declaration) => BelleExpr) extends DLTacticParser {

  def tactic[_: P]: P[BelleExpr] = AnyChar.repX.map(t => ParallelTactic(Nil))

  /** Definitions, should be provided by the outer parser through [[setDefs]]. */
  private var defs: Declaration = Declaration(Map.empty)

  override val tacticParser: String => BelleExpr = this
  override val expressionParser: Parser = DLParser

  /** @inheritdoc */
  override def apply(input: String, defs: Declaration): BelleExpr = {
    setDefs(defs)
    belleParser(input)
  }

  /** Sets the definitions to be used when parsing tactic expressions. Expected to be set
    * before [[apply]] or [[tactic]] are used. */
  override def setDefs(defs: Declaration): Unit = this.defs = defs

  /** Parse the input string in the concrete syntax as a differential dynamic logic expression */
  //@todo store the parser for speed
  val belleParser: String => BelleExpr = (s => fastparse.parse(s, tactic(_)) match {
    case Parsed.Success(value, index) => value
    case f: Parsed.Failure => throw parseException(f)
  })

}
