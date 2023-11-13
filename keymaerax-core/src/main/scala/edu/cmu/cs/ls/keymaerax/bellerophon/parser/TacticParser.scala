/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */
/**
  * Parser for Bellerophon tactics for Differential Dynamic Logic.
  *
  * @author Andre Platzer
  * @see Nathan Fulton, Stefan Mitsch, Brandon Bohrer and André Platzer.  [[https://doi.org/10.1007/978-3-319-66107-0_14 Bellerophon: Tactical theorem proving for hybrid systems]].
  *      In Mauricio Ayala-Rincón and César A. Muñoz, editors, Interactive Theorem Proving, International Conference, ITP 2017, volume 10499 of LNCS, pp. 207-224. Springer, 2017.
  */

package edu.cmu.cs.ls.keymaerax.bellerophon.parser

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, DefTactic}
import edu.cmu.cs.ls.keymaerax.parser.{BuiltinSymbols, Declaration, ParseException, Parser}
import fastparse.P

/**
  * Parser interface for Bellerophon tactics of KeYmaera X.
  * Provides a parser to read string inputs as a Bellerophon tactic.
  * A parser is a function from input strings to [[edu.cmu.cs.ls.keymaerax.bellerophon.BelleExpr Bellerophon expressions]].
  * {{{
  *     Parser: String => BelleExpr
  * }}}
  * Parsers are adjoint to printers, i.e., they reparse printed expressions as the original expressions
  * but fail to parse syntactically ill-formed strings:
  * {{{
  *   parser(printer(tactic)) == tactic
  * }}}
  *
  * @author Andre Platzer
  * @see Nathan Fulton, Stefan Mitsch, Brandon Bohrer and André Platzer.  [[https://doi.org/10.1007/978-3-319-66107-0_14 Bellerophon: Tactical theorem proving for hybrid systems]].
  *      In Mauricio Ayala-Rincón and César A. Muñoz, editors, Interactive Theorem Proving, International Conference, ITP 2017, volume 10499 of LNCS, pp. 207-224. Springer, 2017.
  */
trait TacticParser extends (String => BelleExpr) {
  /** Parse the input string in the concrete syntax of Bellerophon tactics.
    * @param input the string to parse as a Bellerophon tactic.
    * @ensures apply(printer(\result)) == \result
    * @throws ParseException if `input` is not a well-formed Bellerophon tactic.
    */
  final def apply(input: String): BelleExpr = apply(input, BuiltinSymbols.all)

  /** Parse the input string in the concrete syntax of Bellerophon tactics.
    * @param input the string to parse as a Bellerophon tactic.
    * @param defs the definitions to elaborate variables/functions/predicates to their expected type.
    * @ensures apply(printer(\result)) == \result
    * @throws ParseException if `input` is not a well-formed Bellerophon tactic.
    */
  def apply(input: String, defs: Declaration): BelleExpr

  /** Parse the input string in the concrete syntax as a Bellerophon tactic */
  val tacticParser: (String => BelleExpr)

  /** The expression parser for differential dynamic logic */
  val expressionParser: Parser

  /** A pretty-printer that can write the output that this parser reads
    * @ensures \forall e: apply(printer(e)) == e
    */
  val printer: BelleExpr => String

}

/** DL tactic parser with fastparse-compatible entry point. */
trait DLTacticParser extends TacticParser {
  /** Parses a dL Bellerophon tactic. */
  def tactic[$: P]: P[BelleExpr]

  /** Sets the definitions to be used during parsing. */
  def setDefs(defs: Declaration): Unit

  /** Sets the defined tactics to be used during parsing. */
  def setDefTactics(defs: Map[String, DefTactic]): Unit
}