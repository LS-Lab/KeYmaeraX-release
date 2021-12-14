/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
/**
  * Differential Dynamic Logic parser for concrete KeYmaera X notation.
  * @author Andre Platzer
  * @see Andre Platzer. [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 59(2), pp. 219-266, 2017.
  */
package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.core._

import scala.util.Try

/**
  * Parser interface for KeYmaera X.
  * Provides a parser to read string inputs as differential dynamic logic.
  * A parser is a function from input strings to differential dynamic logic [[edu.cmu.cs.ls.keymaerax.core.Expression expressions]].
  * {{{
  *     Parser: String => Expression
  * }}}
  * Parsers are adjoint to printers, i.e., they reparse printed expressions as the original expressions
  * but fail to parse syntactically ill-formed strings:
  * {{{
  *   parser(printer(expr)) == expr
  * }}}
  *
  * @author Andre Platzer
  * @see [[TokenParser]]
  * @see Andre Platzer. [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 59(2), pp. 219-266, 2017.
  */
trait Parser extends (String => Expression) {
  /** Parse the input string in the concrete syntax as a differential dynamic logic expression
    * @param input the string to parse as a dL formula, dL term, or dL program.
    * @ensures apply(printer(\result)) == \result
    * @throws ParseException if `input` is not a well-formed expression of differential dynamic logic or differential game logic.
    */
  def apply(input: String): Expression

  /** Parse the input string in the concrete syntax as a differential dynamic logic term.
    * @throws ParseException whenever its `input` is not a well-formed term of differential dynamic logic or differential game logic.
    */
  val termParser: String => Term

  /** Parse the input string in the concrete syntax as a differential dynamic logic formula.
    * @throws ParseException whenever its `input` is not a well-formed formula of differential dynamic logic or differential game logic.
    */
  val formulaParser: String => Formula

  /** Parse the input string in the concrete syntax as a differential dynamic logic program.
    * @throws ParseException whenever its `input` is not a well-formed program of differential dynamic logic or game of differential game logic.
    */
  val programParser: String => Program

  /** Parse the input string in the concrete syntax as a differential dynamic logic differential program.
    * @throws ParseException whenever its `input` is not a well-formed differential program of differential dynamic logic or differential game of differential game logic.
    */
  val differentialProgramParser: String => DifferentialProgram

  /** Parse the input string in the concrete syntax as a differential dynamic logic sequent.
    * @throws ParseException whenever its `input` is not a well-formed sequent of differential dynamic logic or differential game logic.
    */
  val sequentParser: String => Sequent

//  /** Parse the input string in the concrete syntax as a differential dynamic logic inference.
//    * @return A parser turning strings into the list of conclusion:subgoals corresponding to the input string.
//    * @throws ParseException whenever its `input` is not a syntactically well-formed inference of differential dynamic logic or differential game logic.
//    *                        Syntactical well-formedness does not require the inference to be according to a proof rule or axiom, merely plausible input.
//    */
//@todo add  val inferenceParser: (String => List[Sequent])

  /** A pretty-printer that can write the output that this parser reads
    * @ensures \forall e: apply(printer(e)) == e
    */
  val printer: PrettyPrinter

  /** Sets a listener to be informed when parsing annotations. */
  def setAnnotationListener(listener: (Program,Formula) => Unit): Unit = {}
}

object Parser extends (String => Expression) {
  /* @note mutable state for switching out the default parser. */
  private[this] var p: Parser = ParserInit.fromConfig()

  /** The parser that is presently used per default. */
  def parser: Parser = p

  /** Set a new parser. */
  def setParser(parser: Parser): Unit = { p = parser }

  /** Parses `input`. */
  override def apply(input: String): Expression = parser(input)

  /** Parses a comma-separated list of expressions. */
  def parseExpressionList(s: String): List[Expression] = {
    def splitComma(s: String, prefix: String = ""): List[Expression] = {
      val ci = s.indexOf(',')
      if (ci >= 0) {
        val (a, b) = s.splitAt(ci)
        Try(Parser(prefix + a)).toOption match {
          case Some(e) => e +: splitComma(b.substring(1))
          case None => splitComma(b.substring(1), prefix + a + ",")
        }
      } else List(Parser(prefix + s))
    }
    splitComma(s)
  }
}

/**
 * Parser interface for KeYmaera X reading token streams instead of strings.
 * Provides a parser to read token streams with differential dynamic logic.
 * A token parser is a function from token sequences to differential dynamic logic [[edu.cmu.cs.ls.keymaerax.core.Expression expressions]].
 * {{{
 *     TokenParser: TokenStream => Expression
 * }}}
 * @author Stefan Mitsch
 * @see [[Parser]]
 */
trait TokenParser {
  /** Lexer's token stream with first token at head. */
  type TokenStream = KeYmaeraXLexer.TokenStream

  /** Parse the input tokens in the concrete syntax as a differential dynamic logic expression
    * @param input the token stream to parse as a dL formula, dL term, or dL program.
    * @throws ParseException if `input` is not a well-formed expression of differential dynamic logic or differential game logic.
    */
  def parse(input: TokenStream): Expression

  /** Parse the input tokens in the concrete syntax as a differential dynamic logic term */
  val termTokenParser: TokenStream => Term

  /** Parse the input tokens in the concrete syntax as a differential dynamic logic formula */
  val formulaTokenParser: TokenStream => Formula

  /** Parse the input tokens in the concrete syntax as a differential dynamic logic program */
  val programTokenParser: TokenStream => Program

  /** Parse the input tokens in the concrete syntax as a differential dynamic logic differential program */
  val differentialProgramTokenParser: TokenStream => DifferentialProgram
}

object ParserHelper {
  /** Returns (approximately!) 's' without any Byte Order Mark.
    * @todo DANGER hack: actually just returns a version of 's' that is converted into ASCII (replacing non-ASCII bytes with '?') and then stripping all the '?' from the prefix of the string.
    * In particular, ay also remove completely valid '?' characters if that's what's at the beginning of the string. */
  def removeBOM(s : String): String = {
    if (s.isEmpty) s
    else {
      val asASCII = new String(s.getBytes("US-ASCII"), "US-ASCII")
      //Find the length of a uniformly-'?' prefix on asSCII, then remove that many characters from s.
      //This preserves other unicode characters is s, only removing the potential BOM.
      //@todo be less indiscriminate and only remove these guys: https://en.wikipedia.org/wiki/Byte_order_mark#Representations_of_byte_order_marks_by_encoding
      var toRemove = 0
      while (asASCII(toRemove) == '?')
        toRemove += 1
      s.substring(toRemove)
    }
  }
}
