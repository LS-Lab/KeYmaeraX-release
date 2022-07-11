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
import edu.cmu.cs.ls.keymaerax.bellerophon.ProverSetupException
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

  /** Returns the annotation listener. */
  def annotationListener: (Program, Formula) => Unit
}

object Parser extends (String => Expression) {
  /* @note mutable state for switching out the default parser. */
  private[this] var p: Parser = ParserInit.fromConfig()

  /** `true` has unary negation `-` bind weakly like binary subtraction.
    * `false` has unary negation `-` bind strong just shy of power `^`. */
  val weakNeg: Boolean = true

  /** `true` when negative numbers are picked out specially, e.g. `-2*x` is `(-2)*x`.
    * `false` when negative numbers are handled like unary `-`. */
  val numNeg: Boolean = OpSpec.negativeNumber

  /** The parser that is presently used per default. */
  def parser: Parser = {
    if (p != null) p
    else throw new ProverSetupException("No parser set. Please check the command line during startup for error messages.")
  }

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

  /** Semantic analysis of expressions after parsing, returning errors if any or None. */
  def semanticAnalysis(e: Expression): Option[String] = {
    val symbols = try { StaticSemantics.symbols(e) }
    catch {
      case ex: AssertionError => return Some("semantics: symbols computation error\n" + ex)
      case ex: CoreException => return Some("semantics: symbols computation error\n" + ex)
    }
    val names = symbols.map(s => (s.name, s.index, s.isInstanceOf[DifferentialSymbol]))
    assert(Configuration(Configuration.Keys.DEBUG) == "false" || (names.size == symbols.size) == (symbols.toList.map(s => (s.name, s.index, s.isInstanceOf[DifferentialSymbol])).distinct.length == symbols.toList.map(s => (s.name, s.index, s.isInstanceOf[DifferentialSymbol])).length), "equivalent ways of checking uniqueness via set conversion or list distinctness")
    //@NOTE Stringify avoids infinite recursion of KeYmaeraXPrettyPrinter.apply contract checking.
    if (names.size == symbols.size) None
    else {
      val namesList = symbols.toList.map(s => (s.name, s.index, s.isInstanceOf[DifferentialSymbol]))
      val duplicateNames = namesList.diff(namesList.distinct)
      val duplicates = symbols.filter(s => duplicateNames.contains((s.name, s.index, s.isInstanceOf[DifferentialSymbol])))
      Some("semantics: Expect unique names_index that identify a unique type." +
        "\nambiguous: " + duplicates.toList.map(s => s.fullString).mkString(" and ") +
        "\nsymbols:   " + symbols.mkString(", ") /*+ if (DEBUG) "\nin expression: " + printer.stringify(e)*/)
    }
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
  private val UTF8_BOM = "\uFEFF"

  /** Returns 's' without leading Byte Order Mark. */
  def removeBOM(s : String): String = s.stripPrefix(UTF8_BOM)
}
