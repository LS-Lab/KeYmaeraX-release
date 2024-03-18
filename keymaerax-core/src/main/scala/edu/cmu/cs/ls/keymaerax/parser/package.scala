/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax

import edu.cmu.cs.ls.keymaerax.core.CoreException

/**
 * =Parser & Pretty-Printer for Differential Dynamic Logic=
 *
 * Defines the concrete syntax of differential dynamic logic as used in KeYmaera X. Provides a parser to read string and
 * file inputs with differential dynamic logic. Conversely provides a pretty-printer to format
 * [[edu.cmu.cs.ls.keymaerax.core.Expression differential dynamic logic expression data structure]] as human readable
 * concrete syntax.
 * {{{
 * PrettyPrinter: Expression => String
 * Parser: String => Expression
 * }}}
 *
 * ==Usage Overview==
 *
 * The default pretty-printer for the concrete syntax in KeYmaera X is in
 * [[edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter]]. The corresponding parser for the concrete syntax in
 * [[edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXParser]]. Also see
 * [[http://keymaeraX.org/doc/dL-grammar.md Grammar of KeYmaera X Syntax]]
 *
 * {{{
 * val parser = KeYmaeraXParser
 * val pp = KeYmaeraXPrettyPrinter
 * val input = "x^2>=0 & x<44 -> [x:=2;{x'=1&x<=10}]x>=1"
 * val parse = parser(input)
 * println("Parsed:   " + parse)
 * val print = pp(parse)
 * println("Printed:  " + print)
 * }}}
 *
 * ===Printing Differential Dynamic Logic===
 *
 * [[edu.cmu.cs.ls.keymaerax.parser.PrettyPrinter]] defines the interface for all differential dynamic logic pretty
 * printers in KeYmaera X. {{{PrettyPrinter: Expression => String}}}
 * [[edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter]] implements the pretty-printer for the concrete syntax of
 * differential dynamic logic used in KeYmaera X. A pretty-printer is an injective function from differential dynamic
 * logic [[edu.cmu.cs.ls.keymaerax.core.Expression expressions]] to strings.
 *
 * Printing formulas to strings is straightforward using
 * [[edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter.apply]]:
 * {{{
 * val pp = KeYmaeraXPrettyPrinter
 * // "x < -y"
 * val fml0 = Less(Variable("x"),Neg(Variable("y")))
 * val fml0str = pp(fml0)
 * // "true -> [x:=1;]x>=0"
 * val fml1 = Imply(True, Box(Assign(Variable("x"), Number(1)), GreaterEqual(Variable("x"), Number(0))))
 * val fml1str = pp(fml1)
 * }}}
 *
 * ===Printing Fully Parenthesized Forms===
 * Fully parenthesized strings are obtained using the [[edu.cmu.cs.ls.keymaerax.parser.FullPrettyPrinter]] printer:
 * {{{
 * val pp = FullPrettyPrinter
 * // "x < -(y)"
 * val fml0 = Less(Variable("x"),Neg(Variable("y")))
 * val fml0str = pp(fml0)
 * // "true -> ([x:=1;](x>=0))"
 * val fml1 = Imply(True, Box(Assign(Variable("x"), Number(1)), GreaterEqual(Variable("x"), Number(0))))
 * val fml1str = pp(fml1)
 * }}}
 * The fully-parenthesized pretty printer corresponding to a pretty printer can also be obtained using
 * [[edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrinter.fullPrinter]]
 *
 * ===Parsing Differential Dynamic Logic===
 *
 * [[edu.cmu.cs.ls.keymaerax.parser.Parser]] defines the interface for all differential dynamic logic parsers in
 * KeYmaera X. {{{Parser: String => Expression}}} [[edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXParser]] implements the
 * parser for the concrete syntax of differential dynamic logic used in KeYmaera X. A parser is a function from input
 * strings to differential dynamic logic [[edu.cmu.cs.ls.keymaerax.core.Expression expressions]].
 *
 * Parsing formulas from strings is straightforward using [[edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXParser.apply]]:
 * {{{
 * val parser = KeYmaeraXParser
 * val fml0 = parser("x!=5")
 * val fml1 = parser("x>0 -> [x:=x+1;]x>1")
 * val fml2 = parser("x>=0 -> [{x'=2}]x>=0")
 * }}}
 *
 * The parser parses any dL expression, so will also accept terms or programs from strings, which will lead to
 * appropriate types:
 * {{{
 * val parser = KeYmaeraXParser
 * // formulas
 * val fml0 = parser("x!=5")
 * val fml1 = parser("x>0 -> [x:=x+1;]x>1")
 * val fml2 = parser("x>=0 -> [{x'=2}]x>=0")
 * // terms
 * val term0 = parser("x+5")
 * val term1 = parser("x^2-2*x+7")
 * val term2 = parser("x*y/3+(x-1)^2+5*z")
 * // programs
 * val prog0 = parser("x:=1;")
 * val prog1 = parser("x:=1;x:=5;x:=-1;")
 * val prog2 = parser("x:=1;{{x'=5}++x:=0;}")
 * }}}
 *
 * ===Parsing Only Formulas of Differential Dynamic Logic===
 * The parser that only parses formulas is obtained via [[edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXParser.formulaParser]]
 * {{{
 * // the formula parser only accepts formulas
 * val parser = KeYmaeraXParser.formulaParser
 * // formulas
 * val fml0 = parser("x!=5")
 * val fml1 = parser("x>0 -> [x:=x+1;]x>1")
 * val fml2 = parser("x>=0 -> [{x'=2}]x>=0")
 * // terms will cause exceptions
 * try { parser("x+5") } catch {case e: ParseException => println("Rejected")}
 * // programs will cause exceptions
 * try { parser("x:=1;") } catch {case e: ParseException => println("Rejected")}
 * }}}
 *
 * Similarly, a parser that only parses terms is obtained via
 * [[edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXParser.termParser]] and a parser that only parses programs is obtained via
 * [[edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXParser.programParser]]
 *
 * ===Parsing Pretty-Printed Strings===
 *
 * Corresponding parsers and pretty-printers match with one another. Parsing a pretty-printed expression results in the
 * original expression again:
 * {{{
 *   parse(print(e)) == e
 * }}}
 * [[edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXParser]] and [[[[edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter]]
 * are inverses in this sense. The converse `print(parse(s)) == s` is not quite the case, because there can be minor
 * spacing and superfluous parentheses differences. The following slightly weaker form still holds:
 * {{{
 *   parse(print(parse(s))) == parse(s)
 * }}}
 *
 * Parsing the pretty-print of an expression with compatible printers and parsers always gives the original expression
 * back:
 * {{{
 *   val parser = KeYmaeraXParser
 *   val pp = KeYmaeraXPrettyPrinter
 *   val fml = Imply(True, Box(Assign(Variable("x"), Number(1)), GreaterEqual(Variable("x"), Number(0))))
 *   // something like "true -> [x:=1;]x>=0" modulo spacing
 *   val print = pp(fml)
 *   val reparse = parser(print)
 *   if (fml == reparse) println("Print and reparse successful") else println("Discrepancy")
 * }}}
 *
 * ===Pretty-Printing Parsed Strings===
 *
 * It can be quite helpful to print an expression that has been parsed to check how it got parsed:
 * {{{
 *   val parser = KeYmaeraXParser
 *   val pp = KeYmaeraXPrettyPrinter
 *   val input = "x^2>=0 & x<44 -> [x:=2;{x'=1&x<=10}]x>=1"
 *   val parse = parser(input)
 *   println("Parsed:   " + parse)
 *   val print = pp(parse)
 *   println("Printed:  " + print)
 *   println("Original: " + input)
 *   println("Can differ slightly by spacing and parentheses")
 * }}}
 *
 * Recall that the default pretty printer [[[[edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter]] uses compact
 * parentheses and braces. That is, it only prints them when necessary to disambiguate. For storage purposes and
 * disambiguation it can be better to use fully parenthesized printouts, which is what
 * [[edu.cmu.cs.ls.keymaerax.parser.FullPrettyPrinter]] achieves:
 * {{{
 *   val parser = KeYmaeraXParser
 *   val pp = FullPrettyPrinter
 *   val input = "x^2>=0 & x<44 -> [x:=2;{x'=1&x<=10}]x>=1"
 *   val parse = parser(input)
 *   println("Parsed:   " + parse)
 *   val print = pp(parse)
 *   // (((x)^(2)>=0)&(x < 44))->([{x:=2;}{{x'=1&x<=10}}](x>=1))
 *   println("Printed:  " + print)
 *   println("Original: " + input)
 * }}}
 *
 * ===Pretty-Printing Sequents===
 * Sequents can be pretty-printed using the default pretty printer via
 * [[edu.cmu.cs.ls.keymaerax.core.Sequent.prettyString]]
 * {{{
 *   val parser = KeYmaeraXParser
 *   val sequent = Sequent(IndexedSeq(parse("x<22"), parse("x>0")), IndexedSeq(parse("[x:=x+1;]x<23")))
 *   println("Printed:  " + sequent.prettyString)
 * }}}
 *
 * @author
 *   Andre Platzer
 * @see
 *   Andre Platzer.
 *   [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]].
 *   Journal of Automated Reasoning, 59(2), pp. 219-266, 2017.
 * @see
 *   Andre Platzer.
 *   [[https://doi.org/10.1007/978-3-319-21401-6_32 A uniform substitution calculus for differential dynamic logic]]. In
 *   Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin,
 *   Germany, Proceedings, LNCS. Springer, 2015.
 *   [[http://arxiv.org/pdf/1503.01981.pdf A uniform substitution calculus for differential dynamic logic. arXiv 1503.01981]]
 * @see
 *   Andre Platzer. [[https://doi.org/10.1145/2817824 Differential game logic]]. ACM Trans. Comput. Log. 17(1), 2015.
 *   [[http://arxiv.org/pdf/1408.1980 arXiv 1408.1980]]
 * @see
 *   Nathan Fulton, Stefan Mitsch, Jan-David Quesel, Marcus Volp and Andre Platzer. KeYmaera X: An axiomatic tactical
 *   theorem prover for hybrid systems. In Amy P. Felty and Aart Middeldorp, editors, International Conference on
 *   Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015.
 * @see
 *   [[http://keymaeraX.org/doc/dL-grammar.md Grammar of Differential Dynamic Logic]]
 * @see
 *   [[edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXParser]]
 * @see
 *   [[edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter]]
 */
package object parser {

  /**
   * Check input for requirement being true, throwing a [[ParseException]] if false. This method is a require coming
   * from the parser that cannot be disabled. Blame is on the user input.
   *
   * @param requirement
   *   the expression to test for being true
   * @param message
   *   a String explaining what is expected.
   * @param loc
   *   the location where the parse error occurred.
   * @param state
   *   information about the parser state in which the parse error occurred.
   * @see
   *   [[scala.Predef.require()]]
   */
  @inline
  final def checkInput(
      requirement: Boolean,
      message: => Any,
      loc: => Location,
      state: => String, /*ParseState*/
  ): Unit = { if (!requirement) throw new ParseException(message.toString, loc, "<unknown>", "<unknown>", "", state) }

}
