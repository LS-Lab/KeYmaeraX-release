package edu.cmu.cs.ls.keymaerax

/**
 * KeYmaera X: An Axiomatic Tactical Theorem Prover
 * ================================================
 * KeYmaera X Parser: Parser & Pretty-Printer for Differential Dynamic Logic.
 *
 * Defines the concrete syntax of differential dynamic logic as used in KeYmaera X.
 * Provides a parser to read string and file inputs with differential dynamic logic.
 * Conversely provides a pretty-printer to format [[edu.cmu.cs.ls.keymaerax.core.Expression differential dynamic logic expression data structure]]
 * as human readable concrete syntax.
 *
 * ==Usage Overview==
 *
 * ===Printing Differential Dynamic Logic===
 * [[edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter]] implements the pretty-printer for the concrete syntax
 * of differential dynamic logic used in KeYmaera X.
 *
 * ===Parsing Differential Dynamic Logic===
 * [[edu.cmu.cs.ls.keymaerax.parser.Parser]] defines the interface for all differential dynamic logic parsers in KeYmaera X.
 * [[edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXParser]] implements the parser for the concrete syntax
 * of differential dynamic logic used in KeYmaera X.
 * A parser is essentially a function from input string to differential dynamic logic [[edu.cmu.cs.ls.keymaerax.core.Expression expressions]].
 *
 * Parsing formulas from strings is straightforward:
 * {{{
 * val parser = KeYmaeraXParser
 * val fml0 = parser("x!=5")
 * val fml1 = parser("x>0 -> [x:=x+1;]x>1")
 * val fml2 = parser("x>=0 -> [{x'=2}]x>=0")
 * }}}
 *
 * The parser parses any dL expression, so will also accept terms or programs from strings, which will lead to appropriate types:
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
 * Similarly, a parser that only parses terms is obtained via [[edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXParser.termParser]]
 * and a parser that only parses programs is obtained via [[edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXParser.programParser]]
 *
 * @author aplatzer
 * @see Andre Platzer. [[http://www.cs.cmu.edu/~aplatzer/pub/usubst.pdf A uniform substitution calculus for differential dynamic logic]].  In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015.
 * @see Andre Platzer. [[http://arxiv.org/pdf/1503.01981.pdf A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981]], 2015.
 * @see "Nathan Fulton, Stefan Mitsch, Jan-David Quesel, Marcus Volp and Andre Platzer. KeYmaera X: An axiomatic tactical theorem prover for hybrid systems.  In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015."
 * @see doc/dL-grammar.md
 */
package object parser {}
