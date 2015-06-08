/**
 * Differential Dynamic Logic lexer for concrete KeYmaera X notation.
 * @author aplatzer
 * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981, 2015."
 */
package edu.cmu.cs.ls.keymaerax.parser

import scala.collection.immutable._

/**
 * Terminal symbols of the differential dynamic logic grammar.
 * @author aplatzer
 */
sealed abstract class Terminal(val img: String)
abstract class OPERATORS(opcode: String) extends Terminal(opcode)
case class IDENT(name: String) extends Terminal(name)
case class NUMBER(value: String) extends Terminal(value)
case class OPERATOR(opcode: String) extends OPERATORS(opcode)

object EOF extends Terminal("<EOF>")

object LPARENS extends Terminal("(")
object RPARENS extends Terminal(")")
object LBRACK  extends Terminal("{")
object RBRACK  extends Terminal("}")
object LBOX    extends Terminal("[")
object RBOX    extends Terminal("]")
object LDIA    extends OPERATORS("<") //@todo really operator or better not?
object RDIA    extends OPERATORS(">")

object PRIME   extends OPERATORS("'")
object POWER   extends OPERATORS("^")
object STAR    extends OPERATORS("*")
object SLASH   extends OPERATORS("/")
object PLUS    extends OPERATORS("+")
object MINUS   extends OPERATORS("-")

object NOT     extends OPERATORS("!")
object AND     extends OPERATORS("&")
object OR      extends OPERATORS("|")
object EQUIV   extends OPERATORS("<->")
object IMPLY   extends OPERATORS("->")

object FORALL  extends OPERATORS("\\forall")
object EXISTS  extends OPERATORS("\\exists")

object GREATEREQ extends OPERATORS(">=")
object LESSEQ  extends OPERATORS("<=")

object COMPOSE extends OPERATORS(";")
object CHOICE  extends OPERATORS("++")


sealed abstract class Location
object UnknownLocation extends Location
case class Region(line: Int, column: Int, endLine: Int, endColumn: Int) extends Location


/**
 * Created by aplatzer on 6/8/15.
 */
object KeYmaeraXLexer extends (String => List[Token]) {

  /** Lexer's token stream with first token at head. */
  type TokenStream = List[Token]

  def apply(input: String): TokenStream = ???

}
