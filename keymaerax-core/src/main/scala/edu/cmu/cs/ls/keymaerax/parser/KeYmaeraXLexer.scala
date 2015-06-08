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
sealed abstract class Terminal(val img: String) {
  override def toString = "\"" + img + "\""
}
abstract class OPERATOR(opcode: String) extends Terminal(opcode) {
  override def toString = opcode
}
case class IDENT(name: String) extends Terminal(name) {
  override def toString = "ID(\"" + name + "\")"
}
case class NUMBER(value: String) extends Terminal(value) {
  override def toString = "NUM(" + value + ")"
}
object EOF extends Terminal("<EOF>")

object LPARENS extends Terminal("(")
object RPARENS extends Terminal(")")
object LBRACK  extends Terminal("{")
object RBRACK  extends Terminal("}")
object LBOX    extends Terminal("[")
object RBOX    extends Terminal("]")
object LDIA    extends OPERATOR("<") //@todo really operator or better not?
object RDIA    extends OPERATOR(">")

object PRIME   extends OPERATOR("'")
object POWER   extends OPERATOR("^")
object STAR    extends OPERATOR("*")
object SLASH   extends OPERATOR("/")
object PLUS    extends OPERATOR("+")
object MINUS   extends OPERATOR("-")

object NOT     extends OPERATOR("!")
object AND     extends OPERATOR("&")
object OR      extends OPERATOR("|")
object EQUIV   extends OPERATOR("<->")
object IMPLY   extends OPERATOR("->")

object FORALL  extends OPERATOR("\\forall")
object EXISTS  extends OPERATOR("\\exists")

object GREATEREQ extends OPERATOR(">=")
object LESSEQ  extends OPERATOR("<=")

object ASSIGNANY extends OPERATOR(":=*")
object ASSIGN extends OPERATOR(":=")
object COMPOSE extends OPERATOR(";")
object CHOICE  extends OPERATOR("++")


sealed abstract class Location
object UnknownLocation extends Location {
  override def toString = "<somewhere>"
}
case class Region(line: Int, column: Int, endLine: Int, endColumn: Int) extends Location


/**
 * Created by aplatzer on 6/8/15.
 */
object KeYmaeraXLexer extends (String => List[Token]) {

  /** Lexer's token stream with first token at head. */
  type TokenStream = List[Token]

  def apply(input: String): TokenStream = ???

}
