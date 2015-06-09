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
  override def toString = getClass.getSimpleName + "\"" + img + "\""
}
abstract class OPERATOR(val opcode: String) extends Terminal(opcode) {
  //final def opcode: String = img
  override def toString = getClass.getSimpleName //+ "\"" + img + "\""
}
case class IDENT(name: String) extends Terminal(name) {
  override def toString = "ID(\"" + name + "\")"
}
case class NUMBER(value: String) extends Terminal(value) {
  override def toString = "NUM(" + value + ")"
}
object EOF extends Terminal("<EOF>")

object LPAREN  extends Terminal("(")
object RPAREN  extends Terminal(")")
object LBRACK  extends Terminal("{")
object RBRACK  extends Terminal("}")
object LBOX    extends Terminal("[")
object RBOX    extends Terminal("]")
object LDIA    extends OPERATOR("<") //@todo really operator or better not?
object RDIA    extends OPERATOR(">")

object COMMA   extends OPERATOR(",")

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
object REVIMPLY extends OPERATOR("<-")

object FORALL  extends OPERATOR("\\forall")
object EXISTS  extends OPERATOR("\\exists")

object EQ      extends OPERATOR("=")
object NOTEQ   extends OPERATOR("!=")
object GREATEREQ extends OPERATOR(">=")
object LESSEQ  extends OPERATOR("<=")

object TRUE    extends OPERATOR("true")
object FALSE   extends OPERATOR("false")

object ASSIGNANY extends OPERATOR(":=*")
object ASSIGN  extends OPERATOR(":=")
object TEST    extends OPERATOR("?")
object SEMI    extends OPERATOR(";")
object CHOICE  extends OPERATOR("++")

// pseudos: could probably demote so that some are not OPERATOR
object NOTHING extends Terminal("")
object DOT     extends OPERATOR("•") //(".")
object PLACE   extends OPERATOR("⎵") //("_")
object PSEUDO  extends Terminal("<pseudo>")


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
