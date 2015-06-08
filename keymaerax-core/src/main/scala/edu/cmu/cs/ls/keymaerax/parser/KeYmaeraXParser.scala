package edu.cmu.cs.ls.keymaerax.parser

import scala.collection.immutable._

import edu.cmu.cs.ls.keymaerax.core._

sealed abstract class Location
object UnknownLocation extends Location

sealed abstract class Terminal(val img: String)
case class OPERATOR(opcode: String) extends Terminal(opcode)
case class IDENT(name: String) extends Terminal(name)
case class NUMBER(value: String) extends Terminal(value)
object LPARENS extends Terminal("(")
object RPARENS extends Terminal(")")
object PRIME extends Terminal("'")

sealed abstract class Item
case class Tok(tok: Terminal) extends Item
case class Expr(expr: Expression) extends Item
object EndToken extends Item

/*sealed abstract class Stack
object Bottom extends Stack
case class St(stack: Stack, item: Item) extends Stack
*/


/**
 * KeYmaera X parser.
 * Created by aplatzer on 6/7/15.
 * @author aplatzer
 */
object KeYmaeraXParser extends (String => Expression) {
  def apply(input: String): Expression = ??? /*parse((Nil, lexer(input)))*/

  type TokenStream = List[Terminal]
  type Stack = List[Item]

  type ParseState = (Stack, TokenStream)

  private def lexer(input: String): TokenStream = ???

  private def parse(st: ParseState): ParseState = {
    val (s, input@(la :: rest)) = st
    s match {
      case Expr(t2: Term) :: (tok@Tok(OPERATOR(_))) :: Expr(t1: Term) :: _
        if op(tok).isInstanceOf[BinaryOpSpec[Term]] =>
        if (op(tok) < op(Tok(la)) || op(tok) <= op(Tok(la)) && op(tok).assoc == LeftAssociative)
          reduce(st, 3, op(tok).asInstanceOf[BinaryOpSpec[Term]].const(tok.tok.img, t1, t2))
        else if (op(tok) > op(Tok(la)) || op(tok) >= op(Tok(la)) && op(tok).assoc == RightAssociative)
          shift(st)
        else error(st)

      case (tok@Tok(OPERATOR(_))) :: Expr(t1: Term) :: _ =>
        if (la.isInstanceOf[IDENT] || la == LPARENS) shift(st) else error(st)

      case Tok(RPARENS) :: Expr(t1: Term) :: Tok(LPARENS) :: _ =>
        if (la == LPARENS || la.isInstanceOf[IDENT]) error(st)
        else if (la == PRIME) ??? else reduce(st, 3, t1)

      case Expr(t1: Term) :: Tok(LPARENS) :: _ =>
        if (la.isInstanceOf[OPERATOR] || la == RPARENS) shift(st)
        else if (la == PRIME) ??? else error(st)

      case Tok(LPARENS) :: _ =>
        if (la == LPARENS || la.isInstanceOf[IDENT]) shift(st)
        else error(st)

      case Tok(IDENT(name)) :: _ =>
        if (la == RPARENS || la.isInstanceOf[IDENT]) error(st)
        else if (la == LPARENS) /*function/predicate*/??? else reduce(st, 1, Variable(name,None,Real))

      case Tok(NUMBER(value)) :: _ =>
        if (la.isInstanceOf[NUMBER] || la.isInstanceOf[IDENT] || la == LPARENS) error(st)
        else reduce(st, 1, Number(BigDecimal(value)))

      case Nil =>
        if (la == LPARENS || la.isInstanceOf[IDENT]) shift(st) //@todo or [ or <
        else error(st)
    }
  }

  /** Shift to put the next input token la on the parser stack s. */
  private def shift(st: ParseState): ParseState = {
    val (s, (la :: rest)) = st
    (Tok(la) :: s, rest)
  }

  /** Reduce the parser stack by reducing the consuming many items from the stack to the reduced item. */
  private def reduce(st: ParseState, consuming: Int, reduced: Item): ParseState = {
    val (s, input) = st
    (reduced :: s.drop(consuming), input)
  }
  private def reduce(st: ParseState, consuming: Int, reduced: Expression): ParseState = reduce(st, consuming, Expr(reduced))

  /** Error parsing the next input token la when in parser stack s. */
  private def error(st: ParseState): ParseState = {
    val (s, (la :: rest)) = st
    throw new ParseException("Unexpected token cannot be parsedn\nFound: " + la)
  }

  /** The operator notation of the top-level operator of expr with opcode, precedence and associativity  */
  private[parser] def op(tok: Tok): OpSpec = OpSpec.op(tok.tok)
}
