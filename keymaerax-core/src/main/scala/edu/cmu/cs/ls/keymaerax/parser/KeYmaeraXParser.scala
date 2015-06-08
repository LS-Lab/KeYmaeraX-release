/**
 * Differential Dynamic Logic parser for concrete KeYmaera X notation.
 * @author aplatzer
 * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981, 2015."
 */
package edu.cmu.cs.ls.keymaerax.parser

import scala.annotation.tailrec
import scala.collection.immutable._

import edu.cmu.cs.ls.keymaerax.core._

/**
 * KeYmaera X parser items on the parser stack.
 * @author aplatzer
 */
sealed trait Item
/** Tokens are terminals occurring at a given location in the input. */
case class Token(tok: Terminal, loc: Location = UnknownLocation) extends Item
/** Expressions that are partially parsed on the parser item stack. */
case class Expr(expr: Expression) extends Item
trait FinalItem extends Item
/** Parser items representing expressions that are accepted by the parser. */
case class Accept(expr: Expression) extends FinalItem
/** Parser items representing erroneous ill-formed input. */
case class Error(msg: String) extends FinalItem

/**
 * KeYmaera X parser.
 * Created by aplatzer on 6/7/15.
 * @author aplatzer
 */
object KeYmaeraXParser extends (String => Expression) {

  def apply(input: String): Expression = parse(lexer(input))

  /** Lexer's token stream with first token at head. */
  type TokenStream = List[Token]
  /** Parser stack of parser items with top at head. */
  type Stack = List[Item]

  type ParseState = (Stack, TokenStream)

  private def lexer(input: String): TokenStream = KeYmaeraXLexer(input)

  /*private*/ def parse(input: TokenStream): Expression = {
    require(input.endsWith(List(Token(EOF))), "token streams have to end in " + EOF)
    parseLoop((Nil, input))._1 match {
      case Accept(e) :: Nil => e
      case Error(msg) :: context => throw new ParseException(msg)
    }
  }

  @tailrec
  private def parseLoop(st: ParseState): ParseState = st._1 match {
    case (result: FinalItem) :: _ => st
    case _ => parseLoop(parseStep(st))
  }


  private def parseStep(st: ParseState): ParseState = {
    val (s, input@(Token(la,_) :: rest)) = st
    s match {
      case Expr(t2) :: (Token(tok:OPERATORS,_)) :: Expr(t1) :: _ =>
        assert(op(tok).isInstanceOf[BinaryOpSpec[_]], "binary operator expected since others should have been reduced\nin " + s)
        if (la==LPARENS || la==LBRACK || la==RBRACK) error(st)
        else if (la==EOF || la==RPARENS || la==RBRACK
          || op(tok) < op(la) || op(tok) <= op(la) && op(tok).assoc == LeftAssociative)
          reduce(st, 3, op(tok).asInstanceOf[BinaryOpSpec[Expression]].const(tok.img, t1, t2))
        else if (op(tok) > op(la) || op(tok) >= op(la) && op(tok).assoc == RightAssociative)
          shift(st)
        else error(st)

      case (tok@Token(_:OPERATORS,_)) :: Expr(t1) :: _ =>
        if (la.isInstanceOf[IDENT] || la.isInstanceOf[NUMBER] || la == LPARENS) shift(st) else error(st)

      case Token(RPARENS,_) :: Expr(t1) :: Token(LPARENS,_) :: _ if t1.isInstanceOf[Term] || t1.isInstanceOf[Formula] =>
        if (la==LPARENS || la.isInstanceOf[IDENT] || la.isInstanceOf[NUMBER]) error(st)
        else if (la==PRIME) ??? else reduce(st, 3, t1)

      case Token(RBRACK,_) :: Expr(t1:Program) :: Token(LBRACK,_) :: _ =>
        if (la==LBRACK || la.isInstanceOf[IDENT] || la.isInstanceOf[NUMBER]) error(st)
        else reduce(st, 3, t1)

      case Expr(t1) :: Token(LPARENS,_) :: _ if t1.isInstanceOf[Term] || t1.isInstanceOf[Formula] =>
        if (la.isInstanceOf[OPERATORS] || la == RPARENS) shift(st)
        else if (la==PRIME) ??? else error(st)

      case Expr(t1:Program) :: Token(LBRACK,_) :: _ =>
        if (la.isInstanceOf[OPERATORS] || la == RBRACK) shift(st)
        else error(st)

      case Token(LPARENS,_) :: _ =>
        if (la==LPARENS || la.isInstanceOf[IDENT] || la.isInstanceOf[NUMBER]) shift(st)
        else error(st)

      case Token(LBRACK,_) :: _ =>
        if (la==LBRACK || la.isInstanceOf[IDENT] || la.isInstanceOf[NUMBER]) shift(st)
        else error(st)

      case Token(IDENT(name),_) :: _ =>
        /*if (la == RPARENS || la.isInstanceOf[IDENT]) error(st)
        else*/ if (la==LPARENS) /*function/predicate*/??? else reduce(st, 1, Variable(name,None,Real))

      case Token(NUMBER(value),_) :: _ =>
        /*if (la.isInstanceOf[NUMBER] || la.isInstanceOf[IDENT] || la == LPARENS) error(st)
        else*/ reduce(st, 1, Number(BigDecimal(value)))

      // small stack cases
      case Expr(t) :: Nil =>
        if (la == EOF) accept(st, t)
        else if (la==LPARENS || la.isInstanceOf[IDENT] || la.isInstanceOf[NUMBER] || la.isInstanceOf[OPERATORS]) shift(st) //@todo or [ or <
        else error(st)

      case Nil =>
        if (la==LPARENS || la.isInstanceOf[IDENT]) shift(st) //@todo or [ or <
        else error(st)
    }
  }

  /** Shift to put the next input token la on the parser stack s. */
  private def shift(st: ParseState): ParseState = {
    val (s, (la :: rest)) = st
    require(la != EOF, "Cannot shift past end of file")
    (la :: s, rest)
  }

  /** Reduce the parser stack by reducing the consuming many items from the stack to the reduced item. */
  private def reduce(st: ParseState, consuming: Int, reduced: Item): ParseState = {
    val (s, input) = st
    (reduced :: s.drop(consuming), input)
  }
  private def reduce(st: ParseState, consuming: Int, reduced: Expression): ParseState = reduce(st, consuming, Expr(reduced))

  /** Accept the given parser result. */
  private def accept(st: ParseState, result: Expression): ParseState = {
    val (s, input) = st
    require(input == List(Token(EOF)), "Can only accept after all input has been read.\nRemaining input: " + input)
    require(s.length == 1, "Can only accept with one single result on the stack.\nRemaining stack: " + s)
    (Accept(result) :: Nil, input)
  }

  /** Error parsing the next input token la when in parser stack s.*/
  private def error(st: ParseState): ParseState = {
    val (s, input@(la :: rest)) = st
    if (true) throw new ParseException("Unexpected token cannot be parsed\nFound: " + la + "\nAfter: " + s.mkString(", "))
    (Error("Unexpected token cannot be parsed\nFound: " + la + "\nAfter: " + s.mkString(", ")) :: s, input)
  }

  /** The operator notation of the top-level operator of expr with opcode, precedence and associativity  */
  private[parser] def op(terminal: Terminal): OpSpec = OpSpec.op(terminal)
}
