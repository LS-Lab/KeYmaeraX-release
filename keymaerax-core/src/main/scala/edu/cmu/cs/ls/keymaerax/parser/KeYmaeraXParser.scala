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
case class Token(tok: Terminal, loc: Location = UnknownLocation) extends Item {
  override def toString = tok.toString
}
/** Expressions that are partially parsed on the parser item stack. */
case class Expr(expr: Expression) extends Item {
  override def toString = expr.toString
}
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
    //@note reverse notation of :: for match since s is a stack represented as a list with top at head
    // This table of LR Parser matches needs an entry for every prefix substring of the grammar.
    s match {
      // binary operators with precedence
      case Expr(t2) :: (Token(tok:OPERATOR,_)) :: Expr(t1) :: r =>
        assert(op(st, tok).isInstanceOf[BinaryOpSpec[_]], "binary operator expected since others should have been reduced\nin " + s)
        if (la==LPAREN || la==LBRACK || la==RBRACK) error(st)
        else {
          val optok = op(st, tok)
          //@todo op(st, la) : Potential problem: st is not the right parser state for la
          if (la==EOF || la==RPAREN || la==RBRACK || la==RBOX /*||@todo la==RDIA or la==COMPOSE RDIA? */
            || optok < op(st, la)  || optok <= op(st, la)  && optok.assoc == LeftAssociative)
            reduce(st, 3, optok.asInstanceOf[BinaryOpSpec[Expression]].const(tok.img, t1, t2), r)
          else if (optok > op(st, la)  || optok >= op(st, la)  && optok.assoc == RightAssociative)
            shift(st)
          else error(st)
        }

      // unary operators
      case Expr(t1) :: (Token(tok:OPERATOR,_)) :: r if op(st, tok).assoc==PrefixFormat =>
        assert(op(st, tok).isInstanceOf[UnaryOpSpec[_]], "only unary operators are currently allowed to have prefix format\nin " + s)
        if (beginExpression(la)) shift(st) // binary operator
        else if (la==EOF || la==RPAREN || la==RBRACK || la==RBOX /*||@todo la==RDIA or la==COMPOSE RDIA? */)
          reduce(st, 2, op(st, tok).asInstanceOf[UnaryOpSpec[Expression]].const(tok.img, t1), r)
        else error(st)

      case (Token(tok:OPERATOR,_)) :: _ if op(st, tok).assoc==PrefixFormat =>
        assert(op(st, tok).isInstanceOf[UnaryOpSpec[_]], "only unary operators are currently allowed to have prefix format\nin " + s)
        if (beginExpression(la)) shift(st)
        else error(st)

      // special cases
      case Token(PRIME,_) :: Expr(x1:Variable) :: r =>
        reduce(st, 2, OpSpec.sDifferentialSymbol.const(PRIME.img, x1), r)

      case Token(PRIME,_) :: Token(RPAREN,_) :: Expr(t1:Term) :: Token(LPAREN,_) :: r =>
        reduce(st, 4, OpSpec.sDifferential.const(PRIME.img, t1), r)

      case Token(PRIME,_) :: Token(RPAREN,_) :: Expr(f1:Formula) :: Token(LPAREN,_) :: r =>
        reduce(st, 4, OpSpec.sDifferentialFormula.const(PRIME.img, f1), r)

      case (tok@Token(op:OPERATOR,_)) :: Expr(t1) :: _ if op != PRIME =>
        if (beginExpression(la)) shift(st) else error(st)

      // modalities
      case Expr(f1:Formula) :: Token(RBOX,_) :: Expr(p1:Program) :: Token(LBOX,_) :: r =>
        reduce(st, 4, OpSpec.sBox.const(PSEUDO.img, p1, f1), r)

      case Expr(f1:Formula) :: Token(RDIA,_) :: Expr(p1:Program) :: Token(LDIA,_) :: r =>
        reduce(st, 4, OpSpec.sDiamond.const(PSEUDO.img, p1, f1), r)

      // function/predicate symbols arity 0
      case Token(RPAREN,_) :: Token(LPAREN,_) :: Token(IDENT(name),_) :: r =>
        //@todo walk past LPAREN in r to disambiguate for cases like 1>0&((((((p(x+y))))))) but unclear for: ((((((p(x+y)))))))&1>0
        //@todo reduce outer RPAREN, LPAREN further first
        if (formulaFollows(la)) reduce(st, 3, PredOf(Function(name, None, Unit, Bool), Nothing), r)
        else if (termFollows(la)) reduce(st, 3, FuncOf(Function(name, None, Unit, Real), Nothing), r)
        else if (la==RPAREN) throw new AssertionError("Problematic case not implemented yet\nFound: " + la + "\nAfter: " + s.reverse.mkString(", ") + "\nRemaining input: " + rest)
        else error(st)

      // function/predicate symbols arity>0
      case Token(RPAREN,_) :: Expr(t1:Term) :: Token(LPAREN,_) :: Token(IDENT(name),_) :: r =>
        //@todo walk past LPAREN in r to disambiguate for cases like 1>0&((((((p(x+y))))))) but unclear for: ((((((p(x+y)))))))&1>0
        //@todo reduce outer RPAREN, LPAREN further first
        if (formulaFollows(la)) reduce(st, 4, PredOf(Function(name, None, Real, Bool), t1), r)
        else if (termFollows(la)) reduce(st, 4, FuncOf(Function(name, None, Real, Real), t1), r)
        else if (la==RPAREN) throw new AssertionError("Problematic case not implemented yet\nFound: " + la + "\nAfter: " + s.reverse.mkString(", ") + "\nRemaining input: " + rest)
        else error(st)

      // parentheses
      case Token(RBOX,_) :: Expr(t1:Program) :: Token(LBOX,_) :: _ =>
        if (beginExpression(la)) shift(st)
        else error(st)

      case Token(RDIA,_) :: Expr(t1:Program) :: Token(LDIA,_) :: _ =>
        if (beginExpression(la)) shift(st)
        else error(st)

      case Token(RPAREN,_) :: Expr(t1) :: Token(LPAREN,_) :: r if t1.isInstanceOf[Term] || t1.isInstanceOf[Formula] =>
        if (la==LPAREN || la.isInstanceOf[IDENT] || la.isInstanceOf[NUMBER]) error(st)
        else if (la==PRIME) shift(st) else reduce(st, 3, t1, r)

      case Token(RBRACK,_) :: Expr(t1:Program) :: Token(LBRACK,_) :: r =>
        if (la==LBRACK || la.isInstanceOf[IDENT] || la.isInstanceOf[NUMBER]) error(st)
        else reduce(st, 3, t1, r)

      case Expr(t1) :: Token(LPAREN,_) :: _ if t1.isInstanceOf[Term] || t1.isInstanceOf[Formula] =>
        if (la.isInstanceOf[OPERATOR] || la == RPAREN) shift(st)
        else error(st)

      case Expr(t1:Program) :: Token(LBRACK,_) :: _ =>
        if (la.isInstanceOf[OPERATOR] || la == RBRACK) shift(st)
        else error(st)

      case Expr(t1) :: Token(LBOX,_) :: _ =>
        if (la.isInstanceOf[OPERATOR] || la == RBOX) shift(st)
        else error(st)

      case Expr(t1) :: Token(LDIA,_) :: _ =>
        if (la.isInstanceOf[OPERATOR] || la == RDIA) shift(st)
        else error(st)

      case Token(LPAREN,_) :: _ =>
        if (beginExpression(la) || la==RPAREN) shift(st)
        else error(st)

      case Token(LBRACK,_) :: _ =>
        if (la==LBRACK || la.isInstanceOf[IDENT] || la.isInstanceOf[NUMBER] || la==TEST) shift(st)
        else error(st)

      case Token(LBOX|LDIA,_) :: _ =>
        if (la==LBRACK || la.isInstanceOf[IDENT] || la.isInstanceOf[NUMBER] || la==TEST) shift(st)
        else error(st)

      // ordinary terminals
      case Token(IDENT(name),_) :: r =>
        /*if (la == RPAREN || la.isInstanceOf[IDENT]) error(st)
        else*/ if (la==LPAREN) shift(st) else reduce(st, 1, Variable(name,None,Real), r)

      case Token(NUMBER(value),_) :: r =>
        /*if (la.isInstanceOf[NUMBER] || la.isInstanceOf[IDENT] || la == LPAREN) error(st)
        else*/ reduce(st, 1, Number(BigDecimal(value)), r)


      // small stack cases
      case Expr(t) :: Nil =>
        if (la == EOF) accept(st, t)
        else if (la.isInstanceOf[OPERATOR]) shift(st)
        else error(st)

      case Expr(t) :: _ :: _ =>
        if (la.isInstanceOf[OPERATOR]) shift(st)
        else error(st)

      case Nil =>
        if (beginExpression(la)) shift(st)
        else error(st)

      case _ =>
        throw new AssertionError("Incomplete parser does not yet know how to handle case.\nFound: " + la + "\nAfter: " + s.reverse.mkString(", "))
    }
  }

  /** Is la the beginning of a new expression? */
  private def beginExpression(la: Terminal): Boolean = la==LPAREN || la==LBRACK || la==LBOX || la==LDIA ||
    la.isInstanceOf[IDENT] || la.isInstanceOf[NUMBER] ||
    la==MINUS

  private def formulaFollows(la: Terminal): Boolean = la==AND || la==OR || la==IMPLY || la==REVIMPLY || la==EQUIV

  private def termFollows(la: Terminal): Boolean = la==PLUS || la==MINUS || la==STAR || la==SLASH || la==POWER ||
    la==EQ || la==NOTEQ || la==LESSEQ || la==LDIA || la==GREATEREQ || la==RDIA

  /** Shift to put the next input token la on the parser stack s. */
  private def shift(st: ParseState): ParseState = {
    val (s, (la :: rest)) = st
    require(la.tok != EOF, "Cannot shift past end of file")
    (la :: s, rest)
  }

  /**
   * Reduce the parser stack by reducing the consuming many items from the stack to the reduced item.
   * @param remainder Redundant parameter, merely for correctness checking.
   */
  private def reduce(st: ParseState, consuming: Int, reduced: Item, remainder: Stack): ParseState = {
    val (s, input) = st
    (reduced :: s.drop(consuming), input)
  } ensuring(r => r._1.tail == remainder, "Expected remainder stack after consuming the indicated number of stack items.")

  private def reduce(st: ParseState, consuming: Int, reduced: Expression, remainder: Stack): ParseState = reduce(st, consuming, Expr(reduced), remainder)

  /** Accept the given parser result. */
  private def accept(st: ParseState, result: Expression): ParseState = {
    val (s, input) = st
    require(input == List(Token(EOF)), "Can only accept after all input has been read.\nRemaining input: " + input)
    require(s.length == 1, "Can only accept with one single result on the stack.\nRemaining stack: " + s.reverse.mkString(", "))
    (Accept(result) :: Nil, input)
  }

  /** Error parsing the next input token la when in parser stack s.*/
  private def error(st: ParseState): ParseState = {
    val (s, input@(la :: rest)) = st
    if (true) throw new ParseException("Unexpected token cannot be parsed\nFound: " + la + "\nAfter: " + s.reverse.mkString(", "))
    (Error("Unexpected token cannot be parsed\nFound: " + la + "\nAfter: " + s.reverse.mkString(", ")) :: s, input)
  }

  /** Drop next input token la from consideration without shifting it to the parser stack s. */
  private def drop(st: ParseState): ParseState = {
    val (s, (la :: rest)) = st
    require(la != EOF, "Cannot drop end of file")
    (s, rest)
  }

  /** The operator notation of the top-level operator of expr with opcode, precedence and associativity  */
  private[parser] def op(st: ParseState, terminal: Terminal): OpSpec = OpSpec.op(st, terminal)
}
