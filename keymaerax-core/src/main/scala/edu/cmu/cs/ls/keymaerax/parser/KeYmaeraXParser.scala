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
 * @see doc/dL-grammar.md
 */
object KeYmaeraXParser extends Parser {
  /** The operator notation of the top-level operator of expr with opcode, precedence and associativity  */
  import OpSpec.op
  import OpSpec.statementSemicolon

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
      case _ => throw new AssertionError("Parser terminated with unexpected stack")
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
      // modalities
      case Expr(f1:Formula) :: Token(RBOX,_) :: Expr(p1:Program) :: Token(LBOX,_) :: r =>
        reduce(st, 4, OpSpec.sBox.const(PSEUDO.img, p1, f1), r)

      case Expr(f1:Formula) :: Token(RDIA,_) :: Expr(p1:Program) :: Token(LDIA,_) :: r =>
        reduce(st, 4, OpSpec.sDiamond.const(PSEUDO.img, p1, f1), r)


      //
      case Expr(p1: Program) :: Expr(p2: Program) :: r if statementSemicolon =>
        reduce(st, 2, op(st, SEMI).asInstanceOf[BinaryOpSpec[Program]].const(SEMI.img, p1, p2), r)

      // binary operators with precedence
      case Expr(t2) :: (Token(tok:OPERATOR,_)) :: Expr(t1) :: r =>
        assert(op(st, tok).isInstanceOf[BinaryOpSpec[_]], "binary operator expected since others should have been reduced\nin " + s)
        if (la==LPAREN || la==LBRACE) error(st)
        else {
          val optok = op(st, tok)
          //@todo op(st, la) : Potential problem: st is not the right parser state for la
          if (la==EOF || la==RPAREN || la==RBRACE || la==RBOX /*||@todo la==RDIA or la==SEMI RDIA? */
            || optok < op(st, la)  || optok <= op(st, la)  && optok.assoc == LeftAssociative) {
            val result = optok.asInstanceOf[BinaryOpSpec[Expression]].const(tok.img, t1, t2)
            if (statementSemicolon && result.isInstanceOf[AtomicProgram] && !(result.isInstanceOf[DifferentialProgram])) {if (la==SEMI) reduce(shift(st), 4, result, r) else error(st)}
            else reduce(st, 3, result, r)
          } else if (optok > op(st, la)  || optok >= op(st, la)  && optok.assoc == RightAssociative)
            shift(st)
          else error(st)
        }

      // unary operators
      case Expr(t1) :: (Token(tok:OPERATOR,_)) :: r if op(st, tok).assoc==PrefixFormat =>
        assert(op(st, tok).isInstanceOf[UnaryOpSpec[_]], "only unary operators are currently allowed to have prefix format\nin " + s)
        if (firstExpression(la)) shift(st) // binary operator //@todo be more specific depending on kind of t1
        else if (la==EOF || la==RPAREN || la==RBRACE || la==RBOX /*||@todo la==RDIA or la==SEMI RDIA? */
          || followsTerm(la))
          reduce(st, 2, op(st, tok).asInstanceOf[UnaryOpSpec[Expression]].const(tok.img, t1), r)
        else error(st)

      case (Token(tok:OPERATOR,_)) :: _ if op(st, tok).assoc==PrefixFormat || tok==MINUS =>
        assert(op(st, tok).isInstanceOf[UnaryOpSpec[_]] || tok==MINUS, "only unary operators are currently allowed to have prefix format\nin " + s)
        if (firstExpression(la)) shift(st)
        else error(st)

      // special cases
      case Token(PRIME,_) :: Expr(x1:Variable) :: r =>
        reduce(st, 2, OpSpec.sDifferentialSymbol.const(PRIME.img, x1), r)

      case Token(PRIME,_) :: Token(RPAREN,_) :: Expr(t1:Term) :: Token(LPAREN,_) :: r =>
        reduce(st, 4, OpSpec.sDifferential.const(PRIME.img, t1), r)

      case Token(PRIME,_) :: Token(RPAREN,_) :: Expr(f1:Formula) :: Token(LPAREN,_) :: r =>
        reduce(st, 4, OpSpec.sDifferentialFormula.const(PRIME.img, f1), r)

      case (tok@Token(op:OPERATOR,_)) :: Expr(t1) :: _ if op != PRIME =>
        if (firstExpression(la)) shift(st) else error(st)

      // function/predicate symbols arity 0
      case Token(RPAREN,_) :: Token(LPAREN,_) :: Token(IDENT(name),_) :: r =>
        //@todo walk past LPAREN in r to disambiguate for cases like 1>0&((((((p(x+y))))))) but unclear for: ((((((p(x+y)))))))&1>0
        //@todo reduce outer RPAREN, LPAREN further first
        if (followsFormula(la)) reduce(st, 3, PredOf(Function(name, None, Unit, Bool), Nothing), r)
        else if (followsTerm(la)) reduce(st, 3, FuncOf(Function(name, None, Unit, Real), Nothing), r)
        else if (followsFormula(stackToken(r))) reduce(st, 3, PredOf(Function(name, None, Unit, Bool), Nothing), r)
        else if (followsTerm(stackToken(r))) reduce(st, 3, FuncOf(Function(name, None, Unit, Real), Nothing), r)
        else if (la==RPAREN) shift(st)
        else if (la==EOF) throw new ParseException("Ambiguous input\nFound: " + la + "\nAfter: " + s.reverse.mkString(", ") + "\nRemaining input: " + rest)
        else error(st)

      // function/predicate symbols arity>0
      case Token(RPAREN,_) :: Expr(t1:Term) :: Token(LPAREN,_) :: Token(IDENT(name),_) :: r =>
        //@todo walk past LPAREN in r to disambiguate for cases like 1>0&((((((p(x+y))))))) but unclear for: ((((((p(x+y)))))))&1>0
        //@todo reduce outer RPAREN, LPAREN further first
        if (followsFormula(la)) reduce(st, 4, PredOf(Function(name, None, Real, Bool), t1), r)
        else if (followsTerm(la)) reduce(st, 4, FuncOf(Function(name, None, Real, Real), t1), r)
        else if (la==RPAREN) shift(st)
        else if (la==EOF) throw new ParseException("Ambiguous input\nFound: " + la + "\nAfter: " + s.reverse.mkString(", ") + "\nRemaining input: " + rest)
        else error(st)

      // function/predicate symbols arity 0 compactify superfluous brackets to enable disambiguation
      case Token(RPAREN,_) :: (tok3@Token(RPAREN,_)) :: (tok2@Token(LPAREN,_)) :: (tok1@Token(IDENT(name),_)) :: Token(LPAREN,_) :: r =>
        reduce(st, 5, List(tok3, tok2, tok1), r)

      // function/predicate symbols arity>0 compactify superfluous brackets to enable disambiguation
      case Token(RPAREN,_) :: (tok3@Token(RPAREN,_)) :: Expr(t1:Term) :: (tok2@Token(LPAREN,_)) :: (tok1@Token(IDENT(name),_)) :: Token(LPAREN,_) :: r =>
        reduce(st, 6, List(tok3, Expr(t1), tok2, tok1), r)

      // modalities
      case Token(RBOX,_) :: Expr(t1:Program) :: Token(LBOX,_) :: _ =>
        if (firstFormula(la)) shift(st)
        else error(st)

      case Token(RDIA,_) :: Expr(t1:Program) :: Token(LDIA,_) :: _ =>
        if (firstFormula(la)) shift(st)
        else error(st)

      // parentheses
      case Token(RPAREN,_) :: Expr(t1) :: Token(LPAREN,_) :: r if t1.isInstanceOf[Term] || t1.isInstanceOf[Formula] =>
        /*if (la==LPAREN || la.isInstanceOf[IDENT] || la.isInstanceOf[NUMBER]) error(st)
        else*/ if (la==PRIME) shift(st) else reduce(st, 3, t1, r)

      case Token(RBRACE,_) :: Expr(t1:Program) :: Token(LBRACE,_) :: r =>
        /*if (la==LBRACE || la.isInstanceOf[IDENT] || la.isInstanceOf[NUMBER]) error(st)
        else*/ reduce(st, 3, t1, r)

      case Expr(t1) :: Token(LPAREN,_) :: _ if t1.isInstanceOf[Term] || t1.isInstanceOf[Formula] =>
        if (followsExpression(t1, la)) shift(st)
        else error(st)

      case Expr(t1:Program) :: Token(LBRACE,_) :: _ =>
        if (followsProgram(la)) shift(st)
        else error(st)

      case Expr(t1) :: Token(LBOX,_) :: _ =>
        if (t1.isInstanceOf[Program] && followsProgram(la)) shift(st)
        else if (t1.isInstanceOf[Variable] && followsIdentifier(la)) shift(st)
        else error(st)

      case Expr(t1) :: Token(LDIA,_) :: _ =>
        if (followsExpression(t1, la)) shift(st)
        else error(st)

      case Token(LPAREN,_) :: _ =>
        if (firstFormula(la) /*|| firstTerm(la)*/ || la==RPAREN) shift(st)
        else error(st)

      case Token(LBRACE,_) :: _ =>
        if (firstProgram(la) /*|| firstFormula(la) for predicationals*/) shift(st)
        else error(st)

      case Token(LBOX|LDIA,_) :: _ =>
        if (firstProgram(la)) shift(st)
        else error(st)

      // ordinary terminals
      case Token(IDENT(name),_) :: r =>
        /*if (la == RPAREN || la.isInstanceOf[IDENT]) error(st)
        else*/ if (la==LPAREN) shift(st) else reduce(st, 1, Variable(name,None,Real), r)

      case Token(NUMBER(value),_) :: r =>
        /*if (la.isInstanceOf[NUMBER] || la.isInstanceOf[IDENT] || la == LPAREN) error(st)
        else*/ reduce(st, 1, Number(BigDecimal(value)), r)


      // non-accepting expression
      case Expr(t) :: _ :: _ =>
        if (followsExpression(t, la)) shift(st)
        else error(st)

      // small stack cases
      case Expr(t) :: Nil =>
        if (la == EOF) accept(st, t)
        else if (followsExpression(t, la)) shift(st)
        else error(st)

      case Nil =>
        if (firstExpression(la)) shift(st)
        else error(st)

      case _ =>
        throw new AssertionError("Incomplete parser missing an item, so does not yet know how to handle case.\nFound: " + la + "\nAfter: " + s.reverse.mkString(", "))
    }
  }

  // stack helper

  /** Top terminal token from stack or EOF if the top item is not a token or the stack is empty. */
  private def stackToken(s: Stack): Terminal =
    if (s.length>0 && s.head.isInstanceOf[Token]) s.head.asInstanceOf[Token].tok else EOF

  // FIRST lookahead sets

  /** Is la the beginning of a new expression? */
  private def firstExpression(la: Terminal): Boolean = firstFormula(la) || firstProgram(la) /*|| firstTerm(la) */

  /** First(Term): Is la the beginning of a new term? */
  private def firstTerm(la: Terminal): Boolean = la.isInstanceOf[IDENT] || la.isInstanceOf[NUMBER] ||
    la==MINUS || la==LPAREN || la==DOT

  /** First(Formula): Is la the beginning of a new formula? */
  private def firstFormula(la: Terminal): Boolean = firstTerm(la) || /*la.isInstanceOf[IDENT] ||*/
    la==NOT || la==FORALL || la==EXISTS || la==LBOX || la==LDIA /*|| la==LPAREN */

  /** First(Program): Is la the beginning of a new program? */
  private def firstProgram(la: Terminal): Boolean = la.isInstanceOf[IDENT] || la==TEST || la==LBRACE

  // FOLLOW sets

  /** Follow(Formula): Can la follow after a formula? */
  private def followsFormula(la: Terminal): Boolean = la==AMP || la==OR || la==IMPLY || la==REVIMPLY || la==EQUIV
    /*@todo || la=RBRACE from predicationals */

  /** Follow(Term): Can la follow after a term? */
  private def followsTerm(la: Terminal): Boolean = la==RPAREN ||
    la==POWER || la==STAR || la==SLASH || la==PLUS || la==MINUS ||  // from T in terms
    la==EQ || la==NOTEQ || la==GREATEREQ || la==RDIA || la==LESSEQ || la==LDIA || // from T in formulas
    followsFormula(la) ||
    (if (statementSemicolon) la==SEMI || la==RBRACE || la==AMP
    else la==SEMI || la==CHOICE || la==STAR || la==RBRACE ) // from T in programs

  /** Follow(Program): Can la follow after a program? */
  private def followsProgram(la: Terminal): Boolean = la==RBRACE || la==CHOICE || la==STAR/**/ ||
    (if (statementSemicolon) firstProgram(la) else la==SEMI)  ||
    la==RBOX || la==RDIA ||  // from P in programs
    la==COMMA || la==AMP     // from D in differential programs

  /** Follow(kind(expr)): Can la follow an expression of the kind of expr? */
  private def followsExpression(expr: Expression, la: Terminal): Boolean = expr match {
    case _: Variable => followsIdentifier(la)
    case _: Term => followsTerm(la)
    case _: Formula => followsFormula(la)
    case _: Program => followsProgram(la)
  }

  /** Follow(Identifier): Can la follow after an identifier? */
  private def followsIdentifier(la: Terminal): Boolean = followsTerm(la) ||
    la==LPAREN || la==PRIME ||
    la==ASSIGN || la==ASSIGNANY

  // parser actions

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

  /**
   * Reduce the parser stack by reducing the consuming many items from the stack to the reduced item.
   * @param remainder Redundant parameter, merely for correctness checking.
   */
  private def reduce(st: ParseState, consuming: Int, reduced: Stack, remainder: Stack): ParseState = {
    val (s, input) = st
    (reduced ++ s.drop(consuming), input)
  } ensuring(r => r._1.drop(reduced.length) == remainder, "Expected remainder stack after consuming the indicated number of stack items.")

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
    require(la.tok != EOF, "Cannot drop end of file")
    (s, rest)
  }

}
