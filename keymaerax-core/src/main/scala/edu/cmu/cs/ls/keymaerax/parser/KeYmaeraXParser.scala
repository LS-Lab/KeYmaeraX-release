/**
 * Differential Dynamic Logic parser for concrete KeYmaera X notation.
 * @author aplatzer
 * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981, 2015."
 */
package edu.cmu.cs.ls.keymaerax.parser

import scala.annotation.{switch, tailrec}
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
  import OpSpec.statementSemicolon

  def apply(input: String): Expression = parse(ExpressionKind, lexer(input))

  /** Lexer's token stream with first token at head. */
  type TokenStream = List[Token]

  /** Parser state consisting of expected syntactic kind to parse currently, the item stack, and remaining input. */
  sealed case class ParseState(kind: Kind, stack: Stack[Item], input: TokenStream)

  private def lexer(input: String): TokenStream = KeYmaeraXLexer(input)

  override def termParser: (String => Expression) =
    input => parse(TermKind, lexer(input)) match {
      case t: Term => t
      case e@_ => throw new ParseException("Input does not parse as a term but as " + e.kind + "\nInput: " + input + "\nParsed: " + e)
    }

  override def formulaParser: (String => Expression) =
    input => parse(FormulaKind, lexer(input)) match {
      case f: Formula => f
      case e@_ => throw new ParseException("Input does not parse as a formula but as " + e.kind + "\nInput: " + input + "\nParsed: " + e)
    }

  override def programParser: (String => Expression) =
    input => parse(ProgramKind, lexer(input)) match {
      case p: Program => p
      case e@_ => throw new ParseException("Input does not parse as a program but as " + e.kind + "\nInput: " + input + "\nParsed: " + e)
    }

  /*private*/ def parse(input: TokenStream): Expression = parse(ExpressionKind, input)

  /*private*/ def parse(kind: Kind, input: TokenStream): Expression = {
    require(input.endsWith(List(Token(EOF))), "token streams have to end in " + EOF)
    parseLoop(ParseState(kind, Bottom, input)).stack match {
      case Bottom :+ Accept(e) => e
      case context :+ Error(msg) => throw new ParseException(msg)
      case _ => throw new AssertionError("Parser terminated with unexpected stack")
    }
  }

  @tailrec
  private def parseLoop(st: ParseState): ParseState = st.stack match {
    case _ :+ (result: FinalItem) => st
    case _ => parseLoop(parseStep(st))
  }


  private def parseStep(st: ParseState): ParseState = {
    val ParseState(kind, s, input@(Token(la,_) :: rest)) = st
    // This table of LR Parser matches needs an entry for every prefix substring of the grammar.
    s match {
      // modalities
      case r :+ Token(LBOX,_) :+ Expr(p1:Program) :+ Token(RBOX,_) :+ Expr(f1:Formula) =>
        reduce(st, 4, OpSpec.sBox.const(PSEUDO.img, p1, f1), r)

      case r :+ Token(LDIA,_) :+ Expr(p1:Program) :+ Token(RDIA,_) :+ Expr(f1:Formula) =>
        reduce(st, 4, OpSpec.sDiamond.const(PSEUDO.img, p1, f1), r)


      //@note fixed during Stack top-reversal
      case r :+ Expr(p1: Program) :+ Expr(p2: Program) if statementSemicolon =>
        reduce(st, 2, op(st, SEMI).asInstanceOf[BinaryOpSpec[Program]].const(SEMI.img, p1, p2), r)

      // binary operators with precedence
      case r :+ Expr(t1) :+ (Token(tok:OPERATOR,_)) :+ Expr(t2) =>
        assert(op(st, tok).isInstanceOf[BinaryOpSpec[_]], "binary operator expected since others should have been reduced\nin " + s)
        if (la==LPAREN || la==LBRACE) error(st)
        else {
          val optok = op(st, tok)
          //@todo op(st, la) : Potential problem: st is not the right parser state for la
          if (la==EOF || la==RPAREN || la==RBRACE || la==RBOX /*||@todo la==RDIA or la==SEMI RDIA? */
            || optok < op(st, la)  || optok <= op(st, la)  && optok.assoc == LeftAssociative) {
            println("\tGOT: " + tok + "\t" + "LA: " + la + "\tAfter: " + s + "\tRemaining: " + input)
            val result = optok.asInstanceOf[BinaryOpSpec[Expression]].const(tok.img, t1, t2)
            if (statementSemicolon && result.isInstanceOf[AtomicProgram] && !(result.isInstanceOf[DifferentialProgram])) {if (la==SEMI) reduce(shift(st), 4, result, r) else error(st)}
            else reduce(st, 3, result, r)
          } else if (optok > op(st, la)  || optok >= op(st, la)  && optok.assoc == RightAssociative)
            shift(st)
          else error(st)
        }

      // special case unary operator
      case r :+ Token(TEST,_) :+ Expr(t1:Formula) =>
        if (la==SEMI || la==RBRACE || la==CHOICE || la==STAR) {
          val result = op(st, TEST).asInstanceOf[UnaryOpSpec[Expression]].const(TEST.img, t1)
          if (statementSemicolon) {if (la==SEMI) switch(reduce(shift(st), 3, result, r), ProgramKind) else error(st)}
          else switch(reduce(st, 2, result, r), ProgramKind)
        }
        else error(st)

      // unary operators
      case r :+ Token(tok:OPERATOR,_) :+ Expr(t1)  if op(st, tok).assoc==PrefixFormat =>
        assert(op(st, tok).isInstanceOf[UnaryOpSpec[_]], "only unary operators are currently allowed to have prefix format\nin " + s)
        if (firstExpression(la)) shift(st) // binary operator //@todo be more specific depending on kind of t1
        else if (la==EOF || la==RPAREN || la==RBRACE || la==RBOX /*||@todo la==RDIA or la==SEMI RDIA? */
          || followsTerm(la))
          reduce(st, 2, op(st, tok).asInstanceOf[UnaryOpSpec[Expression]].const(tok.img, t1), r)
        else error(st)

      // special case
      case _ :+ Token(TEST,_) =>
        if (firstFormula(la)) shift(switch(st, FormulaKind))
        else error(st)

      case _ :+ Token(tok:OPERATOR,_) if op(st, tok).assoc==PrefixFormat || tok==MINUS =>
        assert(op(st, tok).isInstanceOf[UnaryOpSpec[_]] || tok==MINUS, "only unary operators are currently allowed to have prefix format\nin " + s)
        if (firstExpression(la)) shift(st)
        else error(st)

      // special cases
      case r :+ Expr(x1:Variable) :+ Token(PRIME,_) =>
        reduce(st, 2, OpSpec.sDifferentialSymbol.const(PRIME.img, x1), r)

      case r :+ Token(LPAREN,_) :+ Expr(t1:Term) :+ Token(RPAREN,_) :+ Token(PRIME,_) =>
        reduce(st, 4, OpSpec.sDifferential.const(PRIME.img, t1), r)

      case r :+ Token(LPAREN,_) :+ Expr(f1:Formula) :+ Token(RPAREN,_) :+ Token(PRIME,_) =>
        reduce(st, 4, OpSpec.sDifferentialFormula.const(PRIME.img, f1), r)

      case _ :+ Expr(t1) :+ (tok@Token(op:OPERATOR,_)) if op != PRIME =>
        if (firstExpression(la)) shift(st) else error(st)

      // function/predicate symbols arity 0
      case r :+ Token(IDENT(name),_) :+ Token(LPAREN,_) :+ Token(RPAREN,_)  =>
        //@todo walk past LPAREN in r to disambiguate for cases like 1>0&((((((p(x+y))))))) but unclear for: ((((((p(x+y)))))))&1>0
        //@todo reduce outer RPAREN, LPAREN further first
        if (followsFormula(la) && !followsTerm(la)) reduce(st, 3, PredOf(Function(name, None, Unit, Bool), Nothing), r)
        else if (followsTerm(la) && !followsFormula(la)) reduce(st, 3, FuncOf(Function(name, None, Unit, Real), Nothing), r)
        else if (followsFormula(stackToken(r)) && !followsTerm(stackToken(r))) reduce(st, 3, PredOf(Function(name, None, Unit, Bool), Nothing), r)
        else if (followsTerm(stackToken(r)) && !followsFormula(stackToken(r))) reduce(st, 3, FuncOf(Function(name, None, Unit, Real), Nothing), r)
        else if (la==RPAREN) shift(st)
        else if (la==EOF) throw new ParseException("Ambiguous input\nFound: " + la + "\nAfter: " + s + "\nRemaining input: " + rest)
        else error(st)

      // function/predicate symbols arity>0
      case r :+ Token(IDENT(name),_) :+ Token(LPAREN,_) :+ Expr(t1:Term) :+ Token(RPAREN,_)  =>
        //@todo walk past LPAREN in r to disambiguate for cases like 1>0&((((((p(x+y))))))) but unclear for: ((((((p(x+y)))))))&1>0
        //@todo reduce outer RPAREN, LPAREN further first
        if (followsFormula(la) && !followsTerm(la)) reduce(st, 4, PredOf(Function(name, None, Real, Bool), t1), r)
        else if (followsTerm(la) && !followsFormula(la)) reduce(st, 4, FuncOf(Function(name, None, Real, Real), t1), r)
        else if (la==RPAREN) shift(st)
        else if (la==EOF) throw new ParseException("Ambiguous input\nFound: " + la + "\nAfter: " + s + "\nRemaining input: " + rest)
        else error(st)

      // function/predicate symbols arity 0 compactify superfluous brackets to enable disambiguation
      case r :+ Token(LPAREN,_) :+ (tok1@Token(IDENT(name),_)) :+ (tok2@Token(LPAREN,_)) :+ (tok3@Token(RPAREN,_)) :+ Token(RPAREN,_) =>
        reduce(st, 5, Bottom :+ tok1 :+ tok2 :+ tok3, r)

      // function/predicate symbols arity>0 compactify superfluous brackets to enable disambiguation
      case r :+ Token(LPAREN,_) :+ (tok1@Token(IDENT(name),_)) :+ (tok2@Token(LPAREN,_)) :+ Expr(t1:Term) :+ (tok3@Token(RPAREN,_)) :+ Token(RPAREN,_) =>
        reduce(st, 6, Bottom :+ tok1 :+ tok2 :+ Expr(t1) :+ tok3, r)

      // modalities
      case _ :+ Token(LBOX,_) :+ Expr(t1:Program) :+ Token(RBOX,_) =>
        if (firstFormula(la)) switch(shift(st), FormulaKind)
        else error(st)

      case _ :+ Token(LDIA,_) :+ Expr(t1:Program) :+ Token(RDIA,_) =>
        if (firstFormula(la)) switch(shift(st), FormulaKind)
        else error(st)

      // parentheses
      case r :+ Token(LPAREN,_) :+ Expr(t1) :+ Token(RPAREN,_) if t1.isInstanceOf[Term] || t1.isInstanceOf[Formula] =>
        /*if (la==LPAREN || la.isInstanceOf[IDENT] || la.isInstanceOf[NUMBER]) error(st)
        else*/ if (la==PRIME) shift(st) else reduce(st, 3, t1, r)

      case r :+ Token(LBRACE,_) :+ Expr(t1:Program) :+ Token(RBRACE,_) =>
        /*if (la==LBRACE || la.isInstanceOf[IDENT] || la.isInstanceOf[NUMBER]) error(st)
        else*/ reduce(st, 3, t1, r)

      case _ :+ Token(LPAREN,_) :+ Expr(t1) if t1.isInstanceOf[Term] || t1.isInstanceOf[Formula] =>
        if (followsExpression(t1, la)) shift(st)
        else error(st)

      case _ :+ Token(LBRACE,_) :+ Expr(t1:Program) =>
        if (followsProgram(la)) shift(st)
        else error(st)

      case _ :+ Token(LBOX,_) :+ Expr(t1) =>
        if (t1.isInstanceOf[Program] && followsProgram(la)) shift(st)
        else if (t1.isInstanceOf[Variable] && followsIdentifier(la)) shift(st)
        else error(st)

      case _ :+ Token(LDIA,_) :+ Expr(t1)  =>
        if (followsExpression(t1, la)) shift(st)
        else error(st)

      case _ :+ Token(LPAREN,_) =>
        if (firstFormula(la) /*|| firstTerm(la)*/ || la==RPAREN) shift(st)
        else error(st)

      case _ :+ Token(LBRACE,_) =>
        if (firstProgram(la) /*|| firstFormula(la) for predicationals*/) shift(switch(st, ProgramKind))
        else error(st)

      case _ :+ Token(LBOX,_) =>
        if (firstProgram(la)) switch(shift(st), ProgramKind)
        else error(st)

      case _ :+ Token(LDIA,_) =>
        if (firstProgram(la)) if (!firstTerm(la)) switch(shift(st), ProgramKind) else shift(st)
        else if (firstTerm(la)) shift(switch(st, TermKind))
        //if (firstProgram(la) || firstTerm(la)) shift(st)
        else error(st)

      // ordinary terminals
      case r :+ Token(IDENT(name),_) =>
        /*if (la == RPAREN || la.isInstanceOf[IDENT]) error(st)
        else*/ if (la==LPAREN) shift(st) else reduce(st, 1, Variable(name,None,Real), r)

      case r :+ Token(NUMBER(value),_) =>
        /*if (la.isInstanceOf[NUMBER] || la.isInstanceOf[IDENT] || la == LPAREN) error(st)
        else*/ reduce(st, 1, Number(BigDecimal(value)), r)


      // non-accepting expression
      case _ :+ _ :+ Expr(t) =>
        if (followsExpression(t, la)) shift(st)
        else error(st)

      // small stack cases
      case Bottom :+ Expr(t) =>
        if (la == EOF) accept(st, t)
        else if (followsExpression(t, la)) shift(st)
        else error(st)

      case Bottom =>
        if (firstExpression(la)) shift(st)
        else error(st)

      case _ =>
        throw new AssertionError("Incomplete parser missing an item, so does not yet know how to handle case.\nFound: " + la + "\nAfter: " + s)
    }
  }

  // stack helper

  /** Top terminal token from stack or EOF if the top item is not a token or the stack is empty. */
  private def stackToken(s: Stack[Item]): Terminal =
    if (!s.isEmpty && s.top.isInstanceOf[Token]) s.top.asInstanceOf[Token].tok else EOF

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
    else la==SEMI || la==CHOICE || la==STAR || la==RBRACE || la==COMMA) // from T in programs

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
    val ParseState(kind, s, (la :: rest)) = st
    require(la.tok != EOF, "Cannot shift past end of file")
    ParseState(kind, s :+ la, rest)
  }

  /**
   * Reduce the parser stack by reducing the consuming many items from the stack to the reduced item.
   * @param remainder Redundant parameter, merely for correctness checking.
   */
  private def reduce(st: ParseState, consuming: Int, reduced: Item, remainder: Stack[Item]): ParseState = {
    val ParseState(kind, s, input) = st
    ParseState(kind, s.drop(consuming) :+ reduced, input)
  } ensuring(r => r.stack.tail == remainder, "Expected remainder stack after consuming the indicated number of stack items.")

  private def reduce(st: ParseState, consuming: Int, reduced: Expression, remainder: Stack[Item]): ParseState = reduce(st, consuming, Expr(reduced), remainder)

  /**
   * Reduce the parser stack by reducing the consuming many items from the stack to the reduced item.
   * @param remainder Redundant parameter, merely for correctness checking.
   */
  private def reduce(st: ParseState, consuming: Int, reduced: Stack[Item], remainder: Stack[Item]): ParseState = {
    val ParseState(kind, s, input) = st
    ParseState(kind, s.drop(consuming) ++ reduced, input)
  } ensuring(r => r.stack.drop(reduced.length) == remainder, "Expected remainder stack after consuming the indicated number of stack items.")

  /** Accept the given parser result. */
  private def accept(st: ParseState, result: Expression): ParseState = {
    val ParseState(kind, s, input) = st
    require(input == List(Token(EOF)), "Can only accept after all input has been read.\nRemaining input: " + input)
    require(s.length == 1, "Can only accept with one single result on the stack.\nRemaining stack: " + s)
    ParseState(kind, Bottom :+ Accept(result), input)
  }

  /** Error parsing the next input token la when in parser stack s.*/
  private def error(st: ParseState): ParseState = {
    val ParseState(kind, s, input@(la :: rest)) = st
    if (true) throw new ParseException("Unexpected token cannot be parsed\nFound: " + la + "\nAfter: " + s)
    ParseState(kind, s :+ Error("Unexpected token cannot be parsed\nFound: " + la + "\nAfter: " + s), input)
  }

  /** Drop next input token la from consideration without shifting it to the parser stack s. */
  private def drop(st: ParseState): ParseState = {
    val ParseState(kind, s, (la :: rest)) = st
    require(la.tok != EOF, "Cannot drop end of file")
    ParseState(kind, s, rest)
  }

  /** Switch parser to parse the given kind from now on. */
  private def switch(st: ParseState, kind: Kind): ParseState = ParseState(kind, st.stack, st.input)


  // operator precedence lookup

  /** If the stack starts with an expr item, so has been reduced already, it can't be a prefix operator */
  private def isNotPrefix(st: KeYmaeraXParser.ParseState): Boolean = st.stack match {
    case _ :+ Expr(_) :+ Token(_:OPERATOR, _)  :+ _ => true
    case _ => false
  }

  private def isFormula(st: KeYmaeraXParser.ParseState): Boolean = st.kind==FormulaKind || (st.stack match {
    case _ :+ Expr(_:Formula) => true
    case _ => false
  })

  // this is a terrible approximation
  private def isProgram(st: KeYmaeraXParser.ParseState): Boolean = st.kind==ProgramKind || (st.stack match {
    case _ :+ Expr(_:Program) => true
    case _ :+ Token(LBRACE,_) => true
    case _ :+ Token(LBOX,_) => true
    case _ :+ Token(LBRACE,_) :+ _ => true
    case _ :+ Token(LBOX,_) :+ _ => true
    case _ :+ Expr(_:Program) :+ _ => true
    case _ => false
  })

  private def isVariable(st: KeYmaeraXParser.ParseState): Boolean = st.stack match {
    case _ :+ Expr(_:Variable) => true
    case _ => false
  }

  private def isDifferentialSymbol(st: KeYmaeraXParser.ParseState): Boolean = st.stack match {
    case _ :+ Expr(_:DifferentialSymbol) => true
    case _ => false
  }

  import OpSpec._

  /** The operator notation of the top-level operator of expr with opcode, precedence and associativity  */
  private[parser] def op(st: KeYmaeraXParser.ParseState, tok: Terminal): OpSpec = {
    (tok: @switch) match {
      //@note could almost(!) replace by reflection to search through all OpSpec and check their images.
      // terms
      case sDotTerm.op => sDotTerm
      //case sNothing.opcode => sNothing
      case sAnything.op => sAnything
      //case t: Variable => sVariable
      //case t: Number => sNumber
      //case t: FuncOf => sFuncOf
      case sDifferential.op => if (isVariable(st)) sDifferential
      else if (isFormula(st)) sDifferentialFormula
      else sDifferential
      //case t: Pair => sPair
      case sMinus.op => if (isNotPrefix(st)) sMinus else sNeg
      case sPower.op => sPower
      case sTimes.op => if (isProgram(st)) sLoop else sTimes
      case sDivide.op => sDivide
      case sPlus.op => sPlus

      // formulas
      case sDotFormula.op => sDotFormula
      case sTrue.op => sTrue
      case sFalse.op => sFalse
      //case f: PredOf => sPredOf
      //case f: PredicationalOf => sPredicationalOf
      //case f: DifferentialFormula => sDifferentialFormula
      case sEqual.op => if (isProgram(st)) sAtomicODE else sEqual
      case sNotEqual.op => sNotEqual
      case sGreaterEqual.op => sGreaterEqual
      case sGreater.op => sGreater
      case sLessEqual.op => sLessEqual
      case sLess.op => sLess
      case sForall.op => sForall
      case sExists.op => sExists
      //      case f: Box => sBox
      //      case f: Diamond => sDiamond
      case sNot.op => sNot
      case sAnd.op => if (isProgram(st)) sODESystem else sAnd
      case sOr.op => sOr
      case sImply.op => sImply
      case sRevImply.op => sRevImply
      case sEquiv.op => sEquiv

      // programs
      //case p: ProgramConst => sProgramConst
      //case p: DifferentialProgramConst => sDifferentialProgramConst
      case sAssign.op => if (isDifferentialSymbol(st)) sDiffAssign else sAssign
      //      case p: AssignAny => sAssignAny
      case sTest.op => sTest
      //      case p: ODESystem => sODESystem
      //      case p: AtomicODE => sAtomicODE
      case sDifferentialProduct.op => sDifferentialProduct
      //      case sLoop.op => sLoop
      case sCompose.op => sCompose
      case sChoice.op => sChoice

      //case
      case sEOF.op => sEOF
    }
  } ensuring(r => r.op == tok && r.opcode == tok.img, "OpSpec's opcode coincides with expected token " + tok)


}
