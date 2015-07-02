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
case class Error(msg: String, loc: Location, st: String) extends FinalItem


/**
 * KeYmaera X parser.
 * Created by aplatzer on 6/7/15.
 * @author aplatzer
 * @see doc/dL-grammar.md
 */
object KeYmaeraXParser extends Parser {
  import OpSpec.statementSemicolon

  private val immediateError = true
  def apply(input: String): Expression = parse(KeYmaeraXLexer.inMode(input, ExpressionMode()))

  /** Lexer's token stream with first token at head. */
  type TokenStream = List[Token]

  /** Parser state consisting of expected syntactic kind to parse currently, the item stack, and remaining input. */
  sealed case class ParseState(stack: Stack[Item], input: TokenStream) {
    /** Lookahead location of this parser state */
    private[parser] def location: Location = input.head.loc
    override def toString: String = "ParseState(" + stack + "  <|>  " + input.mkString(", ") +")"
  }

  override def termParser: (String => Term) =
    input => apply(input) match {
      case t: Term => t
      case e@_ => throw new ParseException("Input does not parse as a term but as " + e.kind + "\nInput: " + input + "\nParsed: " + e, UnknownLocation, e.toString)
    }

  override def formulaParser: (String => Formula) =
    input => elaborate(eofState, OpSpec.sNone, FormulaKind, apply(input)) match {
      case f: Formula => f
      case e@_ => throw new ParseException("Input does not parse as a formula but as " + e.kind + "\nInput: " + input + "\nParsed: " + e, UnknownLocation, e.toString)
    }

  private[parser] def formulaTokenParser: (TokenStream => Formula) =
    input => elaborate(eofState, OpSpec.sNone, FormulaKind, parse(input)) match {
      case f: Formula => f
      case e@_ => throw new ParseException("Input does not parse as a formula but as " + e.kind + "\nInput: " + input + "\nParsed: " + e, UnknownLocation, e.toString)
    }

  override def programParser: (String => Program) =
    input => elaborate(eofState, OpSpec.sNone, ProgramKind, apply(input)) match {
      case p: Program => p
      case e@_ => throw new ParseException("Input does not parse as a program but as " + e.kind + "\nInput: " + input + "\nParsed: " + e, UnknownLocation, e.toString)
    }

  override def differentialProgramParser: (String => DifferentialProgram) =
    input => elaborate(eofState, OpSpec.sNone, DifferentialProgramKind, apply(input)) match {
      case p: DifferentialProgram => p
      case e@_ => throw new ParseException("Input does not parse as a program but as " + e.kind + "\nInput: " + input + "\nParsed: " + e, UnknownLocation, e.toString)
    }

  private val eofState = ParseState(Bottom, List(Token(EOF, UnknownLocation)))

  /*private[core]*/ def parse(input: TokenStream): Expression = {
    require(input.endsWith(List(Token(EOF))), "token streams have to end in " + EOF)
    parseLoop(ParseState(Bottom, input)).stack match {
      case Bottom :+ Accept(e) => e
      case context :+ Error(msg, loc, st) => throw new ParseException(msg, loc, st)
      case _ => throw new AssertionError("Parser terminated with unexpected stack")
    }
  }

  @tailrec
  private def parseLoop(st: ParseState): ParseState = st.stack match {
    case _ :+ (result: FinalItem) => st
    case _ => parseLoop(parseStep(st))
  }

  // elaboration based on expected types

  /** Elaborate e to the expected kind of a part of op by lifting defaulted types as needed or return None. */
  private def elaboratable(kind: Kind, e: Expression): Option[Expression] = if (e.kind==kind) Some(e) else e match {
    // lift misclassified defaulted function application to predicate application when required by context type.
    case FuncOf(f, t) if kind==FormulaKind => Some(PredOf(Function(f.name,f.index,f.domain,Bool), t))
    // lift misclassified defaulted differential program constant
    case x: Variable if kind==DifferentialProgramKind && x.index==None => Some(DifferentialProgramConst(x.name))
    // lift misclassified defaulted program constant
    case x: Variable if kind==ProgramKind && x.index==None => Some(ProgramConst(x.name))
    // lift misclassified defaulted differential equation
    case Equal(xp:DifferentialSymbol, e) if kind==DifferentialProgramKind || kind==ProgramKind => Some(AtomicODE(xp, e))
    // lift misclassified defaulted differential equation
    case And(Equal(xp:DifferentialSymbol, e), h) if kind==DifferentialProgramKind || kind==ProgramKind => Some(ODESystem(AtomicODE(xp, e), h))
    // lift differential equations without evolution domain constraints to ODESystems
    case ode: DifferentialProgram if ode.kind==DifferentialProgramKind && kind==ProgramKind => Some(ODESystem(ode, True))
    case _ => None
  }

  /** Elaborate e to the expected kind of a part of op by lifting defaulted types as needed or throw exception. */
  private def elaborate(st: ParseState, op: OpSpec, kind: Kind, e: Expression): Expression = elaboratable(kind, e) match {
    case Some(e) => e
    case None => throw new ParseException("Cannot elaborate " + e + " of kind " + e.kind + " to expected kind " + kind + " for use in operator " + op, st.location, st.toString)
  }

  /** Elaborate e to the expected kind of a part of op by lifting defaulted types as needed or leave as is. */
  private def possibleElaborate(kind: Kind, e: Expression): Expression = elaboratable(kind, e) match {
    case Some(e) => e
    case None => e
  }

  /** Elaborate the composition op(e) that is coming from token tok by lifting defaulted types as needed. */
  private def elaborate(st: ParseState, tok: Terminal, op: UnaryOpSpec[Expression], e: Expression): Expression =
    op.const(tok.img, elaborate(st, op, op.kind, e))

  /** Elaborate the composition op(e1, e2) that is coming from token tok by lifting defaulted types as needed. */
  private def elaborate(st: ParseState, tok: Terminal, op: BinaryOpSpec[Expression], e1: Expression, e2: Expression): Expression =
    op.const(tok.img, elaborate(st, op, op.kind._1, e1), elaborate(st, op, op.kind._2, e2))


  // parsing

  private def parseStep(st: ParseState): ParseState = {
    val ParseState(s, input@(Token(la,_) :: rest)) = st
    // This table of LR Parser matches needs an entry for every prefix substring of the grammar.
    s match {
      // ordinary terminals
      case r :+ Token(IDENT(name),_) =>
        if (la==LPAREN || la==LBRACE) shift(st) else reduce(st, 1, Variable(name,None,Real), r)

      case r :+ Token(NUMBER(value),_) =>
        reduce(st, 1, Number(BigDecimal(value)), r)


      case r :+ Token(tok@(DOT|PLACE|NOTHING|ANYTHING),_) =>
        reduce(st, 1, op(st, tok, List()).asInstanceOf[UnitOpSpec].const(tok.img), r)

      // special cases for early prime conversion
      case r :+ Expr(x1:Variable) :+ Token(PRIME,_) =>
        reduce(st, 2, OpSpec.sDifferentialSymbol.const(PRIME.img, x1), r)

      case r :+ Token(LPAREN,_) :+ Expr(t1:Term) :+ Token(RPAREN,_) :+ Token(PRIME,_) =>
        reduce(st, 4, OpSpec.sDifferential.const(PRIME.img, t1), r)

      case r :+ Token(LPAREN,_) :+ Expr(f1:Formula) :+ Token(RPAREN,_) :+ Token(PRIME,_) =>
        reduce(st, 4, OpSpec.sDifferentialFormula.const(PRIME.img, f1), r)


      // modal formulas bind tight
      case r :+ Token(LBOX,_) :+ Expr(p1:Program) :+ Token(RBOX,_) :+ Expr(f1:Formula) =>
        reduce(st, 4, elaborate(st, OpSpec.sBox.op, OpSpec.sBox, p1, f1), r)

      case r :+ Token(LDIA,_) :+ Expr(p1:Program) :+ Token(RDIA,_) :+ Expr(f1:Formula) =>
        reduce(st, 4, elaborate(st, OpSpec.sDiamond.op, OpSpec.sDiamond, p1, f1), r)

      // special case to force elaboration of modalities at the end
      case r :+ (tok1@Token(LBOX,_)) :+ Expr(p1:Program) :+ (tok3@Token(RBOX,_)) :+ Expr(e1)
        if (la==EOF || la==RPAREN) && e1.kind!=FormulaKind =>
        reduce(st, 1, elaborate(st, OpSpec.sNone, FormulaKind, e1), r :+ tok1 :+ Expr(p1) :+ tok3 )
        //reduce(st, 4, elaborate(OpSpec.sBox.op, OpSpec.sBox, p1, e1), r)

      // special case to force elaboration of modalities at the end
      case r :+ (tok1@Token(LDIA,_)) :+ Expr(p1:Program) :+ (tok3@Token(RDIA,_)) :+ Expr(e1)
        if (la==EOF || la==RPAREN) && e1.kind!=FormulaKind =>
        reduce(st, 1, elaborate(st, OpSpec.sNone, FormulaKind, e1), r :+ tok1 :+ Expr(p1) :+ tok3)
        //reduce(st, 4, elaborate(st, OpSpec.sDiamond.op, OpSpec.sDiamond, p1, e1), r)

      // special quantifier notation
      case r :+ (tok1@Token(FORALL,_)) :+ Expr(v1:Variable) :+ Expr(f1:Formula) =>
        reduce(st, 3, OpSpec.sForall.const(tok1.tok.img, v1, f1), r)

      case r :+ (tok1@Token(EXISTS,_)) :+ Expr(v1:Variable) :+ Expr(f1:Formula) =>
        reduce(st, 3, OpSpec.sExists.const(tok1.tok.img, v1, f1), r)

      // special case to force elaboration of quantifiers at the end
      case r :+ (tok1@Token(FORALL|EXISTS,_)) :+ Expr(v1:Variable) :+ Expr(e1)
        if (la==EOF || la==RPAREN) && e1.kind!=FormulaKind =>
        reduce(st, 1, elaborate(st, OpSpec.sNone, FormulaKind, e1), r :+ tok1 :+ Expr(v1) )

      case r :+ (tok1@Token(FORALL,_)) =>
        if (la.isInstanceOf[IDENT]) shift(st) else error(st)

      case r :+ (tok1@Token(EXISTS,_)) =>
        if (la.isInstanceOf[IDENT]) shift(st) else error(st)

      // special case for statementSemicolon
      case r :+ Expr(p1: Program) :+ Expr(p2: Program) if statementSemicolon =>
        reduce(st, 2, op(st, SEMI, List(p1.kind,p2.kind)).asInstanceOf[BinaryOpSpec[Program]].const(SEMI.img, p1, p2), r)

      // binary operators with precedence
      case r :+ Expr(t1) :+ (Token(tok:OPERATOR,_)) :+ Expr(t2) if !(t1.kind==ProgramKind && tok==RDIA) =>
        assert(op(st, tok, List(t1.kind,t2.kind)).isInstanceOf[BinaryOpSpec[_]], "binary operator expected since others should have been reduced\nin " + s)
        if (la==LPAREN || la==LBRACE) error(st)
        else {
          // pass t1,t2 kinds so that op/2 can make up its mind well in disambiguation.
          val optok = op(st, tok, List(t1.kind,t2.kind))
          //@todo op(st, la) : Potential problem: st is not the right parser state for la
          if (la==EOF || la==RPAREN || la==RBRACE || la==RBOX /*||@todo la==RDIA or la==SEMI RDIA? */
            || optok < op(st, la, List(t2.kind,ExpressionKind)) || optok <= op(st, la, List(t2.kind,ExpressionKind)) && optok.assoc == LeftAssociative) {
            //println("\tGOT: " + tok + "\t" + "LA: " + la + "\tAfter: " + s + "\tRemaining: " + input)
            val result = elaborate(st, tok, optok.asInstanceOf[BinaryOpSpec[Expression]], t1, t2)
            if (statementSemicolon && result.isInstanceOf[AtomicProgram]) {
              if (la == SEMI) reduce(shift(st), 4, result, r)
              else if (result.isInstanceOf[DifferentialProgram] || result.isInstanceOf[ODESystem]) reduce(st, 3, result, r) // optional SEMI
              else error(st)
            } else reduce(st, 3, result, r)
          } else if (optok > op(st, la, List(t2.kind,ExpressionKind)) || optok >= op(st, la, List(t2.kind,ExpressionKind)) && optok.assoc == RightAssociative)
            shift(st)
          else error(st)
        }

      // unary prefix operators with precedence
      case r :+ Token(tok:OPERATOR,_) :+ Expr(t1)  if op(st, tok, List(t1.kind)).assoc==PrefixFormat =>
        assert(op(st, tok, List(t1.kind)).isInstanceOf[UnaryOpSpec[_]], "only unary operators are currently allowed to have prefix format\nin " + s)
        val optok = op(st, tok, List(t1.kind))
        if (firstExpression(la)) shift(st) // binary operator //@todo be more specific depending on kind of t1
        else if (la==EOF || la==RPAREN || la==RBRACE || la==RBOX /*||@todo la==RDIA or la==SEMI RDIA? */
          || optok <= op(st, la, List(t1.kind,ExpressionKind))) //|| followsTerm(la))
          reduce(st, 2, elaborate(st, tok, op(st, tok, List(t1.kind)).asInstanceOf[UnaryOpSpec[Expression]], t1), r)
        else if (optok > op(st, la, List(t1.kind,ExpressionKind))) shift(st)
        else error(st)

      case _ :+ Token(tok:OPERATOR,_) if op(st, tok, List(ExpressionKind)).assoc==PrefixFormat || tok==MINUS =>
        assert(op(st, tok, List(ExpressionKind)).isInstanceOf[UnaryOpSpec[_]] || tok==MINUS, "only unary operators are currently allowed to have prefix format\nin " + s)
        if (firstExpression(la)) shift(st)
        else error(st)

      // special case for elaboration to a;
      case r :+ Expr(t1:Variable) :+ Token(SEMI,_) if statementSemicolon =>
        //@note should not have gone to SEMI if there would have been another reduction to an atomic program already.
        reduce(st, 2, elaborate(st, OpSpec.sProgramConst, ProgramKind, t1), r)

      case _ :+ Expr(t1) :+ (tok@Token(STAR,_)) =>
        if (firstExpression(la) ||
          t1.isInstanceOf[Program] && followsProgram((la))) shift(st) else error(st)

      case _ :+ Expr(t1) :+ (tok@Token(op:OPERATOR,_)) if op != PRIME =>
        if (firstExpression(la)) shift(st) else error(st)

      // function/predicate symbols arity 0
      case r :+ Token(IDENT(name),_) :+ Token(LPAREN,_) :+ Token(RPAREN,_)  =>
        if (followsTerm(la) /*|| followsFormula(la)*/) reduce(st, 3, FuncOf(Function(name, None, Unit, Real), Nothing), r)
        else if (la==RPAREN) shift(st)
        else error(st)

      // function/predicate symbols of argument ANYTHING
      case r :+ Token(IDENT(name),_) :+ Token(LPAREN,_) :+ Token(ANYTHING,_) :+ Token(RPAREN,_)  =>
        if (followsTerm(la) /*|| followsFormula(la)*/) reduce(st, 4, FuncOf(Function(name, None, Real, Real), Anything), r)
        else if (la==RPAREN) shift(st)
        else error(st)

      // function/predicate symbols arity>0
      case r :+ Token(IDENT(name),_) :+ Token(LPAREN,_) :+ Expr(t1:Term) :+ Token(RPAREN,_)  =>
        if (followsTerm(la) /*|| followsFormula(la)*/) reduce(st, 4, FuncOf(Function(name, None, Real, Real), t1), r)
        else if (la==RPAREN) shift(st)
        else error(st)

      // predicational symbols arity>0
      case r :+ Token(IDENT(name),_) :+ Token(LBRACE,_) :+ Expr(f1:Formula) :+ Token(RBRACE,_)  =>
        if (followsFormula(la)) reduce(st, 4, PredicationalOf(Function(name, None, Bool, Bool), f1), r)
        else error(st)

      // modalities
      case _ :+ Token(LBOX,_) :+ Expr(t1:Program) :+ Token(RBOX,_) =>
        if (firstFormula(la)) shift(st)
        else error(st)

      case _ :+ Token(LDIA,_) :+ Expr(t1:Program) :+ Token(RDIA,_) =>
        if (firstFormula(la)) shift(st)
        else error(st)

      // parentheses
      case r :+ Token(LPAREN,_) :+ Expr(t1) :+ Token(RPAREN,_) if t1.isInstanceOf[Term] || t1.isInstanceOf[Formula] =>
        if (la==PRIME) shift(st) else reduce(st, 3, t1, r)

      case r :+ Token(LBRACE,_) :+ Expr(t1:Program) :+ Token(RBRACE,_) =>
        reduce(st, 3, t1, r)

      // elaboration special pattern case
      case r :+ (tok1@Token(LBRACE,_)) :+ Expr(t1@Equal(_:DifferentialSymbol,_)) =>
        reduce(st, 2, Bottom :+ tok1 :+ Expr(elaborate(st, OpSpec.sODESystem, DifferentialProgramKind, t1)), r)

      // elaboration special pattern case
      case r :+ (tok1@Token(LBRACE,_)) :+ Expr(t1@And(Equal(_:DifferentialSymbol,_),_)) =>
        reduce(st, 2, Bottom :+ tok1 :+ Expr(elaborate(st, OpSpec.sODESystem, DifferentialProgramKind, t1)), r)

      case _ :+ Token(LPAREN,_) :+ Expr(t1) if t1.isInstanceOf[Term] || t1.isInstanceOf[Formula] =>
        if (followsExpression(t1, la)) shift(st)
        else error(st)

      case _ :+ Token(LBRACE,_) :+ Expr(t1:Program) =>
        if (followsProgram(la)) shift(st)
        else error(st)

      case _ :+ Token(LBOX,_) :+ Expr(t1) =>
        if (t1.isInstanceOf[Program] && followsProgram(la)) shift(st)
        else if ((t1.isInstanceOf[Variable] || t1.isInstanceOf[DifferentialSymbol]) && followsIdentifier(la)) shift(st)
        else if ((elaboratable(ProgramKind, t1)!=None || elaboratable(DifferentialProgramKind, t1)!=None) && followsProgram(la)) shift(st)
        else error(st)

      case _ :+ Token(LDIA,_) :+ Expr(t1)  =>
        if (followsExpression(t1, la)) shift(st)
        else error(st)

      case _ :+ Token(LPAREN,_) =>
        if (firstFormula(la) /*|| firstTerm(la)*/ || la==RPAREN || la==ANYTHING) shift(st)
        else error(st)

      case _ :+ Token(LBRACE,_) =>
        if (firstProgram(la) || firstFormula(la) /*for predicationals*/) shift(st)
        else error(st)

      case _ :+ Token(LBOX,_) =>
        if (firstProgram(la)) shift(st)
        else error(st)

      case _ :+ Token(LDIA,_) =>
        if (firstProgram(la) || firstTerm(la)) shift(st)
        else error(st)

      // non-accepting expression
      case _ :+ _ :+ Expr(t) =>
        if (followsExpression(t, la) && la!=EOF) shift(st)
        else error(st)

      // small stack cases
      case Bottom :+ Expr(t) =>
        if (la == EOF) accept(st, t)
        else if (followsExpression(t, la) && la!=EOF) shift(st)
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
    la==NOT || la==FORALL || la==EXISTS || la==LBOX || la==LDIA || la==TRUE || la==FALSE || la==PLACE /*|| la==LPAREN */

  /** First(Program): Is la the beginning of a new program? */
  private def firstProgram(la: Terminal): Boolean = la.isInstanceOf[IDENT] || la==TEST || la==LBRACE

  // FOLLOW sets

  /** Follow(Formula): Can la follow after a formula? */
  private def followsFormula(la: Terminal): Boolean = la==AMP || la==OR || la==IMPLY || la==REVIMPLY || la==EQUIV || la==RPAREN ||
    la==RBRACE /* from predicationals */ ||
    la==EOF

  /** Follow(Term): Can la follow after a term? */
  private def followsTerm(la: Terminal): Boolean = la==RPAREN ||
    la==POWER || la==STAR || la==SLASH || la==PLUS || la==MINUS ||  // from T in terms
    la==EQ || la==NOTEQ || la==GREATEREQ || la==RDIA || la==LESSEQ || la==LDIA || // from T in formulas
    followsFormula(la) ||
    (if (statementSemicolon) la==SEMI || la==RBRACE || la==AMP
    else la==SEMI || la==CHOICE || la==STAR || la==RBRACE || la==COMMA) || // from T in programs
    la==EOF

  /** Follow(Program): Can la follow after a program? */
  private def followsProgram(la: Terminal): Boolean = la==RBRACE || la==CHOICE || la==STAR/**/ ||
    (if (statementSemicolon) firstProgram(la) else la==SEMI)  ||
    la==RBOX || la==RDIA ||  // from P in programs
    la==COMMA || la==AMP ||  // from D in differential programs
    la==EOF

  /** Follow(kind(expr)): Can la follow an expression of the kind of expr? */
  private def followsExpression(expr: Expression, la: Terminal): Boolean = expr match {
    case _: Variable => followsIdentifier(la) || /*if elaborated to program*/ followsProgram(la)
    case FuncOf(_,_) => followsTerm(la) || /*if elaborated to formula*/ followsFormula(la) //@todo line irrelevant since followsTerm subsumes followsFormula
    case _: Term => followsTerm(la)
    case And(Equal(_:DifferentialSymbol, _), _) => followsFormula(la) || /*if elaborated to ODE*/ followsProgram(la)
    case Equal(_:DifferentialSymbol, _) => followsFormula(la) || /*if elaborated to ODE*/ followsProgram(la)
    case _: Formula => followsFormula(la)
    case _: Program => followsProgram(la)
  }

  /** Follow(Identifier): Can la follow after an identifier? */
  private def followsIdentifier(la: Terminal): Boolean = followsTerm(la) ||
    la==LPAREN || la==PRIME ||
    la==ASSIGN || la==ASSIGNANY || la==EOF || firstFormula(la) /* from \exists x ... */


  // parser actions

  /** Shift to put the next input token la on the parser stack s. */
  private def shift(st: ParseState): ParseState = {
    val ParseState(s, (la :: rest)) = st
    require(la.tok != EOF, "Cannot shift past end of file")
    ParseState(s :+ la, rest)
  }

  /**
   * Reduce the parser stack by reducing the consuming many items from the stack to the reduced item.
   * @param remainder Redundant parameter, merely for correctness checking.
   */
  private def reduce(st: ParseState, consuming: Int, reduced: Item, remainder: Stack[Item]): ParseState = {
    val ParseState(s, input) = st
    ParseState(s.drop(consuming) :+ reduced, input)
  } ensuring(r => r.stack.tail == remainder, "Expected remainder stack after consuming the indicated number of stack items.")

  private def reduce(st: ParseState, consuming: Int, reduced: Expression, remainder: Stack[Item]): ParseState = reduce(st, consuming, Expr(reduced), remainder)

  /**
   * Reduce the parser stack by reducing the consuming many items from the stack to the reduced item.
   * @param remainder Redundant parameter, merely for correctness checking.
   */
  private def reduce(st: ParseState, consuming: Int, reduced: Stack[Item], remainder: Stack[Item]): ParseState = {
    val ParseState(s, input) = st
    ParseState(s.drop(consuming) ++ reduced, input)
  } ensuring(r => r.stack.drop(reduced.length) == remainder, "Expected remainder stack after consuming the indicated number of stack items.")

  /** Accept the given parser result. */
  private def accept(st: ParseState, result: Expression): ParseState = {
    val ParseState(s, input) = st
    require(input == List(Token(EOF)), "Can only accept after all input has been read.\nRemaining input: " + input)
    require(s.length == 1, "Can only accept with one single result on the stack.\nRemaining stack: " + s)
    ParseState(Bottom :+ Accept(result), input)
  }

  /** Error parsing the next input token la when in parser stack s.*/
  private def error(st: ParseState): ParseState = {
    val ParseState(s, input@(la :: rest)) = st
    if (immediateError) throw new ParseException("Unexpected token cannot be parsed\nFound: " + la, la.loc, st.toString)
    else ParseState(s :+ Error("Unexpected token cannot be parsed\nFound: " + la, la.loc, st.toString), input)
  }

  /** Drop next input token la from consideration without shifting it to the parser stack s. */
  private def drop(st: ParseState): ParseState = {
    val ParseState(s, (la :: rest)) = st
    require(la.tok != EOF, "Cannot drop end of file")
    ParseState(s, rest)
  }


  // operator precedence lookup

  /** If the stack starts with an expr item, so has been reduced already, it can't be a prefix operator */
  private def isNotPrefix(st: ParseState): Boolean = st.stack match {
    case _ :+ Expr(_) :+ Token(_:OPERATOR, _)  :+ _ => true
    case _ => false
  }

  private def isFormula(st: ParseState): Boolean = (st.stack match {
    case _ :+ Expr(_:Formula) => true
    case _ => false
  })

  // this is a terrible approximation
  private def isProgram(st: ParseState): Boolean = (st.stack match {
    case _ :+ Expr(_:Program) => true
    case _ :+ Token(LBRACE,_) => true
    case _ :+ Token(LBOX,_) => true
    case _ :+ Token(LBRACE,_) :+ _ => true
    case _ :+ Token(LBOX,_) :+ _ => true
    case _ :+ Expr(_:Program) :+ _ => true
    case _ => false
  })

  private def isVariable(st: ParseState): Boolean = st.stack match {
    case _ :+ Expr(_:Variable) => true
    case _ => false
  }

  private def isDifferentialSymbol(st: ParseState): Boolean = st.stack match {
    case _ :+ Expr(_:DifferentialSymbol) => true
    case _ => false
  }

  import OpSpec._

  /** The operator notation of the top-level operator of expr with opcode, precedence and associativity  */
  private[parser] def op(st: ParseState, tok: Terminal, kinds: List[Kind]): OpSpec = {
   // println("\top(" + tok +" " + kinds)
    (tok: @switch) match {
      //@note could almost(!) replace by reflection to search through all OpSpec and check their images.
      // terms
      case sDotTerm.op => sDotTerm
      case sNothing.op => sNothing
      case sAnything.op => sAnything
      //case t: Variable => sVariable
      //case t: Number => sNumber
      //case t: FuncOf => sFuncOf
      case sDifferential.op => if (isVariable(st)) sDifferential else if (isFormula(st)) sDifferentialFormula
      else sDifferential
      //case t: Pair => sPair
      case sMinus.op => if (isNotPrefix(st)) sMinus else sNeg
      case sPower.op => sPower
      case sTimes.op => if (!kinds.isEmpty && kinds(0)==ProgramKind)/*if (isProgram(st))*/ sLoop else sTimes
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
      case sGreater.op => if (!kinds.isEmpty && kinds(0)==ProgramKind) sNone else sGreater   // 1/2 sDiamond
      case sLessEqual.op => sLessEqual
      case sLess.op => if (kinds.length>=2 && kinds(1)==ProgramKind) sNone else sLess    // 1/2 sDiamond
      case sForall.op => sForall
      case sExists.op => sExists
      //      case f: Box => sBox
      //      case f: Diamond => sDiamond
      case sNot.op => sNot
      case sAnd.op => if (!kinds.isEmpty && kinds(0)==ProgramKind||kinds(0)==DifferentialProgramKind)/*if (isProgram(st))*/ sODESystem else sAnd
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
  } ensuring(r => r.op == tok && r.opcode == tok.img || r==sNone, "OpSpec's opcode coincides with expected token " + tok)


}
