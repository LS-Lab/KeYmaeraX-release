/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
/**
 * Differential Dynamic Logic parser for concrete KeYmaera X notation.
  *
  * @author Andre Platzer
  * @see Andre Platzer. [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 59(2), pp. 219-266, 2017.
 */
package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.{Configuration, Logging}

import scala.annotation.{switch, tailrec}
import scala.collection.immutable._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXParser.ParseState
import edu.cmu.cs.ls.keymaerax.parser.OpSpec.{func, statementSemicolon}

/**
 * KeYmaera X parser items on the parser stack.
  *
  * @author Andre Platzer
 */
private[parser] sealed trait Item
/** Tokens are terminals occurring at a given location in the input. */
private[parser] case class Token(tok: Terminal, loc: Location = UnknownLocation) extends Item {
  override def toString: String = tok.toString
  /** Human-readable description followed by internal info */
  def description: String = tok.description
}
private[parser] object UnknownToken extends Token(PSEUDO, UnknownLocation)
/** Expressions that are partially parsed on the parser item stack. */
private[parser] case class Expr(expr: Expression) extends Item {
  //@NOTE Not just "override def toString = expr.toString" to avoid infinite recursion of KeYmaeraXPrettyPrinter.apply contract checking.
  override def toString: String = KeYmaeraXPrettyPrinter.stringify(expr)
}
/** Parts of expressions that are partially recognized on the parser item stack but not parsed to a proper Expression yet so merely stashed for later. */
private[parser] case class RecognizedQuant[T <: Expression](v: List[T]) extends Item {
  //@NOTE Not just "override def toString = expr.toString" to avoid infinite recursion of KeYmaeraXPrettyPrinter.apply contract checking.
  override def toString: String = "Rec(" + v.map(KeYmaeraXPrettyPrinter.stringify).mkString(",") +")"
}
/** Parts of expressions that are partially recognized on the parser item stack but not parsed to a proper Expression yet so merely stashed for later. */
private[parser] case class RecognizedModal(ltok: Token, program: Program, rtok: Token) extends Item {
  require(ltok.tok==LBOX && rtok.tok==RBOX || ltok.tok==LDIA && rtok.tok==RDIA, "Compatible modality tokens required " + this)
  /** The region that this recognized item spans. */
  def loc: Location = ltok.loc--rtok.loc
  //@NOTE Not just "override def toString = expr.toString" to avoid infinite recursion of KeYmaeraXPrettyPrinter.apply contract checking.
  override def toString: String = "Rec" + ltok.tok.img + KeYmaeraXPrettyPrinter.stringify(program) + rtok.tok.img
}

private[parser] case class RecognizedSpace(space: List[Variable]) extends Item {
  //@NOTE Not just "override def toString = expr.toString" to avoid infinite recursion of KeYmaeraXPrettyPrinter.apply contract checking.
  override def toString: String = "|" + space.map(KeYmaeraXPrettyPrinter.stringify).mkString(",") + "|"
}
///** Parts of expressions that are partially recognized on the parser item stack but not parsed to a proper Expression yet so merely stashed for later. */
//private[parser] case class RecognizedAnnotation(program: Program) extends Item {
//  //@NOTE Not just "override def toString = expr.toString" to avoid infinite recursion of KeYmaeraXPrettyPrinter.apply contract checking.
//  override def toString: String = "Rec(" + KeYmaeraXPrettyPrinter.stringify(program) + "@)"
//}
private[parser] trait FinalItem extends Item
/** Parser items representing expressions that are accepted by the parser. */
private[parser] case class Accept(expr: Expression) extends FinalItem
/** Parser items representing erroneous ill-formed input. */
private[parser] case class Error(msg: String, loc: Location, st: String) extends FinalItem
/** Other items for extending the parser. */
private[parser] trait OtherItem extends Item

/** Expected inputs */
private[parser] trait Expected
private object Expected {
  /** Terminal input expected */
  private[parser] implicit class ExpectTerminal(tok: Terminal) extends Expected {
    override def toString: String = tok.description
  }
}
/** Nonterminal or pseudo-nonterminal input expected */
private[parser] case class ExpectNonterminal(nonterm: String) extends Expected {
  override def toString: String = nonterm
}
private object BINARYTERMOP extends ExpectNonterminal("<BinaryTermOp>")
private object BINARYFORMULAOP extends ExpectNonterminal("<BinaryFormulaOp>")
private object BINARYPROGRAMOP extends ExpectNonterminal("<BinaryProgramOp>")
private object FIRSTTERM extends ExpectNonterminal("<BeginningOfTerm>")
private object FIRSTFORMULA extends ExpectNonterminal("<BeginningOfFormula>")
private object FIRSTPROGRAM extends ExpectNonterminal("<BeginningOfProgram>")
private object FIRSTEXPRESSION extends ExpectNonterminal("<BeginningOfExpression>")
private object FOLLOWSTERM extends ExpectNonterminal("<FollowsTerm>")
private object FOLLOWSFORMULA extends ExpectNonterminal("<FollowsFormula>")
private object FOLLOWSPROGRAM extends ExpectNonterminal("<FollowsProgram>")
private object FOLLOWSEXPRESSION extends ExpectNonterminal("<FollowsExpression>")
private object FOLLOWSIDENT extends ExpectNonterminal("<FollowsIdentifier>")
private object ANYIDENT extends ExpectNonterminal("<Identifier>")
/** Pseudo-nonterminal encoding that there's other possible expectations beyond what's listed */
private object MORE extends ExpectNonterminal("<more>") {override def toString = "..."}

/**
  * KeYmaera X parser reads input strings in the concrete syntax of differential dynamic logic of KeYmaera X.
  *
  * Also consider using the alternative parser [[DLParser]].
  *
  * @example
  * Parsing formulas from strings is straightforward using [[edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXParser.apply]]:
  * {{{
  * val parser = KeYmaeraXParser
  * val fml0 = parser("x!=5")
  * val fml1 = parser("x>0 -> [x:=x+1;]x>1")
  * val fml2 = parser("x>=0 -> [{x'=2}]x>=0")
  * // parse only formulas
  * val fml3 = parser.formulaParser("x>=0 -> [{x'=2}]x>=0")
  * // parse only programs/games
  * val prog1 = parser.programParser("x:=x+1;{x'=2}")
  * // parse only terms
  * val term1 = parser.termParser("x^2+2*x+1")
  * }}}
  * @author Andre Platzer
  * @see [[edu.cmu.cs.ls.keymaerax.parser]]
  * @see [[DLParser]]
  * @see [[http://keymaeraX.org/doc/dL-grammar.md Grammar]]
  * @see [[https://github.com/LS-Lab/KeYmaeraX-release/wiki/KeYmaera-X-Syntax-and-Informal-Semantics Wiki]]
  */
class KeYmaeraXParser(val LAX_MODE: Boolean) extends Parser with TokenParser with Logging {
  private val PSEUDOTOK = UnknownToken

  private val eofState = ParseState(Bottom, List(Token(EOF, UnknownLocation)))

  override def apply(input: String): Expression = KeYmaeraXParser.apply(input, LAX_MODE)
  override def parse(input: TokenStream): Expression = KeYmaeraXParser.parse(input, LAX_MODE)

  override val termParser: String => Term =
    input => elaborate(eofState, PSEUDOTOK, OpSpec.sNone, TermKind, apply(input), LAX_MODE) match {
      case t: Term => t
      case e => throw ParseException("Input does not parse as a term but as " + e.kind, e).inInput(input)
    }

  override val termTokenParser: KeYmaeraXParser.TokenStream => Term =
    input => elaborate(eofState, PSEUDOTOK, OpSpec.sNone, TermKind, parse(input), LAX_MODE) match {
      case t: Term => t
      case e => throw ParseException("Input does not parse as a term but as " + e.kind, e).inInput("<unknown>", Some(input))
    }

  override val formulaParser: String => Formula =
    input => elaborate(eofState, PSEUDOTOK, OpSpec.sNone, FormulaKind, apply(input), LAX_MODE) match {
      case f: Formula => f
      case e => throw ParseException("Input does not parse as a formula but as " + e.kind, e).inInput(input)
    }

  /** Parse the input token stream in the concrete syntax as a differential dynamic logic formula */
  override val formulaTokenParser: TokenStream => Formula =
    input => elaborate(eofState, PSEUDOTOK, OpSpec.sNone, FormulaKind, parse(input), LAX_MODE) match {
      case f: Formula => f
      case e => throw ParseException("Input does not parse as a formula but as " + e.kind, e).inInput("<unknown>", Some(input))
    }

  override val programParser: String => Program =
    input => elaborate(eofState, PSEUDOTOK, OpSpec.sNone, ProgramKind, apply(input), LAX_MODE) match {
      case p: Program => p
      case e => throw ParseException("Input does not parse as a program but as " + e.kind, e).inInput(input)
    }

  override val programTokenParser: KeYmaeraXParser.TokenStream => Program =
    input => elaborate(eofState, PSEUDOTOK, OpSpec.sNone, ProgramKind, parse(input), LAX_MODE) match {
      case prg: Program => prg
      case e => throw ParseException("Input does not parse as a program but as " + e.kind, e).inInput("<unknown>", Some(input))
    }

  override val differentialProgramParser: String => DifferentialProgram =
    input => elaborate(eofState, PSEUDOTOK, OpSpec.sNone, DifferentialProgramKind, apply(input), LAX_MODE) match {
      case p: DifferentialProgram => p
      case ODESystem(p, _) => p
      case e => throw ParseException("Input does not parse as a differential program but as " + e.kind, e).inInput(input)
    }

  override val differentialProgramTokenParser: KeYmaeraXParser.TokenStream => DifferentialProgram =
    input => elaborate(eofState, PSEUDOTOK, OpSpec.sNone, DifferentialProgramKind, parse(input), LAX_MODE) match {
      case prg: DifferentialProgram => prg
      case e => throw ParseException("Input does not parse as a differential program but as " + e.kind, e).inInput("<unknown>", Some(input))
    }

  override val sequentParser: String => Sequent = SequentParser.parseSequent

  lazy val strictParser: KeYmaeraXParser = new KeYmaeraXParser(LAX_MODE = false)
  lazy val laxParser: KeYmaeraXParser = new KeYmaeraXParser(LAX_MODE = true)

  override lazy val printer: KeYmaeraXPrettyPrinter.type = KeYmaeraXPrettyPrinter

  private val parseErrorsAsExceptions = true

  /** Parse the input string in the concrete syntax as a differential dynamic logic expression */
  def apply(input: String, lax: Boolean): Expression = {
    val tokenStream = KeYmaeraXLexer.inMode(input, ExpressionMode)
    //if (DEBUG) println("\t" + input)
    try { parse(tokenStream, lax) }
    catch {case e: ParseException => throw e.inInput(input, Some(tokenStream))}
  }

  def parse(input: TokenStream, lax: Boolean): Expression = {
    require(input.last.tok == EOF, "token streams have to end in " + EOF)
    val parse = parseLoop(ParseState(Bottom, input), lax).stack match {
      case Bottom :+ Accept(e) => e
      case _ :+ Error(msg, loc, st) => throw ParseException(msg, loc, "<unknown>", "<unknown>", "", st)
      case _ => throw new AssertionError("Parser terminated with unexpected stack")
    }
    semanticAnalysis(parse) match {
      case None => parse
      case Some(error) => if (lax) { logger.trace("WARNING: " + "Semantic analysis" + "\nin " + "parsed: " + printer.stringify(parse) + "\n" + error); parse}
      else throw ParseException("Semantic analysis error " + error, parse).inInput("<unknown>", Some(input))
    }
  }

  /** Repeatedly perform parseStep until a final parser item is produced. */
  @tailrec
  private def parseLoop(st: ParseState, lax: Boolean): ParseState = st.stack match {
    case _ :+ (_: FinalItem) => st
    case _ => parseLoop(parseStep(st, lax), lax)
  }

  /** Semantic analysis of expressions after parsing, returning errors if any or None. */
  def semanticAnalysis(e: Expression): Option[String] = {
    val symbols = try { StaticSemantics.symbols(e) }
    catch {
      case ex: AssertionError => return Some("semantics: symbols computation error\n" + ex)
      case ex: CoreException => return Some("semantics: symbols computation error\n" + ex)
    }
    val names = symbols.map(s => (s.name, s.index, s.isInstanceOf[DifferentialSymbol]))
    assert(Configuration(Configuration.Keys.DEBUG) == "false" || (names.size == symbols.size) == (symbols.toList.map(s => (s.name, s.index, s.isInstanceOf[DifferentialSymbol])).distinct.length == symbols.toList.map(s => (s.name, s.index, s.isInstanceOf[DifferentialSymbol])).length), "equivalent ways of checking uniqueness via set conversion or list distinctness")
    //@NOTE Stringify avoids infinite recursion of KeYmaeraXPrettyPrinter.apply contract checking.
    if (names.size == symbols.size) None
    else {
      val namesList = symbols.toList.map(s => (s.name, s.index, s.isInstanceOf[DifferentialSymbol]))
      val duplicateNames = namesList.diff(namesList.distinct)
      val duplicates = symbols.filter(s => duplicateNames.contains((s.name, s.index, s.isInstanceOf[DifferentialSymbol])))
      Some("semantics: Expect unique names_index that identify a unique type." +
        "\nambiguous: " + duplicates.toList.map(s => s.fullString).mkString(" and ") +
        "\nsymbols:   " + symbols.mkString(", ") /*+ if (DEBUG) "\nin expression: " + printer.stringify(e)*/)
    }
  }

  // elaboration based on expected types

  /** Elaborate `e` to the expected `kind` of a part of op by lifting defaulted types as needed or return None. */
  private def elaboratable(kind: Kind, e: Expression, lax: Boolean): Option[Expression] = if (e.kind==kind) Some(e) else e match {
    // lift misclassified defaulted function application to predicate application when required by context type.
    case FuncOf(f, t) if kind==FormulaKind =>
      OpSpec.interpretedFuncSortDomain(f.name) match {
        case None | Some((Bool, _)) => Some(PredOf(func(f.name,f.index,f.domain,Bool), t))
        case Some((s, _)) => throw ParseException("Interpreted symbol " + f.name + ": expected sort " + s + " but got " + Bool, UnknownLocation, Bool.toString, s.toString)
      }
    // lift misclassified defaulted predicate application to function application when required by context type.
    case PredOf(f, t) if kind==TermKind =>
      OpSpec.interpretedFuncSortDomain(f.name) match {
        case None | Some((Real, _)) => Some(FuncOf(func(f.name,f.index,f.domain,Real), t))
        case Some((s, _)) => throw ParseException("Interpreted symbol " + f.name + ": expected sort " + s + " but got " + Real, UnknownLocation, Real.toString, s.toString)
      }
    // lift misclassified defaulted differential program constant
    case x: Variable if kind==DifferentialProgramKind && x.index.isEmpty => Some(DifferentialProgramConst(x.name, AnyArg))
    // lift misclassified defaulted program constant
    case x: Variable if kind==ProgramKind && x.index.isEmpty => Some(ProgramConst(x.name))
    // lift misclassified predicational
    case x: Variable if lax && kind==FormulaKind && x.index.isEmpty && x.name.charAt(0).isUpper =>
      Some(UnitPredicational(x.name, AnyArg))
    // lift misclassified nullary predicate
    case x: Variable if lax && kind==FormulaKind && x.index.isEmpty && x.name.charAt(0).isLower =>
      Some(PredOf(Function(x.name, x.index, Unit, Bool), Nothing))
    // lift misclassified defaulted term (p(x))' to formula as needed.
    case Differential(t) if kind==FormulaKind => elaboratable(kind, t, lax) match {
      case Some(f:Formula) => Some(DifferentialFormula(f))
      case _ => None
    }
    // lift misclassified defaulted formula (f(x))' to term as needed.
    case DifferentialFormula(f) if kind==TermKind => elaboratable(kind, f, lax) match {
      case Some(t:Term) => Some(Differential(t))
      case _ => None
    }
    // lift misclassified defaulted differential equation
    case Equal(xp:DifferentialSymbol, e) if kind==DifferentialProgramKind && !StaticSemantics.isDifferential(e) => Some(AtomicODE(xp, e))
    // refuse to lift misclassified defaulted differential equation to program directly
    case Equal(_:DifferentialSymbol, e) if kind==ProgramKind && !StaticSemantics.isDifferential(e) => None
    //@todo And(And(x'=5,x>0),x<12)) is not lifted yet
    // lift misclassified defaulted differential equation
    case And(Equal(xp:DifferentialSymbol, e), h)
      if (kind==DifferentialProgramKind || kind==ProgramKind) && !StaticSemantics.isDifferential(h) => Some(ODESystem(AtomicODE(xp, e), h))
    case ode: ODESystem if kind==ProgramKind => Some(ode)
    // whether ODESystem is classified as ProgramKind or DifferentialProgramKind
    case ode: ODESystem if kind==ProgramKind || kind==DifferentialProgramKind => Some(ode)
    // lift misclassified differential program constants without evolution domain constraints to program constants
    //case ode: DifferentialProgramConst if kind==ProgramKind => Some(ProgramConst(ode.name, ode.space))
    // lift differential equations without evolution domain constraints to ODESystems
    case ode: DifferentialProgram if ode.kind==DifferentialProgramKind && kind==ProgramKind => assert(!ode.isInstanceOf[ODESystem], "wrong kind"); Some(ODESystem(ode))

    // space-dependent elaborations
    case UnitPredicational(name, space)    if kind==TermKind => Some(UnitFunctional(name,space,Real))
    case UnitFunctional(name, space, Real) if kind==FormulaKind => Some(UnitPredicational(name,space))
    //    case UnitPredicational(name, space)    if kind==DifferentialProgramKind => Some(DifferentialProgramConst(name,space))
    //    case UnitFunctional(name, space, Real) if kind==DifferentialProgramKind => Some(DifferentialProgramConst(name,space))
    case _ => None
  }

  /** Elaborate `e` to the expected `kind` of a part of operator `op` at token `tok` by lifting defaulted types as needed or throw exception. */
  private def elaborate(st: ParseState, optok: Token, op: OpSpec, kind: Kind, e: Expression, lax: Boolean): Expression = elaboratable(kind, e, lax) match {
    case Some(e) => e
    //@todo locations are a little off in error reporting here. Would need original operator token.
    case None => e match {
      case Equal(_: DifferentialSymbol, t) if kind==ProgramKind && !StaticSemantics.isDifferential(t) => throw ParseException("Unexpected " + optok.tok.img + " in system of ODEs", st, optok, COMMA.img)
      case _ =>
        throw ParseException("Impossible elaboration: Operator " + op.op + " expects a " + kind + " as argument but got the " + e.kind + " "  + e.prettyString,
          st, optok, kind.toString)
    }
  }

  /** Elaborate the composition op(e) that is coming from token tok by lifting defaulted types as needed. */
  private def elaborate(st: ParseState, tok: Token, op: UnaryOpSpec[Expression], e: Expression, lax: Boolean): Expression =
    op.const(tok.tok.img, elaborate(st, tok, op, op.kind, e, lax))

  /** Elaborate the composition op(e1, e2) that is coming from token tok by lifting defaulted types as needed. */
  private def elaborate(st: ParseState, tok: Token, op: BinaryOpSpec[Expression], e1: Expression, e2: Expression, lax: Boolean): Expression =
    op.const(tok.tok.img, elaborate(st, tok, op, op.kind._1, e1, lax), elaborate(st, tok, op, op.kind._2, e2, lax))

  /** Elaborate the composition op(e1, e2) that is coming from token tok by lifting defaulted types as needed. */
  private def elaborate(st : ParseState, tok1:Token, op:TernaryOpSpec[Expression], e1: Expression, e2:Expression, e3:Expression, lax: Boolean): Expression =
    op.const(tok1.tok.img, elaborate(st, tok1, op, op.kind._1, e1, lax), elaborate(st, tok1, op, op.kind._2, e2, lax), elaborate(st, tok1, op, op.kind._3, e3, lax))

  private[parser] var annotationListener: (Program,Formula) => Unit = {
    (p,inv) => logger.trace("Annotation: " + p + " @invariant(" + inv + ")")
  }
  /**
    * Register a listener for @annotations during the parse.
    *
    * @todo this design is suboptimal.
    */
  override def setAnnotationListener(listener: (Program,Formula) => Unit): Unit =
    this.annotationListener = listener

  /** Report an @invariant @annotation to interested parties */
  private def reportAnnotation(p: Program, invariant: Formula): Unit = annotationListener(p,invariant)

  /** Whether p is compatible with @annotation */
  @tailrec
  private def isAnnotable(p: Program): Boolean = p match {
    case _: Loop => true
    case _: ODESystem => true
    case Compose(_, r) => isAnnotable(r)
    case Choice(_, r) => isAnnotable(r)
    case p => p.kind == DifferentialProgramKind
  }

  @tailrec
  private def annotatedProgram(p: Program): Program = p match {
    case Compose(_, r) => annotatedProgram(r)
    case Choice(_, r) => annotatedProgram(r)
    case p =>
      assert(isAnnotable(p), "Program " + p.prettyString + " cannot be annotated; only loops and differential equations support annotations")
      p
  }


  // parsing

  //@todo the style of this parser should probably be rewritten to a more functional style close to the grammar with more inline shifting/reducing for improved clarity and speed

  //@todo performance bottleneck
  //@todo reorder cases also such that pretty cases like fully parenthesized get parsed fast and early
  private def parseStep(st: ParseState, lax: Boolean): ParseState = {
    val ParseState(s, (next@Token(la, laloc)) :: _) = st
    logger.info(s.toString)
    logger.info(la.toString)
    //@note This table of LR Parser matches needs an entry for every prefix substring of the grammar.
    s match {
      // nonproductive: help KeYmaeraXLexer recognize := * with whitespaces as ASSIGNANY
      case r :+ Token(ASSIGN, loc1) if la == STAR =>
        reduce(shift(st), 2, Bottom :+ Token(ASSIGNANY, loc1 -- laloc), r)

      // nonproductive: special notation for annotations
      case r :+ Expr(p: Program) :+ (tok@Token(INVARIANT | VARIANT, _)) :+ Token(LPAREN, _) :+ Expr(f1) :+ Token(RPAREN, _) if isAnnotable(p) =>
        //@note elaborate DifferentialProgramKind to ODESystem to make sure annotations are stored on top-level
        reportAnnotation(annotatedProgram(elaborate(st, tok, OpSpec.sNone, ProgramKind, p, lax).asInstanceOf[Program]),
          elaborate(st, tok, OpSpec.sNone, FormulaKind, f1, lax).asInstanceOf[Formula])
        reduce(st, 4, Bottom, r :+ Expr(p))
      case r :+ Expr(p: Program) :+ (tok@Token(INVARIANT | VARIANT, _)) :+ (lpar@Token(LPAREN, _)) :+ Expr(f1) :+ Token(COMMA, _) if isAnnotable(p) =>
        //@note elaborate DifferentialProgramKind to ODESystem to make sure annotations are stored on top-level
        reportAnnotation(annotatedProgram(elaborate(st, tok, OpSpec.sNone, ProgramKind, p, lax).asInstanceOf[Program]),
          elaborate(st, tok, OpSpec.sNone, FormulaKind, f1, lax).asInstanceOf[Formula])
        reduce(st, 2, Bottom, r :+ Expr(p) :+ tok :+ lpar)
      case _ :+ Expr(p: Program) :+ Token(INVARIANT | VARIANT, _) :+ Token(LPAREN, _) :+ Expr(_: Formula) if isAnnotable(p) =>
        if (la == RPAREN || la == COMMA || formulaBinOp(la)) shift(st) else error(st, List(RPAREN, COMMA, BINARYFORMULAOP))
      case _ :+ Expr(p: Program) :+ Token(INVARIANT | VARIANT, _) =>
        if (isAnnotable(p)) if (la == LPAREN) shift(st) else error(st, List(LPAREN))
        else errormsg(st, "requires an operator that supports annotation")


      // special quantifier notation
      case r :+ (tok1@Token(FORALL, _)) :+ RecognizedQuant(vs: List[Variable]) :+ Expr(f1: Formula) =>
        reduce(st, 3, vs.foldLeft[Expression](f1)((f,v) => OpSpec.sForall.const(tok1.tok.img, v, f)), r)

      case r :+ (tok1@Token(EXISTS, _)) :+ RecognizedQuant(vs: List[Variable]) :+ Expr(f1: Formula) =>
        reduce(st, 3, vs.foldLeft[Expression](f1)((f,v) => OpSpec.sExists.const(tok1.tok.img, v, f)), r)

      // special case typing to force elaboration of quantifiers at the end
      case r :+ (tok1@Token(FORALL | EXISTS, _)) :+ (tok2@RecognizedQuant(_: List[Variable])) :+ Expr(e1)
        if (la == EOF || la == RPAREN || la == RBRACE || la == SEMI || formulaBinOp(la)) && e1.kind != FormulaKind =>
        //@todo assert(!formulaBinOp(la) || quantifier binds stronger than la)
        reduce(st, 1, elaborate(st, tok1, OpSpec.sNone, FormulaKind, e1, lax), r :+ tok1 :+ tok2)

      // ordinary identifiers disambiguate quantifiers versus predicate/function/predicational versus variable
      case r :+ (tok1@Token(FORALL | EXISTS, _)) :+ RecognizedQuant(vs: List[Variable]) :+ Token(COMMA, _) :+ Token(IDENT(name, idx), _) =>
        if (la == COMMA || firstFormula(la)) shift(reduce(st, 3, Bottom :+ RecognizedQuant(vs :+ Variable(name, idx, Real)), r :+ tok1))
        else error(st, List(COMMA,FIRSTFORMULA))

      case _ :+ Token(FORALL | EXISTS, _) :+ RecognizedQuant(_) :+ Token(COMMA, _) =>
        if (la.isInstanceOf[IDENT]) shift(st) else error(st, List(IDENT("IDENT")))

      case r :+ (tok1@Token(FORALL | EXISTS, _)) :+ Token(IDENT(name, idx), _) =>
        //@note Recognized(Variable()) instead of IDENT to avoid item overlap IDENT LPAREN with function/predicate symbols
        //@note Recognized(Variable()) instead of Variable to avoid detecting lookup confusion with Variable PLUS ... too late
        //@note Recognized should also generalize better to block quantifiers and multi-sorted quantifiers
        if (la == PRIME) shift(reduce(shift(st), 2, Bottom :+ RecognizedQuant(DifferentialSymbol(Variable(name, idx, Real)) :: Nil), r :+ tok1))
        else if (la == COMMA || firstFormula(la)) shift(reduce(st, 1, Bottom :+ RecognizedQuant(Variable(name, idx, Real) :: Nil), r :+ tok1))
        else error(st, List(COMMA,FIRSTFORMULA))

      case _ :+ Token(FORALL | EXISTS, _) => if (la.isInstanceOf[IDENT]) shift(st) else error(st, List(IDENT("IDENT")))

      //custom error messages for multiplication that doesn't properly use *
      //@note These must come after quantifiers because otherwise \forall x x=1 doesn't parse.
      case _ :+ Token(x: IDENT, _) if la.isInstanceOf[IDENT] || la.isInstanceOf[NUMBER] => errormsg(st, s"Multiplication in KeYmaera X requires an explicit * symbol. E.g. ${x.name}*term")
      case _ :+ Token(n: NUMBER, _) if la.isInstanceOf[IDENT] || la.isInstanceOf[NUMBER] => errormsg(st, s"Multiplication in KeYmaera X requires an explicit * symbol. E.g. ${n.value}*term")

      // special cases for early prime conversion
      case r :+ Token(IDENT(name, idx), _) :+ Token(PRIME, _) =>
        assert(isNoQuantifier(r), "Quantifier stack items handled above\n" + st)
        reduce(st, 2, OpSpec.sDifferentialSymbol.const(PRIME.img, Variable(name, idx, Real)), r)

      //      // special cases for early prime conversion, possibly redundant
      //      case r :+ Expr(x1:Variable) :+ Token(PRIME,_) =>
      //        reduce(st, 2, OpSpec.sDifferentialSymbol.const(PRIME.img, x1), r)

      // ordinary identifiers outside quantifiers disambiguate to predicate/function/predicational versus variable
      case r :+ Token(IDENT(name, idx), _) =>
        assert(isNoQuantifier(r), "Quantifier stack items handled above\n" + st)
        if (la == LPAREN || la == LBRACE || la == PRIME || la == LBANANA || la == LBARB) shift(st) else reduce(st, 1, Variable(name, idx, Real), r)

      // function/predicate symbols arity 0
      case r :+ Token(tok: IDENT, _) :+ Token(LPAREN, _) :+ Token(RPAREN, _) =>
        assert(isNoQuantifier(r), "Quantifier stack items handled above\n" + st)
        reduceFuncOrPredOf(st, 3, tok, Nothing, r)


      // nullary functional/predicational symbols of argument ANYTHING
      case r :+ Token(tok: IDENT, _) :+ Token(LPAREN, _) :+ Token(ANYTHING, _) :+ Token(RPAREN, _) =>
        assert(isNoQuantifier(r), "Quantifier stack items handled above\n" + st)
        reduceUnitFuncOrPredOf(st, 4, tok, AnyArg, r)

      // nullary functional/predicational symbols
      case r :+ Token(tok: IDENT, _) :+ Token(LBANANA, _) :+ RecognizedSpace(s) :+ Token(RBANANA, _) =>
        reduceUnitFuncOrPredOf(st, 4, tok, if (s.isEmpty) AnyArg else Except(s), r)
      case _ :+ Token(_: IDENT, _) :+ Token(LBANANA, _) =>
        if (la == RBANANA || la.isInstanceOf[IDENT]) shift(reduce(st, 0, RecognizedSpace(Nil), st.stack))
        else error(st, List(RBANANA, ANYIDENT))
      case _ :+ Token(_: IDENT, _) :+ Token(LBANANA, _) :+ RecognizedSpace(s) :+ Expr(x: Variable) =>
        if (la == RBANANA) shift(reduce(st, 2, RecognizedSpace(s :+ x), st.stack.tail.tail))
        else if (la == COMMA) shift(reduce(shift(st), 3, RecognizedSpace(s :+ x), st.stack.tail.tail))
        else error(st, List(RBANANA,COMMA))
      case _ :+ Token(_: IDENT, _) :+ Token(LBANANA, _) :+ RecognizedSpace(_) :+ Expr(_) =>
        errormsg(st, "Identifier expected after state-dependent predicational/functional")

      // DifferentialProgramConst symbols of argument AnyArg
      case r :+ Token(tok: IDENT, _) :+ Token(LBARB, _) :+ RecognizedSpace(s) :+ Token(RBARB, _) :+ Token(SEMI, _) if statementSemicolon =>
        require(tok.index.isEmpty, "no index supported for ProgramConst")
        reduce(st, 5, ProgramConst(tok.name, if (s.isEmpty) AnyArg else Except(s)), r)
      // DifferentialProgramConst symbols of argument Taboo
      case r :+ Token(tok: IDENT, _) :+ Token(LBARB, _) :+ RecognizedSpace(s) :+ Token(RBARB, _) =>
        if (la == SEMI) shift(st)
        else {
          require(tok.index.isEmpty, "no index supported for DifferentialProgramConst")
          reduce(st, 4, DifferentialProgramConst(tok.name, if (s.isEmpty) AnyArg else Except(s)), r)
        }
      case r :+ Token(tok: IDENT, _) :+ Token(LBARB, _) :+ Token(DUAL, _) :+ RecognizedSpace(s) :+ Token(RBARB, _) :+ Token(SEMI, _) if statementSemicolon =>
        require(tok.index.isEmpty, "no index supported for SystemConst")
        reduce(st, 6, SystemConst(tok.name, if (s.isEmpty) AnyArg else Except(s)), r)
      case r :+ Token(tok: IDENT, _) :+ Token(LBARB, _) :+ Token(DUAL, _) :+ RecognizedSpace(s) :+ Token(RBARB, _) =>
        if (la == SEMI) shift(st)
        else {
          require(tok.index.isEmpty, "no index supported for DifferentialProgramConst")
          reduce(st, 4, DifferentialProgramConst(tok.name, if (s.isEmpty) AnyArg else Except(s)), r)
        }
      case _ :+ Token(_: IDENT, _) :+ Token(LBARB, _) =>
        if (la == DUAL) reduce(shift(st), 0, RecognizedSpace(Nil), st.stack :+ next)
        else if (la == RBARB || la.isInstanceOf[IDENT]) shift(reduce(st, 0, RecognizedSpace(Nil), st.stack))
        else error(st, List(RBARB, ANYIDENT, DUAL))
      case _ :+ Token(_: IDENT, _) :+ Token(LBARB, _) :+ RecognizedSpace(s) :+ Expr(x: Variable) =>
        if (la == RBARB) shift(reduce(st, 2, RecognizedSpace(s :+ x), st.stack.tail.tail))
        else if (la == COMMA) shift(reduce(shift(st), 3, RecognizedSpace(s :+ x), st.stack.tail.tail))
        else error(st, List(RBARB, COMMA))
      case _ :+ Token(_: IDENT, _) :+ Token(LBARB, _) :+ RecognizedSpace(_) :+ Expr(_) =>
        errormsg(st, "Identifier expected after state-dependent ProgramConst or DiffProgramConst")
      case _ :+ Token(_: IDENT, _) :+ Token(LBARB, _) :+ RecognizedSpace(_) :+ Token(DUAL, _) =>
        if (la == RBARB || la.isInstanceOf[IDENT]) shift(st)
        else error(st, List(RBARB, ANYIDENT))
      case _ :+ Token(_: IDENT, _) :+ Token(LBARB, _) :+ Token(DUAL, _) :+ RecognizedSpace(_) =>
        if (la == RBARB || la.isInstanceOf[IDENT]) shift(st)
        else error(st, List(RBARB, ANYIDENT))
      case _ :+ Token(_: IDENT, _) :+ Token(LBARB, _) :+ Token(DUAL, _) :+ RecognizedSpace(s) :+ Expr(x: Variable)  =>
        if (la == RBARB) shift(reduce(st, 2, RecognizedSpace(s :+ x), st.stack.tail.tail))
        else if (la == COMMA) shift(reduce(shift(st), 3, RecognizedSpace(s :+ x), st.stack.tail.tail))
        else error(st, List(RBARB, COMMA))
      case _ :+ Token(_: IDENT, _) :+ Token(LBARB, _) :+ Token(DUAL, _) :+ RecognizedSpace(_) :+ Expr(_) =>
        errormsg(st, "Identifier expected after state-dependent ProgramConst or DiffProgramConst")

      // function/predicate symbols arity>0
      case r :+ Token(tok: IDENT, _) :+ Token(LPAREN, _) :+ Expr(t1: Term) :+ Token(RPAREN, _) =>
        assert(isNoQuantifier(r), "Quantifier stack items handled above\n" + st)
        reduceFuncOrPredOf(st, 4, tok, t1, r)

      // function/predicate symbols arity>0: special elaboration case for misclassified t() as formula
      case r :+ Token(tok: IDENT, _) :+ (optok@Token(LPAREN, _)) :+ Expr(t1: Formula) :+ Token(RPAREN, _) =>
        assert(isNoQuantifier(r), "Quantifier stack items handled above\n" + st)
        reduceFuncOrPredOf(st, 4, tok, elaborate(st, optok, OpSpec.sFuncOf, TermKind, t1, lax).asInstanceOf[Term], r)

      // DOT arity=0
      case r :+ Token(DOT(index), _) =>
        assert(isNoQuantifier(r), "Quantifier stack items handled above\n" + st)
        if (la == LPAREN) shift(st) else reduce(st, 1, DotTerm(Real, index), r)

      case r :+ Token(DOT(index), _) :+ Token(LPAREN, _) :+ Token(RPAREN, _) =>
        assert(isNoQuantifier(r), "Quantifier stack items handled above\n" + st)
        reduce(st, 3, DotTerm(Real, index), r)

      // DOT arity>0
      case r :+ Token(DOT(index), _) :+ Token(LPAREN, _) :+ Expr(t1: Term) :+ Token(RPAREN, _) =>
        assert(isNoQuantifier(r), "Quantifier stack items handled above\n" + st)
        reduce(st, 4, DotTerm(t1.sort, index), r)

      // predicational symbols arity>0
      case r :+ Token(IDENT(name, idx), _) :+ Token(LBRACE, _) :+ Expr(f1: Formula) :+ Token(RBRACE, _) =>
        if (followsFormula(la)) reduce(st, 4, PredicationalOf(func(name, idx, Bool, Bool), f1), r)
        else error(st, List(FOLLOWSFORMULA))

      // predicational symbols arity>0: special elaboration case for misclassified c() as formula in P{c()}
      case r :+ Token(IDENT(name, idx), _) :+ (optok@Token(LBRACE, _)) :+ Expr(f1: Term) :+ Token(RBRACE, _) =>
        if (followsFormula(la)) reduce(st, 4, PredicationalOf(func(name, idx, Bool, Bool), elaborate(st, optok, OpSpec.sPredOf, FormulaKind, f1, lax).asInstanceOf[Formula]), r)
        else error(st, List(FOLLOWSFORMULA))

      case r :+ Token(_: IDENT, _) :+ Token(LPAREN, _) =>
        assert(isNoQuantifier(r), "Quantifier stack items handled above")
        if (firstTerm(la) || firstFormula(la) || la == RPAREN || la == ANYTHING) shift(st) else error(st, List(FIRSTTERM, FIRSTFORMULA, RPAREN, ANYTHING))

      case _ :+ Token(_: IDENT, _) :+ Token(LBRACE, _) =>
        //assert(isNoQuantifier(r), "Quantifier stack items handled above")
        if (firstFormula(la)) shift(st) else error(st, List(FIRSTFORMULA))


      // special case for negative numbers to turn lexer's MINUS, NUMBER("5") again into NUMBER("-5")
      case r :+ Token(MINUS, loc1) :+ Token(NUMBER(n), loc) if OpSpec.negativeNumber && !n.startsWith("-") && !isNotPrefix(st) &&
        loc1.adjacentTo(loc) =>
        assert(r.isEmpty || !r.top.isInstanceOf[Expr], "Can no longer have an expression on the stack, which would cause a binary operator")
        if (la == LPAREN || la == LBRACE) error(st, List(FOLLOWSTERM))
        else reduce(st, 2, Number(BigDecimal("-" + n)), r)

      case r :+ Token(NUMBER(value), _) =>
        if (la == LPAREN || la == LBRACE) error(st, List(FOLLOWSTERM))
        else reduce(st, 1, Number(BigDecimal(value)), r)


      case r :+ Token(tok@(PLACE | NOTHING | TRUE | FALSE), _) =>
        reduce(st, 1, op(st, tok, List()).asInstanceOf[UnitOpSpec].const(tok.img), r)

      // differentials

      case r :+ Token(LPAREN, _) :+ Expr(t1: Term) :+ Token(RPAREN, _) :+ Token(PRIME, _) =>
        reduce(st, 4, OpSpec.sDifferential.const(PRIME.img, t1), r)

      case r :+ Token(LPAREN, _) :+ Expr(f1: Formula) :+ Token(RPAREN, _) :+ Token(PRIME, _) =>
        reduce(st, 4, OpSpec.sDifferentialFormula.const(PRIME.img, f1), r)

      // special notation for loops
      case r :+ Token(LBRACE, _) :+ Expr(t1: DifferentialProgram) :+ Token(RBRACE, _) :+ (tok@Token(STAR, _)) =>
        // special elaboration for not-yet-ODESystem Programs
        assume(r.isEmpty || !r.top.isInstanceOf[IDENT], "Can no longer have an IDENT on the stack")
        if (la == INVARIANT || la == VARIANT) shift(reduce(st, 4, OpSpec.sLoop.const(tok.tok.img, elaborate(st, tok, OpSpec.sNone, ProgramKind, t1, lax).asInstanceOf[Program]), r))
        else reduce(st, 4, OpSpec.sLoop.const(tok.tok.img, elaborate(st, tok, OpSpec.sNone, ProgramKind, t1, lax).asInstanceOf[Program]), r)
      case r :+ Token(LBRACE, _) :+ Expr(t1: Program) :+ Token(RBRACE, _) :+ (tok@Token(STAR, _)) =>
        assume(r.isEmpty || !r.top.isInstanceOf[IDENT], "Can no longer have an IDENT on the stack")
        if (la == INVARIANT || la == VARIANT) shift(reduce(st, 4, OpSpec.sLoop.const(tok.tok.img, t1), r))
        else reduce(st, 4, OpSpec.sLoop.const(tok.tok.img, t1), r)
      // Leave parentheses around for IF to find later
      case _ :+ Token(IF, _) :+ Token(LPAREN, _) :+ Expr(_) :+ Token(RPAREN, _) =>
        shift(st)
      case _ :+ Token(IF, _) :+ Token(LPAREN, _) :+ Expr(_) :+ Token(RPAREN, _) :+ Token(LBRACE, _) =>
        shift(st)
      // Special case: if with no else
      case r :+ (optok1@Token(tok1@IF, _)) :+ Token(LPAREN, _) :+ Expr(t1) :+ Token(RPAREN, _) :+ Token(LBRACE, _) :+ Expr(t2) :+ Token(RBRACE, _) =>
        if ((followsProgram(la) || la == EOF) && la != ELSE) {
          assume(op(st, tok1, List(t1.kind)).isInstanceOf[TernaryOpSpec[_]], "expected ternary prefix operator\nin " + s)
          val kinds = List(t1.kind, t2.kind, t2.kind)
          val t3 = Test(True)
          val result = elaborate(st, optok1, op(st, tok1, kinds).asInstanceOf[TernaryOpSpec[Expression]], t1, t2, t3, lax)
          reduce(st, 7, result, r)
        } else shift(st)
      case _ :+ Token(IF,_) :+ Token(LPAREN,_) :+ Expr(_) :+ Token(RPAREN,_) :+ Token(LBRACE,_) :+ Expr(_) :+ Token(RBRACE,_) :+ Token(ELSE,_)=> la match {
        case LBRACE => shift(st)
        case _ => error(st, List(LBRACE))
      }
      case _ :+ Token(IF,_) :+ Token(LPAREN,_) :+ Expr(_) :+ Token(RPAREN,_) :+ Token(LBRACE,_) :+ Expr(_) :+ Token(RBRACE,_) :+ Token(ELSE,_) :+ Token(LBRACE, _)=>
        shift(st)
      case _ :+ Token(IF,_) :+ Token(LPAREN,_) :+ Expr(_) :+ Token(RPAREN,_) :+ Token(LBRACE,_) :+ Expr(_) :+ Token(RBRACE,_) :+ Token(ELSE,_) :+ Token(LBRACE, _) :+ Expr(_) =>
        shift(st)
      // ternary prefix operators *without* any special attention to precedence,because as of this writing there is exactly one
      //@todo review
      case r :+ (optok1@Token(tok1@IF,_)) :+ Token(LPAREN,_) :+ Expr(t1) :+ Token(RPAREN,_) :+ Token(LBRACE,_) :+ Expr(t2) :+ Token(RBRACE,_) :+ Token(ELSE,_)  :+ Token(LBRACE,_) :+ Expr(t3) :+ Token(RBRACE,_)
        //case r :+ (optok1@Token(tok1:OPERATOR,_)) :+ Expr(t1)  :+ (optok2@Token(tok2:OPERATOR,_)) :+ Expr(t2)  :+ (optok3@Token(tok3:OPERATOR,_)) :+ Expr(t3)
        if  followsProgram(la) || la==EOF =>
        assume(op(st, tok1, List(t1.kind)).isInstanceOf[TernaryOpSpec[_]], "expected ternary prefix operator\nin " + s)
        val kinds = List(t1.kind, t2.kind, t3.kind)
        val result = elaborate(st, optok1, op(st, tok1, kinds).asInstanceOf[TernaryOpSpec[Expression]], t1, t2, t3, lax)
        reduce(st, 11, result, r)

      // parentheses for grouping
      case r :+ Token(LPAREN,_) :+ Expr(t1) :+ Token(RPAREN,_) if t1.isInstanceOf[Term] || t1.isInstanceOf[Formula] =>
        assert(r.isEmpty || !r.top.isInstanceOf[IDENT], "Can no longer have an IDENT on the stack")
        if (la==PRIME) shift(st) else reduce(st, 3, t1, r)

      case r :+ Token(LBRACE,_) :+ Expr(t1:DifferentialProgram) :+ Token(RBRACE,_) =>
        assume(r.isEmpty || !r.top.isInstanceOf[IDENT], "Can no longer have an IDENT on the stack")
        reduce(st, 3, ODESystem(t1), r)

      case r :+ Token(LBRACE,_) :+ Expr(t1:Program) :+ Token(RBRACE,_) =>
        assume(r.isEmpty || !r.top.isInstanceOf[IDENT], "Can no longer have an IDENT on the stack")
        if (la==STAR) shift(st) else reduce(st, 3, t1, r)


      ///////

      // modalities
      case r :+ (ltok@Token(LBOX,_)) :+ Expr(t1:Program) :+ (rtok@Token(RBOX,_)) =>
        if (firstFormula(la)) shift(reduce(st, 3, RecognizedModal(ltok, elaborate(st, ltok, OpSpec.sBox, ProgramKind, t1, lax).asInstanceOf[Program], rtok), r))
        else error(st, List(FIRSTFORMULA))

      case r :+ (ltok@Token(LDIA,_)) :+ Expr(t1:Program) :+ (rtok@Token(RDIA,_)) =>
        //@note convert to RecognizedMoal to avoid subsequent item confusion with t1 > la
        if (firstFormula(la)) shift(reduce(st, 3, RecognizedModal(ltok, elaborate(st, ltok, OpSpec.sDiamond, ProgramKind, t1, lax).asInstanceOf[Program], rtok), r))
        else error(st, List(FIRSTFORMULA))

      // modal formulas bind tight
      //case r :+ Token(LBOX,_) :+ Expr(p1:Program) :+ Token(RBOX,_) :+ Expr(f1:Formula) =>
      case r :+ RecognizedModal(tok@Token(LBOX,_), p1:Program, Token(RBOX,_)) :+ Expr(f1:Formula) =>
        //@todo assert(modality binds tight)
        reduce(st, 4-2, elaborate(st, tok, OpSpec.sBox, p1, f1, lax), r)

      //@todo could turn the first 3 into Recognized to stash for later and disambiguate
      //case r :+ Token(LDIA,_) :+ Expr(p1:Program) :+ Token(RDIA,_) :+ Expr(f1:Formula) =>
      case r :+ RecognizedModal(tok@Token(LDIA,_), p1:Program, Token(RDIA,_)) :+ Expr(f1:Formula) =>
        //@todo assert(modality binds tight)
        reduce(st, 4-2, elaborate(st, tok, OpSpec.sDiamond, p1, f1, lax), r)

      // special case to force elaboration of modalities at the end
      //case r :+ (tok1@Token(LBOX,_)) :+ Expr(p1:Program) :+ (tok3@Token(RBOX,_)) :+ Expr(e1)
      //@todo
      case r :+ (mod:RecognizedModal) :+ Expr(e1)
        if (la==EOF || la==RPAREN || la==RBRACE || formulaBinOp(la)) && e1.kind!=FormulaKind
          || (if (statementSemicolon) la==SEMI else programOp(la)) =>
        reduce(st, 1, elaborate(st, mod.rtok, OpSpec.sNone,  FormulaKind, e1, lax), r :+ mod)

      //      // special case to force elaboration of modalities at the end
      //      case r :+ (tok1@Token(LDIA,_)) :+ Expr(p1:Program) :+ (tok3@Token(RDIA,_)) :+ Expr(e1)
      //        if (la==EOF || la==RPAREN || la==RBRACE || formulaBinOp(la)) && e1.kind!=FormulaKind =>
      //        reduce(st, 1, elaborate(st, OpSpec.sNone, FormulaKind, e1), r :+ tok1 :+ Expr(p1) :+ tok3)

      // special case to force elaboration to DifferentialProgramConst {c} and {c,...} and {c&...}
      case r :+ (tok1@Token(LBRACE,_)) :+ Expr(e1:Variable) if la==AMP || la==COMMA || la==RBRACE =>
        assume(r match {case _ :+ Token(_:IDENT,_) => false case _ => true}, "IDENT stack for predicationals has already been handled")
        reduce(st, 1, elaborate(st, tok1, OpSpec.sNone, DifferentialProgramKind, e1, lax), r :+ tok1)

      // differential equation system special notation
      //      case r :+ (tok1@Token(LBRACE,_)) :+ Expr(p1:DifferentialProgram) :+ (tok2@Token(AMP,_)) :+ Expr(f1:Formula) :+ (tok3@Token(RBRACE,_)) =>
      //        reduce(st, 5, elaborate(st, tok2, OpSpec.sODESystem, p1, f1), r)
      case r :+ Token(LBRACE,_) :+ Expr(p1:DifferentialProgram) :+ (tok2@Token(AMP,_)) :+ Expr(f1) :+ (tok3@Token(RBRACE,_)) =>
        if (StaticSemantics.isDifferential(f1)) throw new ParseException("No differentials can be used in evolution domain constraints", tok2.loc.spanTo(tok3.loc), printer.stringify(f1), "In an evolution domain constraint, instead of the primed variables use their right-hand sides.", "", "")
        else reduce(st, 5, elaborate(st, tok2, OpSpec.sODESystem, p1, f1, lax), r)

      // elaboration special pattern case to DifferentialProgram
      case r :+ (tok1@Token(LBRACE,_)) :+ Expr(t1@Equal(_:DifferentialSymbol,_)) if (la==AMP || la==COMMA || la==RBRACE) &&
        (r match {case _ :+ Token(_:IDENT,_) => false case _ => true})  =>
        //assume(r.isEmpty || !r.top.isInstanceOf[IDENT], "Equal stack for predicationals has already been handled")
        reduce(st, 2, Bottom :+ tok1 :+ Expr(elaborate(st, tok1, OpSpec.sODESystem, DifferentialProgramKind, t1, lax)), r)

      // elaboration special pattern case to DifferentialProgram
      case r :+ (tok1@Token(LBRACE,_)) :+ Expr(t1@And(Equal(_:DifferentialSymbol,_),_)) if (la==AMP || la==COMMA || la==RBRACE) &&
        (r match {case _ :+ Token(_:IDENT,_) => false case _ => true}) =>
        //assume(r.isEmpty || !r.top.isInstanceOf[IDENT], "And stack for predicationals has already been handled")
        reduce(st, 2, Bottom :+ tok1 :+ Expr(elaborate(st, tok1, OpSpec.sODESystem, DifferentialProgramKind, t1, lax)), r)

      // special case for sDchoice -- notation
      case _ :+ Expr(_: Program) :+ Token(MINUS,loc) if la==MINUS =>
        reduce(ParseState(st.stack, Token(DCHOICE, loc.spanTo(laloc)) +: st.input.tail), 1, Bottom, st.stack.tail)

      // special case for sCompose in case statementSemicolon
      //@todo review
      case r :+ Expr(p1: Program) :+ Expr(p2: Program) if statementSemicolon =>
        if (la==LPAREN || !statementSemicolon&&la==LBRACE) error(st, if (statementSemicolon) List(LPAREN) else List(LPAREN,LBRACE))
        val optok = OpSpec.sCompose
        assume(optok.assoc==RightAssociative)
        //@todo op(st, la) : Potential problem: st is not the right parser state for la
        if (la==EOF || la==RPAREN || la==RBRACE || la==RBOX
          || (la == RDIA/* || la == RDIA*/) && (p1.kind == ProgramKind || p1.kind == DifferentialProgramKind)
          || la!=LBRACE && (optok < op(st, la, List(p2.kind,ExpressionKind)) || optok <= op(st, la, List(p2.kind,ExpressionKind)) && optok.assoc == LeftAssociative))
          reduce(st, 2, elaborate(st, Token(SEMI, UnknownLocation), op(st, SEMI, List(p1.kind,p2.kind)).asInstanceOf[BinaryOpSpec[Expression]], p1, p2, lax), r)
        else if (statementSemicolon&&la==LBRACE || optok > op(st, la, List(p2.kind,ExpressionKind)) || optok >= op(st, la, List(p2.kind,ExpressionKind)) && optok.assoc == RightAssociative)
          shift(st)
        else {assert(statementSemicolon); error(st, List(EOF,RPAREN,RBRACE,RBOX,RDIA, LBRACE))}

      //      // lax accepts optional or possibly even extra SEMI between the two programs for sequential composition
      //      case r :+ Expr(p1: Program) :+ (tok@Token(SEMI,_)) :+ Expr(p2: Program) if statementSemicolon && LAX =>
      //        if (la==LPAREN || !statementSemicolon&&la==LBRACE) error(st)
      //        val optok = OpSpec.sCompose
      //        assume(optok.assoc==RightAssociative)
      //        //@todo op(st, la) : Potential problem: st is not the right parser state for la
      //        if (la==EOF || la==RPAREN || la==RBRACE || la==RBOX
      //          || (la == RDIA || la == RDIA) && (p1.kind == ProgramKind || p1.kind == DifferentialProgramKind)
      //          || la!=LBRACE && (optok < op(st, la, List(p2.kind,ExpressionKind)) || optok <= op(st, la, List(p2.kind,ExpressionKind)) && optok.assoc == LeftAssociative))
      //          reduce(st, 3, op(st, tok.tok, List(p1.kind,p2.kind)).asInstanceOf[BinaryOpSpec[Program]].const(tok.tok.img, p1, p2), r)
      //        else if (statementSemicolon&&la==LBRACE || optok > op(st, la, List(p2.kind,ExpressionKind)) || optok >= op(st, la, List(p2.kind,ExpressionKind)) && optok.assoc == RightAssociative)
      //          shift(st)
      //        else error(st)

      // generic operators

      // binary operators with precedence
      //@todo review
      //@todo should really tok!=COMMA and handle that one separately to enforce (x,y) notation but only allow p(x,y) without p((x,y)) sillyness
      case r :+ Expr(t1) :+ (optok1@Token(tok:OPERATOR,_)) :+ Expr(t2) if !((t1.kind==ProgramKind||t1.kind==DifferentialProgramKind) && tok==RDIA) &&
        tok!=TEST && tok != ELSE=>
        // pass t1,t2 kinds so that op/2 can disambiguate based on kinds
        val optok = op(st, tok, List(t1.kind,t2.kind))
        if (optok==OpSpec.sNoneUnfinished && la!=EOF) shift(st)
        else {
          assume(optok.isInstanceOf[BinaryOpSpec[_]], "binary operator expected for " + optok + " since others should have been reduced\nin " + s)
          if (la==LPAREN || !statementSemicolon && la==LBRACE) error(st, List(LPAREN, LBRACE))
          else {
            //@todo op(st, la) : Potential problem: st is not the right parser state for la
            //@todo if statementSemicolon then the missing SEMI causes incorrect predictions of operator precedence ++ versus ;
            if (la==EOF || la==RPAREN || la==RBRACE || la==RBOX
              || (la==RDIA /*|| la==RDIA*/) && (t1.kind == ProgramKind || t1.kind == DifferentialProgramKind)
              || la!=LBRACE &&
              (optok<op(st, la, List(t2.kind, ExpressionKind))
                || optok<=op(st, la, List(t2.kind, ExpressionKind)) && optok.assoc==LeftAssociative && op(st, la, List(t2.kind, ExpressionKind)).assoc==LeftAssociative)) {
              //println("\tGOT: " + tok + "\t" + "LA: " + la + "\tAfter: " + s + "\tRemaining: " + input)
              val result = elaborate(st, optok1, optok.asInstanceOf[BinaryOpSpec[Expression]], t1, t2, lax)
              if (statementSemicolon && result.isInstanceOf[AtomicProgram]) {
                if (la==SEMI) reduce(shift(st), 4, result, r)
                else if (result.isInstanceOf[DifferentialProgram] || result.isInstanceOf[ODESystem]) reduce(st, 3, result, r) // optional SEMI
                else error(st, List(SEMI))
              } else reduce(st, 3, result, r)
            } else if (statementSemicolon && la==LBRACE
              || optok>op(st, la, List(t2.kind, ExpressionKind))
              || optok>=op(st, la, List(t2.kind, ExpressionKind)) && optok.assoc==RightAssociative && op(st, la, List(t2.kind, ExpressionKind)).assoc==RightAssociative)
              shift(st)
            else error(st, List(LPAREN, EOF, RPAREN, RBRACE, RBOX, RDIA, LBRACE, MORE))
          }
        }

      // unary prefix operators with precedence
      //@todo review
      case r :+ (optok1@Token(tok:OPERATOR,_)) :+ Expr(t1) if op(st, tok, List(t1.kind)).assoc==PrefixFormat =>
        assume(op(st, tok, List(t1.kind)).isInstanceOf[UnaryOpSpec[_]], "expected unary prefix operator\nin " + s)
        val optok = op(st, tok, List(t1.kind))
        if (la==EOF || la==RPAREN || la==RBRACE || la==RBOX
          || (la == RDIA || la == RDIA) && (t1.kind == ProgramKind || t1.kind == DifferentialProgramKind)
          || optok <= op(st, la, List(t1.kind,ExpressionKind))) {
          //|| followsTerm(la))
          //@note By operator precedence, will only elaborate if need be, i.e. unless lookahead says shifting will get the right type
          val result = elaborate(st, optok1, op(st, tok, List(t1.kind)).asInstanceOf[UnaryOpSpec[Expression]], t1, lax)
          if (statementSemicolon && result.isInstanceOf[AtomicProgram]) {
            if (la == SEMI) reduce(shift(st), 3, result, r)
            else error(st, List(SEMI))
          } else reduce(st, 2, result, r)
        } else if (optok > op(st, la, List(t1.kind,ExpressionKind))) shift(st)
        else error(st, List(MORE))
      case _ :+ Token(tok:OPERATOR,_) if op(st, tok, List(ExpressionKind)).assoc==PrefixFormat || tok==MINUS =>
        //@note MINUS will always have to be shifted before reduction, whether binary infix or unary prefix
        assert(op(st, tok, List(ExpressionKind)).isInstanceOf[UnaryOpSpec[_]] || tok==MINUS, "only unary operators are currently allowed to have prefix format\nin " + s)
        if (firstExpression(la)) shift(st)
        else error(st, List(FIRSTEXPRESSION))

      // unary postfix operator
      case r :+ Expr(t1) :+ (optok@Token(tok:OPERATOR,_)) if op(st, tok, List(t1.kind)).assoc==PostfixFormat && tok!=STAR =>
        //@note STAR from sLoop needs explicit braces
        assert(op(st, tok, List(t1.kind)).isInstanceOf[UnaryOpSpec[_]], "only unary operators are currently allowed to have postfix format\nin " + s)
        val result = elaborate(st, optok, op(st, tok, List(t1.kind)).asInstanceOf[UnaryOpSpec[Expression]], t1, lax)
        if (statementSemicolon && result.isInstanceOf[AtomicProgram]) {
          if (la == SEMI) reduce(shift(st), 3, result, r)
          else error(st, List(SEMI))
        } else reduce(st, 2, result, r)

      // special case for elaboration to a;
      case r :+ Expr(t1:Variable) :+ (optok@Token(SEMI,_)) if statementSemicolon =>
        assert(r.isEmpty || !r.top.isInstanceOf[Token] || !(r.top.asInstanceOf[Token].tok==ASSIGN || r.top.asInstanceOf[Token].tok==EQ || r.top.asInstanceOf[Token].tok==TEST), "Would have recognized as atomic statement already or would not even have shifted to SEMI")
        //@todo assert r.top is not formula or term operator or assignment or test
        //@note should not have gone to SEMI if there would have been another reduction to an atomic program already.
        reduce(st, 2, elaborate(st, optok, OpSpec.sProgramConst, ProgramKind, t1, lax), r)

      case _ :+ Expr(_) :+ Token(STAR,_) =>
        if (firstTerm(la) && la!=EOF) shift(st) else error(st, List(FIRSTTERM))
      //@note explicit braces around loops so can't happen:
      //        if (firstExpression(la) ||
      //          t1.isInstanceOf[Program] && followsProgram((la))) shift(st) else error(st)

      case _ :+ Expr(t1) :+ Token(op, _) if isOrContainsDifferentialSymbol(t1) && op == EQ =>
        if (firstExpression(la) && la!=EOF) shift(st)
        else throw ParseException("Missing right-hand side " + t1 + "=", st, List[Expected](TERM))

      // better error message for missing {} around ODEs
      case _ :+ Expr(t1) :+ Token(op, _) if isOrContainsDifferentialSymbol(t1) && op != COMMA && op != AMP && op != RBRACE =>
        if (firstExpression(la) && la!=EOF) shift(st)
        else throw ParseException("ODE without {}", st, List[Expected](RBRACE))

      case _ :+ Expr(DifferentialProduct(_,_)) :+ Token(op, loc) if op != COMMA && op != AMP && op != RBRACE =>
        throw ParseException("ODE without {}", loc, op.img, RBRACE.img)

      case _ :+ Expr(DifferentialProduct(_,_)) :+ Token(AMP,_) :+ Expr(_) :+ Token(op, loc) if op != COMMA && op != AMP && op != RBRACE =>
        if (la != EOF && (firstFormula(la) || firstTerm(la))) shift(st)
        else throw ParseException("ODE without {}", loc, op.img, RBRACE.img)
      // end error message


      case _ :+ Expr(_) :+ Token(op:OPERATOR,_) if op != PRIME =>
        if (firstExpression(la) && la!=EOF) shift(st) else error(st, List(FIRSTEXPRESSION))

      case _ :+ (tok@Token(LPAREN,_)) :+ Expr(t1) if t1.isInstanceOf[Term] || t1.isInstanceOf[Formula] =>
        if (followsExpression(t1, la, lax) && la!=EOF) shift(st)
        else if (la==EOF) throw ParseException.imbalancedError("Imbalanced parenthesis", tok, st)
        else error(st, List(FOLLOWSEXPRESSION))

      case _ :+ (tok@Token(LBRACE,_)) :+ Expr(_:Program) =>
        if (followsProgram(la) && la!=EOF) shift(st)
        else if (la==EOF) throw ParseException.imbalancedError("Imbalanced parenthesis", tok, st)
        else error(st, List(FOLLOWSPROGRAM))

      case _ :+ (tok@Token(LBOX,_)) :+ Expr(t1) =>
        if (t1.isInstanceOf[Program] && followsProgram(la) && la!=EOF) shift(st)
        else if (la==EOF) throw ParseException.imbalancedError("Unmatched modality", tok, st)
        else if ((t1.isInstanceOf[Variable] || t1.isInstanceOf[DifferentialSymbol]) && followsIdentifier(la)) shift(st)
        else if ((elaboratable(ProgramKind, t1, lax).isDefined || elaboratable(DifferentialProgramKind, t1, lax).isDefined) && followsProgram(la)) shift(st)
        else error(st, List(FOLLOWSPROGRAM, FOLLOWSIDENT))

      case _ :+ (tok@Token(LDIA,_)) :+ Expr(t1)  =>
        if (followsExpression(t1, la, lax) && la!=EOF) shift(st)
        else if (la==EOF) throw ParseException.imbalancedError("Unmatched suspected modality", tok, st)
        else if ((t1.isInstanceOf[Variable] || t1.isInstanceOf[DifferentialSymbol]) && followsIdentifier(la)) shift(st)
        else if ((elaboratable(ProgramKind, t1, lax).isDefined || elaboratable(DifferentialProgramKind, t1, lax).isDefined) && followsProgram(la)) shift(st)
        else error(st, List(FOLLOWSEXPRESSION, FOLLOWSIDENT))

      case _ :+ Token(IF,_) =>
        if (firstFormula(la)) shift(st)
        else error(st, List(FIRSTFORMULA))

      case _ :+ (tok@Token(IF,_)) :+ Token(LPAREN,_) :+ Expr(t1) =>
        if (followsExpression(t1, la, lax) && la!=EOF) shift(st)
        else if (la==EOF) throw ParseException.imbalancedError("Unmatched if-then-else", tok, st)
        else if (elaboratable(FormulaKind, t1, lax).isDefined && followsFormula(la)) shift(st)
        else error(st, List(FOLLOWSEXPRESSION))

      case _ :+ Token(IF,_) :+ Token(LPAREN,_) :+ Expr(_) :+ Token(RPAREN,_) :+ Token(LBRACE,_) =>
        if (firstProgram(la)) shift(st)
        else error(st, List(FIRSTPROGRAM))

      case _ :+ Token(IF,_) :+ Token(LPAREN,_) :+ Expr(_) :+ Token(RPAREN,_) :+ Token(LBRACE,_) :+ Expr(_) :+ Token(RBRACE,_) if la == ELSE => shift(st)
      case _ :+ Token(IF,_) :+ Token(LPAREN,_) :+ Expr(_) :+ Token(RPAREN,_) :+ (tok2@Token(LBRACE,_)) :+ Expr(_) if la == EOF =>
        throw ParseException.imbalancedError("Unmatched if-then-else", tok2, st)
      case _ :+ Token(LPAREN,_) =>
        if (firstFormula(la) /*|| firstTerm(la)*/ || la==RPAREN || la==ANYTHING) shift(st)
        else error(st, List(FIRSTFORMULA, RPAREN, ANYTHING))

      case _ :+ Token(LBRACE,_) =>
        if (firstProgram(la) || firstFormula(la) /*for predicationals*/) shift(st)
        else error(st, List(FIRSTPROGRAM, FIRSTFORMULA))

      case _ :+ Token(LBOX,_) =>
        if (firstProgram(la)) shift(st)
        else error(st, List(FIRSTPROGRAM))

      case _ :+ Token(LDIA,_) =>
        if (firstProgram(la) || firstTerm(la)) shift(st)
        else error(st, List(FIRSTPROGRAM, FIRSTTERM))

      // non-accepting expression
      case _ :+ _ :+ Expr(t) =>
        if (followsExpression(t, la, lax) && la!=EOF) shift(st)
        else error(st, List(FOLLOWSEXPRESSION))

      // Help lexer convert PERIOD to DOT for convenience
      case r :+ Token(PERIOD,loc) =>
        reduce(st, 1, Bottom :+ Token(DOT(),loc), r)

      // small stack cases
      case Bottom :+ Expr(t) =>
        if (la == EOF) accept(st, t)
        else if (followsExpression(t, la, lax) && la!=EOF) shift(st)
        else error(st, List(EOF, FOLLOWSEXPRESSION))

      case Bottom =>
        if (firstExpression(la)) shift(st)
        else if (la==EOF) throw ParseException("Empty input is not a well-formed expression ", st, List(FIRSTEXPRESSION)) else error(st, List(FIRSTEXPRESSION))

      // error handling message extras

      case rest :+ (tok@Token(RPAREN,_)) if rest.find(tok => tok.isInstanceOf[Token] && tok.asInstanceOf[Token].tok==LPAREN).isEmpty =>
        throw ParseException.imbalancedError("Imbalanced parenthesis", tok, st)

      case rest :+ (tok@Token(RBRACE,_)) if rest.find(tok => tok.isInstanceOf[Token] && tok.asInstanceOf[Token].tok==LBRACE).isEmpty =>
        throw ParseException.imbalancedError("Imbalanced parenthesis", tok, st)

      case rest :+ (tok@Token(RBOX,_)) if rest.find(tok => tok.isInstanceOf[Token] && tok.asInstanceOf[Token].tok==LBOX).isEmpty =>
        throw ParseException.imbalancedError("Unmatched modality", tok, st)

      case rest :+ (tok@Token(RDIA,_)) if rest.find(tok => tok.isInstanceOf[Token] && tok.asInstanceOf[Token].tok==LDIA).isEmpty =>
        throw ParseException.imbalancedError("Syntax error or unmatched modality", tok, st)

      case _ =>
        //Try to make a good error message.
        goodErrorMessage(st) match {
          case Some(msg) => throw ParseException(msg, st)
          case None => imbalancedParentheses(st) match {
            case Some(exc) => throw exc
            case None => throw ParseException(s"Syntax error (or incomplete parser missing an item).\nWe could not generate a nice error message for stack: ${st.stack}", st)
          }
        }
        //@todo cases should be completed to complete the parser items, but it's easier to catch-all and report legible parse error.

        //throw new AssertionError("Incomplete parser missing an item, so does not yet know how to handle case.\nFound: " + la + "\nAfter: " + s)
    }
  }

  /** Tests an expression for being or containing a differential or differential symbol. */
  private def isOrContainsDifferentialSymbol(t: Expression): Boolean = t match {
    //@note isDifferential introduces double-primes when applied to differential terms (extends all variables to differential symbols)
    case _: DifferentialSymbol => true
    case _: Differential => true
    case _ => try {
      StaticSemantics.isDifferential(t)
    } catch {
      case _: AssertionError => true //@note StaticSemantics.freeVars may extend to differential symbols, which fails on infinite sets
    }
  }

  // error message handling

  private def goodErrorMessage(st: ParseState): Option[String] = st.stack match {
    case _ :+ Token(edu.cmu.cs.ls.keymaerax.parser.RBOX, _) => Some("Syntax error. Perhaps the program contained in your box modality is ill-formed or incomplete?")
    case _ :+ (e: edu.cmu.cs.ls.keymaerax.parser.Expr) :+ Token(edu.cmu.cs.ls.keymaerax.parser.RBRACE, _) if !e.isInstanceOf[Program] =>
      Some("Syntax error. Expression " + e.expr.prettyString + " is not a program, perhaps ; is missing?")
    case _ :+ Token(edu.cmu.cs.ls.keymaerax.parser.RBRACE, _) => Some("Syntax error. Perhaps the program contained in {} is ill-formed or incomplete?")
    case _ => None
  }

  private def imbalancedParentheses(st: ParseState): Option[ParseException] = {
    var brace = 0
    var paren = 0
    var box = 0
    //@todo dia is an approximation because 2<8 might be misunderstood during parse.
    var dia = 0
    var stack = st.stack
    while (!stack.isEmpty) {
      val rest :+ t = stack
      t match {
        case Token(RBRACE,_)     => brace = brace + 1
        case tok@Token(LBRACE,_) => if (brace>0) brace = brace - 1
        else return Some(ParseException.imbalancedError("Imbalanced parentheses led to unclosed {", tok, "}", st))
        case Token(RPAREN,_)     => paren = paren + 1
        case tok@Token(LPAREN,_) => if (paren>0) paren = paren - 1
        else return Some(ParseException.imbalancedError("Imbalanced parentheses led to unclosed (", tok, ")", st))
        case Token(RBOX,_)       => box = box + 1
        case tok@Token(LBOX,_)   => if (box>0) box = box - 1
        else return Some(ParseException.imbalancedError("Imbalanced parentheses led to unclosed [", tok, "]", st))
        case Token(RDIA,_)       => dia = dia + 1
        case tok@Token(LDIA,_)   => if (dia>0) dia = dia - 1
        else return Some(ParseException.imbalancedError("Imbalanced parentheses might have led to unclosed <", tok, ">", st))
        case _ =>
      }
      stack = rest
    }
    None
  }

  // stack helper

  /**
    * Reduce consuming items in the parse state st to function/predicate name applied to argument arg,
    * while automatically disambiguating between function and predicate symbols based on lookahead
    * and parser state of stack items.
    *
    * @NOTE Needs to be able to disambiguate early in [x:=q()]f()->r()+c(x)>0
    */
  private def reduceFuncOrPredOf(st: ParseState, consuming: Int, name: IDENT, arg: Term, remainder: Stack[Item]): ParseState = {
    val ParseState(_, Token(la, _) :: _) = st
    OpSpec.interpretedFuncSortDomain(name.name) match {
      // backwards compatibility: allow declaring interpreted functions
      case Some((Real, d)) =>
        if (arg.sort == d) reduce(st, consuming, FuncOf(func(name.name, name.index, arg.sort, Real), arg), remainder)
        else throw ParseException("Interpreted symbol " + name.name + ": expected domain " + d + " but got " + arg.sort, st.location, arg.sort.toString, d.toString)
      case Some((Bool, d)) =>
        if (arg.sort == d) reduce(st, consuming, PredOf(func(name.name, name.index, arg.sort, Bool), arg), remainder)
        else throw ParseException("Interpreted symbol " + name.name + ": expected domain " + d + " but got " + arg.sort, st.location, arg.sort.toString, d.toString)
      case Some((s, _)) => throw ParseException("Unknown sort " + s, st)
      case None =>
        if (termBinOp(la) || isTerm(st) && followsTerm(la))
          reduce(st, consuming, FuncOf(func(name.name, name.index, arg.sort, Real), arg), remainder)
        else if (formulaBinOp(la) || isFormula(st) && followsFormula(la))
          reduce(st, consuming, PredOf(func(name.name, name.index, arg.sort, Bool), arg), remainder)
        else if (followsFormula(la) && !followsTerm(la))
          reduce(st, consuming, PredOf(func(name.name, name.index, arg.sort, Bool), arg), remainder)
        else if (followsTerm(la) && !followsFormula(la))
          reduce(st, consuming, FuncOf(func(name.name, name.index, arg.sort, Real), arg), remainder)
        //@note the following cases are on plausibility so need ultimate elaboration to get back from misclassified
        //    else if (followsFormula(la))
        //      reduce(st, consuming, PredOf(predFunc(name.name, name.index, arg.sort, Bool), arg), remainder)
        else if (followsTerm(la))
          reduce(st, consuming, FuncOf(func(name.name, name.index, arg.sort, Real), arg), remainder)
        else if (followsFormula(la))
          reduce(st, consuming, PredOf(func(name.name, name.index, arg.sort, Bool), arg), remainder)
        else if (la == RPAREN) shift(st)
        else error(st, List(BINARYTERMOP,BINARYFORMULAOP,RPAREN,MORE))
    }
  }

  private def reduceUnitFuncOrPredOf(st: ParseState, consuming: Int, name: IDENT, arg: Space, remainder: Stack[Item]): ParseState = {
    val ParseState(_, Token(la, _) :: _) = st
    require(name.index.isEmpty, "no index supported for unit functional or unit predicational")
    if (termBinOp(la) || isTerm(st) && followsTerm(la))
      reduce(st, consuming, UnitFunctional(name.name, arg, Real), remainder)
    else if (formulaBinOp(la) || isFormula(st) && followsFormula(la))
      reduce(st, consuming, UnitPredicational(name.name, arg), remainder)
    else if (followsFormula(la) && !followsTerm(la))
      reduce(st, consuming, UnitPredicational(name.name, arg), remainder)
    else if (followsTerm(la) && !followsFormula(la))
      reduce(st, consuming, UnitFunctional(name.name, arg, Real), remainder)
    //@note the following cases are on plausibility so need ultimate elaboration to get back from misclassified
    //    else if (followsFormula(la))
    //      reduce(st, consuming, PredOf(predFunc(name.name, name.index, arg.sort, Bool), arg), remainder)
    else if (followsTerm(la))
      reduce(st, consuming, UnitFunctional(name.name, arg, Real), remainder)
    else if (followsFormula(la))
      reduce(st, consuming, UnitPredicational(name.name, arg), remainder)
    else if (la == RPAREN) shift(st)
    else error(st, List(BINARYTERMOP,BINARYFORMULAOP,RPAREN,MORE))
  }

  // FIRST lookahead sets

  /** Is la the beginning of a new expression? */
  private def firstExpression(la: Terminal): Boolean = firstFormula(la) || firstProgram(la) /*|| firstTerm(la) */

  /** First(Term): Is la the beginning of a new term? */
  private def firstTerm(la: Terminal): Boolean = la.isInstanceOf[IDENT] || la.isInstanceOf[NUMBER] ||
    la==MINUS || la==LPAREN || la.isInstanceOf[DOT] ||
    la==PERIOD      // from DotTerm

  /** First(Formula): Is la the beginning of a new formula? */
  private def firstFormula(la: Terminal): Boolean = firstTerm(la) || /*la.isInstanceOf[IDENT] ||*/
    la==NOT || la==FORALL || la==EXISTS || la==LBOX || la==LDIA || la==TRUE || la==FALSE || la==PLACE /*|| la==LPAREN */

  /** First(Program): Is la the beginning of a new program? */
  private def firstProgram(la: Terminal): Boolean = la.isInstanceOf[IDENT] || la==TEST || la==LBRACE || la==IF

  // FOLLOW sets

  /** Follow(Formula): Can la follow after a formula? */
  private def followsFormula(la: Terminal): Boolean = la==AMP || la==OR || la==IMPLY || la==REVIMPLY || la==EQUIV || la==RPAREN ||
    la==SEMI /* from tests */ ||
    la==RBRACE /* from predicationals */ ||
    la==COMMA /* from invariant annotations */ ||
    la==PRIME || la==EOF

  /** Is la a (binary) operator that only works for formulas? */
  private def formulaBinOp(la: Terminal): Boolean = la==AMP || la==OR || la==IMPLY || la==REVIMPLY || la==EQUIV

  /** Is la a (unary/binary) operator that only works for programs? */
  private def programOp(la: Terminal): Boolean = la==SEMI || la==CHOICE || la==DCHOICE || la==DSTAR || la==DUAL

  /** Follow(Term): Can la follow after a term? */
  private def followsTerm(la: Terminal): Boolean = la==RPAREN ||
    la==POWER || la==STAR || la==SLASH || la==PLUS || la==MINUS ||  // from T in terms
    la==EQ || la==NOTEQ || la==GREATEREQ || la==RDIA || la==LESSEQ || la==LDIA || // from T in formulas
    followsFormula(la) ||
    (if (statementSemicolon) la==SEMI || la==RBRACE || la==AMP
    else la==SEMI || la==CHOICE || la==STAR || la==DCHOICE || la==DSTAR || la==RBRACE || la==COMMA) || // from T in programs
    la==COMMA || // from T in ODE systems
    la==PRIME || la==EOF

  /** Is la a (binary) operator that only works for terms? */
  private def termBinOp(la: Terminal): Boolean =
    la==POWER || la==STAR || la==SLASH || la==PLUS || la==MINUS ||  // from T in terms
      la==EQ || la==NOTEQ || la==GREATEREQ || la==LESSEQ // from T in formulas
  //|| la==RDIA || la==LDIA // from T in formulas but also possibly as modalities

  /** Follow(Program): Can la follow after a program? */
  private def followsProgram(la: Terminal): Boolean = la==RBRACE || la==CHOICE || la==STAR/**/ ||
    la==DCHOICE || la==MINUS /* -- demonic choice notation */ || la==DSTAR ||
    (if (statementSemicolon) firstProgram(la) || /*Not sure:*/ la==SEMI else la==SEMI)  ||
    la==RBOX || la==RDIA ||  // from P in programs
    la==COMMA || la==AMP ||  // from D in differential programs
    la==EOF ||
    la==DUAL ||              // from P in hybrid games
    la==INVARIANT ||         // extra: additional @annotations
    la==VARIANT ||
    la==ELSE

  /** Follow(kind(expr)): Can la follow an expression of the kind of expr? */
  private def followsExpression(expr: Expression, la: Terminal, lax: Boolean): Boolean = expr match {
    case _: DifferentialSymbol => followsTerm(la) || la==ASSIGN
    case _: Variable => followsIdentifier(la) || /*if elaborated to program*/ followsProgram(la)
    case FuncOf(_,_) => followsTerm(la) || /*elaboratable(FormulaKind, t)!=None &&*/ followsFormula(la) //@todo line irrelevant since followsTerm subsumes followsFormula
    case _: Term => followsTerm(la)
    case And(Equal(_:DifferentialSymbol, _), _) => followsFormula(la) || /*if elaborated to ODE*/ followsProgram(la)
    case Equal(_:DifferentialSymbol, _) => followsFormula(la) || /*if elaborated to ODE*/ followsProgram(la)
    case f: Formula => followsFormula(la) || elaboratable(TermKind, f, lax).isDefined && followsTerm(la)
    case _: Program => followsProgram(la)
    case _ => throw ParseException("Terminal " + la.img + " unknown whether allowed to follow expression", expr)
  }

  /** Follow(Identifier): Can la follow after an identifier? */
  private def followsIdentifier(la: Terminal): Boolean = followsTerm(la) ||
    la==LPAREN || la==PRIME ||
    la==ASSIGN || la==ASSIGNANY || la==EOF || firstFormula(la) /* from \exists x ... */ ||
    la==LBANANA || la==LBARB


  // parser actions

  /** Shift to put the next input token la on the parser stack s. */
  private def shift(st: ParseState): ParseState = {
    val ParseState(s, la :: rest) = st
    if (parseErrorsAsExceptions && la.tok == EOF) throw ParseException("Unfinished input. Parser cannot shift past end of file", st)
    else require(la.tok != EOF, "Cannot shift past end of file")
    ParseState(s :+ la, rest)
  }

  /**
    * Reduce the parser stack by reducing the consuming many items from the stack to the reduced item.
    *
    * @param remainder Redundant parameter, merely for correctness checking.
    */
  private def reduce(st: ParseState, consuming: Int, reduced: Item, remainder: Stack[Item]): ParseState = {
    val ParseState(s, input) = st
    ParseState(s.drop(consuming) :+ reduced, input)
  } ensures(r => r.stack.tail == remainder, "Expected remainder stack after consuming the indicated number of stack items.")

  private def reduce(st: ParseState, consuming: Int, reduced: Expression, remainder: Stack[Item]): ParseState = reduce(st, consuming, Expr(reduced), remainder)

  /**
    * Reduce the parser stack by reducing the consuming many items from the stack to the reduced item.
    *
    * @param remainder Redundant parameter, merely for correctness checking.
    */
  private def reduce(st: ParseState, consuming: Int, reduced: Stack[Item], remainder: Stack[Item]): ParseState = {
    val ParseState(s, input) = st
    ParseState(s.drop(consuming) ++ reduced, input)
  } ensures(r => r.stack.drop(reduced.length) == remainder, "Expected remainder stack after consuming the indicated number of stack items.")

  /** Accept the given parser result. */
  private def accept(st: ParseState, result: Expression): ParseState = {
    val ParseState(s, input) = st
    require(input.length == 1 && input.head.tok == EOF, "Can only accept after all input has been read.\nRemaining input: " + input)
    require(s.length == 1, "Can only accept with one single result on the stack.\nRemaining stack: " + s)
    ParseState(Bottom :+ Accept(result), input)
  }

  /** Error parsing the next input token la when in parser stack s.*/
  private def error(st: ParseState, expect: List[Expected]): ParseState = {
    if (parseErrorsAsExceptions) throw ParseException("Unexpected token cannot be parsed", st, expect)
    else {
      val ParseState(s, la :: _) = st
      ParseState(s :+ Error("Unexpected token cannot be parsed\nFound: " + la + "\nExpected: " + expect, la.loc, st.toString), st.input)
    }
  }

  /** Error parsing the next input token la when in parser stack s.*/
  private def errormsg(st: ParseState, expect: String): ParseState = {
    val ParseState(s, la :: _) = st
    if (parseErrorsAsExceptions) throw ParseException("Unexpected token cannot be parsed", st, expect)
    else ParseState(s :+ Error("Unexpected token cannot be parsed\nFound: " + la + "\nExpected: " + expect, la.loc, st.toString), st.input)
  }

  // state lookup based on parser state

  /** Checks that stack does not start with a quantifier directly on top */
  private def isNoQuantifier(stack: Stack[Item]): Boolean =
    stack.isEmpty || !(stack.top.isInstanceOf[Token] && (stack.top.asInstanceOf[Token].tok==FORALL || stack.top.asInstanceOf[Token].tok==EXISTS))

  /** If the stack starts with an expr item, so has been reduced already, it can't be a prefix operator */
  private def isNotPrefix(st: ParseState): Boolean = st.stack match {
    case _ :+ Expr(_) :+ Token(_:OPERATOR, _)  :+ _ => true
    case _ => false
  }

  /** If the stack starts with something that is guaranteed to be a formula item */
  private def isFormula(st: ParseState): Boolean = st.stack match {
    case _ :+ Token(op:OPERATOR,_) => formulaBinOp(op)
    case _ :+ Token(op:OPERATOR,_) :+ Expr(_) => formulaBinOp(op)
    case _ :+ Expr(_:Formula) => true
    case _ => false
  }

  /** If the stack starts with something that is guaranteed to be a term item */
  private def isTerm(st: ParseState): Boolean = st.stack match {
    case _ :+ Token(op:OPERATOR,_) => termBinOp(op)
    case _ :+ Token(op:OPERATOR,_) :+ Expr(_) => termBinOp(op)
    case _ :+ Expr(_:Term) => true
    case _ => false
  }

  // this is a terrible approximation
  private def isProgram(st: ParseState): Boolean = st.stack match {
    case _ :+ Expr(_:Program) => true
    case _ :+ Token(LBRACE,_) => true
    case _ :+ Token(LBOX,_) => true
    case _ :+ Token(LBRACE,_) :+ _ => true
    case _ :+ Token(LBOX,_) :+ _ => true
    case _ :+ Expr(_:Program) :+ _ => true
    case _ => false
  }

  private def isVariable(st: ParseState): Boolean = st.stack match {
    case _ :+ Expr(_:Variable) => true
    case _ => false
  }

  // operator precedence lookup based on parser state

  import OpSpec._

  /**
    * The operator notation of the top-level operator of expr with opcode, precedence and associativity.
    * Main responsibility is to disambiguate different operators with the same notation based on kinds and parse state.
    */
  private[parser] def op(st: ParseState, tok: Terminal, kinds: List[Kind]): OpSpec = {
    // println("\top(" + tok +" " + kinds)
    (tok: @switch) match {
      //@note could almost(!) replace by reflection to search through all OpSpec and check their images.
      // terms
      case sDotTerm.op => sDotTerm
      case sNothing.op => sNothing
      case _:IDENT/*sVariable.op*/ => sVariable //@todo could also be FuncOf/PredOf if la==LPAREN but does not really change precedence
      case _:NUMBER/*sNumber.op*/ => sNumber
      //case t: FuncOf => sFuncOf
      case sDifferential.op => if (isVariable(st)) sDifferential else if (isFormula(st)) sDifferentialFormula else sDifferential
      case sPair.op => if (kinds.nonEmpty && kinds(0)!=TermKind) sDifferentialProduct else sPair
      case sMinus.op => if (kinds==List(TermKind,TermKind)||kinds==List(TermKind,ExpressionKind)) sMinus else if (kinds==List(TermKind)) sNeg
      else if (isNotPrefix(st)) sMinus else sNeg
      case sPower.op => sPower
      case sTimes.op => if (kinds==List(ProgramKind) || kinds==List(ExpressionKind))/*if (isProgram(st))*/ sLoop else sTimes
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
      case sGreater.op => if (kinds.nonEmpty && kinds(0)==ProgramKind) sNoneDone else sGreater   // 1/2 sDiamond
      case sLessEqual.op => sLessEqual
      case sLess.op => if (kinds.length>=2 && kinds(1)==ProgramKind) sNone else sLess    // 1/2 sDiamond
      case sForall.op => sForall
      case sExists.op => sExists
      //      case f: Box => sBox
      //      case f: Diamond => sDiamond
      case sNot.op => sNot
      case sAnd.op => if (kinds.nonEmpty && (kinds(0)==ProgramKind||kinds(0)==DifferentialProgramKind))/*if (isProgram(st))*/ sNoneUnfinished/*sODESystem*/ else sAnd
      case sOr.op => sOr
      case sImply.op => sImply
      case sRevImply.op => sRevImply
      case sEquiv.op => sEquiv

      // programs
      //case p: ProgramConst => sProgramConst
      //case p: DifferentialProgramConst => sDifferentialProgramConst
      case sAssign.op => sAssign //if (isDifferentialAssign(st)) sDiffAssign else sAssign
      case sAssignAny.op => sAssignAny
      case sTest.op => sTest
      case sIfThenElse.op | ELSE => sIfThenElse
      //      case p: ODESystem => sODESystem
      //      case p: AtomicODE => sAtomicODE
      case sDifferentialProduct.op => sDifferentialProduct
      //      case sLoop.op => sLoop
      case sDual.op => sDual
      case sCompose.op => sCompose
      case sChoice.op => sChoice
      case sDChoice.op => sDChoice
      case sDLoop.op => sDLoop

      case INVARIANT => sNone
      case VARIANT => sNone
      //case
      case sEOF.op => sEOF
      case o => throw ParseException("Unknown operator " + o, st)
    }
  } ensures(r => r.op == tok && r.opcode == tok.img || r==sNone || r==sNoneDone || tok.isInstanceOf[IDENT] || tok.isInstanceOf[NUMBER] || tok == ELSE, "OpSpec's opcode coincides with expected token " + tok)

}
object KeYmaeraXParser extends KeYmaeraXParser(Configuration(Configuration.Keys.LAX) == "true") {
  /** Parser state consisting of expected syntactic kind to parse currently, the item stack, and remaining input. */
  private[parser] sealed case class ParseState(stack: Stack[Item], input: TokenStream) {
    /** Lookahead location of this parser state */
    private[parser] def location: Location = input.head.loc
    /** Lookahead token of this parser state */
    private[parser] def la: Token = input.head
    override def toString: String = "ParseState(" + stack + "  <|>  " + input.mkString(", ") +")"
    /** Explanation of the top few items on the parser stack */
    def topString: String = stack.take(5).fold("")((s, e) => s + " " + e)
  }

  /** This default parser. */
  val parser: Parser = this

}
