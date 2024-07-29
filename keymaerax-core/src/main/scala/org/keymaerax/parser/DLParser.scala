/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

/**
 * Differential Dynamic Logic parser for concrete KeYmaera X notation.
 * @author
 *   Andre Platzer, James Gallicchio
 * @see
 *   Andre Platzer.
 *   [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]].
 *   Journal of Automated Reasoning, 59(2), pp. 219-266, 2017.
 */
package org.keymaerax.parser

import fastparse._
import fastparse.internal.{Msgs, Util}
import org.keymaerax.core._

import scala.annotation.{nowarn, switch, tailrec}
import scala.collection.immutable._

/**
 * Differential Dynamic Logic parser reads input strings in the concrete syntax of differential dynamic logic of
 * KeYmaera X.
 * @example
 *   Parsing formulas from strings is straightforward using [[org.keymaerax.parser.KeYmaeraXParser.apply]]:
 *   {{{
 *   val parser = DLParser
 *   val fml0 = parser("x!=5")
 *   val fml1 = parser("x>0 -> [x:=x+1;]x>1")
 *   val fml2 = parser("x>=0 -> [{x'=2}]x>=0")
 *   // parse only formulas
 *   val fml3 = parser.formulaParser("x>=0 -> [{x'=2}]x>=0")
 *   // parse only programs/games
 *   val prog1 = parser.programParser("x:=x+1;{x'=2}")
 *   // parse only terms
 *   val term1 = parser.termParser("x^2+2*x+1")
 *   }}}
 * @author
 *   Andre Platzer
 * @see
 *   [[KeYmaeraXParser]]
 */
object DLParser extends DLParser {
  assert(OpSpec.statementSemicolon, "This parser is built for formulas whose atomic statements end with a ;")
  assert(
    !OpSpec.negativeNumber,
    "This parser accepts negative number literals although it does not give precedence to them",
  )

  /** Converts Parsed.Failure to corresponding ParseException to throw. */
  private[keymaerax] def parseException(f: Parsed.Failure): ParseException = {
    val tr: Parsed.TracedFailure = f.trace()
    val inputString = f.extra.input match {
      case IndexedParserInput(input) => input
      case _ => tr.input.toString
    }

    def formatStack(input: ParserInput, stack: List[(String, Int)]) = {
      stack.map { case (s, i) => s"$s at ${input.prettyIndex(i)}" }.mkString(" / ")
    }

    def formatFound(input: ParserInput, index: Int): String = {
      val endIdx = Math.min(input.length, index + 10)
      val slice = input.slice(index, endIdx)
      // Cut off early if we encounter a \n
      val slice2 = if (slice.indexOf('\n') >= 0) slice.take(slice.indexOf('\n')) else slice
      // Escape "s and surround with "s
      "\"" + slice2.replace("\"", "\\\"") + "\""
    }

    /** The location of a parse failure. */
    def location(f: Parsed.Failure): Location =
      try {
        f.extra.input.prettyIndex(f.index).split(':').toList match {
          case line :: col :: Nil => Region(line.toInt, col.toInt)
          case line :: col :: unexpected => Region(line.toInt, col.toInt)
          case unexpected => UnknownLocation
        }
      } catch { case _: NumberFormatException => UnknownLocation }

    ParseException(
      msg = "Error parsing " +
        (tr.stack.lastOption match {
          case None => "input"
          case Some(last) => formatStack(tr.input, List(last))
        }),
      location(f),
      found = formatFound(f.extra.input, f.index),
      expect = tr.groupAggregateString,
      after = "" + tr.stack.lastOption.getOrElse(""),
      // state = tr.longMsg,
      // state = Parsed.Failure.formatMsg(tr.input, tr.stack ++ List(tr.label -> tr.index), tr.index),
      hint = "Try " + tr.terminalAggregateString,
    ).inInput(inputString, None)
  }

  /** parse from a parser with more friendly error reporting */
  private[keymaerax] def parseValue[T](input: String, parser: P[_] => P[T]): T =
    fastparse.parse(input, parser(_)) match {
      case Parsed.Success(value, index) => value
      case f: Parsed.Failure => throw parseException(f)
    }
}

/**
 * Differential Dynamic Logic parser reads input strings in the concrete syntax of differential dynamic logic of
 * KeYmaera X.
 *
 * @example
 *   Parsing formulas from strings is straightforward using [[org.keymaerax.parser.KeYmaeraXParser.apply]]:
 *   {{{
 *   val parser = DLParser
 *   val fml0 = parser("x!=5")
 *   val fml1 = parser("x>0 -> [x:=x+1;]x>1")
 *   val fml2 = parser("x>=0 -> [{x'=2}]x>=0")
 *   // parse only formulas
 *   val fml3 = parser.formulaParser("x>=0 -> [{x'=2}]x>=0")
 *   // parse only programs/games
 *   val prog1 = parser.programParser("x:=x+1;{x'=2}")
 *   // parse only terms
 *   val term1 = parser.termParser("x^2+2*x+1")
 *   }}}
 * @author
 *   Andre Platzer
 * @see
 *   [[KeYmaeraXParser]]
 * @see
 *   [[org.keymaerax.parser]]
 * @see
 *   [[http://keymaeraX.org/doc/dL-grammar.md Grammar]]
 * @see
 *   [[https://github.com/LS-Lab/KeYmaeraX-release/wiki/KeYmaera-X-Syntax-and-Informal-Semantics Wiki]]
 */
class DLParser extends Parser {
  import DLParser.parseException
  private val checkAgainst: Option[Parser] = ParserInit.checkAgainstFromConfig()

  /**
   * Parse the input string in the concrete syntax as a differential dynamic logic expression
   *
   * @param input
   *   the string to parse as a dL formula, dL term, or dL program.
   * @ensures
   *   apply(printer(\result)) == \result
   * @throws ParseException
   *   if `input` is not a well-formed expression of differential dynamic logic or differential game logic.
   */
  override def apply(input: String): Expression = exprParser(ParserHelper.checkUnicode(ParserHelper.removeBOM(input)))

  private def parseAndCompare[A](
      newParser: P[_] => P[A],
      checkAgainst: Option[String => A],
      name: String,
  ): String => A = s => {
    val newres = fastparse.parse(ParserHelper.checkUnicode(ParserHelper.removeBOM(s)), newParser(_)) match {
      case Parsed.Success(value, _) => Right(value)
      case f: Parsed.Failure => Left(parseException(f))
    }
    checkAgainst match {
      case Some(p) =>
        val oldres =
          try { Right(p(s)) }
          catch { case e: Throwable => Left(e) }
        if (oldres != newres && (oldres.isRight || newres.isRight)) {
          println(s"Parser disagreement ($name): `$s`")
          println(s"KYXParser:\n${oldres match {
              case Left(x) => x.toString
              case Right(x: Expression) => KeYmaeraXNoContractPrettyPrinter(x)
              case Right(x) => x.toString
            }}")
          println(s"DLParser:\n${newres match {
              case Left(x) => x.toString
              case Right(x: Expression) => KeYmaeraXNoContractPrettyPrinter(x)
              case Right(x) => x.toString
            }}")
        }
      case None => // nothing to do
    }

    newres match {
      case Left(e) => throw e
      case Right(res) => res
    }
  }

  /** Parse the input string in the concrete syntax as a differential dynamic logic expression */
  val exprParser: String => Expression = parseAndCompare(fullExpression(_), checkAgainst.map(_.apply), "expression")

  /** Parse the input string in the concrete syntax as a differential dynamic logic term */
  override val termParser: String => Term = parseAndCompare(fullTerm(_), checkAgainst.map(_.termParser), "term")

  /** Parse the input string in the concrete syntax as a differential dynamic logic formula */
  override val formulaParser: String => Formula =
    parseAndCompare(fullFormula(_), checkAgainst.map(_.formulaParser), "formula")

  /** Parse the input string in the concrete syntax as a differential dynamic logic program */
  override val programParser: String => Program =
    parseAndCompare(fullProgram(_), checkAgainst.map(_.programParser), "program")

  /** Parse the input string in the concrete syntax as a differential dynamic logic differential program */
  override val differentialProgramParser: String => DifferentialProgram =
    parseAndCompare(fullDifferentialProgram(_), checkAgainst.map(_.differentialProgramParser), "diff. program")

  /** Parse the input string in the concrete syntax as a differential dynamic logic sequent. */
  override val sequentParser: String => Sequent =
    parseAndCompare(fullSequent(_), checkAgainst.map(_.sequentParser), "sequent")

  /* TODO: Unused
  /** Parse the input string in the concrete syntax as a ;; separated list fof differential dynamic logic sequents . */
  val sequentListParser: String => List[Sequent] = parseAndCompare(fullSequentList(_), KeYmaeraXParser.sequentListParser, "term")
   */

  /** Parse the input string in the concrete syntax as a stored list of differential dynamic logic sequents. */
  override val storedInferenceParser: String => List[Sequent] =
    parseAndCompare(storedProvable(_), checkAgainst.map(_.storedInferenceParser), "provable")

  /**
   * A pretty-printer that can write the output that this parser reads
   *
   * @ensures
   *   \forall e: apply(printer(e)) == e
   */
  override lazy val printer: KeYmaeraXPrettyPrinter.type = KeYmaeraXPrettyPrinter

  /**
   * Register a listener for @annotations during the parse.
   *
   * @todo
   *   this design is suboptimal.
   */
  override def setAnnotationListener(listener: (Program, Formula) => Unit): Unit = this.theAnnotationListener = listener

  /** @inheritdoc */
  override def annotationListener: (Program, Formula) => Unit = theAnnotationListener

  // internals

  private[parser] var theAnnotationListener: ((Program, Formula) => Unit) = { (p, inv) => }

  /** Report an @invariant @annotation to interested parties */
  private def reportAnnotation(p: Program, invariant: Formula): Unit = theAnnotationListener(p, invariant)

  // *****************
  // implementation
  // *****************

  // Whitespace is the usual ' \t\n\r' but also comments /* ... */
  implicit object DLWhitespace extends Whitespace {
    override def apply(ctx: P[_]): P[Unit] = {
      val input = ctx.input
      val startIndex = ctx.index

      @tailrec
      def rec(current: Int, state: Int): ParsingRun[Unit] = {
        if (!input.isReachable(current)) {
          if (state == 0) {
            if (ctx.verboseFailures) ctx.reportTerminalMsg(startIndex, Msgs.empty)
            ctx.freshSuccessUnit(current)
          } else if (state == 1) {
            if (ctx.verboseFailures) ctx.reportTerminalMsg(startIndex, Msgs.empty)
            ctx.freshSuccessUnit(current - 1)
          } else {
            ctx.cut = true
            val res = ctx.freshFailure(current)
            if (ctx.verboseFailures) ctx.reportTerminalMsg(startIndex, () => Util.literalize("*/"))
            res
          }
        } else {
          val currentChar = input(current)
          (state: @switch) match {
            case 0 => (currentChar: @switch) match {
                case ' ' | '\t' | '\n' | '\r' => rec(current + 1, state)
                case '/' => rec(current + 1, state = 1)
                case _ => ctx.freshSuccessUnit(current)
              }
            case 1 => (currentChar: @switch) match {
                case '*' => rec(current + 1, state = 2)
                case _ => ctx.freshSuccessUnit(current - 1)
              }
            case 2 => rec(current + 1, state = if (currentChar == '*') 3 else state)
            case 3 => (currentChar: @switch) match {
                case '/' => rec(current + 1, state = 0)
                case '*' => rec(current + 1, state = 3)
                case _ => rec(current + 1, state = 2)
              }
          }
        }
      }

      rec(current = ctx.index, state = 0)
    }
  }

  import DLWhitespace._

  def fullTerm[$: P]: P[Term] = P(Start ~ term(true) ~ End)
  def fullFormula[$: P]: P[Formula] = P(Start ~ formula ~ End)
  def fullProgram[$: P]: P[Program] = P(Start ~ program ~ End)
  def fullDifferentialProgram[$: P]: P[DifferentialProgram] = {
    /* Surrounding braces are not allowed in differential programs
      but some code has an extra surrounding {} */
    P(Start ~ ("{" ~ diffProgram ~ "}" | diffProgram) ~ End)
  }

  def fullExpression[$: P]: P[Expression] = P(
    Start ~
      // try if the entire string parses as program, term, or formula, backtrack to start for each attempt since
      // cuts in program/term may prevent parsing a perfectly well-shaped term/formula
      (NoCut(program) ~ End | NoCut(term(false)) ~ End | NoCut(formula) ~ End)
      // but if all of those fail, try parsing with cuts for better error message
      | expression ~ End
  )

  def expression[$: P]: P[Expression] = P(
    program |
      // Term followed by comparator, or ambiguous term followed by formula operators,
      // should not be parsed as a term
      !(term(true) ~ (comparator | StringIn("->", "<-", "<->", "&", "|", "→", "←", "↔", "∧", "∨"))) ~
      // Even then, if ambiguous we still want to backtrack
      term(false) | formula
  )

  def fullSequent[$: P]: P[Sequent] = P(Start ~ sequent ~ End)

  def fullSequentList[$: P]: P[List[Sequent]] = P(Start ~ sequentList ~ End)

  // *****************
  // terminals
  // *****************

  /** Explicit nonempty whitespace terminal. */
  def blank[$: P]: P[Unit] = P(CharsWhileIn(" \t\r\n", 1))

  /** parse a number literal enclosed in (), which is allowed to be a negative number */
  def negNumberLiteral[$: P]: P[Number] = P(
    "(" ~ P(("-".? ~~ CharIn("0-9").repX(1) ~~ ("." ~~ CharIn("0-9").repX(1)).?).!).map(s => Number(BigDecimal(s))) ~
      ")" ~~ !"'"
  )

  /** parses a number literal */
  def numberLiteral[$: P]: P[Number] = P((CharIn("0-9").repX(1) ~~ ("." ~~/ CharIn("0-9").repX(1)).?).!)
    .map(s => Number(BigDecimal(s)))

  /** parses a number */
  def number[$: P](doAmbigCuts: Boolean): P[Number] = P(
    (if (doAmbigCuts) negNumberLiteral./ else NoCut(negNumberLiteral)) |
      (if (doAmbigCuts) numberLiteral./ else NoCut(numberLiteral))
  )

  /** matches keywords. An identifier cannot be a keyword. */
  def keywords: Set[String] = Set(
    "true",
    "false",
    "Real",
    "Bool",
    "HP",
    "HG",
    "Axiom",
    "End",
    "Functions",
    "Definitions",
    "ProgramVariables",
    "Variables",
    "Problem",
    "Tactic",
    "implicit",
    "Sequent",
    "Formula",
    "Lemma",
    "Tool",
    "SharedDefinitions",
    "ArchiveEntry",
    "Lemma",
    "Theorem",
    "Exercise",
  )

  /**
   * parse an identifier.
   * @return
   *   the name and its index (if any).
   * @note
   *   Index is normalized so that x_00 cannot be mentioned and confused with x_0.
   * @note
   *   Keywords are not allowed as identifiers.
   */
  def ident[$: P]: P[(String, Option[Int])] = P(
    DLParserUtils.filterWithMsg((CharIn("a-zA-Z") ~~ CharIn("a-zA-Z0-9").repX ~~ ("_" ~~ !CharIn("0-9")).?).!)(
      !keywords.contains(_)
    )("Keywords cannot be used as identifiers") ~~ ("_" ~~ normNatural).? ~~ (!CharIn("a-zA-Z_"))
  )

  /** `.` or `._2`: dot parsing */
  def dot[$: P]: P[DotTerm] = P(("." | "•") ~~ ("_" ~~ ("0" | CharIn("1-9") ~~ CharIn("0-9").repX).!).?)
    .map(idx => DotTerm(Real, idx.map(_.toInt)))

  // terminals not used here but provided for other DL parsers

  def stringInterior[$: P]: P[String] = (CharPred(c => c != '\\' && c != '\"')./ | "\\\""./ | "\\").repX.!

  /** "whatevs": Parse a string literal. (([^\\"]|\\"|\\(?!"))*+) */
  def string[$: P]: P[String] = P("\"" ~~/ stringInterior ~~ "\"")

  /** "-532": Parse an integer literal, unnormalized. */
  def integer[$: P]: P[Int] = P(("-".? ~~ CharIn("0-9").repX(1)).!).map(s => s.toInt)

  /** "532": Parse a (nonnegative) natural number literal, unnormalized. */
  def natural[$: P]: P[Int] = P(CharIn("0-9").repX(1).!).map(s => s.toInt)

  /** "532": Parse a (nonnegative) natural number literal, normalized. */
  def normNatural[$: P]: P[Int] =
    P(("0" | CharIn("1-9") ~~ CharIn("0-9").repX).!)("normalized natural number", implicitly).map(s => s.toInt)

  // *****************
  // base parsers
  // *****************

  def baseVariable[$: P]: P[BaseVariable] = ident.map(s => Variable(s._1, s._2, Real))
  def diffVariable[$: P]: P[DifferentialSymbol] = P(baseVariable ~ "'").map(DifferentialSymbol(_))
  @nowarn("msg=match may not be exhaustive")
  def variable[$: P]: P[Variable] = P(baseVariable ~ "'".!.?).map {
    case (v, None) => v
    case (v, Some("'")) => DifferentialSymbol(v)
  }

  // *****************
  // term parser
  // *****************

  private def getEither(e: Either[Term, Term]): Term = e match {
    case Left(t) => t
    case Right(t) => t
  }

  private def assocSign(t: Either[Term, Term]): Term = t match {
    case Left(t) => t
    case Right(Neg(Times(l, r))) if !Parser.weakNeg => Times(Neg(l), r)
    case Right(Neg(Divide(l, r))) if !Parser.weakNeg => Divide(Neg(l), r)
    case Right(t) => t
  }

  /**
   * Parse a term.
   *
   * Some terms are ambiguous with formulas, in particular
   *   - Parentheses (term parens vs function parens)
   *   - Functions vs predicates
   *   - UnitFunctionals vs UnitPredicationals
   * So, we want to allow backtracking on these ambiguous syntax forms if we are not sure whether the input is a term or
   * a formula.
   *
   * If doAmbigCuts is true, we assume the input is a term, and perform all permissible cuts. If it is false, we only
   * perform cuts that are unambiguous indicators the input is a term.
   */
  @nowarn("msg=match may not be exhaustive")
  def term[$: P](doAmbigCuts: Boolean): P[Term] = P(
    (if (Parser.weakNeg) signed(summand(doAmbigCuts)) else summand(doAmbigCuts).map(t => Left(t))) ~
      // Note: on weakNeg, the summand is signed, rather than the first multiplicand
      // in `summand`, because -5*6 is parsed as -(5*6),
      // otherwise (on !weakNeg), the multiplicand is signed because then -x*y is parsed as (-x)*y
      (("+" | "-" ~ !">").!./ ~ signed(summand(doAmbigCuts))).rep
  ).map { case (left, sums) =>
    sums.foldLeft(assocSign(left)) {
      case (m1, ("+", m2)) => Plus(m1, assocSign(m2))
      case (m1, ("-", m2)) => Minus(m1, assocSign(m2))
    }
  }

  @nowarn("msg=Exhaustivity analysis reached max recursion depth") @nowarn("msg=match may not be exhaustive")
  private def mulDiv(left: Term, rest: Seq[(String, Either[Term, Term])]): Term = (left, rest) match {
    case (l, Nil) => l
    case (l, (op, Right(n @ Neg(c))) +: r) if Parser.weakNeg =>
      op match {
        case "*" => Times(l, Neg(mulDiv(c, r)))
        case "/" => r match {
            case Nil => Divide(left, n)
            case ("*", _) +: _ => mulDiv(Divide(left, n), r)
            case ("/", _) +: _ => Divide(l, Neg(mulDiv(c, r)))
          }
      }
    case (l, (op, t) +: r) => op match {
        case "*" => mulDiv(Times(l, getEither(t)), r)
        case "/" => mulDiv(Divide(l, getEither(t)), r)
      }
  }

  def summand[$: P](doAmbigCuts: Boolean): P[Term] =
    // Lookahead is to avoid /* */ comments
    ((if (Parser.weakNeg) multiplicand(doAmbigCuts).map(t => Left(t)) else signed(multiplicand(doAmbigCuts))) ~
      (("*" | "/" ~~ !"*").!./ ~ signed(multiplicand(doAmbigCuts))).rep).map { case (left, rest) =>
      mulDiv(getEither(left), rest)
    }

  def multiplicand[$: P](doAmbigCuts: Boolean): P[Term] =
    (baseTerm(doAmbigCuts) ~ ("^"./ ~ signed(multiplicand(doAmbigCuts))).rep).map { case (left, pows) =>
      (left +: pows.map(getEither)).reduceRight(Power)
    }

  def baseTerm[$: P](doAmbigCuts: Boolean): P[Term] = number(doAmbigCuts) | dot./ | function(doAmbigCuts)
    .flatMapX[Term](diff) | unitFunctional(doAmbigCuts).flatMapX[Term](diff) | variable | termList(doAmbigCuts)
    .flatMapX[Term](diff) | "__________".!.map(_ => UnitFunctional("exerciseF_", AnyArg, Real))

  def function[$: P](doAmbigCuts: Boolean): P[FuncOf] = P(
    // Note interpretations can only appear on functions (not predicates)
    // so that cut is safe
    ident ~~ ("<<" ~/ formula ~ ">>").? ~
      // Note that ident(termList) can still be ambiguous even if termList
      // is unambiguously a term (it will always be unambiguously a term)
      // so in the doAmbigCuts == false case we want to ignore those cuts
      (if (doAmbigCuts) termList(true) else NoCut(termList(true)))
  ).map({ case (s, idx, interp, ts) =>
    FuncOf(
      interp match {
        case Some(i) => Function(s, idx, ts.sort, Real, Some(i))
        case None => OpSpec.func(s, idx, ts.sort, Real)
      },
      ts,
    )
  })

  @nowarn("msg=match may not be exhaustive")
  def unitFunctional[$: P](doAmbigCuts: Boolean): P[UnitFunctional] =
    P(ident ~~ (if (doAmbigCuts) space else NoCut(space))).map({ case (s, None, sp) => UnitFunctional(s, sp, Real) })

  /**
   * `p | -p`: possibly signed occurrences of what is parsed by parser `p` Note we try `p` before `-p` because some
   * parsers (like `number`) also consume -s. Distinguishes between Left(Neg(x)) = (-x) and Right(Neg(x)) = -x.
   */
  def signed[$: P](p: => P[Term]): P[Either[Term, Term]] = p.map(t => Left(t)) | (("-" ~~ !">") ~ signed(p)).map({
    case Left(t) => Right(Neg(t))
    case Right(t) => Right(Neg(t))
  })

  /** Parses term' */
  @nowarn("msg=match may not be exhaustive")
  def diff[$: P](left: Term): P[Term] = "'"
    .!
    .?
    .map {
      case None => left
      case Some("'") => Differential(left)
    }

  /** (t1,t2,t3,...,tn) parenthesized list of terms */
  def termList[$: P](doAmbigCuts: Boolean): P[Term] = P(
    "(" ~~ !"|" ~ (if (doAmbigCuts) Pass./ else Pass) ~
      // Note that a single-element termList can be ambiguous with formulas,
      // but a multi-element termList must be a term
      (if (doAmbigCuts) term(true) else NoCut(term(true))).rep(sep = ","./) ~ ")"
  ).map(ts => ts.reduceRightOption(Pair).getOrElse(Nothing))

  /** (|x1,x2,x3|) parses a space declaration */
  def space[$: P]: P[Space] = P("(|" ~ variable.rep(sep = ",") ~ "|)").map(ts => if (ts.isEmpty) AnyArg else Except(ts))

  // *****************
  // formula parser
  // *****************

  def formula[$: P]: P[Formula] = P(biimplication)

  /* <-> (lowest prec, non-assoc) */
  def biimplication[$: P]: P[Formula] = (backImplication ~ (("<->" | "↔") ~/ backImplication).?).map {
    case (left, None) => left
    case (left, Some(r)) => Equiv(left, r)
  }

  /* <- (left-assoc) */
  def backImplication[$: P]: P[Formula] =
    (implication ~~ (((blank ~ "<-" ~~ blank).opaque("\" <- \"") | (blank.? ~ "←").opaque("\"←\"")) ~/ implication).rep)
      .map { case (left, hyps) => hyps.foldLeft(left) { case (acc, hyp) => Imply(hyp, acc) } }

  /* -> (right-assoc) */
  def implication[$: P]: P[Formula] = (disjunct ~ (("->" | "→") ~/ disjunct).rep).map { case (left, concls) =>
    (left +: concls).reduceRight(Imply)
  }

  /* | (right-assoc) */
  def disjunct[$: P]: P[Formula] = (conjunct ~ (("|" | "∨") ~/ conjunct).rep).map { case (left, conjs) =>
    (left +: conjs).reduceRight(Or)
  }

  /* & (right-assoc) */
  def conjunct[$: P]: P[Formula] = (baseF ~ (("&" | "∧") ~/ baseF).rep).map { case (left, forms) =>
    (left +: forms).reduceRight(And)
  }

  /** Base formulas */
  def baseF[$: P]: P[Formula] =
    (
      // First try unambiguously formula things
      unambiguousBaseF |
        // Now we try parsing a comparison, which will fail & backtrack
        // if it can't parse a term
        comparison |
        // Since we already tried (and failed) to parse a term, now we
        // can safely try the ambiguous cases
        ambiguousBaseF
    )

  // Ambiguous base formula cases. Note that we still do not cut on
  // the ambiguous constructions, because we want error aggregates to
  // still allow for these ambiguous cases to actually be terms
  @nowarn("msg=match may not be exhaustive")
  def ambiguousBaseF[$: P]: P[Formula] =
    (
      /* variables */
      (ident ~~ !"(").map { case (name, idx) => PredOf(Function(name, idx, Unit, Bool), Nothing) } |
        /* predicate OR function */
        (ident ~~ NoCut(termList(true)) ~ "'".!.?).map { case (name, idx, args, diff) =>
          val p = PredOf(Function(name, idx, args.sort, Bool), args)
          diff match {
            case None => p
            case Some("'") => DifferentialFormula(p)
          }
        }
        /* unit predicational OR unit functional */
        |
        DLParserUtils
          .filterWithMsg(ident ~~ NoCut(space) ~ "'".!.?)(_._2.isEmpty)("Unit predicationals cannot have indices")
          .map({ case (name, _, args, diff) =>
            val p = UnitPredicational(name, args)
            diff match {
              case None => p
              case Some("'") => DifferentialFormula(p)
            }
          })
        /* parenthesized formula OR term */
        | ("(" ~ formula ~ ")" ~ "'".!.?).map({
          case (form, None) => form
          case (form, Some("'")) => DifferentialFormula(form)
        })
    )

  @nowarn("msg=match may not be exhaustive")
  def unambiguousBaseF[$: P]: P[Formula] =
    /* atomic formulas, constant T/F, quantifiers, modalities */
    "true".!.map(_ => True) | "false".!.map(_ => False) |
      /* Note we cannot cut after true/false because it could also
       * be the start of an identifier */
      (("\\forall" | "\\exists" | "∀" | "∃").! ~~/ blank ~ variable.repX(min = 1, sep = ",") ~ baseF).map {
        case ("\\forall" | "∀", x, f) => x.foldLeft(f)({ case (f, x) => Forall(x :: Nil, f) })
        case ("\\exists" | "∃", x, f) => x.foldLeft(f)({ case (f, x) => Exists(x :: Nil, f) })
      } | ((("[".! ~/ program ~ "]".!) | ("<".! ~/ program ~ ">".!)) ~/ baseF).map {
        case ("[", p, "]", f) => Box(p, f)
        case ("<", p, ">", f) => Diamond(p, f)
      } | ("!" ~/ baseF).map(Not) | predicational | "⎵".!.map(_ => DotFormula) |
      /* Exercise */
      "__________".!.map(_ => UnitPredicational("exerciseP_", AnyArg))

  /** Parses a comparison, given the left-hand term */
  @nowarn("msg=match may not be exhaustive")
  def comparison[$: P]: P[Formula] = P(
    // We don't know if the starting input is a term, but after
    // seeing the comparator we know the RHS must be a term
    (term(false) ~ comparator.! ~/ term(true)).map {
      case (left, "=", right) => Equal(left, right)
      case (left, "!=" | "≠", right) => NotEqual(left, right)
      case (left, ">=" | "≥", right) => GreaterEqual(left, right)
      case (left, ">", right) => Greater(left, right)
      case (left, "<=" | "≤", right) => LessEqual(left, right)
      case (left, "<", right) => Less(left, right)
    }
  )

  def comparator[$: P]: P[Unit] = P("=" ~~ !"=" | "!=" | "≠" | ">=" | "≥" | ">" | "<=" | "≤" | "<" ~~ !"-")

  /** Unit predicationals c(||) */
  @nowarn("msg=match may not be exhaustive")
  def unitPredicational[$: P]: P[UnitPredicational] = P(ident ~~ space).map({ case (s, None, sp) =>
    UnitPredicational(s, sp)
  })

  /** Regular predicationals C{} */
  def predicational[$: P]: P[PredicationalOf] = P(ident ~~ "{" ~/ formula ~ "}").map({ case (s, idx, f) =>
    PredicationalOf(Function(s, idx, Bool, Bool), f)
  })

  // *****************
  // program parser
  // *****************

  @nowarn("msg=match may not be exhaustive")
  def programSymbol[$: P]: P[Program] = P(
    DLParserUtils
      .filterWithMsg(ident ~~ odeSpace.? ~ (";" | "^@").!./)(_._2.isEmpty)("Program symbols cannot have an index")
      .map({ case (s, None, taboo, postfix) =>
        val p = ProgramConst(s, taboo.getOrElse(AnyArg))
        postfix match {
          case ";" => p
          case "^@" => Dual(p)
        }
      })
  )
  // @todo combine system symbol and space taboo
  @nowarn("msg=match may not be exhaustive")
  def systemSymbol[$: P]: P[AtomicProgram] = P(
    DLParserUtils
      .filterWithMsg(ident ~~ "{|^@" ~/ variable.rep(sep = ","./) ~ "|}" ~ ";")(_._2.isEmpty)(
        "System symbols cannot have an index"
      )
      .map({ case (s, None, taboo) => SystemConst(s, if (taboo.isEmpty) AnyArg else Except(taboo)) })
  )

  def programExercise[$: P]: P[AtomicProgram] = "__________".!.map(_ => SystemConst("exerciseS_", AnyArg))

  @nowarn("msg=match may not be exhaustive")
  def assign[$: P]: P[AtomicProgram] = ((variable ~ ":=" ~/ ("*".!./.map(Left(_)) | term(true).map(Right(_))) ~ ";")
    .map({
      case (x, Left("*")) => AssignAny(x)
      case (x, Right(t)) => Assign(x, t)
    }))
  def test[$: P]: P[Test] = ("?" ~/ formula ~ ";").map(f => Test(f))
  @nowarn("msg=match may not be exhaustive")
  def braceP[$: P]: P[Program] = ("{" ~ program ~ "}" ~/ (("*" | "×")./.! ~ annotation.?).?).map({
    case (p, None) => p
    case (p, Some(("*", None))) => Loop(p)
    case (p, Some(("*", Some(inv)))) => inv.foreach(reportAnnotation(Loop(p), _)); Loop(p)
    case (p, Some(("×", _))) => Dual(Loop(Dual(p)))
  })
  def odeprogram[$: P]: P[ODESystem] =
    (diffProgram ~
      ("&" ~/ formula.flatMapX(f => {
        if (StaticSemantics.isDifferential(f)) Fail.opaque(
          "No differentials in evolution domain constraints; instead of the primed variables use their right-hand sides."
        )
        else Pass(f)
      })).?).map({ case (p, f) => ODESystem(p, f.getOrElse(True)) })
  def odesystem[$: P]: P[ODESystem] = ("{" ~ odeprogram ~ "}" ~/ annotation.?).map({
    case (p, None) => p
    case (p, Some(inv)) => inv.foreach(reportAnnotation(p, _)); p
  })

  def baseP[$: P]: P[Program] =
    (systemSymbol | programSymbol | assign | test | ifthen | odesystem | braceP | programExercise)

  /** Parses dual notation: baseP or baseP&#94;@ */
  @nowarn("msg=match may not be exhaustive")
  def dual[$: P]: P[Program] = (baseP ~ "^@".!./.?).map({
    case (p, None) => p
    case (p, Some("^@")) => Dual(p)
  })

  /** Parses an annotation */
  def annotation[$: P]: P[Seq[Formula]] =
    ("@invariant" | "@variant") ~/ "(" ~/ formula.rep(min = 1, sep = ","./).map(_.toList) ~ ")"

  def sequence[$: P]: P[Program] = ((dual ~/ ";".?).rep(1)).map(ps => ps.reduceRight(Compose))

  @nowarn("msg=match may not be exhaustive")
  def choice[$: P]: P[Program] = (sequence ~/ (("++"./ | "∪"./ | "--" | "∩"./).! ~ sequence).rep).map({ case (p, ps) =>
    ((None, p) +: ps.map { case (s, p) => (Some(s), p) })
      .reduceRight[(Option[String], Program)] {
        case ((pre, p), (Some("++" | "∪"), q)) => (pre, Choice(p, q))
        case ((pre, p), (Some("--" | "∩"), q)) => (pre, Dual(Choice(Dual(p), Dual(q))))
      }
      ._2
  })

  // @note macro-expands
  def ifthen[$: P]: P[Program] = ("if" ~/ "(" ~/ formula ~ ")" ~ braceP ~ ("else" ~/ braceP).?).map({
    case (f, p, None) => Choice(Compose(Test(f), p), Test(Not(f)))
    case (f, p, Some(q)) => Choice(Compose(Test(f), p), Compose(Test(Not(f)), q))
  })

  /** program: Parses a dL program. */
  def program[$: P]: P[Program] = P(choice)

  // *****************
  // differential program parser
  // *****************

  def ode[$: P]: P[AtomicODE] = P(diffVariable ~ "=" ~/ term(true)).map({ case (x, t) => AtomicODE(x, t) })
  @nowarn("msg=match may not be exhaustive")
  def diffProgramSymbol[$: P]: P[DifferentialProgramConst] = P(
    DLParserUtils
      .filterWithMsg(ident ~~ odeSpace.?)(_._2.isEmpty)("Differential program symbols cannot have an index")
      .map({
        case (s, None, None) => DifferentialProgramConst(s)
        case (s, None, Some(sp)) => DifferentialProgramConst(s, sp)
      })
  )
  def diffExercise[$: P]: P[DifferentialProgramConst] = "__________"
    .!
    .map(_ => DifferentialProgramConst("exerciseD_", AnyArg))
  def atomicDP[$: P]: P[AtomicDifferentialProgram] = (ode | diffProgramSymbol | diffExercise)

  /** {|x1,x2,x3|} parses a space declaration */
  def odeSpace[$: P]: P[Space] = P("{|" ~ (variable ~ ("," ~/ variable).rep).? ~ "|}").map({
    case Some((t, ts)) => Except(ts.+:(t))
    case None => AnyArg
  })

  def diffProduct[$: P]: P[DifferentialProgram] = (atomicDP ~ ("," ~/ atomicDP).rep).map({ case (p, ps) =>
    (ps.+:(p)).reduceRight(DifferentialProduct.apply)
  })

  /** diffProgram: Parses a dL differential program. */
  def diffProgram[$: P]: P[DifferentialProgram] = P(diffProduct)

  // *****************
  // sequent parser
  // *****************

  /** sequent ::= `aformula1 , aformula2 , ... , aformulan ==>  sformula1 , sformula2 , ... , sformulam`. */
  def sequent[$: P]: P[Sequent] = P(formula.rep(sep = ","./) ~ "==>" ~ formula.rep(sep = ","./))
    .map({ case (ante, succ) => Sequent(ante.toIndexedSeq, succ.toIndexedSeq) })

  /** sequentList ::= sequent `;;` sequent `;;` ... `;;` sequent. */
  def sequentList[$: P]: P[List[Sequent]] = P(sequent.rep(sep = ";;"./)).map(_.toList)

  /** sequent ::= `aformula1 :: aformula2 :: ... :: aformulan ==>  sformula1 :: sformula2 :: ... :: sformulam`. */
  def storedSequent[$: P]: P[Sequent] = P(formula.rep(sep = "::"./) ~ "==>" ~ formula.rep(sep = "::"./))
    .map({ case (ante, succ) => Sequent(ante.toIndexedSeq, succ.toIndexedSeq) })

  def storedProvable[$: P]: P[List[Sequent]] = P(Start ~ storedSequent.rep(sep = "\\from"./) ~ "\\qed" ~ End)
    .map(_.toList)
}
