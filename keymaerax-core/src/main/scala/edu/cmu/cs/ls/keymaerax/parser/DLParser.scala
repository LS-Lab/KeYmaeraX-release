/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
/**
  * Differential Dynamic Logic parser for concrete KeYmaera X notation.
  * @author Andre Platzer, James Gallicchio
  * @see Andre Platzer. [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 59(2), pp. 219-266, 2017.
  */
package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.core._
import fastparse._
import fastparse.internal.Util

import scala.annotation.{switch, tailrec}
import scala.collection.immutable._

/**
  * Differential Dynamic Logic parser reads input strings in the concrete syntax of differential dynamic logic of KeYmaera X.
  * @example
  * Parsing formulas from strings is straightforward using [[edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXParser.apply]]:
  * {{{
  * val parser = DLParser
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
  * @see [[KeYmaeraXParser]]
  */
object DLParser extends DLParser {
  assert(OpSpec.statementSemicolon, "This parser is built for formulas whose atomic statements end with a ;")
  assert(!OpSpec.negativeNumber, "This parser accepts negative number literals although it does not give precedence to them")

  /** Converts Parsed.Failure to corresponding ParseException to throw. */
  private[keymaerax] def parseException(f: Parsed.Failure): ParseException = {
    val tr: Parsed.TracedFailure = f.trace()
    val inputString = f.extra.input match {
      case IndexedParserInput(input) => input
      case _ => tr.input + ""
    }

    def formatStack(input: ParserInput, stack: List[(String, Int)]) = {
      stack.map{case (s, i) => s"$s at ${input.prettyIndex(i)}"}.mkString(" / ")
    }

    def formatFound(input: ParserInput, index: Int): String = {
      val endIdx = Math.min(input.length, index+10)
      val slice = input.slice(index, endIdx)
      // Cut off early if we encounter a \n
      val slice2 = if (slice.indexOf('\n') >= 0) slice.take(slice.indexOf('\n')) else slice
      // Escape "s and surround with "s
      "\"" + slice2.replaceAllLiterally("\"","\\\"") + "\""
    }

    /** The location of a parse failure. */
    def location(f: Parsed.Failure): Location = try {
      f.extra.input.prettyIndex(f.index).split(':').toList match {
        case line::col::Nil => Region(line.toInt, col.toInt)
        case line::col::unexpected => Region(line.toInt, col.toInt)
        case unexpected => UnknownLocation
      }
    } catch {
      case _: NumberFormatException => UnknownLocation
    }

    ParseException(
      msg = "Error parsing " + (tr.stack.lastOption match {
        case None => "input"
        case Some(last) => formatStack(tr.input, List(last))
      }),
      location(f),
      found = formatFound(f.extra.input, f.index),
      expect = tr.groupAggregateString,
      after = "" + tr.stack.lastOption.getOrElse(""),
      // state = tr.longMsg,
      // state = Parsed.Failure.formatMsg(tr.input, tr.stack ++ List(tr.label -> tr.index), tr.index),
      hint = "Try " + tr.terminalAggregateString
    ).inInput(inputString, None)
  }

  /** parse from a parser with more friendly error reporting */
  private[keymaerax] def parseValue[T](input: String, parser: P[_] => P[T]): T = fastparse.parse(input, parser(_)) match {
    case Parsed.Success(value, index) => value
    case f: Parsed.Failure => throw parseException(f)
  }
}

/**
  * Differential Dynamic Logic parser reads input strings in the concrete syntax of differential dynamic logic of KeYmaera X.
  *
  * @example
  * Parsing formulas from strings is straightforward using [[edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXParser.apply]]:
  * {{{
  * val parser = DLParser
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
  * @see [[KeYmaeraXParser]]
  * @see [[edu.cmu.cs.ls.keymaerax.parser]]
  * @see [[http://keymaeraX.org/doc/dL-grammar.md Grammar]]
  * @see [[https://github.com/LS-Lab/KeYmaeraX-release/wiki/KeYmaera-X-Syntax-and-Informal-Semantics Wiki]]
  */
class DLParser extends Parser {
  import DLParser.parseException
  private val checkAgainst: Option[Parser] = ParserInit.checkAgainstFromConfig()
  /** Parse the input string in the concrete syntax as a differential dynamic logic expression
    *
    * @param input the string to parse as a dL formula, dL term, or dL program.
    * @ensures apply(printer(\result)) == \result
    * @throws ParseException if `input` is not a well-formed expression of differential dynamic logic or differential game logic.
    */
  override def apply(input: String): Expression = exprParser(ParserHelper.checkUnicode(ParserHelper.removeBOM(input)))

  private def parseAndCompare[A](newParser: P[_] => P[A], checkAgainst: Option[String => A], name: String): String => A =
    s => {
      val newres = fastparse.parse(ParserHelper.checkUnicode(ParserHelper.removeBOM(s)), newParser(_)) match {
        case Parsed.Success(value, _) => Right(value)
        case f: Parsed.Failure => Left(parseException(f))
      }
      checkAgainst match {
        case Some(p) =>
          val oldres = try {
            Right(p(s))
          } catch {
            case e: Throwable => Left(e)
          }
          if (oldres != newres && (oldres.isRight || newres.isRight)) {
            println(s"Parser disagreement ($name): `$s`")
            println(s"KYXParser:\n${oldres match {case Left(x) => x.toString case Right(x: Expression) => x.prettyString case Right(x) => x.toString}}")
            println(s"DLParser:\n${newres match {case Left(x) => x.toString case Right(x: Expression) => x.prettyString case Right(x) => x.toString}}")
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
  override val formulaParser: String => Formula = parseAndCompare(fullFormula(_), checkAgainst.map(_.formulaParser), "formula")

  /** Parse the input string in the concrete syntax as a differential dynamic logic program */
  override val programParser: String => Program = parseAndCompare(fullProgram(_), checkAgainst.map(_.programParser), "program")

  /** Parse the input string in the concrete syntax as a differential dynamic logic differential program */
  override val differentialProgramParser: String => DifferentialProgram =
    parseAndCompare(fullDifferentialProgram(_), checkAgainst.map(_.differentialProgramParser), "diff. program")

  /** Parse the input string in the concrete syntax as a differential dynamic logic sequent. */
  override val sequentParser: String => Sequent = parseAndCompare(fullSequent(_), checkAgainst.map(_.sequentParser), "sequent")

  /* TODO: Unused
  /** Parse the input string in the concrete syntax as a ;; separated list fof differential dynamic logic sequents . */
  val sequentListParser: String => List[Sequent] = parseAndCompare(fullSequentList(_), KeYmaeraXParser.sequentListParser, "term")
  */

  /** A pretty-printer that can write the output that this parser reads
    *
    * @ensures \forall e: apply(printer(e)) == e
    */
  override lazy val printer: KeYmaeraXPrettyPrinter.type = KeYmaeraXPrettyPrinter


  /**
    * Register a listener for @annotations during the parse.
    *
    * @todo this design is suboptimal.
    */
  override def setAnnotationListener(listener: (Program,Formula) => Unit): Unit =
    this.theAnnotationListener = listener

  /** @inheritdoc */
  override def annotationListener: (Program, Formula) => Unit = theAnnotationListener

  // internals

  private[parser] var theAnnotationListener: ((Program,Formula) => Unit) = {(p,inv) => }

  /** Report an @invariant @annotation to interested parties */
  private def reportAnnotation(p: Program, invariant: Formula): Unit = theAnnotationListener(p,invariant)

  //*****************
  // implementation
  //*****************

  // Whitespace is the usual ' \t\n\r' but also comments /* ... */
  private object DLWhitespace {
    implicit val whitespace = {implicit ctx: ParsingRun[_] =>
      val input = ctx.input
      val startIndex = ctx.index
      @tailrec def rec(current: Int, state: Int): ParsingRun[Unit] = {
        if (!input.isReachable(current)) {
          if (state == 0) ctx.freshSuccessUnit(current)
          else if (state == 1)  ctx.freshSuccessUnit(current - 1)
          else {
            ctx.cut = true
            val res = ctx.freshFailure(current)
            if (ctx.verboseFailures) ctx.setMsg(startIndex, () => Util.literalize("*/"))
            res
          }
        } else {
          val currentChar = input(current)
          (state: @switch) match{
            case 0 =>
              (currentChar: @switch) match{
                case ' ' | '\t' | '\n' | '\r' => rec(current + 1, state)
                case '/' => rec(current + 1, state = 1)
                case _ => ctx.freshSuccessUnit(current)
              }
            case 1 =>
              (currentChar: @switch) match{
                case '*' => rec(current + 1, state = 2)
                case _ => ctx.freshSuccessUnit(current - 1)
              }
            case 2 => rec(current + 1, state = if (currentChar == '*') 3 else state)
            case 3 =>
              (currentChar: @switch) match{
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

  def fullTerm[_: P]: P[Term]   = P( Start ~ term(true) ~ End )
  def fullFormula[_: P]: P[Formula]   = P( Start ~ formula ~ End )
  def fullProgram[_: P]: P[Program]   = P( Start ~ program ~ End )
  def fullDifferentialProgram[_: P]: P[DifferentialProgram]   = {
    /* Surrounding braces are not allowed in differential programs
      but some code has an extra surrounding {} */
    P( Start ~ ("{" ~ diffProgram ~ "}" | diffProgram) ~ End )
  }

  def fullExpression[_: P]: P[Expression] = P( Start ~
    // try if the entire string parses as program, term, or formula, backtrack to start for each attempt since
    // cuts in program/term may prevent parsing a perfectly well-shaped term/formula
    (NoCut(program) ~ End | NoCut(term(false)) ~ End | NoCut(formula) ~ End )
    // but if all of those fail, try parsing with cuts for better error message
    | expression ~ End
  )

  def expression[_: P]: P[Expression] = P(
    program |
      // Term followed by comparator, or ambiguous term followed by formula operators,
      // should not be parsed as a term
      !(term(true) ~ (comparator | StringIn("->","<-","<->","&","|","→","←","↔","∧","∨"))) ~
        // Even then, if ambiguous we still want to backtrack
        term(false) |
      formula
  )

  def fullSequent[_: P]: P[Sequent]   = P( Start ~ sequent ~ End )

  def fullSequentList[_: P]: P[List[Sequent]]   = P( Start ~ sequentList ~ End )

  //*****************
  // terminals
  //*****************

  /** Explicit nonempty whitespace terminal. */
  def blank[_:P]: P[Unit] = P( CharsWhileIn(" \t\r\n", 1) )

  /** parse a number literal enclosed in (), which is allowed to be a negative number */
  def numberLiteral[_: P]: P[Number] = "(" ~ P(
    ("-".? ~~ CharIn("0-9").repX(1) ~~ ("." ~~/ CharIn("0-9").repX(1)).?).!
  ).map(s => Number(BigDecimal(s))) ~ ")" ~~ !"'"

  /** parses a number literal */
  def number[_: P]: P[Number] = P(
    (CharIn("0-9").repX(1) ~~ ("." ~~/ CharIn("0-9").repX(1)).?).!
  ).map(s => Number(BigDecimal(s)))

  /** matches keywords. An identifier cannot be a keyword. */
  def keywords: Set[String] = Set(
    "true", "false", "Real", "Bool", "HP", "HG",
    "Axiom", "End", "Functions", "Definitions", "ProgramVariables", "Variables",
    "Problem", "Tactic",
    "implicit", "Sequent", "Formula", "Lemma", "Tool", "SharedDefinitions",
    "ArchiveEntry", "Lemma", "Theorem", "Exercise"
  )

  /** parse an identifier.
    * @return the name and its index (if any).
    * @note Index is normalized so that x_00 cannot be mentioned and confused with x_0.
    * @note Keywords are not allowed as identifiers. */
  def ident[_: P]: P[(String,Option[Int])] = P(
    DLParserUtils.filterWithMsg(
      (CharIn("a-zA-Z") ~~ CharIn("a-zA-Z0-9").repX ~~ ("_" ~~ !CharIn("0-9")).?).!
    )(!keywords.contains(_))("Keywords cannot be used as identifiers")
      ~~ ("_" ~~ normNatural).? ~~ (!CharIn("a-zA-Z_"))
  )

  /** `.` or `._2`: dot parsing */
  def dot[_:P]: P[DotTerm] = P(
    ("." | "•") ~~ ("_" ~~ ("0" | CharIn("1-9") ~~ CharIn("0-9").repX).!).?
  ).map(idx => DotTerm(Real, idx.map(_.toInt)))

  // terminals not used here but provided for other DL parsers

  def stringInterior[_: P]: P[String] =
    (CharPred(c => c != '\\' && c != '\"')./ | "\\\""./ | "\\").repX.!

  /** "whatevs": Parse a string literal. (([^\\"]|\\"|\\(?!"))*+) */
  def string[_: P]: P[String] = P(
    "\"" ~~/ stringInterior ~~ "\""
  )

  /** "-532": Parse an integer literal, unnormalized. */
  def integer[_: P]: P[Int] = P(
    ("-".? ~~ CharIn("0-9").repX(1)).!
  ).map(s => s.toInt)

  /** "532": Parse a (nonnegative) natural number literal, unnormalized. */
  def natural[_: P]: P[Int] = P(
    CharIn("0-9").repX(1).!
  ).map(s => s.toInt)

  /** "532": Parse a (nonnegative) natural number literal, normalized. */
  def normNatural[_: P]: P[Int] = P(
    ("0" | CharIn("1-9") ~~ CharIn("0-9").repX).!
  )("normalized natural number",implicitly).
    map(s => s.toInt)


  //*****************
  // base parsers
  //*****************


  def baseVariable[_: P]: P[BaseVariable] = ident.map(s => Variable(s._1,s._2,Real))
  def diffVariable[_: P]: P[DifferentialSymbol] = P(baseVariable ~ "'").map(DifferentialSymbol(_))
  def variable[_: P]: P[Variable] = P(baseVariable ~ "'".!.?).map{
    case (v,None) => v
    case (v,Some("'")) => DifferentialSymbol(v)
  }

  //*****************
  // term parser
  //*****************

  /** Parse a term.
   *
   * Some terms are ambiguous with formulas, in particular
   *    - Parentheses (term parens vs function parens)
   *    - Functions vs predicates
   *    - UnitFunctionals vs UnitPredicationals
   * So, we want to allow backtracking on these ambiguous
   * syntax forms if we are not sure whether the input is
   * a term or a formula.
   *
   * If doAmbigCuts is true, we assume the input is a term, and
   * perform all permissible cuts. If it is false, we only perform
   * cuts that are unambiguous indicators the input is a term.
   */
  def term[_: P](doAmbigCuts: Boolean): P[Term] = P(
    signed(summand(doAmbigCuts)) ~
    // Note: the summand is signed, rather than the first multiplicand
    // in `summand`, because -5*6 is parsed as -(5*6)
    (("+" | "-" ~ !">").!./ ~ signed(summand(doAmbigCuts))).rep
  ).map { case (left, sums) =>
    sums.foldLeft(left) {
      case (m1, ("+", m2)) => Plus(m1, m2)
      case (m1, ("-", m2)) => Minus(m1, m2)
    }
  }

  def summand[_: P](doAmbigCuts: Boolean): P[Term] =
    // Lookahead is to avoid /* */ comments
    (multiplicand(doAmbigCuts) ~ (("*" | "/" ~~ !"*").!./ ~ signed(multiplicand(doAmbigCuts))).rep).map {
      case (left, (op1, t1@Neg(c)) +: r1) if Parser.weakNeg =>
        op1 match {
          case "*" =>
            Times(left, Neg(r1.foldLeft(c) {
              case (m1, ("*", m2)) => Times(m1, m2)
              case (m1, ("/", m2)) => Divide(m1, m2)
            }))
          case "/" => r1 match {
            case Nil => Divide(left, t1)
            case ("/", _) +: _ =>
              Divide(left, Neg(r1.foldLeft[Term](c) {
                case (m1, ("*", m2)) => Times(m1, m2)
                case (m1, ("/", m2)) => Divide(m1, m2)
              }))
            case ("*", _) +: _ =>
              r1.foldLeft[Term](Divide(left, t1)) {
                case (m1, ("*", m2)) => Times(m1, m2)
                case (m1, ("/", m2)) => Divide(m1, m2)
              }
          }
        }
      case (left, mults) => mults.foldLeft(left) {
        case (m1, ("*", m2)) => Times(m1, m2)
        case (m1, ("/", m2)) => Divide(m1, m2)
      }
    }

  def multiplicand[_: P](doAmbigCuts: Boolean): P[Term] =
    (baseTerm(doAmbigCuts) ~ ("^"./ ~ signed(multiplicand(doAmbigCuts))).rep).map{ case (left, pows) =>
      (left +: pows).reduceRight(Power)
    }

  def baseTerm[_: P](doAmbigCuts: Boolean): P[Term] =
    (if (doAmbigCuts) numberLiteral./ else NoCut(numberLiteral)) |
      (if (doAmbigCuts) number./ else NoCut(number)) |
      dot./ |
      function(doAmbigCuts).flatMapX(diff) |
      unitFunctional(doAmbigCuts).flatMapX(diff) |
      variable |
      termList(doAmbigCuts).flatMapX(diff) |
      "__________".!.map(_ => UnitFunctional("exerciseF_", AnyArg, Real))

  def function[_: P](doAmbigCuts: Boolean): P[FuncOf] = P(
    // Note interpretations can only appear on functions (not predicates)
    // so that cut is safe
    ident ~~ ("<<" ~/ formula ~ ">>").? ~
      // Note that ident(termList) can still be ambiguous even if termList
      // is unambiguously a term (it will always be unambiguously a term)
      // so in the doAmbigCuts == false case we want to ignore those cuts
      (if (doAmbigCuts) termList(true)
      else NoCut(termList(true)))
  ).map({case (s,idx,interp,ts) =>
    FuncOf(
      interp match {
        case Some(i) => Function(s,idx,ts.sort,Real,Some(i))
        case None => OpSpec.func(s, idx, ts.sort, Real)
      },
      ts)
  })

  def unitFunctional[_: P](doAmbigCuts: Boolean): P[UnitFunctional] = P(
    ident ~~ (if (doAmbigCuts) space else NoCut(space))
  ).map({case (s,None,sp) => UnitFunctional(s,sp,Real)})

  /** `p | -p`: possibly signed occurrences of what is parsed by parser `p`
   * Note we try `p` before `-p` because some parsers (like `number`)
   * also consume -s. */
  def signed[_: P](p: => P[Term]): P[Term] =
    p | (("-" ~~ !">") ~ signed(p)).map(Neg)

  /** Parses term' */
  def diff[_: P](left: Term): P[Term] =
    "'".!.?.map{case None => left case Some("'") => Differential(left)}

  /** (t1,t2,t3,...,tn) parenthesized list of terms */
  def termList[_: P](doAmbigCuts: Boolean): P[Term] = P(
    "(" ~~ !"|" ~ (if (doAmbigCuts) Pass./ else Pass) ~
      // Note that a single-element termList can be ambiguous with formulas,
      // but a multi-element termList must be a term
      (if (doAmbigCuts) term(true) else NoCut(term(true))).rep(sep=","./) ~
      ")"
  ).
    map(ts => ts.reduceRightOption(Pair).getOrElse(Nothing))

  /** (|x1,x2,x3|) parses a space declaration */
  def space[_: P]: P[Space] = P(
    "(|" ~ variable.rep(sep=",") ~ "|)"
  ).map(ts => if (ts.isEmpty) AnyArg else Except(ts.to))

  //*****************
  // formula parser
  //*****************

  def formula[_: P]: P[Formula] = P(biimplication)

  /* <-> (lowest prec, non-assoc) */
  def biimplication[_: P]: P[Formula] =
    (backImplication ~ (("<->"|"↔") ~/ backImplication).?).
      map{ case (left,None) => left case (left,Some(r)) => Equiv(left,r) }

  /* <- (left-assoc) */
  def backImplication[_: P]: P[Formula] =
    (implication ~~ (((blank ~ "<-" ~~ blank).opaque("\" <- \"")|(blank.? ~ "←").opaque("\"←\"")) ~/ implication).rep).
      map{ case (left, hyps) =>
        hyps.foldLeft(left){case (acc,hyp) => Imply(hyp,acc)} }

  /* -> (right-assoc) */
  def implication[_: P]: P[Formula] =
    (disjunct ~ (("->"|"→") ~/ disjunct).rep).
      map{ case (left, concls) => (left +: concls).reduceRight(Imply) }

  /* | (right-assoc) */
  def disjunct[_: P]: P[Formula] =
    (conjunct ~ (("|"|"∨") ~/ conjunct).rep).
      map{ case (left, conjs) => (left +: conjs).reduceRight(Or) }

  /* & (right-assoc) */
  def conjunct[_: P]: P[Formula] =
    (baseF ~ (("&"|"∧") ~/ baseF).rep).
      map{ case (left, forms) => (left +: forms).reduceRight(And) }

  /** Base formulas */
  def baseF[_: P]: P[Formula] = (
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
  def ambiguousBaseF[_: P]: P[Formula] = (
    /* variables */
    (ident ~~ !"(").map{
      case (name, idx) => PredOf(Function(name, idx, Unit, Bool), Nothing)
    } |
    /* predicate OR function */
    ( ident ~~ NoCut(termList(true)) ~ "'".!.? ).map {
      case (name, idx, args, diff) =>
        val p = PredOf(Function(name, idx, args.sort, Bool), args)
        diff match {
          case None => p
          case Some("'") => DifferentialFormula(p)
        }
    }
    /* unit predicational OR unit functional */
    | DLParserUtils.filterWithMsg( ident ~~ NoCut(space) ~ "'".!.?)(_._2.isEmpty)("Unit predicationals cannot have indices").map({
        case (name, _, args, diff) =>
          val p = UnitPredicational(name, args)
          diff match {
            case None => p
            case Some("'") => DifferentialFormula(p)
          }
      })
    /* parenthesized formula OR term */
    | ("(" ~ formula ~ ")" ~ "'".!.?).map({
        case (form,None) => form
        case (form,Some("'")) => DifferentialFormula(form)
      })
  )

  def unambiguousBaseF[_: P]: P[Formula] =
    /* atomic formulas, constant T/F, quantifiers, modalities */
      "true".!.map(_ => True) | "false".!.map(_ => False) |
    /* Note we cannot cut after true/false because it could also
     * be the start of an identifier */
    ( ("\\forall"|"\\exists"|"∀"|"∃").! ~~/ blank ~ variable.repX(min=1,sep=",") ~ baseF ).
      map{
        case ("\\forall"|"∀",x, f) => x.foldLeft(f)({ case (f, x) => Forall(x::Nil, f) })
        case ("\\exists"|"∃",x, f) => x.foldLeft(f)({ case (f, x) => Exists(x::Nil, f) })
      } |
    ( (("[".! ~/ program ~ "]".!) | ("<".! ~/ program ~ ">".!)) ~/ baseF ).
      map{case ("[",p,"]", f) => Box(p, f)
      case ("<",p,">", f) => Diamond(p, f)} |
    ("!" ~/ baseF ).map(Not) |
    predicational |
    "⎵".!.map(_ => DotFormula) |
    /* Exercise */
    "__________".!.map(_ => UnitPredicational("exerciseP_", AnyArg))

  /** Parses a comparison, given the left-hand term */
  def comparison[_: P]: P[Formula] = P(
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

  def comparator[_: P]: P[Unit] = P("=" ~~ !"=" | "!=" | "≠" | ">=" | "≥" | ">" | "<=" | "≤" | "<" ~~ !"-")

  /** Unit predicationals c(||) */
  def unitPredicational[_: P]: P[UnitPredicational] = P(ident ~~ space).map({case (s,None,sp) => UnitPredicational(s,sp)})
  /** Regular predicationals C{} */
  def predicational[_: P]: P[PredicationalOf] = P(ident ~~ "{" ~/ formula ~ "}").map({case (s,idx,f) => PredicationalOf(Function(s,idx,Bool,Bool),f)})


  //*****************
  // program parser
  //*****************

  def programSymbol[_: P]: P[AtomicProgram] = P(
    DLParserUtils.filterWithMsg(ident ~~ odeSpace.? ~ ";")
        (_._2.isEmpty)("Program symbols cannot have an index").
      map({ case (s,None,taboo) =>
        ProgramConst(s, taboo.getOrElse(AnyArg))
      })
  )
  //@todo combine system symbol and space taboo
  def systemSymbol[_: P]: P[AtomicProgram] = P(
    DLParserUtils.filterWithMsg(ident  ~~ "{|^@" ~/ variable.rep(sep=","./) ~ "|}" ~ ";")
      (_._2.isEmpty)("System symbols cannot have an index").
      map({ case (s,None,taboo) =>
        SystemConst(s, if (taboo.isEmpty) AnyArg else Except(taboo.to))
      })
  )

  def programExercise[_: P]: P[AtomicProgram] = "__________".!.map(_ => SystemConst("exerciseS_", AnyArg))

  def assign[_: P]: P[AtomicProgram] = (
    (variable ~ ":=" ~/ ("*".!./.map(Left(_)) | term(true).map(Right(_)))  ~ ";").
      map({
        case (x, Left("*")) => AssignAny(x)
        case (x, Right(t)) => Assign(x, t)
      })
  )
  def test[_: P]: P[Test] = ( "?" ~/ formula ~ ";").map(f => Test(f))
  def braceP[_: P]: P[Program] = ( "{" ~ program ~ "}" ~/ (("*" | "×")./.! ~ annotation.?).?).
    map({
      case (p,None) => p
      case (p,Some(("*",None))) => Loop(p)
      case (p,Some(("*",Some(inv)))) => inv.foreach(reportAnnotation(Loop(p),_)); Loop(p)
      case (p,Some(("×", _))) => Dual(Loop(Dual(p)))
    })
  def odeprogram[_: P]: P[ODESystem] = ( diffProgram ~ ("&" ~/ formula.flatMapX(f => {
    if (StaticSemantics.isDifferential(f)) Fail.opaque("No differentials in evolution domain constraints; instead of the primed variables use their right-hand sides.")
    else Pass(f)
  })).?).
    map({case (p,f) => ODESystem(p, f.getOrElse(True))})
  def odesystem[_: P]: P[ODESystem] = ( "{" ~ odeprogram ~ "}" ~/ annotation.?).
    map({
      case (p,None) => p
      case (p,Some(inv)) => inv.foreach(reportAnnotation(p,_)); p
    })

  def baseP[_: P]: P[Program] = (
    systemSymbol | programSymbol | assign | test | ifthen | odesystem | braceP | programExercise
  )

  /** Parses dual notation: baseP or baseP^@ */
  def dual[_: P]: P[Program] = (baseP ~ "^@".!./.?).map({
    case (p, None) => p
    case (p, Some("^@")) => Dual(p)
  })

  /** Parses an annotation */
  def annotation[_: P]: P[Seq[Formula]] = ("@invariant" | "@variant") ~/ "(" ~/ formula.rep(min=1,sep=","./).map(_.toList) ~ ")"

  def sequence[_: P]: P[Program] = ( (dual ~/ ";".?).rep(1) ).
    map(ps => ps.reduceRight(Compose))

  def choice[_: P]: P[Program] = (
    sequence ~/ (("++"./ | "∪"./ | "--" | "∩"./).! ~ sequence).rep
  ).map({ case (p, ps) =>
      ((None, p) +: ps.map{case (s,p) => (Some(s),p)}).reduceRight[(Option[String], Program)] {
        case ((pre,p), (Some("++" | "∪"), q)) => (pre, Choice(p,q))
        case ((pre,p), (Some("--" | "∩"), q)) => (pre, Dual(Choice(Dual(p),Dual(q))))
      }._2
    })

  //@note macro-expands
  def ifthen[_: P]: P[Program] = ( "if" ~/ "(" ~/ formula ~ ")" ~ braceP ~ ("else" ~/ braceP).? ).
    map({case (f, p, None) => Choice(Compose(Test(f),p), Test(Not(f)))
         case (f, p, Some(q)) => Choice(Compose(Test(f),p), Compose(Test(Not(f)),q))})

  /** program: Parses a dL program. */
  def program[_: P]: P[Program] = P( choice )


  //*****************
  // differential program parser
  //*****************

  def ode[_: P]: P[AtomicODE] = P( diffVariable ~ "=" ~/ term(true)).map({case (x,t) => AtomicODE(x,t)})
  def diffProgramSymbol[_: P]: P[DifferentialProgramConst] = P(
    DLParserUtils.filterWithMsg(ident ~~ odeSpace.?)(_._2.isEmpty)
                  ("Differential program symbols cannot have an index").map({
      case (s, None, None) => DifferentialProgramConst(s)
      case (s, None, Some(sp)) => DifferentialProgramConst(s, sp)
    })
  )
  def diffExercise[_: P]: P[DifferentialProgramConst] = "__________".!.map(_ => DifferentialProgramConst("exerciseD_", AnyArg))
  def atomicDP[_: P]: P[AtomicDifferentialProgram] = ( ode | diffProgramSymbol | diffExercise )

  /** {|x1,x2,x3|} parses a space declaration */
  def odeSpace[_: P]: P[Space] = P("{|" ~ (variable ~ ("," ~/ variable).rep).? ~ "|}").
    map({case Some((t,ts)) => Except((ts.+:(t)).to) case None => AnyArg})

  def diffProduct[_: P]: P[DifferentialProgram] = ( atomicDP ~ ("," ~/ atomicDP).rep ).
    map({case (p, ps) => (ps.+:(p)).reduceRight(DifferentialProduct.apply)})

  /** diffProgram: Parses a dL differential program. */
  def diffProgram[_: P]: P[DifferentialProgram] = P( diffProduct )

  //*****************
  // sequent parser
  //*****************

  /** sequent ::= `aformula1 , aformula2 , ... , aformulan ==>  sformula1 , sformula2 , ... , sformulam`. */
  def sequent[_: P]: P[Sequent] = P( formula.rep(sep=","./) ~ "==>" ~ formula.rep(sep=","./)).
    map({case (ante, succ) => Sequent(ante.to, succ.to)})

  /** sequentList ::= sequent `;;` sequent `;;` ... `;;` sequent. */
  def sequentList[_: P]: P[List[Sequent]] = P( sequent.rep(sep=";;"./ )).map(_.toList)
}

