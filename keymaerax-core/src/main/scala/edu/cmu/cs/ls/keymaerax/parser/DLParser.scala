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
  assert(OpSpec.negativeNumber, "This parser accepts negative number literals although it does not give precedence to them")

  /** Converts Parsed.Failure to corresponding ParseException to throw. */
  private[keymaerax] def parseException(f: Parsed.Failure): ParseException = {
    val tr: Parsed.TracedFailure = f.trace()
    val inputString = f.extra.input match {
      case IndexedParserInput(input) => input
      case _ => tr.input + ""
    }
    /*@note tr.msg is redundant compared to the following and could be safely elided for higher-level messages */
    /*@note tr.longMsg can be useful for debugging the parser */
    /*@note tr.longAggregateMsg */
    ParseException(tr.longAggregateMsg,
      location(f),
      found = Parsed.Failure.formatTrailing(f.extra.input, f.index),
      expect = Parsed.Failure.formatStack(tr.input, List(tr.label -> f.index)),
      after = "" + tr.stack.headOption.getOrElse(""),
      state = tr.longMsg,
      //state = Parsed.Failure.formatMsg(tr.input, tr.stack ++ List(tr.label -> tr.index), tr.index),
      hint = "Try " + tr.groupAggregateString).inInput(inputString, None)
  }

  /** The location of a parse failure. */
  private[keymaerax] def location(f: Parsed.Failure): Location = try {
    f.extra.input.prettyIndex(f.index).split(':').toList match {
      case line::col::Nil => Region(line.toInt, col.toInt)
      case line::col::unexpected => Region(line.toInt, col.toInt)
      case unexpected => UnknownLocation
    }
  } catch {
    case _: NumberFormatException => UnknownLocation
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
  /** Parse the input string in the concrete syntax as a differential dynamic logic expression
    *
    * @param input the string to parse as a dL formula, dL term, or dL program.
    * @ensures apply(printer(\result)) == \result
    * @throws ParseException if `input` is not a well-formed expression of differential dynamic logic or differential game logic.
    */
  override def apply(input: String): Expression = exprParser(input)


  private def parseAndCompare[A](newParser: P[_] => P[A], oldParser: String => A, name: String): String => A =
    s => {
      val newres = fastparse.parse(s, newParser(_)) match {
        case Parsed.Success(value, _) => Right(value)
        case f: Parsed.Failure => Left(parseException(f))
      }
      val oldres = try {
        Right(oldParser(s))
      } catch {
        case e => Left(e)
      }
      if (oldres != newres && (oldres.isRight || newres.isRight)) {
        println(s"Parser disagreement ($name): `$s`")
        println(s"KYXParser:\n${oldres match {case Left(x) => x.toString case Right(x) => x.toString}}")
        println(s"DLParser:\n${newres match {case Left(x) => x.toString case Right(x) => x.toString}}")
      }
      newres match {
        case Left(e) => throw e
        case Right(res) => res
      }
    }

  /** Parse the input string in the concrete syntax as a differential dynamic logic expression */
  val exprParser: String => Expression = parseAndCompare(fullExpression(_), KeYmaeraXParser.apply, "expression")

  /** Parse the input string in the concrete syntax as a differential dynamic logic term */
  override val termParser: String => Term = parseAndCompare(fullTerm(_), KeYmaeraXParser.termParser, "term")

  /** Parse the input string in the concrete syntax as a differential dynamic logic formula */
  override val formulaParser: String => Formula = parseAndCompare(fullFormula(_), KeYmaeraXParser.formulaParser, "formula")

  /** Parse the input string in the concrete syntax as a differential dynamic logic program */
  override val programParser: String => Program = parseAndCompare(fullProgram(_), KeYmaeraXParser.programParser, "program")

  /** Parse the input string in the concrete syntax as a differential dynamic logic differential program */
  override val differentialProgramParser: String => DifferentialProgram =
    parseAndCompare(fullDifferentialProgram(_), KeYmaeraXParser.differentialProgramParser, "diff. program")

  /** Parse the input string in the concrete syntax as a differential dynamic logic sequent. */
  override val sequentParser: String => Sequent = parseAndCompare(fullSequent(_), KeYmaeraXParser.sequentParser, "sequent")

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
    this.annotationListener = listener

  // internals

  private[parser] var annotationListener: ((Program,Formula) => Unit) = {(p,inv) => }

  /** Report an @invariant @annotation to interested parties */
  private def reportAnnotation(p: Program, invariant: Formula): Unit = annotationListener(p,invariant)

  /** `true` has unary negation `-` bind weakly like binary subtraction.
    * `false` has unary negation `-` bind strong just shy of power `^`. */
  //TODO: Not used (do we need to support it?)
  private val weakNeg: Boolean = true


  //*****************
  // implementation
  //*****************

  // Whitespace is any of ` \t\n\r`
  import MultiLineWhitespace._

  def fullTerm[_: P]: P[Term]   = P( Start ~ term ~ End )
  def fullFormula[_: P]: P[Formula]   = P( Start ~ formula ~ End )
  def fullProgram[_: P]: P[Program]   = P( Start ~ program ~ End )
  def fullDifferentialProgram[_: P]: P[DifferentialProgram]   = {
    /* Hack because old parser allowed with or without {}s */
    P( Start ~ ("{" ~ diffProgram ~ "}" | diffProgram) ~ End )
  }

  def fullExpression[_: P]: P[Expression] = P( Start ~ expression ~ End )

  def expression[_: P]: P[Expression] = P( program | NoCut(formula) | NoCut(term) )

  def fullSequent[_: P]: P[Sequent]   = P( Start ~ sequent ~ End )

  def fullSequentList[_: P]: P[List[Sequent]]   = P( Start ~ sequentList ~ End )

  //*****************
  // terminals
  //*****************

  /** Explicit nonempty whitespace terminal. */
  def blank[_:P]: P[Unit] = P( CharsWhileIn(" \t\r\n", 1) )

  /** parse a number literal */
  def number[_: P]: P[Number] = P(
    ("-".? ~~ CharIn("0-9").repX(1) ~~ ("." ~~/ CharIn("0-9").repX(1)).?).!
  ).map(s => Number(BigDecimal(s)))

  /** parse an identifier.
    * @return the name and its index (if any).
    * @note Index is normalized so that x_00 cannot be mentioned and confused with x_0.*/
  def ident[_: P]: P[(String,Option[Int])] = P(
    (CharIn("a-zA-Z") ~~ CharIn("a-zA-Z0-9").repX).! ~~
      (("_" ~~ ("_".? ~~ ("0" | CharIn("1-9") ~~ CharIn("0-9").repX)).!) |
        "_".!).?
    ).map({
      case (s,None) => (s,None)
      case (s,Some("_")) => (s+"_",None)
      case (s,Some(n))=>
        if (n.startsWith("_")) (s+"_",Some(n.drop(1).toInt))
        else (s,Some(n.toInt))
    })

  /** `.` or `._2`: dot parsing */
  def dot[_:P]: P[DotTerm] = P(
    "." ~~ ("_" ~~ ("0" | CharIn("1-9") ~~ CharIn("0-9").repX).!).?
  ).map(idx => DotTerm(Real, idx.map(_.toInt)))

  // terminals not used here but provided for other DL parsers

  /** "whatevs": Parse a string literal. (([^\\"]|\\"|\\(?!"))*+) */
  def string[_: P]: P[String] = P(
    "\"" ~~/ (!CharIn("\\\"") ~~ AnyChar | "\\\"" | "\\" ~~ !"\"").repX.! ~~ "\""
  )

  /** "-532": Parse an integer literal, unnormalized. */
  def integer[_: P]: P[Int] = P(
    ("-".? ~~ CharIn("0-9").repX(1)).!
  ).map(s => s.toInt)

  /** "532": Parse a (nonnegative) natural number literal, unnormalized. */
  def natural[_: P]: P[Int] = P(
    CharIn("0-9").repX(1).!
  ).map(s => s.toInt)



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
   * If the leftmost character is ( it is interpreted as a term parenthesis,
   * and a cut is made. Should only be used in contexts where the first
   * character must be a part of a term. */
  def term[_: P]: P[Term] = P(signed(summand).flatMap(termRight))

  def termRight[_: P](left: Term): P[Term] = {
    // Note: the summand is signed, rather than the first multiplicand
    // in `summand`, because -5*6 is parsed as -(5*6)
    (("+" | "-" ~ !">").!./ ~ signed(summand)).rep.map(sums =>
      sums.foldLeft(left) {
        case (m1, ("+", m2)) => Plus(m1, m2)
        case (m1, ("-", m2)) => Minus(m1, m2)
        case _ => throw new IllegalStateException()
      }
    )
  }

  def summand[_: P]: P[Term] = P(multiplicand.flatMap(summRight))

  def summRight[_: P](left: Term): P[Term] =
    // Lookahead is to avoid /* */ comments
    (("*" | "/" ~~ !"*").!./ ~ signed(multiplicand)).rep.map(mults =>
      mults.foldLeft(left) {
        case (m1, ("*", m2)) => Times(m1, m2)
        case (m1, ("/", m2)) => Divide(m1, m2)
        case _ => throw new IllegalStateException()
      }
    )

  def multiplicand[_: P]: P[Term] = P(baseTerm.flatMap(multRight))

  def multRight[_: P](left: Term): P[Term] =
    ("^"./ ~ signed(baseTerm)).rep.map(pows => (left +: pows).reduceRight(Power))

  def baseTerm[_: P]: P[Term] = P(
      number./ | dot./ | func.flatMap(diff) | unitFunctional.flatMap(diff) | variable
      /* termList has a cut after (, but this is safe, because we
       * require that if the first available character is ( it is
       * unambiguously a term parenthesis */
      | termList.flatMap(diff)
  )

  def termParenRight[_: P](left: Term): P[Term] =
    ")".!.map(_ => left).flatMap(diff)

  /** Given a base term, builds up to a full term, consuming as much
   * input as possible */
  def extendBaseTerm[_: P](left: Term): P[Term] =
    multRight(left).flatMap(summRight).flatMap(termRight)

  def func[_: P]: P[FuncOf] = P(ident ~~ ("<<" ~/ formula ~ ">>").? ~~ termList).map({case (s,idx,interp,ts) =>
    FuncOf(
      interp match {
        case Some(i) => Function(s,idx,ts.sort,Real,Some(i))
        case None => OpSpec.func(s, idx, ts.sort, Real)
      },
      ts)
  })

  def unitFunctional[_: P]: P[UnitFunctional] = P(ident ~~ space).map({case (s,None,sp) => UnitFunctional(s,sp,Real)})

  /** `p | -p`: possibly signed occurrences of what is parsed by parser `p`
   * Note we try `p` before `-p` because some parsers (like `number`)
   * also consume -s. */
  def signed[_: P](p: => P[Term]): P[Term] =
    p | (("-".! ~~ !">") ~ signed(p)).map{case ("-",t) => Neg(t)}

  /** Parses term' */
  def diff[_: P](left: Term): P[Term] =
    "'".!.?.map{case None => left case Some("'") => Differential(left)}

  /** (t1,t2,t3,...,tn) parenthesized list of terms */
  def termList[_: P]: P[Term] = P("(" ~~ !"|" ~/ term.rep(sep=","./) ~ ")").
    map(ts => ts.reduceRightOption(Pair).getOrElse(Nothing))

  /** (|x1,x2,x3|) parses a space declaration */
  def space[_: P]: P[Space] = P( "(|" ~/ variable.rep(sep=",") ~ "|)" ).
    map(ts => if (ts.isEmpty) AnyArg else Except(ts.to))

  //*****************
  // formula parser
  //*****************

  def formula[_: P] = P(biimplication)

  /* <-> (lowest prec, non-assoc) */
  def biimplication[_: P]: P[Formula] = P(backImplication.flatMap(biimpRight))
  def biimpRight[_: P](left: Formula): P[Formula] =
    ("<->" ~/ backImplication).?.
      map{ case None => left case Some(r) => Equiv(left,r) }

  /* <- (left-assoc) */
  def backImplication[_: P]: P[Formula] = P(implication.flatMap(backImpRight))
  def backImpRight[_: P](left: Formula): P[Formula] =
    ("<-" ~ !">" ~/ implication).rep.map(hyps =>
      hyps.foldLeft(left){case (acc,hyp) => Imply(hyp,acc)}
    )

  /* -> (right-assoc) */
  def implication[_: P]: P[Formula] = P(disjunct.flatMap(impRight))
  def impRight[_: P](left: Formula): P[Formula] =
    ("->" ~/ disjunct).rep.map(concls =>
      (left +: concls).reduceRight(Imply)
    )

  /* | (right-assoc) */
  def disjunct[_: P]: P[Formula] = P(conjunct.flatMap(disjRight))
  def disjRight[_: P](left: Formula): P[Formula] =
    ("|" ~/ conjunct).rep.map(conjs =>
      (left +: conjs).reduceRight(Or)
    )

  /* & (right-assoc) */
  def conjunct[_: P]: P[Formula] = P(baseF.flatMap(conjRight))
  def conjRight[_: P](left: Formula): P[Formula] =
    ("&" ~/ baseF).rep.map(forms =>
      (left +: forms).reduceRight(And)
    )

  def extendBaseFormula[_: P](left: Formula): P[Formula] =
    conjRight(left).flatMap(disjRight).flatMap(impRight).flatMap(backImpRight).flatMap(biimpRight)

  /** Base formulas. Most work done in `termOrBaseF`.
   * `termOrBaseF` consumes as much input as possible, so if
   * we get a term out then it can't work as a formula. */
  def baseF[_: P]: P[Formula] = P(
    termOrBaseF.flatMap{
      case Left((_,form)) => Pass(form)
      case Right(Left(_)) => Fail
      case Right(Right(form)) => Pass(form)
    }
  )

  /* Returns
  * 1. both a term and a formula, if the consumed input can be interpreted as either
  * 2. only a term, if the consumed input can only be a term
  * 3. only a formula, if the consumed input can only be a formula
  *
  * NOTE: Terms MUST BE fully extended, but formulas MUST BE base formulas (CANNOT be extended).
  * Differential formulas f()', f(||)', and (f)' are considered base formulas.
  */
  def termOrBaseF[_: P]: P[Either[(Term, Formula), Either[Term,Formula]]] = (
    unambiguousBaseF.map(f => Right(Right(f))) |

    /* predicate OR function */
    ( ident ~~ ("<<" ~/ formula ~ ">>").? ~~ termList ~ "'".!.?).
      map({case (s,idx,interp,ts,diff) =>
        val (t,f) = (
          FuncOf(OpSpec.func(s, idx, ts.sort, Real),ts),
          PredOf(Function(s,idx,ts.sort,Bool,interp), ts)
        )
        val (dt,df) = diff match {
          case None => (t,f)
          case Some("'") => (Differential(t), DifferentialFormula(f))
        }
        interp match {
          case Some(i) =>
            // Must be a term, since interpreted functions have real domain
            Right(Left(dt))
          case None =>
            // Could be either term or formula
            Left((dt,df))
        }
      }) |

    /* unit predicational OR unit functional */
    ( ident ~~ space ~ "'".!.?).flatMap({
      case (_, Some(_), _, _) =>
        Fail.opaque("Indices are not yet allowed in predicational/functional names")
      case (name, None, space, diff) =>
        // Could be either term or formula
        val (t,f) = (
          UnitFunctional(name, space, sort=Real),
          UnitPredicational(name, space)
        )
        Pass(Left(diff match {
          case None => (t,f)
          case Some("'") => (Differential(t), DifferentialFormula(f))
        }))
    }) |

    /* Parenthesized term OR formula */
    /* TODO: support parsing (x,(y,z)) in this context?
    Currently the only way to get a formula out of a term is via
    a comparison, and comparisons only occur on Reals, but if this
    changes then the parsing here will need to change.
    */
    "(" ~/ termOrBaseF.
      /* Since parens contain full terms/formulas (not just base ones)
       * we should extend formulas where possible */
      flatMap({
        case Left((t,f)) =>
          /* Note if we can (strictly) extend the formula, then the
           * consumed input must have been a formula because there is
           * no overloaded syntax between composite formulas & terms */
          (Index ~~ extendBaseFormula(f) ~~ Index).map {
            case (startIdx, f_, endIdx) =>
              if (startIdx < endIdx)
                Right(Right(f_))
              else
                Left((t, f))
          }
        case Right(Right(f)) =>
          // Extend formula
          extendBaseFormula(f).
            map(f => Right(Right(f)))
        case Right(Left(t)) =>
          // Term already extended
          Pass(Right(Left(t)))
      }).
      // Then we find the matching right parenthesis
      flatMap{
        case Left((a,b)) =>
          /* Note this doesn't disambiguate term/formula so
           * both remain a possibility */
          (")" ~ "'".!.?).map {
            case Some("'") =>
              Left((Differential(a), DifferentialFormula(b)))
            case None =>
              Left((a, b))
          }

        case Right(Left(term)) =>
          // Try closing paren as a term paren
          termParenRight(term).
            map(t => Right(Left(t)))

        case Right(Right(form)) =>
          // Try closing paren as a formula paren
          formulaParenRight(form).
            map(f => Right(Right(f)))
      } |

    /* Just a plain old term */
    term.map(t => Right(Left(t)))
  ).
  // Now we ensure the terms are fully extended
  flatMap{
    case Left((t,f)) =>
      /* Note if we can (strictly) extend a term, then the
       * consumed input must have been a term */
      (Index ~~ extendBaseTerm(t) ~~ Index).map {
        case (startIdx, t_, endIdx) =>
          if (startIdx < endIdx)
            Right(Left(t_))
          else
            Left((t, f))
      }
    case Right(Left(t)) =>
      // Try extending term
      extendBaseTerm(t).
        map(t => Right(Left(t)))
    case Right(Right(f)) =>
      // Formulas remain unextended
      Pass(Right(Right(f)))
  }.
  // Now we try turning terms into comparisons
  flatMap{
    case parsed @ Left((t,_)) =>
      comparison(t).map(f => Right(Right(f))) |
        Pass(parsed)
    case parsed @ Right(Left(t)) =>
      comparison(t).map(f => Right(Right(f))) |
        Pass(parsed)
    case parsed => Pass(parsed)
  }

  def unambiguousBaseF[_: P]: P[Formula] =
    /* atomic formulas, constant T/F, quantifiers, modalities */
      "true".!.map(_ => True) | "false".!.map(_ => False) |
    /* Note we cannot cut after true/false because it could also
     * be the start of an identifier */
    ( ("\\forall"|"\\exists").! ~~/ blank ~ variable ~ baseF ).
      map{
        case ("\\forall",x, f) => Forall(x::Nil, f)
        case ("\\exists",x, f) => Exists(x::Nil, f)
      } |
    ( (("[".! ~/ program ~ "]".!) | ("<".! ~/ program ~ ">".!)) ~/ baseF ).
      map{case ("[",p,"]", f) => Box(p, f)
      case ("<",p,">", f) => Diamond(p, f)} |
    ("!" ~/ baseF ).map(f => Not(f)) |
    predicational

  /** Parses a right formula parenthesis given the pair's contents  */
  def formulaParenRight[_: P](left: Formula): P[Formula] =
    (")" ~ "'".!.?).map {
      case None => left
      case Some("'") => DifferentialFormula(left)
    }

  /** Parses a comparison, given the left-hand term */
  def comparison[_: P](left: Term): P[Formula] = P(
    (("=" ~~ !"=" | "!=" | ">=" | ">" | "<=" | "<" ~~ !"-").! ~/ term).map {
      case ("=", right) => Equal(left, right)
      case ("!=", right) => NotEqual(left, right)
      case (">=", right) => GreaterEqual(left, right)
      case (">", right) => Greater(left, right)
      case ("<=", right) => LessEqual(left, right)
      case ("<", right) => Less(left, right)
    }
  )

  /** Unit predicationals c(||) */
  def unitPredicational[_: P]: P[UnitPredicational] = P(ident ~~ space).map({case (s,None,sp) => UnitPredicational(s,sp)})
  /** Regular predicationals C{} */
  def predicational[_: P]: P[PredicationalOf] = P(ident ~~ "{" ~/ formula ~ "}").map({case (s,idx,f) => PredicationalOf(Function(s,idx,Bool,Bool),f)})


  //*****************
  // program parser
  //*****************

  def programSymbol[_: P]: P[AtomicProgram] = P(ident ~~ odeSpace.? ~ ";").flatMap({
    case (s,None,taboo) => Pass(ProgramConst(s, taboo.getOrElse(AnyArg)))
    case (s,Some(i),_) => Fail.opaque("Program symbols cannot have an index: " + s + "_" + i)
  })
  //@todo combine system symbol and space taboo
  def systemSymbol[_: P]: P[AtomicProgram] =
    P( ident  ~~ "{|^@" ~/ variable.rep(sep=","./) ~ "|}" ~ ";").
    flatMap({
      case (s,None,taboo) => Pass(SystemConst(s, if (taboo.isEmpty) AnyArg else Except(taboo.to)))
      case (s,Some(i),_) => Fail.opaque("System symbols cannot have an index: " + s + "_" + i)
    })

  def assign[_: P]: P[AtomicProgram] = P(
    (variable ~ ":="./).flatMap(x =>
      "*".!.map(_ => AssignAny(x))
        | term.map(t => Assign(x,t))
    ) ~ ";"
  )
  def test[_: P]: P[Test] = P( "?" ~/ formula ~ ";").map(f => Test(f))
  def braceP[_: P]: P[Program] = P( "{" ~ program ~ "}" ~/ (("*" | "×")./.! ~ annotation.?).?).
    map({
      case (p,None) => p
      case (p,Some(("*",None))) => Loop(p)
      case (p,Some(("*",Some(inv)))) => reportAnnotation(Loop(p),inv); Loop(p)
      case (p,Some(("×", _))) => Dual(Loop(Dual(p)))
    })
  def odeprogram[_: P]: P[ODESystem] = P( diffProgram ~ ("&" ~/ formula).?).
    map({case (p,f) => ODESystem(p,f.getOrElse(True))})
  def odesystem[_: P]: P[ODESystem] = P( "{" ~ odeprogram ~ "}" ~/ annotation.?).
    map({case (p,None) => p case (p,Some(inv)) => reportAnnotation(p,inv); p})

  def baseP[_: P]: P[Program] = P(
    systemSymbol | programSymbol | assign | test | ifthen | odesystem | braceP
  )

  /** Parses dual notation: baseP or baseP^@ */
  def dual[_: P]: P[Program] = (baseP ~ "^@".!./.?).map({
    case (p, None) => p
    case (p, Some("^@")) => Dual(p)
  })

  /** Parses an annotation */
  def annotation[_: P]: P[Formula] = "@invariant" ~/ "(" ~/ formula ~ ")"

  def sequence[_: P]: P[Program] = P( (dual ~/ ";".?).rep(1) ).
    map(ps => ps.reduceRight(Compose))

  def choice[_: P]: P[Program] = P(
    sequence ~/ (("++"./ | "∪"./ | "--" | "∩"./).! ~ sequence).rep
  ).map({ case (p, ps) =>
      ((None, p) +: ps.map{case (s,p) => (Some(s),p)}).reduceRight[(Option[String], Program)] {
        case ((pre,p), (Some("++" | "∪"), q)) => (pre, Choice(p,q))
        case ((pre,p), (Some("--" | "∩"), q)) => (pre, Dual(Choice(Dual(p),Dual(q))))
      }._2
    })

  //@note macro-expands
  def ifthen[_: P]: P[Program] = P( "if" ~/ "(" ~/ formula ~ ")" ~ braceP ~ ("else" ~/ braceP).? ).
    map({case (f, p, None) => Choice(Compose(Test(f),p), Test(Not(f)))
         case (f, p, Some(q)) => Choice(Compose(Test(f),p), Compose(Test(Not(f)),q))})

  /** program: Parses a dL program. */
  def program[_: P]: P[Program] = P( choice )


  //*****************
  // differential program parser
  //*****************

  def ode[_: P]: P[AtomicODE] = P( diffVariable ~ "=" ~/ term).map({case (x,t) => AtomicODE(x,t)})
  def diffProgramSymbol[_: P]: P[DifferentialProgramConst] =
    P( ident ~~ odeSpace.?).flatMap({
      case (s, None, None)     => Pass(DifferentialProgramConst(s))
      case (s, None, Some(sp)) => Pass(DifferentialProgramConst(s,sp))
      case (s, Some(i), _)     => Fail.opaque("Differential program symbols cannot have an index: " + s + "_" + i)})
  def atomicDP[_: P]: P[AtomicDifferentialProgram] = P( ode | diffProgramSymbol )

  /** {|x1,x2,x3|} parses a space declaration */
  def odeSpace[_: P]: P[Space] = P("{|" ~ (variable ~ ("," ~/ variable).rep).? ~ "|}").
    map({case Some((t,ts)) => Except((ts.+:(t)).to) case None => AnyArg})

  def diffProduct[_: P]: P[DifferentialProgram] = P( atomicDP ~ ("," ~/ atomicDP).rep ).
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

