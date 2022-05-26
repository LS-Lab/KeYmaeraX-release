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
import edu.cmu.cs.ls.keymaerax.parser.DLParser.ambiguousBaseF
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

    def formatStack(input: ParserInput, stack: List[(String, Int)]) = {
      stack.map{case (s, i) => s"$s at ${input.prettyIndex(i)}"}.mkString(" / ")
    }

    ParseException(tr.msg,
      location(f),
      found = Parsed.Failure.formatTrailing(f.extra.input, f.index),
      expect = formatStack(tr.input, tr.stack),
      after = "" + tr.stack.headOption.getOrElse(""),
      // state = tr.longMsg,
      // state = Parsed.Failure.formatMsg(tr.input, tr.stack ++ List(tr.label -> tr.index), tr.index),
      hint = "Try " + tr.terminalAggregateString).inInput(inputString, None)
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

  // Whitespace is the usual ' \t\n\r' but also comments /* ... */ and // ...
  import JavaWhitespace._

  def fullTerm[_: P]: P[Term]   = P( Start ~ term ~ End )
  def fullFormula[_: P]: P[Formula]   = P( Start ~ formula ~ End )
  def fullProgram[_: P]: P[Program]   = P( Start ~ program ~ End )
  def fullDifferentialProgram[_: P]: P[DifferentialProgram]   = {
    /* Surrounding braces are not allowed in differential programs
      but some code has an extra surrounding {} */
    P( Start ~ ("{" ~ diffProgram ~ "}" | diffProgram) ~ End )
  }

  def fullExpression[_: P]: P[Expression] = P( Start ~ expression ~ End )

  def expression[_: P]: P[Expression] = P( program | formula | term )

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
  ).map(s => Number(BigDecimal(s))).
    opaque("constant")

  /** matches keywords. An identifier cannot be a keyword. */
  def keywords: Set[String] = Set(
    "true", "false", "Real", "Bool",
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
    (CharIn("a-zA-Z") ~~ CharIn("a-zA-Z0-9").repX).!.
      flatMapX(id =>
        if (keywords.contains(id))
          Fail.opaque(s"Keyword $id cannot be used as identifiers")
        else Pass(id)
      ) ~~
      (("_" ~~ ("_".? ~~ ("0" | CharIn("1-9") ~~ CharIn("0-9").repX)).!) |
        "_".!).?
    ).opaque("identifier").map({
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
  def term[_: P]: P[Term] = P(
    signed(summand) ~
    // Note: the summand is signed, rather than the first multiplicand
    // in `summand`, because -5*6 is parsed as -(5*6)
    (("+" | "-" ~ !">").!./ ~ signed(summand)).rep
  ).map { case (left, sums) =>
    sums.foldLeft(left) {
      case (m1, ("+", m2)) => Plus(m1, m2)
      case (m1, ("-", m2)) => Minus(m1, m2)
    }
  }

  def summand[_: P]: P[Term] =
    // Lookahead is to avoid /* */ comments
    (multiplicand ~ (("*" | "/" ~~ !"*").!./ ~ signed(multiplicand)).rep).
      map { case (left, mults) =>
        mults.foldLeft(left) {
          case (m1, ("*", m2)) => Times(m1, m2)
          case (m1, ("/", m2)) => Divide(m1, m2)
        }
      }

  def multiplicand[_: P]: P[Term] =
    (baseTerm ~ ("^"./ ~ signed(baseTerm)).rep).map{ case (left, pows) =>
      (left +: pows).reduceRight(Power)
    }

  def baseTerm[_: P]: P[Term] = P(
      number./ | dot./ | function.flatMap(diff) | unitFunctional.flatMap(diff) | variable
      /* termList has a cut after (, but this is safe, because we
       * require that if the first available character is ( it is
       * unambiguously a term parenthesis */
      | termList.flatMap(diff)
  )

  def function[_: P]: P[FuncOf] = P(ident ~~ ("<<" ~/ formula ~ ">>").? ~~ termList).map({case (s,idx,interp,ts) =>
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
  def biimplication[_: P]: P[Formula] =
    (backImplication ~ ("<->" ~/ backImplication).?).
      map{ case (left,None) => left case (left,Some(r)) => Equiv(left,r) }

  /* <- (left-assoc) */
  def backImplication[_: P]: P[Formula] =
    (implication ~ ("<-" ~ !">" ~/ implication).rep).
      map{ case (left, hyps) =>
        hyps.foldLeft(left){case (acc,hyp) => Imply(hyp,acc)} }

  /* -> (right-assoc) */
  def implication[_: P]: P[Formula] =
    (disjunct ~ ("->" ~/ disjunct).rep).
      map{ case (left, concls) => (left +: concls).reduceRight(Imply) }

  /* | (right-assoc) */
  def disjunct[_: P]: P[Formula] =
    (conjunct ~ ("|" ~/ conjunct).rep).
      map{ case (left, conjs) => (left +: conjs).reduceRight(Or) }

  /* & (right-assoc) */
  def conjunct[_: P]: P[Formula] =
    (baseF ~ ("&" ~/ baseF).rep).
      map{ case (left, forms) => (left +: forms).reduceRight(And) }

  /** Base formulas */
  def baseF[_: P]: P[Formula] = (
    unambiguousBaseF |
      // Cut is safe -- we handle all viable cases here
      &(recAmbiguousBaseF)./ ~ (
        &(recAmbiguousBaseF ~ ("+" | "-" ~ !">" | "*" | "/" ~~ !"*" | "^" | comparator))./ ~~ comparison |
        recAmbiguousBaseF
        ) |
      // Now we know that the following baseF is either a comparison
      // (which starts with an unambiguous term)
      &(term) ~/ comparison |
      // or an ambiguous formula (which doesn't start with a term)
      ambiguousBaseF(formula)
  )

  def recAmbiguousBaseF[_: P]: P[Formula] = ambiguousBaseF(recAmbiguousBaseF)

  def ambiguousBaseF[_: P](rec: => P[Formula]): P[Formula] = (
    /* predicate OR function */
    ( ident ~~ termList ~ "'".!.? ).map {
      case (name, idx, args, diff) =>
        val p = PredOf(Function(name, idx, args.sort, Bool), args)
        diff match {
          case None => p
          case Some("'") => DifferentialFormula(p)
        }
    }
    /* unit predicational OR unit functional */
    |  ( ident ~~ space ~ "'".!.?).flatMap {
      case (name, idx, args, diff) =>
        if (idx.isDefined)
          Fail.opaque("Unit predicationals cannot have indices")
        else {
          val p = UnitPredicational(name, args)
          Pass(diff match {
            case None => p
            case Some("'") => DifferentialFormula(p)
          })
        }
    }
    /* parenthesized formula OR term */
    | ("(" ~ rec ~ ")" ~ "'".!.?).map {
      case (form,None) => form
      case (form,Some("'")) => DifferentialFormula(form)
    }
  )

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

  /** Parses a comparison, given the left-hand term */
  def comparison[_: P]: P[Formula] = P(
    (term ~ comparator.! ~/ term).map {
      case (left, "=", right) => Equal(left, right)
      case (left, "!=", right) => NotEqual(left, right)
      case (left, ">=", right) => GreaterEqual(left, right)
      case (left, ">", right) => Greater(left, right)
      case (left, "<=", right) => LessEqual(left, right)
      case (left, "<", right) => Less(left, right)
    }
  )

  def comparator[_: P]: P[Unit] = P("=" ~~ !"=" | "!=" | ">=" | ">" | "<=" | "<" ~~ !"-")

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

  def assign[_: P]: P[AtomicProgram] = (
    (variable ~ ":="./).flatMap(x =>
      "*".!.map(_ => AssignAny(x))
        | term.map(t => Assign(x,t))
    ) ~ ";"
  )
  def test[_: P]: P[Test] = ( "?" ~/ formula ~ ";").map(f => Test(f))
  def braceP[_: P]: P[Program] = ( "{" ~ program ~ "}" ~/ (("*" | "×")./.! ~ annotation.?).?).
    map({
      case (p,None) => p
      case (p,Some(("*",None))) => Loop(p)
      case (p,Some(("*",Some(inv)))) => reportAnnotation(Loop(p),inv); Loop(p)
      case (p,Some(("×", _))) => Dual(Loop(Dual(p)))
    })
  def odeprogram[_: P]: P[ODESystem] = ( diffProgram ~ ("&" ~/ formula).?).
    map({case (p,f) => ODESystem(p,f.getOrElse(True))})
  def odesystem[_: P]: P[ODESystem] = ( "{" ~ odeprogram ~ "}" ~/ annotation.?).
    map({case (p,None) => p case (p,Some(inv)) => reportAnnotation(p,inv); p})

  def baseP[_: P]: P[Program] = (
    systemSymbol | programSymbol | assign | test | ifthen | odesystem | braceP
  )

  /** Parses dual notation: baseP or baseP^@ */
  def dual[_: P]: P[Program] = (baseP ~ "^@".!./.?).map({
    case (p, None) => p
    case (p, Some("^@")) => Dual(p)
  })

  /** Parses an annotation */
  def annotation[_: P]: P[Formula] = "@invariant" ~/ "(" ~/ formula ~ ")"

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

  def ode[_: P]: P[AtomicODE] = P( diffVariable ~ "=" ~/ term).map({case (x,t) => AtomicODE(x,t)})
  def diffProgramSymbol[_: P]: P[DifferentialProgramConst] =
    P( ident ~~ odeSpace.?).flatMap({
      case (s, None, None)     => Pass(DifferentialProgramConst(s))
      case (s, None, Some(sp)) => Pass(DifferentialProgramConst(s,sp))
      case (s, Some(i), _)     => Fail.opaque("Differential program symbols cannot have an index: " + s + "_" + i)})
  def atomicDP[_: P]: P[AtomicDifferentialProgram] = ( ode | diffProgramSymbol )

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

