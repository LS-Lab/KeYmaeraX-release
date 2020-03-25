/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
/**
  * Parse programmatic syntax for Kaisar proofs
  * @author Brandon Bohrer
  */
package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import fastparse._
//@TODO: Nicer whitespace
import MultiLineWhitespace._
//import NoWhitespace._
import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.KaisarProof._
import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.ParserCommon._
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXParser, Parser}
import edu.cmu.cs.ls.keymaerax.core._

private object ParserCommon {
  val reservedWords: Set[String] = Set("by", "RCF", "auto", "prop", "end", "proof", "using", "assert", "assume", "have",
    "ghost", "solve", "induct", "domain", "duration", "left", "right", "yield", "let", "match", "either", "cases",
    "or", "print", "for")
  def identString[_: P]: P[String] = {
    // Because (most of) the parser uses multiline whitespace, rep will allow space between repetitions.
    // locally import "no whitespace" so that identifiers cannot contain spaces.
    import NoWhitespace._
    (CharIn("a-zA-Z") ~ CharIn("a-zA-Z1-9").rep ~ P("'").?).!.filter(s  => !reservedWords.contains(s))
  }
  def reserved[_: P]: P[String]  = CharIn("a-zA-Z'").rep(1).!.filter(reservedWords.contains)
  def ws[_ : P]: P[Unit] = P((" " | "\n").rep)
  def wsNonempty[_ : P]: P[Unit] = P((" " | "\n").rep(1))
  def literal[_: P]: P[String] = "\"" ~ CharPred(c => c != '\"').rep(1).! ~ "\""
  def ident[_: P]: P[Ident] = identString
  def number[_: P]: P[Number] =
    ("-".!.? ~ (("0" | CharIn("1-9") ~ CharIn("0-9").rep) ~ ("." ~ CharIn("0-9").rep(1)).?).!)
    .map({case (None, s) => Number(BigDecimal(s))
          case (Some("-"), s) => Number(BigDecimal("-" + s))})
  def variable[_ : P]: P[Variable] = {
    identString.map(s => {
      //println("Identifier: " + s)
      if (s.endsWith("'")) DifferentialSymbol(BaseVariable(s.dropRight(1))) else BaseVariable(s)
    })
  }

  // hack:  ^d is reserved for dual programs, don't allow in terms
  def opPower[_: P]: P[Unit] =
    P("^") ~ !(P("d") ~ !(CharIn("a-zA-Z")))
}

object ExpressionParser {
  // for parsing extended kaisar expression + pattern syntax
  def wild[_: P]: P[FuncOf] = P("*").map(_ => FuncOf(Function("wild", domain = Unit, sort = Unit, interpreted = true), Nothing))

  def min[_: P]: P[FuncOf] = ("min" ~/ "(" ~ ws ~ term ~ ws ~ "," ~ ws ~ term ~ ws ~ ")")
    .map({case (l, r) => FuncOf(Function("min", domain = Tuple(Real, Real), sort = Real, interpreted=true), Pair(l, r))})

  def max[_: P]: P[FuncOf] = ("max" ~/ "(" ~ ws ~ term ~ ws ~ "," ~ ws ~ term ~ ws ~ ")")
    .map({case (l, r) => FuncOf(Function("max", domain = Tuple(Real, Real), sort = Real, interpreted=true), Pair(l, r))})

  def abs[_: P]: P[FuncOf] = ("abs" ~/ "(" ~ ws ~ term ~ ws ~ ")")
    .map({case e => FuncOf(Function("abs", domain = Real, sort = Real, interpreted=true), e)})

  def parenTerm[_: P]: P[Term] = ("(" ~/ term ~ ")")

  def terminal[_: P]: P[Term] =
    ((parenTerm | min | max | abs | wild | variable | number) ~ (P("'").!.?)).
      map({case (e, None) => e case (e, Some(_)) => Differential(e)})

  def power[_: P]: P[Term] =
    (terminal ~/ (opPower ~ terminal).rep).map({case (x, xs) => (xs.+:(x)).reduce(Power)})

  def neg[_: P]: P[Term] =
    // check neg not followed by numeral since neg followed by numeral is Number() constructor already
    (("-".! ~ !CharIn("0-9")).? ~/ power).map({case (None, e) => e case (Some(_), e) => Neg(e)})

  def at[_: P]: P[Term] = {
    val at = Function("at", domain = Tuple(Real, Unit), sort = Real, interpreted = true)
    (neg ~ (CharIn("@") ~/ ident).?).map({ case (e, None) => e
    case (e, Some(s)) =>
      val label = Function(s, domain = Unit, sort = Unit, interpreted = true)
      FuncOf(at, Pair(e, FuncOf(label, Nothing)))
    })
  }
  //def times[_: P]: P[Term] =
//    (at ~ ("*" ~ at).rep).map({case (x, xs) => (xs.+:(x)).reduce(Times)})
  def divide[_: P]: P[Term] =
    (at ~/ (("/" | "*").! ~/ at).rep).map({case (x: Term, xs: Seq[(String, Term)]) =>
      xs.foldLeft(x)({case (acc, ("/", e)) => Divide(acc, e) case (acc, ("*", e)) => Times(acc, e)})})

  def minus[_: P]: P[Term] =
    (divide ~/ (("-" | "+").! ~/ divide).rep).map({case (x: Term, xs: Seq[(String, Term)]) =>
      xs.foldLeft(x)({case (acc, ("+", e)) => Plus(acc, e) case (acc, ("-", e)) => Minus(acc, e)})})

  def term[_: P]: P[Term] = minus

  def test[_: P]: P[Test] = ("?" ~/ formula).map(Test)
  // semicolon terminator parsed in differentialProduct
  def assign[_: P]: P[Assign] = (variable ~ ":=" ~ term).map({case (x, f) => Assign(x, f)})
  // semicolon terminator parsed in differentialProduct
  def assignAny[_: P]: P[AssignAny] = (variable ~ ":=" ~ ws ~ "*").map(AssignAny)

  def parenProgram[_: P]: P[Program] = "{" ~/ program ~ "}"

  def atomicOde[_: P]: P[AtomicODE] = (variable.filter(_.isInstanceOf[DifferentialSymbol]) ~/  "=" ~  term).
    map({case (x: DifferentialSymbol, f) => AtomicODE(x, f)})

  def terminalProgram[_: P]: P[Program] = (parenProgram | atomicOde | test  | assignAny | assign)

  // @TODO: careful about ; in ode
  def differentialProduct[_: P]: P[Program] =
    // @TODO: Careful about polymorphic list
    ((terminalProgram.opaque("program") ~ ("," ~ terminalProgram.opaque("program")).rep ~ ("&" ~/ formula).? ~ ";").map({
      case (x: AtomicODE, xs: Seq[AtomicODE], Some(fml)) =>
        val odes: Seq[DifferentialProgram] = xs.+:(x)
        ODESystem(odes.reduce[DifferentialProgram]({case (l, r) => DifferentialProduct(l, r)}), fml)
      case (x: AtomicODE, xs: Seq[AtomicODE], None) =>
        val odes: Seq[DifferentialProgram] = xs.+:(x)
        ODESystem(odes.reduce[DifferentialProgram]({case (l, r) => DifferentialProduct(l, r)}))
      case (x, Seq(), None) =>
        x
    }) ~ ((P("*") | P("^d") | P("^@")).!.rep).opaque("postfix")).map({case (atom: Program, posts: Seq[String]) =>
      posts.foldLeft[Program](atom)({case (acc, "*") => Loop(acc) case (acc, ("^d" | "^@")) => Dual(acc)})
    })

  def compose[_: P]: P[Program] =
    (differentialProduct.rep(1)).map({xs => xs.reduceRight(Compose)})

  def choice[_: P]: P[Program] =
    (compose ~ ("++"  ~/ choice).rep).map({case (x, xs) => (xs.+:(x)).reduceRight(Choice)})

  def program[_: P]: P[Program] = choice


  // !P  P & Q   P | Q   P -> Q   P <-> Q   [a]P  <a>P  f ~ g \forall \exists
  def infixTerminal[_: P]: P[Formula] =
    (term.opaque("term") ~ ("<=" | "<" | "=" | "!=" | ">=" | ">").!.opaque("cmp") ~/ term.opaque("term")).map({
      case (l, "<=", r) => LessEqual(l, r)
      case (l, "<", r) => Less(l, r)
      case (l, "=", r) => Equal(l, r)
      case (l, "!=", r) => NotEqual(l, r)
      case (l, ">", r) => Greater(l, r)
      case (l, ">=", r) => GreaterEqual(l, r)
      case (l, s, r) =>
        {val x = s
          //println("Ident: " + s)
          val 2 = 1 + 1
          True
        }
    })

  def parenFormula[_: P]: P[Formula] = ("(" ~/ formula ~ ")")
  def verum[_: P]: P[AtomicFormula] = P("true").map(_ => True)
  def falsum[_: P]: P[AtomicFormula] = P("false").map(_ => False)
  def not[_: P]: P[Formula] = ("!" ~/ prefixTerminal).map(f => Not(f))
  def forall[_: P]: P[Formula] = ("\\forall" ~/ variable  ~ prefixTerminal).map({case (x, p) => Forall(List(x), p)})
  def exists[_: P]: P[Formula] = ("\\exists" ~/ variable  ~ prefixTerminal).map({case (x, p) => Exists(List(x), p)})
  def box[_: P]: P[Formula] = (("[" ~/ program  ~ "]" ~ prefixTerminal)).map({case (l, r) => Box(l ,r)})
  def diamond[_: P]: P[Formula] = ("<"  ~/ program  ~ ">"  ~ prefixTerminal).map({case (l, r) => Diamond(l, r)})

  def prefixTerminal[_: P]: P[Formula] =
    ((parenFormula | verum | falsum | not | forall | exists | box | diamond | infixTerminal) ~ ("'".!.?)).
      map({case (f, None) => f case (f, Some(_)) => DifferentialFormula(f)})

  def and[_: P]: P[Formula] = (prefixTerminal ~ ("&"  ~/ prefixTerminal).rep).map({case (x, xs) => (xs.+:(x)).reduceRight(And)})
  def or[_: P]: P[Formula] = (and ~ ("|"  ~ and).rep).map({case (x, xs) => (xs.+:(x)).reduceRight(Or)})
  def imply[_: P]: P[Formula] = (or ~ ("->"  ~ or).rep).map({case (x, xs) => (xs.+:(x)).reduceRight(Imply)})
  def equiv[_: P]: P[Formula] = (imply ~ ("<->"  ~ imply).rep).map({case (x, xs) => (xs.+:(x)).reduceRight(Equiv)})

  def formula[_: P]: P[Formula] = equiv

  def expression[_: P]: P[Expression] = term | program | formula
}

object KaisarProgramParser {
  def expression[_: P]: P[Expression] = literal.map(KeYmaeraXParser(_))
  def formula[_: P]: P[Formula] = expression.map(_.asInstanceOf[Formula])
  def program[_: P]: P[Program] = expression.map(_.asInstanceOf[Program])
  def differentialProgram[_: P]: P[DifferentialProgram] = expression.map(_.asInstanceOf[DifferentialProgram])
  def term[_: P]: P[Term] = expression.map(_.asInstanceOf[Term])
}
