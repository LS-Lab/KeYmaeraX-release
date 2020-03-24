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
  def identString[_: P]: P[String] = CharIn("a-zA-Z'").rep(1).!.filter(!reservedWords.contains(_))
  def reserved[_: P]: P[String]  = CharIn("a-zA-Z'").rep(1).!.filter(reservedWords.contains)
  def ws[_ : P]: P[Unit] = P((" " | "\n").rep)
  def wsNonempty[_ : P]: P[Unit] = P((" " | "\n").rep(1))
  def literal[_: P]: P[String] = "\"" ~ CharPred(c => c != '\"').rep(1).! ~ "\""
  def ident[_: P]: P[Ident] = identString
  def number[_: P]: P[Number] =
    ("-".? ~ ("0" | CharIn("1-9") ~ CharIn("0-9").rep) ~ ("." ~ CharIn("0-9").rep(1)).?).!
    .map(s => Number(BigDecimal(s)))
  def variable[_ : P]: P[Variable] =
    identString.map(s => if (s.endsWith("'")) DifferentialSymbol(BaseVariable(s.dropRight(1))) else BaseVariable(s))
}

object ExpressionParser {
  // for parsing extended kaisar expression + pattern syntax
  //@todo: careful about term x^d should probably be reserved or illegal
  // x c + * / - ^ min max abs ()
  // precedence:
  // ^
  // *
  // /
  // +
  // -
  def wild[_: P]: P[FuncOf] = P("*").map(_ => FuncOf(Function("wild", domain = Unit, sort = Unit, interpreted = true), Nothing))

  def min[_: P]: P[FuncOf] = ("min" ~ ws ~ "(" ~ ws ~ term ~ ws ~ "," ~ ws ~ term ~ ws ~ ")")
    .map({case (l, r) => FuncOf(Function("min", domain = Tuple(Real, Real), sort = Real, interpreted=true), Pair(l, r))})

  def max[_: P]: P[FuncOf] = ("max" ~ ws ~ "(" ~ ws ~ term ~ ws ~ "," ~ ws ~ term ~ ws ~ ")")
    .map({case (l, r) => FuncOf(Function("max", domain = Tuple(Real, Real), sort = Real, interpreted=true), Pair(l, r))})

  def abs[_: P]: P[FuncOf] = ("abs" ~ ws ~ "(" ~ ws ~ term ~ ws ~ ")")
    .map({case e => FuncOf(Function("abs", domain = Real, sort = Real, interpreted=true), e)})

  def parenTerm[_: P]: P[Term] = ("(" ~ ws ~ term ~ ws ~ ")")

  def terminal[_: P]: P[Term] =
    ((parenTerm | min | max | abs | wild | variable | number) ~ (P("'").!.?)).
      map({case (e, None) => e case (e, Some(_)) => Differential(e)})

  def power[_: P]: P[Term] =
    (terminal ~ ("^" ~ terminal).rep).map({case (x, xs) => (xs.+:(x)).reduce(Power)})
  def neg[_: P]: P[Term] =
    ("-".!.? ~ power).map({case (None, e) => e case (Some(_), e) => Neg(e)})
  def at[_: P]: P[Term] = {
    val at = Function("at", domain = Tuple(Real, Unit), sort = Real, interpreted = true)
    (neg ~ (CharIn("@") ~ ident).?).map({ case (e, None) => e
    case (e, Some(s)) =>
      val label = Function(s, domain = Unit, sort = Unit, interpreted = true)
      FuncOf(at, Pair(e, FuncOf(label, Nothing)))
    })
  }
  def times[_: P]: P[Term] =
    (at ~ ("*" ~ power).rep).map({case (x, xs) => (xs.+:(x)).reduce(Times)})
  def divide[_: P]: P[Term] =
    (times ~ ("/" ~ times).rep).map({case (x, xs) => (xs.+:(x)).reduce(Divide)})
  def plus[_: P]: P[Term] =
    (divide ~ ("+" ~ divide).rep).map({case (x, xs) => (xs.+:(x)).reduce(Plus)})
  def minus[_: P]: P[Term] =
    (plus ~ ("-" ~ plus).rep).map({case (x, xs) => (xs.+:(x)).reduce(Minus)})

  def term[_: P]: P[Term] = minus

/*  def at[_: P]: P[FuncOf] = (term ~ ws ~ "@" ~ ws ~ ident).map({case (e, l) =>
    val label = FuncOf(Function(l, domain = Unit, sort = Unit, interpreted = true), Nothing)
    FuncOf(Function("at", domain = Tuple(Real, Unit), sort = Real), Pair(e, label))})*/
  //def plus[_: P]: P[Plus] = (term ~ ws ~ "+" ~ ws ~ term).map({case (l, r) => Plus(l, r)})
/*  def times[_: P]: P[Times] = (term ~ ws ~ "*" ~ ws ~ term).map({case (l, r) => Times(l, r)})
  def divide[_: P]: P[Divide] = (term ~ ws ~ "/" ~ ws ~ term).map({case (l, r) => Divide(l, r)})
  def minus[_: P]: P[Minus] = (term ~ ws ~ "-" ~ ws ~ term).map({case (l, r) => Minus(l, r)})
  def neg[_: P]: P[Neg] = ("-" ~ ws ~ term).map(e => Neg(e))
  def power[_: P]: P[Power] = (term ~ ws ~ "^" ~ ws ~ term).map({case (l, r) => Power(l, r)})*/

  // ?  :=   :=* x'=f  ; ++  * d
  def test[_: P]: P[Test] = ("?" ~ ws ~ formula ~ ws ~ ";").map(Test)
  def assign[_: P]: P[Assign] = (variable ~ ws ~ ":=" ~ ws ~ term ~ ws ~ ";").map({case (x, f) => Assign(x, f)})
  def assignAny[_: P]: P[AssignAny] = (variable ~ ws ~ ":=" ~ ws ~ "*" ~ ws ~ ";").map(AssignAny)
  def odeSystem[_: P]: P[ODESystem] = (differentialProgram ~ ws ~ ("&" ~ ws ~ formula).? ~ ws ~ ";").map({
    case (dp, None) => ODESystem(dp)
    case (dp, Some(dc)) => ODESystem(dp, dc)
  })
  def compose[_: P]: P[Compose] = (program ~ ws ~ ";" ~ ws ~ program).map({case (l, r) => Compose(l, r)})
  def choice[_: P]: P[Choice] = (program ~ ws ~ "++" ~ ws ~ program).map({case (l, r) => Choice(l, r)})
  def loop[_: P]: P[Loop] = (program ~ ws ~ "*").map(Loop)
  def dual[_: P]: P[Dual] = (program ~ ws ~ "^d").map(Dual)
  def parenProgram[_: P]: P[Program] = "{" ~ ws ~ program ~ ws ~ "}"
  def program[_: P]: P[Program] = test | assignAny | assign | odeSystem | compose | choice | loop | dual | parenProgram

  def atomicOde[_: P]: P[AtomicODE] = (variable.filter(_.isInstanceOf[DifferentialSymbol]) ~ ws ~ "=" ~ ws ~ term).
    map({case (x: DifferentialSymbol, f) => AtomicODE(x, f)})
  def differentialProduct[_: P]: P[DifferentialProduct] =
    (differentialProgram ~ ws ~ "," ~ ws ~ differentialProgram).
      map({case (l, r) => DifferentialProduct(l, r)})
  def differentialProgram[_: P]: P[DifferentialProgram] = atomicOde | differentialProduct

  // !P  P & Q   P | Q   P -> Q   P <-> Q   [a]P  <a>P  f ~ g \forall \exists
  def not[_: P]: P[Not] = ("!" ~ ws ~ formula).map(f => Not(f))
  def and[_: P]: P[And] = (formula ~ ws ~ "&" ~ ws ~ formula).map({case (l, r) => And(l, r)})
  def or[_: P]: P[Or] = (formula ~ ws ~ "|" ~ ws ~ formula).map({case (l, r) => Or(l, r)})
  def imply[_: P]: P[Imply] = (formula ~ ws ~ "->" ~ ws ~ formula).map({case (l, r) => Imply(l, r)})
  def equiv[_: P]: P[Equiv] = (formula ~ ws ~ "<->" ~ ws ~ formula).map({case (l, r) => Equiv(l ,r)})
  def box[_: P]: P[Box] = (("[" ~ ws ~ program ~ ws ~ "]" ~ ws ~ formula)).map({case (l, r) => Box(l ,r)})
  def diamond[_: P]: P[Diamond] = ("<" ~ ws ~ program ~ ws ~ ">" ~ ws ~ formula).map({case (l, r) => Diamond(l, r)})
  def forall[_: P]: P[Forall] = ("\\forall" ~ ws ~ variable ~ ws ~ formula).map({case (x, p) => Forall(List(x), p)})
  def exists[_: P]: P[Exists] = ("\\exists" ~ ws ~ variable ~ ws ~ formula).map({case (x, p) => Exists(List(x), p)})
  def verum[_: P]: P[AtomicFormula] = P("true").map(_ => True)
  def falsum[_: P]: P[AtomicFormula] = P("false").map(_ => False)
  def parenFormula[_: P]: P[Formula] = ("(" ~ ws ~ formula ~ ws ~ ")")

  def lessEqual[_: P]: P[LessEqual] = (term ~ ws ~ "<=" ~ ws ~ term).map({case (l, r) => LessEqual(l, r)})
  def less[_: P]: P[Less] = (term ~ ws ~ "<" ~ ws ~ term).map({case (l, r) => Less(l, r)})
  def equal[_: P]: P[Equal] = (term ~ ws ~ "=" ~ ws ~ term).map({case (l, r) => Equal(l, r)})
  def notEqual[_: P]: P[NotEqual] = (term ~ ws ~ "!=" ~ ws ~ term).map({case (l, r) => NotEqual(l, r)})
  def greater[_: P]: P[Greater] = (term ~ ws ~ ">" ~ ws ~ term).map({case (l, r) => Greater(l, r)})
  def greaterEqual[_: P]: P[GreaterEqual] = (term ~ ws ~ ">=" ~ ws ~ term).map({case (l, r) => GreaterEqual(l, r)})

  def formula[_: P]: P[Formula] =
    (not | and | or | imply | equiv | box | diamond | forall | exists | parenFormula | verum | falsum |
      lessEqual | less | equal | notEqual | greater | greaterEqual)

  def expression[_: P]: P[Expression] = term | program | formula
}

object KaisarProgramParser {
  def expression[_: P]: P[Expression] = literal.map(KeYmaeraXParser(_))
  def formula[_: P]: P[Formula] = expression.map(_.asInstanceOf[Formula])
  def program[_: P]: P[Program] = expression.map(_.asInstanceOf[Program])
  def differentialProgram[_: P]: P[DifferentialProgram] = expression.map(_.asInstanceOf[DifferentialProgram])
  def term[_: P]: P[Term] = expression.map(_.asInstanceOf[Term])
}
