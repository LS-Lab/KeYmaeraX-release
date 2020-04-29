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
import MultiLineWhitespace._
import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.KaisarProof._
import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.ParserCommon._
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXParser, Parser}
import edu.cmu.cs.ls.keymaerax.core._

object ParserCommon {
  val reservedWords: Set[String] = Set("by", "RCF", "auto", "prop", "end", "proof", "using", "assert", "assume", "have",
    "ghost", "solve", "induct", "domain", "duration", "left", "right", "yield", "let", "match", "either", "cases",
    "or", "print", "for", "while")

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
  def number[_: P]: P[Number] = {
    import NoWhitespace._
    ("-".!.? ~  (("0" | CharIn("1-9") ~ CharIn("0-9").rep) ~ ("." ~ CharIn("0-9").rep(1)).?).!)
    .map({case (None, s) => Number(BigDecimal(s))
          case (Some("-"), s) => Number(BigDecimal("-" + s))})
  }

  def variable[_ : P]: P[Variable] = {
    identString.map(s => {
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

  def min[_: P]: P[FuncOf] = ("min" ~ "(" ~ ws ~ term ~ ws ~ "," ~ ws ~ term ~ ws ~ ")")
    .map({case (l, r) => FuncOf(Function("min", domain = Tuple(Real, Real), sort = Real, interpreted=true), Pair(l, r))})

  def max[_: P]: P[FuncOf] = ("max" ~ "(" ~ ws ~ term ~ ws ~ "," ~ ws ~ term ~ ws ~ ")")
    .map({case (l, r) => FuncOf(Function("max", domain = Tuple(Real, Real), sort = Real, interpreted=true), Pair(l, r))})

  def abs[_: P]: P[FuncOf] = ("abs" ~ "(" ~ ws ~ term ~ ws ~ ")")
    .map({case e => FuncOf(Function("abs", domain = Real, sort = Real, interpreted=true), e)})

  def parenTerm[_: P]: P[Term] = (("(" ~ term ~ ")"))

  def terminal[_: P]: P[Term] =
    ((min | max | abs | wild | variable | number | parenTerm) ~ (P("'").!.?)).
      map({case (e, None) => e case (e, Some(_)) => Differential(e)})

  def power[_: P]: P[Term] =
    (terminal ~ (opPower ~ terminal).rep()).
      map({case (x, xs) => (xs.+:(x)).reduce(Power)})

  def neg[_: P]: P[Term] =
    // check neg not followed by numeral since neg followed by numeral is Number() constructor already
    (("-".! ~ !CharIn(">0-9")).? ~ power).map({case (None, e) => e case (Some(_), e) => Neg(e)})

  def at[_: P]: P[Term] = {
    val at = Function("at", domain = Tuple(Real, Unit), sort = Real, interpreted = true)
    (neg ~ (CharIn("@") ~ ident).?).map({
      case (e, None) => e
      case (e, Some(s)) =>
        val label = Function(s, domain = Unit, sort = Unit, interpreted = true)
        FuncOf(at, Pair(e, FuncOf(label, Nothing)))
    })
  }

  def divide[_: P]: P[Term] =
    (at ~ (("/" | "*").! ~ at).rep).map({case (x: Term, xs: Seq[(String, Term)]) =>
      xs.foldLeft(x)({case (acc, ("/", e)) => Divide(acc, e) case (acc, ("*", e)) => Times(acc, e)})})

  def minus[_: P]: P[Term] =
    // disambiguate "-" and "->"
    (divide ~ ((("-"  ~ !P(">")) | "+").! ~ divide).rep).map({case (x: Term, xs: Seq[(String, Term)]) =>
      xs.foldLeft(x)({case (acc, ("+", e)) => Plus(acc, e) case (acc, ("-", e)) => Minus(acc, e)})})

  // @TODO: Need to add function syntax
  def term[_: P]: P[Term] = minus

  def test[_: P]: P[Test] = ("?" ~ formula).map(Test)
  // semicolon terminator parsed in differentialProduct
  def assign[_: P]: P[Assign] = (variable ~ ":=" ~ term).map({case (x, f) => Assign(x, f)})
  // semicolon terminator parsed in differentialProduct
  def assignAny[_: P]: P[AssignAny] = (variable ~ ":=" ~ ws ~ "*").map(AssignAny)

  def parenProgram[_: P]: P[Program] = "{" ~ program ~ "}".?

  // Note: Cut after = since x' could be either ode or assignment
  def atomicOde[_: P]: P[AtomicODE] = (variable.filter(_.isInstanceOf[DifferentialSymbol]) ~  "=" ~  term).
    map({case (x: DifferentialSymbol, f) => AtomicODE(x, f)})

  def terminalProgram[_: P]: P[Program] = (parenProgram | atomicOde | test  | assignAny | assign)

  // @TODO: careful about ; in ode
  // Note: ; needs to be optional since {} is an atomic program which doesn't need ; terminator. If we really care we could
  // do a flapmap and only use ; when not {}
  def differentialProduct[_: P]: P[Program] =
    // @TODO: Careful about polymorphic list
    ((terminalProgram.opaque("program") ~ ("," ~ terminalProgram.opaque("program")).rep ~ ("&" ~ formula).? ~ ";".?).map({
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
    (compose ~ ("++"  ~ compose).rep).map({case (x, xs) => (xs.+:(x)).reduceRight(Choice)})

  def program[_: P]: P[Program] = choice

  // !P  P & Q   P | Q   P -> Q   P <-> Q   [a]P  <a>P  f ~ g \forall \exists
  def infixTerminal[_: P]: P[Formula] =
    (term.opaque("term") ~ (("<=" | "<" | "=" | "!=" | ">=" | ">").!.opaque("cmp") ~ term.opaque("term"))).map({
      case (l, ("<=", r)) => LessEqual(l, r)
      case (l, ("<", r)) => Less(l, r)
      case (l, ("=", r)) => Equal(l, r)
      case (l, ("!=", r)) => NotEqual(l, r)
      case (l, (">", r)) => Greater(l, r)
      case (l, (">=", r)) => GreaterEqual(l, r)
      case (l, (s, r)) => True
    })

  // Note: cut *after* formula because delimiter ( is ambiguous, could be term e.g. (1) <= (2)
  def parenFormula[_: P]: P[Formula] = (("(" ~ formula ~ ")"))
  def verum[_: P]: P[AtomicFormula] = P("true").map(_ => True)
  def falsum[_: P]: P[AtomicFormula] = P("false").map(_ => False)
  def not[_: P]: P[Formula] = ("!" ~ prefixTerminal).map(f => Not(f))
  def forall[_: P]: P[Formula] = ("\\forall" ~ variable  ~ prefixTerminal).map({case (x, p) => Forall(List(x), p)})
  def exists[_: P]: P[Formula] = ("\\exists" ~ variable  ~ prefixTerminal).map({case (x, p) => Exists(List(x), p)})
  def box[_: P]: P[Formula] = (("[" ~ program  ~ "]" ~ prefixTerminal)).map({case (l, r) => Box(l ,r)})
  def diamond[_: P]: P[Formula] = (("<" ~ !P("->"))  ~ program  ~ ">"  ~ prefixTerminal).map({case (l, r) => Diamond(l, r)})

  // @TODO: fix
  def prefixTerminal[_: P]: P[Formula] =
    ((verum | falsum | not | forall | exists | box | diamond  | infixTerminal | parenFormula ) ~ ("'".!.?)).
      map({case (f, None) => f case (f, Some(_)) => DifferentialFormula(f)})

  def and[_: P]: P[Formula] = (prefixTerminal ~ ("&"  ~ prefixTerminal).rep).map({case (x, xs) => (xs.+:(x)).reduceRight(And)})
  def or[_: P]: P[Formula] = (and ~ ("|"  ~ and).rep).map({case (x, xs) => (xs.+:(x)).reduceRight(Or)})
  def imply[_: P]: P[Formula] = (or ~ ("->"  ~ or).rep).map({case (x, xs) => (xs.+:(x)).reduceRight(Imply)})
  def equiv[_: P]: P[Formula] = (imply ~ ("<->"  ~ imply).rep).map({case (x, xs) => (xs.+:(x)).reduceRight(Equiv)})

  def formula[_: P]: P[Formula] = equiv
  def expression[_: P]: P[Expression] = term | program | formula
}

object ProofParser {
  import ExpressionParser.{formula, program, term, expression, atomicOde}
  import KaisarKeywordParser.proofTerm

  def rcf[_: P]: P[RCF] = P("by" ~ ws ~ "RCF").map(_ => RCF())
  def auto[_: P]: P[Auto] = P("by" ~ ws ~ "auto").map(_ => Auto())
  def prop[_: P]: P[Prop] = P("by" ~ ws ~ "prop").map(_ => Prop())
  def using[_: P]: P[Using] = (P("using") ~ selector.rep  ~ method).map({case (sels, meth) => Using(sels.toList, meth)})
  def byProof[_: P]: P[ByProof] = ("proof" ~ proof ~ "end").map(ByProof)

  def forwardSelector[_: P]: P[ForwardSelector] = proofTerm.map(ForwardSelector)
  def patternSelector[_: P]: P[PatternSelector] = (P("*").map(_ => PatternSelector(wild)) | expression.map(PatternSelector))
  def selector[_: P]: P[Selector] = !reserved ~ (forwardSelector | patternSelector)

  def method[_: P]: P[Method] = rcf | auto | prop | using | byProof

  def wildPat[_: P]: P[WildPat] = CharIn("_*").map(_ => WildPat())
  def tuplePat[_: P]: P[IdPat] = ("(" ~ idPat.rep(sep=",") ~ ")").map(ss =>
    ss.length match {
      case 0 => NoPat()
      case 1 => ss.head
      case _ => TuplePat(ss.toList)
    })

  //@TODO: What is the syntax for variable assumptions on :=
  def varPat[_: P]: P[VarPat] = (ident ~ ("{" ~ variable ~ "}").?).map({case (p, x) => VarPat(p, x)})
  def idPat[_: P]: P[IdPat] = tuplePat | wildPat | varPat
  def idOptPat[_: P]: P[IdPat] = (idPat ~ (":" ~ !P("="))).?.map({case None => NoPat() case Some(pat) => pat})

  def assume[_: P]: P[Assume] = ("?" ~  idOptPat ~ formula ~ ";").map({
    case (pat, fml) => Assume(pat, fml)})

  def assert[_: P]: P[Assert] = ("!" ~ idOptPat  ~ formula ~ ":=" ~ method ~ ";").map({
    case (pat, fml, method) => Assert(pat, fml, method)})

  def modify[_: P]: P[Modify] = (idPat ~ ":=" ~ ("*".!.map(Right(_)) | term.map(Left(_))) ~ ";").
    map({case (p, Left(f)) => Modify(p, Left(f)) case (p, Right(_)) => Modify(p, Right())})

  def label[_: P]: P[Label] = {
    import NoWhitespace._
    (ident ~ ":" ~ !P("=")).map(id => Label(id))
  }

  def branch[_: P]: P[(Expression, Statement)] = {
    ("case" ~ formula ~ ":" ~ statement.rep).map({case (fml: Formula, ss: Seq[Statement]) => (fml, block(ss.toList))})
  }

  def switch[_: P]: P[Switch] = {
    ("switch" ~ "{" ~ branch.rep ~ "}").map(branches => Switch(branches.toList))
  }


  def parseBlock[_: P]: P[Statement] = ("{" ~ statement.rep ~ "}").map(ss => block(ss.toList))
  def boxLoop[_: P]: P[BoxLoop] = (statement.rep ~ "*").map(ss => BoxLoop(block(ss.toList)))
  def ghost[_: P]: P[Ghost] = ("(G" ~ statement.rep ~ "G)").map(ss => Ghost(block(ss.toList)))
  def inverseGhost[_: P]: P[InverseGhost] = ("{G" ~ statement.rep ~ "G}").map(ss => InverseGhost(block(ss.toList)))
  def parseWhile[_: P]: P[While] = ("while" ~ "(" ~ formula ~ ")" ~ "{" ~ statement.rep ~ "}").map({case (fml: Formula, ss: Seq[Statement]) => While(NoPat(), fml, block(ss.toList))})

  def let[_: P]: P[Statement] = ("let" ~ ((ident ~ "(" ~ ident ~ ")").map(Left(_)) | expression.map(Right(_))) ~ "=" ~ expression ~ ";").
    map({case (Left((f, x)), e) => LetFun(f, x, e) case (Right(pat), e) => Match(pat, e)})

  def note[_: P]: P[Note] = ("note" ~ ident ~ "=" ~ proofTerm ~ ";").map({case (id, pt) => Note(id, pt)})

  def atomicODEStatement[_: P]: P[AtomicODEStatement] = atomicOde.map(AtomicODEStatement)
  def ghostODE[_: P]: P[DiffStatement] = ("(G" ~ diffStatement ~ "G)").map(DiffGhostStatement)
  def inverseGhostODE[_: P]: P[DiffStatement] = ("{G" ~ diffStatement ~ "G}").map(InverseDiffGhostStatement)
  def terminalODE[_: P]: P[DiffStatement] = ghostODE | inverseGhostODE | atomicODEStatement
  def diffStatement[_: P]: P[DiffStatement] = terminalODE.rep(sep = ",", min = 1).map(_.reduceRight(DiffProductStatement))

  //@TODO: Optional patterns, allow parens i guess
  def domAssume[_: P]: P[DomAssume] = (idOptPat ~ formula).map({case (id, f) => DomAssume(id, f)})
  def domAssert[_: P]: P[DomAssert] = ("!" ~ idPat ~ ":" ~ formula ~ method).map({case (id, f, m) => DomAssert(id, f, m)})
  def domModify[_: P]: P[DomModify] = (variable ~ ":=" ~ term).map({case (id, f) => DomModify(NoPat(), Assign(id, f))})
  def domWeak[_: P]: P[DomWeak] = ("{G" ~ domainStatement ~ "G}").map(DomWeak)
  def terminalDomainStatement[_: P]: P[DomainStatement] = domAssert | domWeak |  domModify | domAssume
  def domainStatement[_: P]: P[DomainStatement] = terminalDomainStatement.rep(sep = "&", min = 1).map(_.reduceRight(DomAnd))

  def proveODE[_: P]: P[ProveODE] =
    (diffStatement ~ ("&" ~ domainStatement).?.
        map({case Some(v) => v case None => DomAssume(NoPat(), True)})
    ).map({case(ds, dc) => ProveODE(ds, dc)})

  def printGoal[_: P]: P[PrintGoal] = ("print" ~ literal ~ ";").map(PrintGoal)

  def atomicStatement[_: P]: P[Statement] =
    printGoal | note | let | switch | assume | assert | ghost | inverseGhost | parseWhile | parseBlock | label | modify

  def postfixStatement[_: P]: P[Statement] =
    ((atomicStatement | proveODE) ~ "*".!.rep).
      map({case (s, stars) => stars.foldLeft(s)({case (acc, x) => BoxLoop(acc)})})

  def sequence[_: P]: P[Statements] =
    postfixStatement.rep(1).map(ss => ss.toList)

  def boxChoice[_: P]: P[Statement] = {
    sequence.rep(sep = "++", min = 1)
      .map(_.reduceRight((l, r) => List(BoxChoice(block(l), block(r)))))
      .map(block)
  }

  def statement[_: P]: P[Statement] = boxChoice
  def statements[_: P]: P[List[Statement]] = statement.rep.map(ss => flatten(ss.toList))
  def proof[_: P]: P[Proof] = boxChoice.map(ss => Proof(List(ss)))
}

object KaisarProgramParser {
  def expression[_: P]: P[Expression] = literal.map(KeYmaeraXParser(_))
  def formula[_: P]: P[Formula] = expression.map(_.asInstanceOf[Formula])
  def program[_: P]: P[Program] = expression.map(_.asInstanceOf[Program])
  def differentialProgram[_: P]: P[DifferentialProgram] = expression.map(_.asInstanceOf[DifferentialProgram])
  def term[_: P]: P[Term] = expression.map(_.asInstanceOf[Term])
}
