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
import fastparse.Parsed.TracedFailure
import fastparse.internal.Msgs

import scala.collection.immutable.StringOps

object ParserCommon {
  val reservedWords: Set[String] = Set("by", "RCF", "auto", "prop", "end", "proof", "using", "assert", "assume", "have",
    "ghost", "solve", "induct", "domain", "duration", "left", "right", "yield", "let", "match", "either", "cases",
    "or", "print", "for", "while", "true", "false")

  def identOrKeyword[_: P]: P[String] = {
    // Because (most of) the parser uses multiline whitespace, rep will allow space between repetitions.
    // locally import "no whitespace" so that identifiers cannot contain spaces.
    import NoWhitespace._
    (CharIn("a-zA-Z") ~ CharIn("a-zA-Z1-9").rep ~ P("'").?).!
  }

  def identString[_: P]: P[String] = {
    identOrKeyword.filter(s  => !reservedWords.contains(s))
  }
  def reserved[_: P]: P[String]  = CharIn("a-zA-Z'").rep(1).!.filter(reservedWords.contains)
  def ws[_ : P]: P[Unit] = P((" " | "\n").rep)
  def wsNonempty[_ : P]: P[Unit] = P((" " | "\n").rep(1))
  def literal[_: P]: P[String] = "\"" ~ CharPred(c => c != '\"').rep(1).! ~ "\""
  def ident[_: P]: P[Ident] = identString.map(c => if (c.endsWith("'")) DifferentialSymbol(BaseVariable(c.dropRight(1))) else BaseVariable(c))
  def number[_: P]: P[Number] = {
    import NoWhitespace._
    ("-".!.? ~  (("0" | CharIn("1-9") ~ CharIn("0-9").rep) ~ ("." ~ CharIn("0-9").rep(1)).?).!)
    .map({case (None, s) => Number(BigDecimal(s))
          case (Some("-"), s) => Number(BigDecimal("-" + s))})
  }

  def variableTrueFalse[_ : P]: P[Expression] = {
    identOrKeyword.map({
      case "true" =>
        True
      case "false" =>
        False
      case s => {
      if (s.endsWith("'")) DifferentialSymbol(BaseVariable(s.dropRight(1))) else
        BaseVariable(s)
    }}).filter({case BaseVariable(x, _, _) => !reservedWords.contains(x) case _ => true})
  }

  // hack:  ^d is reserved for dual programs, don't allow in terms
  def opPower[_: P]: P[Unit] =
    P("^") ~ !(P("d") ~ !(CharIn("a-zA-Z")))
}

object ExpressionParser {
  // for parsing extended kaisar expression + pattern syntax
  def wild[_: P]: P[FuncOf] = (Index ~ P("*")).
    map(i => FuncOf(Function("wild", domain = Unit, sort = Unit, interpreted = true), Nothing))

  def funcOf[_: P]: P[FuncOf] =
    (ident ~ "(" ~ term.rep(min = 1, sep = ",") ~ ")").map({case (f, args) =>
      val builtins = Set("min", "max", "abs")
      val fn = Function(f.name, domain = args.map(_ => Real).reduceRight(Tuple), sort = Real, interpreted = builtins.contains(f.name))
      FuncOf(fn, args.reduceRight(Pair))
    })

  def parenTerm[_: P]: P[Term] = (("(" ~ term ~ ")"))

  def variable[_: P]: P[Variable] = variableTrueFalse.filter(_.isInstanceOf[Variable]).map(_.asInstanceOf[Variable])

  def terminal[_: P]: P[Term] =
    ((funcOf | wild | variable | number | parenTerm) ~ P("'").!.?).
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
        val label = Function(s.name, domain = Unit, sort = Unit, interpreted = true)
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

  // Note: ; needs to be optional since {} is an atomic program which doesn't need ; terminator. If we really care we could
  // do a flapmap and only use ; when not {}
  def differentialProduct[_: P]: P[Program] =
    // @TODO: Careful about polymorphic list
    ((terminalProgram.opaque("program") ~ ("," ~ terminalProgram.opaque("program")).rep ~ ("&" ~ formula).? ~ ";".?).map({
      case (x: AtomicODE, xs: Seq[_], Some(fml)) =>
        val odes: Seq[DifferentialProgram] = xs.map(_.asInstanceOf[DifferentialProgram]).+:(x)
        ODESystem(odes.reduce[DifferentialProgram]({case (l, r) => DifferentialProduct(l, r)}), fml)
      case (x: AtomicODE, xs: Seq[_], None) =>
        val odes: Seq[DifferentialProgram] = xs.map(_.asInstanceOf[DifferentialProgram]).+:(x)
        ODESystem(odes.reduce[DifferentialProgram]({case (l, r) => DifferentialProduct(l, r)}))
      case (x, Seq(), None) => x
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
  //def verum[_: P]: P[AtomicFormula] = P("true").map(_ => True)
  //def falsum[_: P]: P[AtomicFormula] = P("false").map(_ => False)
  def verumFalsum[_: P]: P[AtomicFormula] = variableTrueFalse.filter(_.isInstanceOf[AtomicFormula]).map(_.asInstanceOf[AtomicFormula])
  def not[_: P]: P[Formula] = ("!" ~ prefixTerminal).map(f => Not(f))
  def forall[_: P]: P[Formula] = ("\\forall" ~ variable  ~ prefixTerminal).map({case (x, p) => Forall(List(x), p)})
  def exists[_: P]: P[Formula] = ("\\exists" ~ variable  ~ prefixTerminal).map({case (x, p) => Exists(List(x), p)})
  def box[_: P]: P[Formula] = (("[" ~ program  ~ "]" ~ prefixTerminal)).map({case (l, r) => Box(l ,r)})
  def diamond[_: P]: P[Formula] = (("<" ~ !P("->"))  ~ program  ~ ">"  ~ prefixTerminal).map({case (l, r) => Diamond(l, r)})

  def prefixTerminal[_: P]: P[Formula] =
    ((verumFalsum | not | forall | exists | box | diamond  | infixTerminal | parenFormula ) ~ ("'".!.?)).
      map({case (f, None) => f case (f, Some(_)) => DifferentialFormula(f)})

  def and[_: P]: P[Formula] = (prefixTerminal ~ ("&"  ~ prefixTerminal).rep).map({case (x, xs) => (xs.+:(x)).reduceRight(And)})
  def or[_: P]: P[Formula] = (and ~ ("|"  ~ and).rep).map({case (x, xs) => (xs.+:(x)).reduceRight(Or)})
  def imply[_: P]: P[Formula] = (or ~ ("->"  ~ or).rep).map({case (x, xs) => (xs.+:(x)).reduceRight(Imply)})
  def equiv[_: P]: P[Formula] = (imply ~ ("<->"  ~ imply).rep).map({case (x, xs) => (xs.+:(x)).reduceRight(Equiv)})

  def formula[_: P]: P[Formula] = equiv
  // Term has to be last because of postfix operators
  def expression[_: P]: P[Expression] =  program | formula | term
}

object ProofParser {
  import ExpressionParser.{formula, program, term, expression, atomicOde}
  import KaisarKeywordParser.proofTerm

  def locate[T <: ASTNode](x:T, i: Int): T = {x.setLocation(i); x}

  def rcf[_: P]: P[RCF] = P("by" ~ ws ~ Index ~ "RCF").map(i => locate(RCF(), i))
  def auto[_: P]: P[Auto] = P("by" ~ ws ~ Index ~ "auto").map(i => locate(Auto(), i))
  def prop[_: P]: P[Prop] = P("by" ~ ws ~ Index ~ "prop").map(i => locate(Prop(), i))
  def solution[_: P]: P[Solution] = P("by" ~ ws ~ Index ~ "solution").map(i => locate(Solution(), i))
  def diffInduction[_: P]: P[DiffInduction] = P("by" ~ ws ~ Index ~ "induction").map(i => locate(DiffInduction(), i))
  def using[_: P]: P[Using] = (Index ~ P("using") ~ selector.rep  ~ rawMethod).
    map({case (i, sels, meth) => locate(Using(sels.toList, meth), i)})
  def byProof[_: P]: P[ByProof] = (Index ~ "proof" ~ proof ~ "end").
    map({case (i, pf) => locate(ByProof(pf), i)})

  def forwardSelector[_: P]: P[ForwardSelector] = proofTerm.map(ForwardSelector)
  def patternSelector[_: P]: P[PatternSelector] =
    (Index ~ P("*")).map(i => locate(PatternSelector(wild), i)) |
    (Index ~ expression).map({case (i, e)  => locate(PatternSelector(e), i)})
  def selector[_: P]: P[Selector] = !reserved ~ (forwardSelector | patternSelector)

  def rawMethod[_: P]: P[Method] = rcf | auto | prop | solution | diffInduction | using | byProof
  // If method has no selectors, then insert the "default" heuristic selection method
  def method[_: P]: P[Method] = rawMethod.map({case u: Using => u case m => Using(List(DefaultSelector), m)})

  def wildPat[_: P]: P[WildPat] = (Index ~  CharIn("_*")).map(i => locate(WildPat(), i))
  def tuplePat[_: P]: P[AsgnPat] = (Index ~ "(" ~ idPat.rep(sep=",") ~ ")").map({case (i, ss) =>
    ss.length match {
      case 0 => locate(NoPat(), i)
      case 1 => ss.head
      case _ => locate(TuplePat(ss.toList), i)
    }})

  //Assumptions in assignments are expressed as ?p:(x := f);
  def varPat[_: P]: P[VarPat] = (Index ~ ident).map({case (i, p) => locate(VarPat(p, None), i)})
  /*def varPat[_: P]: P[VarPat] = (Index ~ ident ~ ("{" ~ variable ~ "}").?).
    map({case (i, p, x) => locate(VarPat(p, x), i)})*/
  def idPat[_: P]: P[AsgnPat] = tuplePat | wildPat | varPat
  def exPat[_: P]: P[Expression] = (expression ~ ":" ~ !P("=")).?.map({case None => Nothing case Some(e) => e})

  def assume[_: P]: P[Statement] = (Index ~ "?" ~  exPat ~ "(" ~ expression ~ ")" ~ ";").map({
    case (i, pat, fml: Formula) => locate(Assume(pat, fml), i)
    case (i, pat: Variable, Assign(x, f)) => locate(Modify(VarPat(x, Some(pat)), Left(f)), i)
    case (i, pat, Assign(x, f)) => locate(Modify(VarPat(x, None), Left(f)), i)
    case (i, pat: Variable, AssignAny(x)) => locate(Modify(VarPat(x, Some(pat)), Right(())), i)
    case (i, pat, AssignAny(x)) => locate(Modify(VarPat(x, None), Right(())), i)
    case (a,b,c) => throw new Exception("Unexpected assumption syntax")
  })

  def assert[_: P]: P[Assert] = (Index ~ "!" ~ exPat  ~ "(" ~ formula ~ ")" ~ method ~ ";").map({
    case (i, pat, fml, method) => locate(Assert(pat, fml, method), i)})

  def modify[_: P]: P[Modify] = (Index ~ idPat ~ ":=" ~ ("*".!.map(Right(_)) | term.map(Left(_))) ~ ";").
    map({case (i, p, Left(f)) => locate(Modify(p, Left(f)), i)
         case (i, p, Right(_)) => locate(Modify(p, Right()), i)})

  def label[_: P]: P[Label] = {
    import NoWhitespace._
    (Index ~ ident ~ ":" ~ !P("=")).map({case (i, id) => locate(Label(id.name), i)})
  }

  def branch[_: P]: P[(Expression, Expression, Statement)] = {
    ("case" ~ exPat ~ formula ~ "=>" ~ statement.rep).map({case (exp: Expression, fml: Formula, ss: Seq[Statement]) =>
      (exp, fml, block(ss.toList))})
  }

  def switch[_: P]: P[Switch] = {
    (Index ~ "switch" ~ CharIn("{(").!).flatMap({
      case (i, "{") => (branch.rep ~ "}").map(branches => locate(Switch(None, branches.toList), i))
      case (i, "(") => (selector ~ ")" ~ "{" ~ branch.rep ~ "}").
        map({case (sel, branches) => locate(Switch(Some(sel), branches.toList), i)})})
  }


  def parseBlock[_: P]: P[Statement] = (Index ~ "{" ~ statement.rep ~ "}").map({case (i, ss) => locate(block(ss.toList), i)})
  def boxLoop[_: P]: P[BoxLoop] = (Index ~ statement.rep ~ "*").map({case (i, ss) => locate(BoxLoop(block(ss.toList)), i)})
  def ghost[_: P]: P[Statement] = (Index ~ "(G" ~ statement.rep ~ "G)").map({case (i, ss) => locate(KaisarProof.ghost(block(ss.toList)), i)})
  def inverseGhost[_: P]: P[Statement] = (Index ~ "{G" ~ statement.rep ~ "G}").map({case (i, ss )=> locate(KaisarProof.inverseGhost(block(ss.toList)), i)})
  def parseWhile[_: P]: P[While] = (Index ~ "while" ~ "(" ~ formula ~ ")" ~ "{" ~ statement.rep ~ "}").
    map({case (i, fml: Formula, ss: Seq[Statement]) => locate(While(Nothing, fml, block(ss.toList)), i)})

  def let[_: P]: P[Statement] = (Index ~ "let" ~ ((ident ~ "(" ~ ident.rep(sep = ",") ~ ")").map(Left(_))
           | term.map(Right(_))
           | ("(" ~ (formula | program) ~ ")").map(Right(_))) // formulas and programs should have parens to deconfuse
    ~ "=" ~ expression ~ ";").
    map({case (i, Left((f, xs)), e) => locate(LetFun(f, xs.toList, e), i) case (i, Right(pat), e) => locate(Match(pat, e), i)})

  def note[_: P]: P[Note] = (Index ~ "note" ~ ident ~ "=" ~ proofTerm ~ ";").map({case (i, id, pt) => locate(Note(id, pt), i)})

  def atomicODEStatement[_: P]: P[AtomicODEStatement] = atomicOde.map(AtomicODEStatement)
  def ghostODE[_: P]: P[DiffStatement] = (Index ~ "(G" ~ diffStatement ~ "G)").
    map({case (i, ds) => locate(DiffGhostStatement(ds), i)})
  def inverseGhostODE[_: P]: P[DiffStatement] = (Index ~ "{G" ~ diffStatement ~ "G}").
    map({case (i, ds) => locate(InverseDiffGhostStatement(ds), i)})
  def terminalODE[_: P]: P[DiffStatement] = ghostODE | inverseGhostODE | atomicODEStatement
  def diffStatement[_: P]: P[DiffStatement] =
    (Index ~ terminalODE.rep(sep = ",", min = 1)).
    map({case (i, dps)=> locate(dps.reduceRight(DiffProductStatement), i)})

  def domAssume[_: P]: P[DomAssume] = (Index ~ exPat ~ formula).map({case (i, id, f) => locate(DomAssume(id, f), i)})
  def domAssert[_: P]: P[DomAssert] = (Index ~ "!" ~ exPat ~ formula ~ method).map({case (i, id, f, m) => locate(DomAssert(id, f, m), i)})
  def domModify[_: P]: P[DomModify] = (Index ~ ExpressionParser.variable ~ ":=" ~ term).map({case (i, id, f) => locate(DomModify(VarPat(id), f), i)})
  def domWeak[_: P]: P[DomWeak] = (Index ~ "{G" ~ domainStatement ~ "G}").map({case (i, ds) => locate(DomWeak(ds), i)})
  def terminalDomainStatement[_: P]: P[DomainStatement] = domAssert | domWeak |  domModify | domAssume
  def domainStatement[_: P]: P[DomainStatement] = (Index ~ terminalDomainStatement.rep(sep = "&", min = 1)).
    map({case (i, da) => locate(da.reduceRight(DomAnd), i)})

  def proveODE[_: P]: P[ProveODE] =
    (Index ~ diffStatement ~ ("&" ~ domainStatement).?.
        map({case Some(v) => v case None => DomAssume(Nothing, True)})
    ).map({case(i, ds, dc) => locate(ProveODE(ds, dc), i)})

  def printGoal[_: P]: P[PrintGoal] = (Index ~ "print" ~ literal ~ ";").
    map({case (i, pg) => locate(PrintGoal(pg), i)})

  def atomicStatement[_: P]: P[Statement] =
    printGoal | note | let | switch | assume | assert | ghost | inverseGhost | parseWhile | parseBlock | label | modify

  def postfixStatement[_: P]: P[Statement] =
    ((atomicStatement | proveODE) ~ Index ~ "*".!.rep).
      map({case (s, i, stars) => locate(stars.foldLeft(s)({case (acc, x) =>
        BoxLoop(acc, Context(acc).lastFact)
      }), i)})

  def sequence[_: P]: P[Statements] =
    postfixStatement.rep(1).map(ss => ss.toList)

  def boxChoice[_: P]: P[Statement] = {
    (Index ~ sequence.rep(sep = "++", min = 1))
      .map({case (i, ss: Seq[List[Statement]]) => locate(block(ss.reduceRight((l, r) => List(BoxChoice(block(l), block(r))))), i)})
  }

  def statement[_: P]: P[Statement] = boxChoice
  def statements[_: P]: P[List[Statement]] = statement.rep.map(ss => flatten(ss.toList))
  def proof[_: P]: P[Statements] = boxChoice.map(ss => List(ss))
}

object KaisarProgramParser {
  def expression[_: P]: P[Expression] = literal.map(KeYmaeraXParser(_))
  def formula[_: P]: P[Formula] = expression.map(_.asInstanceOf[Formula])
  def program[_: P]: P[Program] = expression.map(_.asInstanceOf[Program])
  def differentialProgram[_: P]: P[DifferentialProgram] = expression.map(_.asInstanceOf[DifferentialProgram])
  def term[_: P]: P[Term] = expression.map(_.asInstanceOf[Term])

  private def expectedClass(groups: Msgs, terminals: Msgs): String = {
    val grps = groups.value.map(_.force)
    val trms = terminals.value.map(_.force)
    if (trms.contains("\"print\""))
      return "proof statement"
    "<unknown>"
  }

  def recoverErrorMessage(trace: TracedFailure): String = {
    val expected = expectedClass(trace.groups, trace.terminals)
    val location = trace.input.prettyIndex(trace.index)
    val MAX_LENGTH = 80
    val snippet = trace.input.slice(trace.index, trace.index + MAX_LENGTH).filter(c => !Set('\n', '\r').contains(c))
    s"Expected $expected at ${location}, got:\n$snippet"
  }

  def prettyIndex(index: Int, input: String): (Int, Int) = {
    var lines = (input:StringOps).lines.toList
    var colIndex = index
    var lineIndex = 0
    // @TODO: Could be off by one
    while (lines.nonEmpty && colIndex >= lines.head.length) {
      lineIndex = lineIndex + 1
      colIndex = colIndex - lines.head.length
      lines = lines.tail
    }
    (lineIndex, colIndex)
  }

}
