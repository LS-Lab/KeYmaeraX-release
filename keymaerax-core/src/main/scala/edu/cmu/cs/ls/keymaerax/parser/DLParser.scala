/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
/**
  * Differential Dynamic Logic parser for concrete KeYmaera X notation.
  * @author Andre Platzer
  * @see Andre Platzer. [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 59(2), pp. 219-266, 2017.
  */
package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.core._


import fastparse._, MultiLineWhitespace._


/**
  * Differential Dynamic Logic parser reads input strings in the concrete syntax of differential dynamic logic of KeYmaera X.
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
  * @see [[http://keymaeraX.org/doc/dL-grammar.md Grammar]]
  * @see [[https://github.com/LS-Lab/KeYmaeraX-release/wiki/KeYmaera-X-Syntax-and-Informal-Semantics Wiki]]
  */
class DLParser extends Parser {
  /** Parse the input string in the concrete syntax as a differential dynamic logic expression
    *
    * @param input the string to parse as a dL formula, dL term, or dL program.
    * @ensures apply(printer(\result)) == \result
    * @throws ParseException if `input` is not a well-formed expression of differential dynamic logic or differential game logic.
    */
  override def apply(input: String): Expression = exprParser(input)

  val exprParser: String => Expression = (s => parse(s, fullExpression(_)) match {
    case Parsed.Success(value, index) => value
    case f@Parsed.Failure(str, i, extra) => throw ParseException(f.trace().longMsg + "\nin: " + f.extra.input, UnknownLocation)
  })

  /** Parse the input string in the concrete syntax as a differential dynamic logic term */
  override val termParser: String => Term = (s => parse(s, fullTerm(_)) match {
    case Parsed.Success(value, index) => value
    case f@Parsed.Failure(str, i, extra) => throw ParseException(f.trace().longMsg + "\nin: " + f.extra.input, UnknownLocation)
  })
  /** Parse the input string in the concrete syntax as a differential dynamic logic formula */
  override val formulaParser: String => Formula = (s => parse(s, fullFormula(_)) match {
    case Parsed.Success(value, index) => value
    case f@Parsed.Failure(str, i, extra) => throw ParseException(f.trace().longMsg + "\nin: " + f.extra.input, UnknownLocation)
  })
  /** Parse the input string in the concrete syntax as a differential dynamic logic program */
  override val programParser: String => Program = (s => parse(s, fullProgram(_)) match {
    case Parsed.Success(value, index) => value
    case f@Parsed.Failure(str, i, extra) => throw ParseException(f.trace().longMsg + "\nin: " + f.extra.input, UnknownLocation)
  })
  /** Parse the input string in the concrete syntax as a differential dynamic logic differential program */
  override val differentialProgramParser: String => DifferentialProgram = (s => parse(s, fullDifferentialProgram(_)) match {
    case Parsed.Success(value, index) => value
    case f@Parsed.Failure(str, i, extra) => throw ParseException(f.trace().longMsg + "\nin: " + f.extra.input, UnknownLocation)
  })


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
  def setAnnotationListener(listener: (Program,Formula) => Unit): Unit =
  //@todo
    {}

  //*****************
  // implementation
  //*****************

  def fullTerm[_: P]: P[Term]   = P( term ~ End )
  def fullFormula[_: P]: P[Formula]   = P( formula ~ End )
  def fullProgram[_: P]: P[Program]   = P( program ~ End )
  def fullDifferentialProgram[_: P]: P[DifferentialProgram]   = P( diffProgram ~ End )

  def fullExpression[_: P]: P[Expression] = P( (NoCut(formula) | NoCut(term) | program) ~ End )


  //*****************
  // base parsers
  //*****************

  def number[_: P]: P[Number] = {
    import NoWhitespace._
    P(/*"-".!.? ~*/ CharIn("0-9").rep(1) ~ ("." ~ CharIn("0-9").rep(1)).?).!.
      map(s => Number(BigDecimal(s)))
  }
  def ident[_: P]: P[(String,Option[Int])] = {
    import NoWhitespace._
    P( (CharIn("a-zA-Z") ~ CharIn("a-zA-Z0-9").rep).! ~
      ("_" ~ ("0" | CharIn("1-9") ~ CharIn("0-9").rep).!.map(_.toInt)).?)
  }
  def baseVariable[_: P]: P[BaseVariable] = ident.map(s => Variable(s._1,s._2,Real))
  def diffVariable[_: P]: P[DifferentialSymbol] = P(baseVariable ~ "'").map(DifferentialSymbol(_))
  def variable[_: P]: P[Variable] = P(diffVariable | baseVariable)


  //*****************
  // term parser
  //*****************

  def func[_: P]: P[FuncOf] = P(ident ~ termList).map({case (s,idx,ts) => FuncOf(Function(s,idx,ts.sort,Real), ts)})
  def parenT[_: P]: P[Term] = P( "(" ~/ term ~ ")" )
  def differential[_: P]: P[Term] = P( parenT ~ "'".!.?).
    map({case (t,None) => t case (t,Some("'")) => Differential(t)})
  def baseT[_: P]: P[Term] = P( NoCut(func) | variable | (number ~ "'").map(Differential) | number | differential )

  //*****************
  // term parser
  //*****************

  /** `-p`: negative occurrences of what is parsed by parser `p`. */
  def neg[_: P](p: => P[Term]): P[Term] = P(("-" ~ !(">")) ~/ p).map(t => Neg(t))
  /** `p | -p`: possibly signed occurrences of what is parsed by parser `p`, so to `p` or `-p`. */
  def signed[_: P](p: => P[Term]): P[Term] = P(("-".! ~ !(">")).? ~ p).map({case (Some("-"),t) => Neg(t) case (None,t) =>t})

  def factor[_: P]: P[Term] = P( baseT ~ ("^" ~/ (baseT | neg(factor))).rep ).
    map({case (t,ts) => (ts.+:(t)).reduceRight(Power)})

  def summand[_: P]: P[Term] = P( factor ~ (CharIn("*/").! ~/ (factor | neg(summand))).rep ).
    map({case (t,ts) => ts.foldLeft(t)({case (l,("*",r)) => Times(l,r) case (l,("/",r)) => Divide(l,r)})})

  def term[_: P]: P[Term] = P( signed(summand) ~ (("+" | ("-" ~ !(">"))).! ~/ signed(summand)).rep ).
    map({case (t,ts) => ts.foldLeft(t)({case (l,("+",r)) => Plus(l,r)  case (l,("-",r)) => Minus(l,r)})})
  /**
    * {{{
    *     T ::= T+S | T-S | -S | S
    *     S ::= S*F | S*-F | S/F | S/-F | F
    *     F ::= P^F | P^-F | P
    *     P ::= x | x' | num | f(T,...,T) | (T)' | (T)
    * }}}
    */


  def termList[_: P]: P[Term] = P("(" ~ (term ~ ("," ~/ term).rep).? ~ ")").
    map({case Some((t,ts)) => (ts.+:(t)).reduceRight(Pair) case None => Nothing})


  //*****************
  // formula parser
  //*****************

  def pred[_: P]: P[PredOf] = P(ident ~ termList ~ (!CharIn("+\\-*/^!=><") | &("->" | "<-"))).
    map({case (s,idx,ts) => PredOf(Function(s,idx,ts.sort,Bool), ts)})
  def trueFalse[_: P]: P[Formula] = P("true".! | "false".!).map({case "true" => True case "false" => False})
  def comparison[_: P]: P[Formula] = P( term ~ ("=" | ">=" | "<=" | ">" | "<" | "!=").! ~/ term ).
    map({case (l,"=",r) => Equal(l,r) case (l,">=",r) => GreaterEqual(l,r) case (l,"<=",r) => LessEqual(l,r)
    case (l,">",r) => Greater(l,r) case (l,"<",r) => Less(l,r) case (l,"!=",r) => NotEqual(l,r)})
  def parenF[_: P]: P[Formula] = P( "(" ~/ formula ~ ")" )
  def differentialF[_: P]: P[Formula] = P( parenF ~ "'".!.?).
    map({case (f,None) => f case (f,Some("'")) => DifferentialFormula(f)})
  //@todo allow PredicationalOf | UnitPred
  def baseF[_: P]: P[Formula] = P( trueFalse | NoCut(pred) | NoCut(comparison) | differentialF )

  def not[_: P]: P[Formula] = P("!" ~/ conjunct ).map(f => Not(f))
  def modal[_: P]: P[Formula] = P( (("[".! ~/ program ~/ "]".!) | ("<".! ~/ program ~/ ">".!)) ~/ conjunct ).
    map({case ("[",p,"]", f) => Box(p, f)
         case ("<",p,">", f) => Diamond(p, f)})
  //@todo block quantifier \\forall x,y,z Q
  def quantified[_: P]: P[Formula] = P( ("\\forall"|"\\exists").! ~/ variable ~/ conjunct ).
    map({case ("\\forall",x, f) => Forall(x::Nil, f)
         case ("\\exists",x, f) => Exists(x::Nil, f)})
  def conjunct[_: P]: P[Formula] = P( not | quantified | modal | baseF)


  def disjunct[_: P]: P[Formula] = P( conjunct ~ ("&" ~/ conjunct).rep ).
    map({case (f,fs) => (fs.+:(f)).reduceRight(And)})

  def implicand[_: P]: P[Formula] = P( disjunct ~ ("|" ~/ disjunct).rep ).
    map({case (f,fs) => (fs.+:(f)).reduceRight(Or)})

  def implication[_: P]: P[Formula] = P( implicand ~ ("->" ~/ implicand).rep ).
    map({case (f,fs) => (fs.+:(f)).reduceRight(Imply)})

  def backimplication[_: P]: P[Formula] = P( implicand ~ ("<-" ~/ implicand).rep(1) ).
    map({case (f,fs) => (fs.+:(f)).reduceLeft((l,r)=>Imply(r,l))})

  def implicational[_: P]: P[Formula] = P(NoCut(backimplication) | implication)

  def formula[_: P]: P[Formula] = P( implicational ~ ("<->" ~/ implicational).? ).
    map({case (l,None) => l case (l,Some(r)) => Equiv(l,r)})


  //*****************
  // program parser
  //*****************

  def programSymbol[_: P]: P[AtomicProgram] = P( ident  ~ ";").
    map({case (s,None) => ProgramConst(s) case (s,Some(i)) => ???})

  def assign[_: P]: P[Assign] = P( variable ~ ":=" ~/ term ~ ";").map({case (x,t) => Assign(x,t)})
  def assignany[_: P]: P[AssignAny] = P( variable ~ ":=" ~ "*" ~ ";").map({case x => AssignAny(x)})
  def test[_: P]: P[Test] = P( "?" ~/ formula ~ ";").map(f => Test(f))
  def braceP[_: P]: P[Program] = P( "{" ~ program ~ "}" )
  //@todo add @invariant
  def odesys[_: P]: P[Program] = P( "{" ~ diffProgram ~ ("&" ~/ formula).? ~ "}" ).
    map({case (p,None) => ODESystem(p,True) case (p,Some(f)) => ODESystem(p,f)})
  def baseP[_: P]: P[Program] = P(( programSymbol | NoCut(assign) | assignany | test | NoCut(repeat) |
    NoCut(odesys) | NoCut(braceP) |
    ifthen) ~ "^@".!.?).map({case (p,None) => p case (p,Some("^@")) => Dual(p)})

  //@todo add @invariant
  def repeat[_: P]: P[Program] = P( braceP ~ "*".! ).
    map({case (p,"*") => Loop(p)})

  def sequence[_: P]: P[Program] = P( baseP.rep(1) ).
    map(ps => ps.reduceRight(Compose))

  def choice[_: P]: P[Program] = P( sequence ~ ("++" ~/ sequence).rep ).
    map({case (p, ps) => (ps.+:(p)).reduceRight(Choice)})

  //@note macro-expands
  def ifthen[_: P]: P[Program] = P( "if" ~/ parenF ~ braceP ~ ("else" ~/ braceP).? ).
    map({case (f, p, None) => Choice(Compose(Test(f),p), Test(Not(f)))
         case (f, p, Some(q)) => Choice(Compose(Test(f),p), Compose(Test(Not(f)),q))})

  def program[_: P]: P[Program] = P( choice )


  //*****************
  // differential program parser
  //*****************

  def ode[_: P]: P[AtomicODE] = P( diffVariable ~/ "=" ~/ term).map({case (x,t) => AtomicODE(x,t)})
  def diffProgramSymbol[_: P]: P[DifferentialProgramConst] = P( ident ).
    map({case (s,None) => DifferentialProgramConst(s) case (s,Some(i)) => ???})
  def atomicDP[_: P]: P[AtomicDifferentialProgram] = P( ode | diffProgramSymbol )


  def diffProduct[_: P]: P[DifferentialProgram] = P( atomicDP ~ ("," ~/ atomicDP).rep ).
    map({case (p, ps) => (ps.+:(p)).reduceRight(DifferentialProduct.apply)})

  def diffProgram[_: P]: P[DifferentialProgram] = P( diffProduct )

}

object DLParser extends DLParser