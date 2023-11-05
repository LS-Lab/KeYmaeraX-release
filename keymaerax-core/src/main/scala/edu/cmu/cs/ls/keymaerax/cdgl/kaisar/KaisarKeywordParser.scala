/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
/**
  * Parse Kaisar proofs
  * @author Brandon Bohrer
  */
package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.KaisarProof._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXParser
import fastparse.MultiLineWhitespace.whitespace
import fastparse._

object KaisarKeywordParser {
  val reservedWords: Set[String] = Set("by", "RCF", "auto", "prop", "end", "proof", "using", "let", "match", "print", "for")
  // "ghost", "solve", "induct", "domain", "duration", "left", "right", "yield", "or", "assert", "assume", "have", "either", "cases",

  def identString[$: P]: P[String] = {
    // Because (most of) the parser uses multiline whitespace, rep will allow space between repetitions.
    // Thus shadow implicit whitespace definition provided by class scope
    implicit val whitespace: Whitespace = NoWhitespace.noWhitespaceImplicit

    (CharIn("a-zA-Z") ~ CharIn("a-zA-Z1-9").rep ~ P("'").?).!.filter(s  => !reservedWords.contains(s))
  }
  def reserved[$: P]: P[String]  = CharIn("a-zA-Z").rep(1).!.filter(reservedWords.contains)
  def ws[$: P]: P[Unit] = P((" " | "\n").rep)
  def wsNonempty[$: P]: P[Unit] = P((" " | "\n").rep(1))
  def literal[$: P]: P[String] = "\"" ~ CharPred(c => c != '\"').rep(1).! ~ "\""

  def variable[$: P]: P[Variable] = identString.map(Variable(_))
  def ident[$: P]: P[Ident] = identString.map(Variable(_))
  def expression[$: P]: P[Expression] = literal.map(KeYmaeraXParser(_))
  def formula[$: P]: P[Formula] = expression.map(_.asInstanceOf[Formula])
  def program[$: P]: P[Program] = expression.map(_.asInstanceOf[Program])
  def differentialProgram[$: P]: P[DifferentialProgram] = expression.map(_.asInstanceOf[DifferentialProgram])
  def term[$: P]: P[Term] = expression.map(_.asInstanceOf[Term])

  // @TODO: Need syntax to separate proof terms, or elaborator pass to resolve ambiguous parse.
  // For example     (A B), C   vs   ((A B) C)
  //def proofParen[$: P]: P[ProofTerm] = "(" ~  proofTerm  ~ ")"
  //def proofTerminal[$: P]: P[ProofTerm] = !reserved ~ (proofInstance | proofVar | proofParen)
  //(proofTerminal.rep(1, ws)).map(pts => pts.reduceLeft[ProofTerm]({case (acc, pt) => ProofApp(acc, pt)}))
  def proofInstance[$: P]: P[ProofInstance] = expression.map(e => ProofInstance(e))
  def proofVarApp[$: P]: P[ProofTerm] = (ident ~ ("(" ~ proofTerm.rep(sep =",") ~ ")").?).map({
    case (id, None) => ProofVar(id)
    case (id, Some(args)) => args.foldLeft[ProofTerm](ProofVar(id))({case (acc, pt) => ProofApp(acc, pt)})
  })
  //@TODO: add support for distinct ProofVar terms
  def proofTerm[$: P]: P[ProofTerm] = !reserved ~ (proofInstance | proofVarApp)

  def forwardSelector[$: P]: P[ForwardSelector] = proofTerm.map(ForwardSelector)
  def patternSelector[$: P]: P[PatternSelector] = (P("*").map(_ => PatternSelector(wild)) | term.map(PatternSelector))

  def selector[$: P]: P[Selector] = !reserved ~ (forwardSelector | patternSelector)

  def rcf[$: P]: P[RCF] = P("by" ~ ws ~ "RCF").map(_ => RCF())
  def auto[$: P]: P[Auto] = P("by" ~ ws ~ "auto").map(_ => Auto())
  def prop[$: P]: P[Prop] = P("by" ~ ws ~ "prop").map(_ => Prop())
  def using[$: P]: P[Using] = (P("using") ~ ws ~ selector.rep ~ ws ~ method).map({case (sels, meth) => Using(sels.toList, meth)})
  def byProof[$: P]: P[ByProof] = ("proof" ~ ws ~ proof ~ ws ~ "end").map(ByProof)

  def method[$: P]: P[Method] = rcf | auto | prop | using | byProof
  def modify[$: P]: P[Modify] = (ident ~ ws ~ ":=" ~ ws ~ term).map({case (x: Ident, f: Term) => Modify(Nil, List((x, Some(f))))})
  def bassignAny[$: P]: P[Modify] = ((ident ~ ws ~ ":=" ~ ws ~ "*").map({case (x: Ident) => Modify(Nil, List((x, None)))}))
  def assert[$: P]: P[Assert] = ("assert" ~ ws ~ ident ~ ws ~ ":" ~ ws ~ formula ~ ws ~  method).map({case (ident, formula, method) => Assert(ident, formula, method)})
  def assume[$: P]: P[Assume] = ("assume" ~ ws ~ ident ~ ws ~ ":" ~ ws ~ formula).map({case (ident, formula) => Assume(ident, formula)})
  def label[$: P]: P[Label] = (identString ~ ":").map(c => Label(LabelDef(c)))
  def parseMatch[$: P]: P[Match] = ("match" ~ ws ~ term ~ ws ~ "=" ~ ws ~ expression).map({case (e1, e2) => Match(e1, e2)})
  def letFun[$: P]: P[LetSym] = ("let" ~ ws ~ ident ~ "(" ~ ident.rep(sep=",") ~ ")" ~ ws ~ "=" ~ ws ~ expression).map({case (f, xs, e) => LetSym(f, xs.toList, e)})
  def note[$: P]: P[Note] = ("note" ~ ws ~ ident ~ ws ~ "=" ~ ws ~ proofTerm).map({case (id, pt) => Note(id, pt)})
  def parseBlock[$: P]: P[Statement] = ("{" ~ ws ~ statement.rep(2) ~ ws ~ "}").map(ss => block(ss.toList))
  def boxChoice[$: P]: P[BoxChoice] = ("either" ~ ws ~ statement.rep ~ ws ~ "or" ~ ws ~ statement.rep ~ ws ~ "end").
    map({case (ls, rs) => BoxChoice(block(ls.toList), block(rs.toList))})
  //@TODO update
  def branch[$: P]: P[(Term, Formula, Statement)] = (formula ~ ws ~ "=>" ~ ws ~ parseBlock).map({case (e, blk) => (Nothing, e, blk)})
  def patternMatch[$: P]: P[Switch] = ("cases" ~ ws ~ branch.rep ~ ws ~ "end").map(_.toList).map(Switch(None, _))
  def printGoal[$: P]: P[PrintGoal] = ("print" ~ ws ~ literal).map(s => PrintGoal(PrintString(s)))
  def ghost[$: P]: P[Ghost] = ("ghost"~ ws ~ ident ~ ws ~ "=" ~ ws ~ term).map({case (x, f) => Ghost(Modify(Nil, List((x, Some(f)))))})
  def bsolve[$: P]: P[Statement] = (("solve" ~ ws ~ differentialProgram ~ ws ~
    "domain" ~ ws ~ ident ~ ws ~ ":" ~ ws ~ formula ~ ws ~
    "duration" ~ ws ~ ident)).map({case (dp, vdc, dcFml, vdur) =>
    // @TODO
    Block(List())
  })

  //def induct[$: P]: P[Invariant] = ("induct" ~ ws ~ ident ~ ws ~ ":" ~ ws ~ formula ~ ws ~ proof ~ ws ~ "end")
  //  .map({case (x, f, pf) => Invariant(x, f, pf)})
  //def diamondLeft[$: P]: P[DiamondLeft] = (("left" ~ ws ~ block)).map(blk => DiamondLeft(blk.ss))
  //def diamondRight[$: P]: P[DiamondRight] = (("right" ~ ws ~ block)).map(blk => DiamondRight(blk.ss))
  //def dassignAny[$: P]: P[DAssignAny] = ((variable ~ ws ~ "<-" ~ ws ~ term).map({case (x, f) => DAssignAny(x, f)}))
  //def have[$: P]: P[Have] = ("have" ~ ws ~ ident ~ ws ~ ":" ~ ws ~ formula ~ ws ~ method).map({case (id, f, m) => Have(id, f, m)})
  //def show[$: P]: P[Show] = ("show" ~ ws ~ formula ~ ws ~ method).map({case (f, m) => Show(f, m)})

  /*def bsolve[$: P]: P[BSolve] = (("solve" ~ ws ~ differentialProgram ~ ws ~
    "domain" ~ ws ~ ident ~ ws ~ ":" ~ ws ~ formula ~ ws ~
    "duration" ~ ws ~ ident)).map({case (dp, vdc, dcFml, vdur) => BSolve(dp, vdc, dcFml, vdur)})*/

  /*def dsolve[$: P]: P[DSolve] = (("solve" ~ ws ~ differentialProgram ~ ws ~
    "domain" ~ ws ~ ident ~ ws ~ "=" ~ ws ~ proof ~ ws ~
    "duration" ~ ws ~ ident ~ ws ~ "=" ~ proof).map({case (ode, vdc, dcProof, vdur, durProof) =>
    DSolve(ode, vdc, dcProof, vdur, durProof)}))*/

  //def parseYield[$: P]: P[Yield] = P("yield").map(_ => Yield())

  //@TODO: Handle ident1 != ident2
  def parseFor[$: P]: P[Statement] =
    ("for" ~ ws ~ ident ~ ws ~ "=" ~ ws ~ term ~ ws ~ ";" ~ ws ~ ident  ~ ws ~ ":" ~ ws ~ formula ~ ws ~ ";" ~ ws ~ ident ~ ws ~ "-=" ~ ws ~ term)
      .map({case (ident1, f0, vj, j, ident2, f2) =>
        //@TODO
        Block(List())})


  def statement[$: P]: P[Statement] = ws ~ (modify | assert | assume  | label | parseMatch
    | letFun | note | parseBlock | boxChoice  | patternMatch  | printGoal
    | ghost| bassignAny  | bsolve  | parseFor) ~ ws

  def proof[$: P]: P[Statements] = statement.rep.map({ss: Seq[Statement] => ss.toList})
}

class KaisarKeywordParser {

}
