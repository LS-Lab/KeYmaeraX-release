/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
/**
  * Parse Kaisar proofs
  * @author Brandon Bohrer
  */
package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import fastparse._
import NoWhitespace._
import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.KaisarProof._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXParser, Parser}

object KaisarKeywordParser {
  val reservedWords: Set[String] = Set("by", "RCF", "auto", "prop", "end", "proof", "using", "assert", "assume", "have",
  "ghost", "solve", "induct", "domain", "duration", "left", "right", "yield", "let", "match", "either", "cases",
    "or", "print", "for")
  def identString[_: P]: P[String] = CharIn("a-zA-Z").rep(1).!.filter(!reservedWords.contains(_))
  def reserved[_: P]: P[String]  = CharIn("a-zA-Z").rep(1).!.filter(reservedWords.contains)
  def ws[_ : P]: P[Unit] = P((" " | "\n").rep)
  def wsNonempty[_ : P]: P[Unit] = P((" " | "\n").rep(1))
  def literal[_: P]: P[String] = "\"" ~ CharPred(c => c != '\"').rep(1).! ~ "\""

  def variable[_ : P]: P[Variable] = identString.map(Variable(_))
  def ident[_: P]: P[Ident] = identString
  def expression[_: P]: P[Expression] = literal.map(KeYmaeraXParser(_))
  def formula[_: P]: P[Formula] = expression.map(_.asInstanceOf[Formula])
  def program[_: P]: P[Program] = expression.map(_.asInstanceOf[Program])
  def differentialProgram[_: P]: P[DifferentialProgram] = expression.map(_.asInstanceOf[DifferentialProgram])
  def term[_: P]: P[Term] = expression.map(_.asInstanceOf[Term])

  def proofVar[_: P]: P[ProofVar] = ident.map(ProofVar)
  def proofApp[_: P]: P[ProofApp] = (proofTerm ~ wsNonempty ~ proofTerm).map({case (left, right) => ProofApp(left, right)})
  def proofInst[_: P]: P[ProofInst] = ((proofTerm ~ wsNonempty ~ term).map({case (left, right) => ProofInst(left, right)}))
  def proofParen[_: P]: P[ProofTerm] = "(" ~ ws ~ proofTerm ~ ws ~ ")"
  def proofTerm[_: P]: P[ProofTerm] = ws ~ !reserved ~ (proofVar  | proofParen | proofInst | proofApp)


  def forwardSelector[_: P]: P[ForwardSelector] = proofTerm.map(ForwardSelector)
  def patternSelector[_: P]: P[PatternSelector] = expression.map(PatternSelector)

  def selector[_: P]: P[Selector] = !reserved ~ (forwardSelector | patternSelector)

  def rcf[_: P]: P[RCF] = P("by" ~ ws ~ "RCF").map(_ => RCF())
  def auto[_: P]: P[Auto] = P("by" ~ ws ~ "auto").map(_ => Auto())
  def prop[_: P]: P[Prop] = P("by" ~ ws ~ "prop").map(_ => Prop())
  def using[_: P]: P[Using] = (P("using") ~ ws ~ selector.rep ~ ws ~ method).map({case (sels, meth) => Using(sels.toList, meth)})
  def byProof[_: P]: P[ByProof] = ("proof" ~ ws ~ proof ~ ws ~ "end").map(ByProof)

  def method[_: P]: P[Method] = rcf | auto | prop | using | byProof
  def modify[_: P]: P[Modify] = (variable ~ ws ~ ":=" ~ ws ~ term).map({case (x: Variable, f: Term) => Modify(Assign(x, f))})
  def bassignAny[_: P]: P[BAssignAny] = ((variable ~ ws ~ ":=" ~ ws ~ "*").map(BAssignAny))
  def dassignAny[_: P]: P[DAssignAny] = ((variable ~ ws ~ "<-" ~ ws ~ term).map({case (x, f) => DAssignAny(x, f)}))
  def assert[_: P]: P[Assert] = ("assert" ~ ws ~ ident ~ ws ~ ":" ~ ws ~ formula ~ ws ~ /*"=" ~ ws ~*/ method).map({case (ident, formula, method) => Assert(ident, formula, method)})
  def assume[_: P]: P[Assume] = ("assume" ~ ws ~ ident ~ ws ~ ":" ~ ws ~ formula).map({case (ident, formula) => Assume(ident, formula)})
  def have[_: P]: P[Have] = ("have" ~ ws ~ ident ~ ws ~ ":" ~ ws ~ formula ~ ws ~ method).map({case (id, f, m) => Have(id, f, m)})
  def show[_: P]: P[Show] = ("show" ~ ws ~ formula ~ ws ~ method).map({case (f, m) => Show(f, m)})
  def label[_: P]: P[Label] = (identString ~ ":").map(Label)
  def parseMatch[_: P]: P[Match] = ("match" ~ ws ~ expression ~ ws ~ "=" ~ ws ~ expression).map({case (e1, e2) => Match(e1, e2)})
  def letFun[_: P]: P[LetFun] = ("let" ~ ws ~ ident ~ "(" ~ ident ~ ")" ~ ws ~ "=" ~ ws ~ expression).map({case (f, x, e) => LetFun(f, x, e)})
  def note[_: P]: P[Note] = ("note" ~ ws ~ ident ~ ws ~ "=" ~ ws ~ proofTerm).map({case (id, pt) => Note(id, pt)})
  def block[_: P]: P[Block] = ("{" ~ ws ~ statement.rep(2) ~ ws ~ "}").map(ss => Block(ss.toList))
  def boxChoice[_: P]: P[BoxChoice] = ("either" ~ ws ~ statement.rep ~ ws ~ "or" ~ ws ~ statement.rep ~ ws ~ "end").map({case (ls, rs) => BoxChoice(ls.toList, rs.toList)})
  def diamondLeft[_: P]: P[DiamondLeft] = (("left" ~ ws ~ block)).map(blk => DiamondLeft(blk.ss))
  def diamondRight[_: P]: P[DiamondRight] = (("right" ~ ws ~ block)).map(blk => DiamondRight(blk.ss))
  def branch[_: P]: P[(Expression, List[Statement])] = (expression ~ ws ~ "=>" ~ ws ~ block).map({case (e, blk) => (e, blk.ss)})
  def patternMatch[_: P]: P[PatternMatch] = ("cases" ~ ws ~ branch.rep ~ ws ~ "end").map(_.toList).map(PatternMatch)
  def printGoal[_: P]: P[PrintGoal] = ("print" ~ ws ~ literal).map(PrintGoal)
  def induct[_: P]: P[Invariant] = ("induct" ~ ws ~ ident ~ ws ~ ":" ~ ws ~ formula ~ ws ~ proof ~ ws ~ "end")
    .map({case (x, f, pf) => Invariant(x, f, pf)})
  def ghost[_: P]: P[Ghost] = ("ghost"~ ws ~ variable ~ ws ~ "=" ~ ws ~ term).map({case (x, f) => Ghost(Assign(x,f))})
  def bsolve[_: P]: P[BSolve] = (("solve" ~ ws ~ differentialProgram ~ ws ~
    "domain" ~ ws ~ ident ~ ws ~ ":" ~ ws ~ formula ~ ws ~
    "duration" ~ ws ~ ident)).map({case (dp, vdc, dcFml, vdur) => BSolve(dp, vdc, dcFml, vdur)})

  /*def bsolve[_: P]: P[BSolve] = (("solve" ~ ws ~ differentialProgram ~ ws ~
    "domain" ~ ws ~ ident ~ ws ~ ":" ~ ws ~ formula ~ ws ~
    "duration" ~ ws ~ ident)).map({case (dp, vdc, dcFml, vdur) => BSolve(dp, vdc, dcFml, vdur)})*/

  def dsolve[_: P]: P[DSolve] = (("solve" ~ ws ~ differentialProgram ~ ws ~
    "domain" ~ ws ~ ident ~ ws ~ "=" ~ ws ~ proof ~ ws ~
    "duration" ~ ws ~ ident ~ ws ~ "=" ~ proof).map({case (ode, vdc, dcProof, vdur, durProof) =>
    DSolve(ode, vdc, dcProof, vdur, durProof)}))

  def parseYield[_: P]: P[Yield] = P("yield").map(_ => Yield())

  //@TODO: Handle ident1 != ident2
  def parseFor[_: P]: P[For] =
    ("for" ~ ws ~ ident ~ ws ~ "=" ~ ws ~ term ~ ws ~ ";" ~ ws ~ ident  ~ ws ~ ":" ~ ws ~ formula ~ ws ~ ";" ~ ws ~ ident ~ ws ~ "-=" ~ ws ~ term)
      .map({case (ident1, f0, vj, j, ident2, f2) => For(vj, j, ident2, f0, f2)})


  def statement[_: P]: P[Statement] = ws ~ (modify | assert | assume | have | label | show | parseMatch
    | letFun | note | block | boxChoice | diamondLeft | diamondRight | patternMatch  | printGoal
    | induct | ghost| bassignAny | dassignAny | dsolve | bsolve | parseYield | parseFor) ~ ws

  def proof[_: P]: P[Proof] = statement.rep.map({ss: Seq[Statement] => Proof(ss.toList)})
}

class KaisarKeywordParser {

}
