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
import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.KaisarProof.Ident
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXParser, Parser}

object KaisarParser {
  val reservedWords: Set[String] = Set("by", "RCF", "auto", "prop", "end", "proof", "using", "assert", "assume", "have")
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
  def assert[_: P]: P[Assert] = ("assert" ~ ws ~ ident ~ ws ~ ":" ~ ws ~ formula ~ ws ~ /*"=" ~ ws ~*/ method).map({case (ident, formula, method) => Assert(ident, formula, method)})
  def assume[_: P]: P[Assume] = ("assume" ~ ws ~ ident ~ ws ~ ":" ~ ws ~ formula).map({case (ident, formula) => Assume(ident, formula)})
  def have[_: P]: P[Have] = ("have" ~ ws ~ ident ~ ws ~ ":" ~ ws ~ formula ~ ws ~ method).map({case (id, f, m) => Have(id, f, m)})
  def statement[_: P]: P[Statement] = ws ~ (modify.map(Step) | assert.map(Step) | assume.map(Step) | have) ~ ws
  def proof[_: P]: P[Proof] = statement.rep.map({ss: Seq[Statement] => Proof(ss.toList)})


}

class KaisarParser {

  /*
def kwHave[_: P]: P[Unit] = P("have")
def kwShow[_: P]: P[Unit] = P("show")
def kwNote[_: P]: P[Unit] = P("note")
def kwLet[_: P]: P[Unit] = P("let")
def kwSolve[_: P]: P[Unit] = P("solve")
def kwAssume[_: P]: P[Unit] = P("assume")
def kwAssert[_: P]: P[Unit] = P("assert")
def kwCase[_: P]: P[Unit] = P("case")
def kwEnd[_: P]: P[Unit] = P("end")
def kwRepeat[_: P]: P[Unit] = P("repeat")
def kwFor[_: P]: P[Unit] = P("for")
def kwYield[_: P]: P[Unit] = P("yield")*/

}
