/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
/**
  * Bellerophon tactic parser for Differential Dynamic Logic.
  * @author Andre Platzer
  * @see Andre Platzer. [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 59(2), pp. 219-266, 2017.
  */
package edu.cmu.cs.ls.keymaerax.bellerophon.parser

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.{DLAxiomParser, DLParser}
import fastparse._
import MultiLineWhitespace._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary
import edu.cmu.cs.ls.keymaerax.infrastruct.Position

import scala.collection.immutable._

/**
  * Bellerophon tactic parser for Differential Dynamic Logic reads input strings in the concrete syntax of Bellerophon tactics for KeYmaera X.
  * @author Andre Platzer
  */
object DLBelleParser extends DLBelleParser {
}

/**
  * Bellerophon tactic parser for Differential Dynamic Logic reads input strings in the concrete syntax of Bellerophon tactics for KeYmaera X.
  * @author Andre Platzer
  */
class DLBelleParser {

  /** Which formula/term/program parser this archive parser uses. */
  val expParser = DLParser

  def position[_: P]: P[Position] = P( integer ~~ ("." ~~/ natural).repX ).map({case (j,js) => Position(j, js.toList)})
  def locator[_: P]: P[PositionLocator] = P( position ).map(pos => Fixed(pos))

  //@todo parse proper tactic by name instead of nilT
  def tacticSymbol[_: P]: P[BelleExpr] = ident.map(s => TactixLibrary.nil)
  def at[_: P]: P[AppliedPositionTactic] = P(tacticSymbol ~~ "(" ~ (string ~ ",").? ~ locator ~ ")").
    map({case (t,None,j) => t.asInstanceOf[PositionalTactic](j)
      case (t,Some(arg),j) => throw new Exception("Not implemented yet passing formula etc arguments")})
  def parenTac[_: P]: P[BelleExpr] = P( "(" ~ tactic ~ ")" )
  def baseTac[_: P]: P[BelleExpr] = P( NoCut(at) | tacticSymbol |
    branchTac | NoCut(repeatTac) | parenTac
  )

  def branchTac[_: P]: P[BelleExpr] = P( "<" ~/ "(" ~ baseTac.rep(min=1,sep=","./) ~ ")").
    map(BranchTactic)

  def repeatTac[_: P]: P[BelleExpr] = P(
    (parenTac ~ "*" ~ integer).map(pn=>RepeatTactic(pn._1,pn._2))
    | (parenTac ~ "*" ~ !CharIn("0-9")).map(SaturateTactic)
  )

  def seqTac[_: P]: P[BelleExpr] = P( baseTac.rep(min=1,sep=";"./) ).
    map(ts => ts.reduceRight(SeqTactic))

  def eitherTac[_: P]: P[BelleExpr] = P( seqTac.rep(min=1,sep="|"./) ).
    map(ts => ts.reduceRight(EitherTactic))

//  //@note macro-expands
//  def ifthen[_: P]: P[BelleExpr] = P( "if" ~/ parenF ~ braceP ~ ("else" ~/ braceP).? ).
//    map({case (f, p, None) => Choice(Compose(Test(f),p), Test(Not(f)))
//    case (f, p, Some(q)) => Choice(Compose(Test(f),p), Compose(Test(Not(f)),q))})


  /** tactic: Parses a dL Bellerophon tactic. */
  def tactic[_: P]: P[BelleExpr] = P( eitherTac )


  // externals
  //@todo or just import if no dynamic forwarding needed

  /** Explicit nonempty whitespace terminal from [[expParser]]. */
  def blank[_:P]: P[Unit] = expParser.blank

  /** parse a number literal from [[expParser]] */
  def number[_: P]: P[Number] = expParser.number
  /** parse an identifier from [[expParser]] */
  def ident[_: P]: P[(String,Option[Int])] = expParser.ident
  def string[_: P]: P[String] = expParser.string
  def integer[_: P]: P[Int] = expParser.integer
  def natural[_: P]: P[Int] = expParser.natural

  def baseVariable[_: P]: P[BaseVariable] = expParser.baseVariable

  /** term: Parses a dL term from [[expParser]]. */
  def term[_: P]: P[Term] = expParser.term

  /** formula: Parses a dL formula from [[expParser]]. */
  def formula[_: P]: P[Formula] = expParser.formula

  /** program: Parses a dL program from [[expParser]]. */
  def program[_: P]: P[Program] = expParser.program

}
