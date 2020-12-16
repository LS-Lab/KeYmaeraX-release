package edu.cmu.cs.ls.keymaerax.veriphy.experiments

import edu.cmu.cs.ls.keymaerax.cdgl.kaisar._
import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.ProofParser.locate
import edu.cmu.cs.ls.keymaerax.core.{Formula, ODESystem, Variable}
import edu.cmu.cs.ls.keymaerax.parser.DLParser
import fastparse.Parsed.Success
import fastparse._
// allow Scala-style comments and ignore newlines
import ScalaWhitespace._

object StrategyParser {
  def stest[_: P]: P[STest] = (P("STest(") ~ DLParser.formula ~ P(")")).map(STest)
  def sassign[_: P]: P[SAssign] = (P("SAssign(") ~ DLParser.baseVariable ~ "," ~ DLParser.term ~ ")").map({case (x,y) => SAssign((x), y)})
  def sassignAny[_: P]: P[SAssignAny] = (P("SAssignAny(") ~ DLParser.baseVariable ~ ")").map(x => SAssignAny((x)))
  def scompose[_: P]: P[SCompose] = (P("SCompose(") ~ (angelStrategy.rep(min = 1, sep = ",")) ~ ")").map(x => SCompose(x.toList))
  def schoice[_: P]: P[SChoice] = (P("SChoice(") ~ angelStrategy ~ "," ~ angelStrategy ~ ")").map({case (l,r) => SChoice(l,r)})
  def sloop[_: P]: P[SLoop] = (P("SLoop(" ~ angelStrategy ~ ")")).map(SLoop)

  def sode[_: P]: P[SODE] = (P("SODE(") ~ DLParser.odesystem ~ ")").map(dp => SODE(dp))
  def aloop[_: P]: P[ALoop] = (P("ALoop(") ~ DLParser.formula ~ "," ~ angelStrategy ~ ")").map({case (x,y) => ALoop(x, y)})
  def aswitch[_: P]: P[ASwitch] = (P("ASwitch(") ~ branch.rep(sep = ",") ~ ")").map(brs => ASwitch(brs.toList))
  def aode[_: P]: P[AODE] = (P("AODE(") ~ DLParser.odesystem ~ "," ~ DLParser.term ~ ")").map({case (x,y) => AODE(x,y)})

  def branch[_: P]: P[(Formula, AngelStrategy)] = "(" ~ DLParser.formula ~ "," ~ angelStrategy ~ ")"

  def angelStrategy[_: P]: P[AngelStrategy] = stest | sassign | sassignAny | scompose | schoice | sloop | sode | aloop | aswitch | aode

  def apply(str: String): AngelStrategy = {
    fastparse.parse(str, angelStrategy(_)) match {
      case Parsed.Success(value, _) => value
      case f: Parsed.Failure => throw new Exception(f.msg)
    }
  }
}
