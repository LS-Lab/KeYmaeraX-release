package edu.cmu.cs.ls.keymaerax.cdgl.kaisar


//import edu.cmu.cs.ls.keymaerax.cdgl.kaisar._
import ProofParser.locate
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct._
import edu.cmu.cs.ls.keymaerax.parser.DLParser
import fastparse.Parsed.Success
import fastparse._
// allow Scala-style comments and ignore newlines
import ScalaWhitespace._

object StrategyParser {
  private def alloc[T <: AngelStrategy](maybe: Option[Int], as: T): T = {
    val theId =
      maybe match {
        case Some(id) =>
          IDCounter.set(id, as); id
        case None => IDCounter.next(as)
      }
    as.nodeID = theId
    as
  }

  def maybeId[_: P]: P[Option[Int]] = ((P("[") ~ DLParser.integer ~ P("]")).? ~ "(")

  def stest[_: P]: P[STest] = (P("STest") ~ maybeId ~ DLParser.formula ~ P(")")).map({ case (id, fml) => alloc(id, STest(fml)) })

  def sassign[_: P]: P[SAssign] = (P("SAssign") ~ maybeId ~ DLParser.variable ~ "," ~ DLParser.term(true) ~ ")").map({ case (id, x, y) => alloc(id, SAssign((x), y)) })

  def sassignAny[_: P]: P[SAssignAny] = (P("SAssignAny") ~ maybeId ~ DLParser.variable ~ ")").map({ case (id, x) => alloc(id, SAssignAny((x))) })

  def scompose[_: P]: P[SCompose] = (P("SCompose") ~ maybeId ~ (angelStrategy.rep(min = 1, sep = ",")) ~ ")").map({ case (id, x) => alloc(id, SCompose(x.toList)) })

  def schoice[_: P]: P[SChoice] = (P("SChoice") ~ maybeId ~ angelStrategy ~ "," ~ angelStrategy ~ ")").map({ case (id, l, r) => alloc(id, SChoice(l, r)) })

  def sloop[_: P]: P[SLoop] = (P("SLoop" ~ maybeId ~ angelStrategy ~ ")")).map({ case (id, body) => alloc(id, SLoop(body)) })

  def sode[_: P]: P[SODE] = (P("SODE") ~ maybeId ~ DLParser.odesystem ~ ")").map({ case (id, dp) => alloc(id, SODE(dp)) })

  def aloop[_: P]: P[ALoop] = (P("ALoop") ~ maybeId ~ DLParser.formula ~ "," ~ angelStrategy ~ ")").map({ case (id, x, y) => alloc(id, ALoop(x, y)) })

  def aforloop[_: P]: P[AForLoop] =
    (P("AForLoop") ~ maybeId ~ DLParser.variable ~ "," ~ DLParser.term(true) ~ "," ~ DLParser.formula ~ "," ~ angelStrategy ~ "," ~ DLParser.term(true) ~ ("," ~ DLParser.term(true)).?).map({
      case (id, idx, idx0, conv, body, idxup, delta) => alloc(id, AForLoop(idx, idx0, conv, body, idxup, delta))
    })

  def aswitch[_: P]: P[ASwitch] = (P("ASwitch") ~ maybeId ~ branch.rep(sep = ",") ~ ")").map({ case (id, brs) => alloc(id, ASwitch(brs.toList)) })

  def aode[_: P]: P[AODE] = (P("AODE") ~ maybeId ~ DLParser.odesystem ~ "," ~ DLParser.term(true) ~ ")").map({ case (id, x, y) => alloc(id, AODE(x, y)) })

  def branch[_: P]: P[(Formula, AngelStrategy)] = "(" ~ DLParser.formula ~ "," ~ angelStrategy ~ ")"

  def angelStrategy[_: P]: P[AngelStrategy] = stest | sassign | sassignAny | scompose | schoice | sloop | sode | aforloop | aloop | aswitch | aode

  def apply(str: String): AngelStrategy = {
    fastparse.parse(str, angelStrategy(_)) match {
      case Parsed.Success(value, _) => value
      case f: Parsed.Failure => throw new Exception(f.msg)
    }
  }
}