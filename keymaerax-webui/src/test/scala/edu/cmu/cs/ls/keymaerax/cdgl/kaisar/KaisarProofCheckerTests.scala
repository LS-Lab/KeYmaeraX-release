package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import fastparse.Parsed.{Failure, Success}
import fastparse._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase

class KaisarProofCheckerTests extends TacticTestBase {
  import KaisarProof._
  val pc = ParserCommon
  val ep = ExpressionParser
  val pp = ProofParser
  val kp = KaisarKeywordParser

  //  class KPPTestException(msg: String) extends Exception (msg)

  def p[T](s: String, parser: P[_] => P[T]): T =
    parse(s, parser) match {
      case x: Success[T] => x.value
      case x: Failure => throw new Exception(x.trace().toString)
    }

  "Proof checker" should "check assignments" in {
    val pfStr = "x:=1; ++ x:=2; ++ x:=3;"
    val pf = p(pfStr, pp.statement(_))
    val (ss, ff) = ProofChecker(Context.empty, pf)
    ff shouldBe "[x:=1; ++ x:=2; ++ x:=3;]true".asFormula
  }

  it should "check compositions" in {
    val pfStr = "x := *; y := x^2;"
    val pf = p(pfStr, pp.statement(_))
    val (ss, ff) = ProofChecker(Context.empty, pf)
    ff shouldBe "[x:=*; y:=x^2;]true".asFormula
  }

  it should "compose assertions" in {
    val pfStr = "x := *; y := x^2; !p:(y >= 0) := by auto;"
    val pf = p(pfStr, pp.statement(_))
    val (ss, ff) = ProofChecker(Context.empty, pf)
    ff shouldBe "[x:=*; y:=x^2; {?y>=0;}^@]true".asFormula
  }
}
