package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import fastparse.Parsed._
import fastparse._

class SSAPassTests extends TacticTestBase {
  import KaisarProof._
  val pc = ParserCommon
  val ep = ExpressionParser
  val pp = ProofParser
  val kp = KaisarKeywordParser

  class KPPTestException(msg: String) extends Exception (msg)

  def p[T](s: String, parser: P[_] => P[T]): T =
    parse(s, parser) match {
      case x: Success[T] => x.value
      case x: Failure => throw new KPPTestException(x.trace().toString)
    }

  def pssa(s: String): Statement = SSAPass(p(s, pp.statement(_)))
  def checkSSA(s: String): (Statement, Formula) = {
    val (con, fml) = ProofChecker(Context.empty, pssa(s))
    (con.s, fml)
  }

  "SSA pass" should "transform assignment" in {
    val pfStr = "x:=x+1;"
    pssa(pfStr) shouldBe Modify(VarPat(Variable("x", Some(0)), None), Left(Plus(Variable("x"), Number(1))))
  }

  it should "check fancy assignments" in {
    val pfStr = "x := *; x := x^2; "
    val (ss, ff) = checkSSA(pfStr)
    ff shouldBe "[x_0:=*; x_1:=x_0^2;]true".asFormula
  }


}
