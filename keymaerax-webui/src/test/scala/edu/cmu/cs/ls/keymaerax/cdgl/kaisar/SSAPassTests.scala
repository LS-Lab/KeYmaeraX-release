/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.KaisarTest
import fastparse.Parsed._
import fastparse._

@KaisarTest
class SSAPassTests extends TacticTestBase {
  val pc = ParserCommon
  val ep = ExpressionParser
  val pp = ProofParser
  val kp = KaisarKeywordParser

  class KPPTestException(msg: String) extends Exception(msg)

  def p[T](s: String, parser: P[_] => P[T]): T = parse(s, parser) match {
    case x: Success[T] => x.value
    case x: Failure => throw new KPPTestException(x.trace().toString)
  }

  def pssa(s: String): Statement = SSAPass(p(s, pp.statement(_)))
  def checkSSA(s: String): (Statement, Formula) = {
    val (con, fml) = ProofChecker(Context.empty, pssa(s))
    (con.s, fml)
  }

  "SSA for hybrid programs" should "have expected output on examples from refinement tests" in {
    val in = "y:=0;x:=0;{?x>=0;}^@{x:=x+1;{?x>=0;}^@}*{?x>=y;}^@".asProgram
    val out = "y_1:=0;x_1:=0;{?x_1>=0;}^@ {x_2:=x_1;{{x_3:=x_2+1;{?x_3>=0;}^@ x_2 := x_3;}}*}{?x_2>=y_1;}^@".asProgram
    SSAPass(in) shouldBe out
  }

  "SSA pass for statements" should "transform assignment" in {
    val pfStr = "x:=x+1;"
    pssa(pfStr) shouldBe Modify(Nil, List((Variable("x", Some(1)), Some(Plus(Variable("x", Some(0)), Number(1))))))
  }

  it should "check fancy assignments" in {
    val pfStr = "x := *; x := x^2; "
    val (ss, ff) = checkSSA(pfStr)
    ff shouldBe "[x_1:=*; x_2:=x_1^2;]true".asFormula
  }

}
