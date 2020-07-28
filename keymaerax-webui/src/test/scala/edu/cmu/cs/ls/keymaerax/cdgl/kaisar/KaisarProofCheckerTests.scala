package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import fastparse.Parsed.{Failure, Success}
import fastparse._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase
import edu.cmu.cs.ls.keymaerax.pt.ProofChecker.ProofCheckException

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

  it should "check fancy assignments" in {
    // @TODO: Tests for shadowing / admissibility / etc, what do
    val pfStr = "x := *; x := x^2; "
    val pf = p(pfStr, pp.statement(_))
    val (ss, ff) = ProofChecker(Context.empty, pf)
    //ff shouldBe "[x:=*; y:=x^2;]true".asFormula
  }

  it should "compose assertions" in withMathematica { _ =>
    val pfStr = "x := *; y := x^2; !p:(y >= 0) := by auto;"
    val pf = p(pfStr, pp.statement(_))
    val (ss, ff) = ProofChecker(Context.empty, pf)
    ff shouldBe "[x:=*; y:=x^2; {?y>=0;}^@]true".asFormula
  }

  it should "compose assumption" in {
    val pfStr = "x := *; ?p:(x^2 = y & x >= 0);"
    val pf = p(pfStr, pp.statement(_))
    val (ss, ff) = ProofChecker(Context.empty, pf)
    ff shouldBe "[x:=*; ?(x^2 = y & x >= 0);]true".asFormula
  }

  it should "check box loop" in withMathematica { _ =>
    val pfStr = "?xZero:(x >= 1); {{x := x + 1; !IS:(x >= 1) := by auto;}*} ?xFin:(x>=0);"
    val pf = p(pfStr, pp.statement(_))
    val (ss, ff) = ProofChecker(Context.empty, pf)
    ff shouldBe "[?(x>=1); {x:=x+1;{?(x>=1);}^@}*;?(x>=0);]true".asFormula
  }

  it should "reject invalid auto step" in withMathematica { _ =>
    val pfStr  = "!falsehood:(1 <= 0) := by auto;"
    val pf = p(pfStr, pp.statement(_))
    a[ProofCheckException] shouldBe (thrownBy(ProofChecker(Context.empty, pf)))
    //ff shouldBe "1>=0".asFormula
  }

  it should "succeed switch" in withMathematica { _ =>
    val pfStr = "switch { case xNeg:(x <= 1) => !x: true := by auto; case xPos:(x >= 0) => !x: true := by auto;}"
    val pf = p(pfStr, pp.statement(_))
    val (ss, ff) = ProofChecker(Context.empty, pf)
    ff shouldBe "[{{?(x<=1); {?(true);}^@}^@ ++ {?(x>=0); {?(true);}^@}^@}^@]true".asFormula
  }

  it should "fail bad switch" in withMathematica { _ =>
    val pfStr = "switch { case xOne:(x >= 1) => !x: true := by auto; case xNeg:(x < 0) => !x: true := by auto;}"
    val pf = p(pfStr, pp.statement(_))
    a[ProofCheckException] shouldBe (thrownBy(ProofChecker(Context.empty, pf)))
  }

  it should "support paramaterized switch" in withMathematica { _ =>
    val pfStr = "?eitherOr: (x >= 1 | x < 0 | x = 1); switch (eitherOr) { case xOne:(x >= 1) => !x: true := by auto; case xNeg:(x < 0) => !x: true := by auto; case x =1 => !x: true := by auto;}"
    val pf = p(pfStr, pp.statement(_))
    val (ss, ff) = ProofChecker(Context.empty, pf)
    ff shouldBe "[?(x>=1|x<0|x=1);{{?(x>=1); {?(true);}^@}^@ ++ {?(x<0); {?(true);}^@}^@ ++{?(x=1); {?(true);}^@}^@}^@]true".asFormula
  }

  it should "reject mismatched case" in withMathematica { _ =>
    val pfStr = "?eitherOr: (x >= 1 | x < 0); switch (eitherOr) { case xOne:(x >= 1) => !x: true := by auto; case xNeg:(x < 0) => !x: true := by auto; case x =1 => !x: true := by auto;}"
    val pf = p(pfStr, pp.statement(_))
    a[ProofCheckException] shouldBe (thrownBy(ProofChecker(Context.empty, pf)))
  }

  it should "support note" in withMathematica { _ =>
    val pfStr = "?l:(x = 1); ?r:(y = 0); note lr = andI l r ;"
    val pf = p(pfStr, pp.statement(_))
    val (ss, ff) = ProofChecker(Context.empty, pf)
    ff shouldBe "[?x=1;?y=0;{?(x=1&y=0);}^@]true".asFormula
  }

  it should "check admissibility and SSA" in withMathematica { _ =>
    val pfStr = "x:=x+1;"
    val pf = p(pfStr, pp.statement(_))
    a[ProofCheckException] shouldBe (thrownBy(ProofChecker(Context.empty, pf)))
  }

  it should "ban ghost program variable escaping scope" in withMathematica { _ =>
    val pfStr = "x:=1; (G y:= 2; G) !p:(x + y = 3) := by auto;"
    val pf = p(pfStr, pp.statement(_))
    a[ProofCheckException] shouldBe (thrownBy(ProofChecker(Context.empty, pf)))
  }

  it should "ban inverse ghost proof variable escaping scope" in withMathematica { _ =>
    val pfStr = "{G ?p:(x = 0); G} !q:(x = 0) := using p by auto;"
    val pf = p(pfStr, pp.statement(_))
    a[ProofCheckException] shouldBe (thrownBy(ProofChecker(Context.empty, pf)))
  }

  it should "allow ghost proof variable escaping scope" in withMathematica { _ =>
    val pfStr = "x{xVal}:=1; (G y:= 2; !p:(x + y = 3) := using andI xVal y by auto; !q:(x > 0) := using andI p y by auto; G) !p:(x + 1 > 0) := using q by auto;"
    val pf = p(pfStr, pp.statement(_))
    val (ss, ff) = ProofChecker(Context.empty, pf)
    ff shouldBe "[x:=1;{?(x+1>0);}^@]true".asFormula
  }

  it should "allow inverse ghost program variable escaping scope for tautological purposes" in withMathematica { _ =>
    val pfStr = "{G x := 0; G} !q:(x^2 >= 0) := by auto;"
    val pf = p(pfStr, pp.statement(_))
    val (ss, ff) = ProofChecker(Context.empty, pf)
    ff shouldBe "[{?(x^2 >= 0);}^@]true".asFormula
  }

}
