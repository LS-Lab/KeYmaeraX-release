/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/

package edu.cmu.cs.ls.keymaerax.bellerophon.parser

import edu.cmu.cs.ls.keymaerax.bellerophon.{AppliedPositionTactic, Find, Fixed, LazySequentialInterpreter, PartialTactic, ReflectiveExpressionBuilder, SeqTactic, Using}
import edu.cmu.cs.ls.keymaerax.btactics.{DebuggingTactics, TactixInit, TactixLibrary}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.{PosInExpr, SuccPosition}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter.StringToStringConverter
import edu.cmu.cs.ls.keymaerax.parser.{Declaration, ParseException, Parser}
import edu.cmu.cs.ls.keymaerax.tools.KeYmaeraXTool
import edu.cmu.cs.ls.keymaerax.{Configuration, FileConfiguration}
import org.scalamock.scalatest.MockFactory
import org.scalatest.{BeforeAndAfterAll, BeforeAndAfterEach, FlatSpec, Matchers}
import testHelper.KeYmaeraXTestTags.TodoTest

/**
  * Tests the DLBelleParser.
  * @author James Gallicchio
  */
class DLBelleParserTests extends FlatSpec with Matchers with BeforeAndAfterEach with BeforeAndAfterAll with MockFactory {

  override def beforeAll(): Unit = {
    Configuration.setConfiguration(FileConfiguration)
    KeYmaeraXTool.init(Map(
      KeYmaeraXTool.INIT_DERIVATION_INFO_REGISTRY -> "true",
      KeYmaeraXTool.INTERPRETER -> LazySequentialInterpreter.getClass.getSimpleName
    ))
    parser = new DLBelleParser(BellePrettyPrinter, ReflectiveExpressionBuilder(_, _, Some(TactixInit.invSupplier), _))
  }
  override def afterEach(): Unit = { Parser.parser.setAnnotationListener((_, _) => {}) }

  private var parser: DLBelleParser = _
  private def parse(input: String) = parser.belleParser(input)

  "DLBelleParser" should "parse postfix \"using\"" in {
    parse(raw"""QE using "x^2+y^2=init :: init=0 :: x=0&y=0 :: nil"""".stripMargin) shouldBe Using(List("x^2+y^2=init".asFormula, "init=0".asFormula, "x=0&y=0".asFormula), TactixLibrary.QE)
    parse(raw"""implyR(1); QE using "x^2+y^2=init :: init=0 :: x=0&y=0 :: nil"""".stripMargin) shouldBe
      SeqTactic(List(TactixLibrary.implyR(1), Using(List("x^2+y^2=init".asFormula, "init=0".asFormula, "x=0&y=0".asFormula), TactixLibrary.QE)))
  }

  it should "parse implications correctly" in {
    parse("""implyR('R=="assumptions(x,y,v,xo,yo)->true")""") shouldBe
      TactixLibrary.implyR(Find.FindRPlain("assumptions(x,y,v,xo,yo)->true".asFormula))
  }

  it should "parse useLemma" in {
    val parsed = parse(
      raw"""useLemma("Khalil Exercise 2.28 and 3.14 (bound)", "prop")
           |""".stripMargin
    )
    //TODO: shouldBes
  }

  it should "parse integer position locators" in {
    parse("""hideL(-3=="x>=0")""") should have ('locator (Fixed(AntePos(2), Some("x>=0".asFormula))))
    parse("""hideR(2~="x>=0")""") should have ('locator (Fixed(SuccPos(1), Some("x>=0".asFormula), exact=false)))
    parse("""trueAnd(2.1.1=="true&x=2")""") should have ('locator
      (Fixed(SuccPosition.base0(1, PosInExpr(1::1::Nil)), Some("true&x=2".asFormula), exact=true)))
    parse("""trueAnd(2~="[x:=2;]#(true&x=2)#")""") should have ('locator
      (Fixed(SuccPosition.base0(1, PosInExpr(1::Nil)), Some("true&x=2".asFormula), exact=false)))
    parse("""trueAnd(2.1=="[x:=2;]#(true&x=2)#")""") should have ('locator
      (Fixed(SuccPosition.base0(1, PosInExpr(1::Nil)), Some("true&x=2".asFormula), exact=true)))
    the [ParseException] thrownBy parse("""trueAnd(2.1.1=="[x:=2;]#(true&x=2)#")""") should have message
      """1:37 Error parsing locator at 1:9
        |Found:    ")" at 1:37
        |Expected: Non-conflicting sub-positions (but .1.1 != .1)
        |Hint: Try Non-conflicting sub-positions (but .1.1 != .1)""".stripMargin
  }

  it should "parse tactic argument list syntax" in {
    val parsed = parse(
      raw"""hideFactsAbout("kA1::kB1::nil")
           |""".stripMargin
    )
    //TODO: shouldBes
  }

  it should "parse tactic argument list syntax and position locators" in {
    val parsed = parse(
      raw"""stabilityStateMLF("4331*x1^2/1000000+x1*x2/200000+87*x2^2/200000::217*x1^2/500000-x1*x2/200000+2161*x2^2/500000::nil", 'R=="\forall eps (eps>0->\exists del (del>0&\forall x1 \forall x2 (x1^2+x2^2 < del^2->[{{x1'=-x1+10*x2,x2'=(-100)*x1-x2&x1+x2>=0}++{x1'=-x1+100*x2,x2'=(-10)*x1-x2&x1+x2<=0}}*]x1^2+x2^2 < eps^2)))")
           |""".stripMargin
    )
    //TODO: shouldBes
  }

  it should "FEATURE_REQUST: parse PosInExpr attached to locator" taggedAs TodoTest in {
    val parsed = parse(
      raw"""derive('Rlast.1)
           |""".stripMargin
    )
    //TODO: shouldBes
  }

  it should "parse hash locators" in {
    val t = parse("""trueAnd('R=="[x:=1;]#true&x=1#")""").asInstanceOf[AppliedPositionTactic]
    t.locator shouldBe Find.FindR(0, Some("[x:=1;](true&x=1)".asFormula), PosInExpr(1::Nil), exact=true, defs=Declaration(Map.empty))
  }

  it should "parse suffix partial" in {
    parse("""implyR(1) partial""") shouldBe PartialTactic(TactixLibrary.implyR(1))
    parse("""QE using "x>=0::nil" partial""") shouldBe PartialTactic(Using(List("x>=0".asFormula), TactixLibrary.QE))
    parse("""implyR(1); andL(-1) partial""") shouldBe SeqTactic(List(TactixLibrary.implyR(1), PartialTactic(TactixLibrary.andL(-1))))
  }

  it should "parse substitutions" in {
    parse("""US("J(.) ~> .>=0")""") shouldBe TactixLibrary.USX(
      List(SubstitutionPair(PredOf(Function("J", None, Real, Bool), DotTerm()), GreaterEqual(DotTerm(), Number(0)))))
  }

  it should "parse dC" in {
    parse("""dC("x>=0 :: y=1 :: nil", 1)""") shouldBe TactixLibrary.dC(List("x>=0".asFormula, "y=1".asFormula))(1)
    parse("""dC("x>=0 :: nil", 1)""") shouldBe TactixLibrary.dC(List("x>=0".asFormula))(1)
    parse("""dC("x>=0", 1)""") shouldBe TactixLibrary.dC(List("x>=0".asFormula))(1)
  }

  it should "parse strings" in {
    parse("""print("Test")""") shouldBe DebuggingTactics.printX("Test")
  }

}
