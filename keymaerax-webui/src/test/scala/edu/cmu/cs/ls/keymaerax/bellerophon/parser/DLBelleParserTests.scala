/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/

package edu.cmu.cs.ls.keymaerax.bellerophon.parser

import edu.cmu.cs.ls.keymaerax.bellerophon.{AppliedPositionTactic, Find, LazySequentialInterpreter, ReflectiveExpressionBuilder}
import edu.cmu.cs.ls.keymaerax.btactics.TactixInit
import edu.cmu.cs.ls.keymaerax.infrastruct.PosInExpr
import edu.cmu.cs.ls.keymaerax.parser.StringConverter.StringToStringConverter
import edu.cmu.cs.ls.keymaerax.parser.{Declaration, Parser}
import edu.cmu.cs.ls.keymaerax.tools.KeYmaeraXTool
import edu.cmu.cs.ls.keymaerax.{Configuration, FileConfiguration}
import org.scalamock.scalatest.MockFactory
import org.scalatest.{BeforeAndAfterAll, BeforeAndAfterEach, FlatSpec, Matchers}

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

  private var parser: DLBelleParser = null
  private def parse(input: String) = parser.belleParser(input)

  "DLBelleParser" should "parse postfix \"using\"" in {
    val parsed = parse(
      raw"""QE using "x^2+y^2=init :: init=0 :: x=0&y=0 :: nil"
           |""".stripMargin
    )
    //TODO: shouldBes
  }

  it should "parse implications correctly" in {
    val parsed = parse(
      raw"""implyR('R=="assumptions(x,y,v,xo,yo)->true")
           |""".stripMargin
    )
  }

  it should "parse useLemma" in {
    val parsed = parse(
      raw"""useLemma("Khalil Exercise 2.28 and 3.14 (bound)", "prop")
           |""".stripMargin
    )
    //TODO: shouldBes
  }

  it should "parse integer position locators" in {
    val parsed = parse(
      raw"""hideL(-3=="\forall x1 \forall x2 (x1*x1+x2*x2=eps*eps->x1^2/2+x2^4/4>=k)")
           |""".stripMargin
    )
    //TODO: shouldBes
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

  it should "parse PosInExpr attached to locator" in {
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

}
