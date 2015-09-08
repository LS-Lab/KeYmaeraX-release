package parserTests

import edu.cmu.cs.ls.keymaerax.parser._
import org.scalatest.{Matchers, FlatSpec}

/**
 * Created by nfulton on 9/1/15.
 */
class DeclsTests extends FlatSpec with Matchers {
  "Declarations parser" should "parse declarations block correctly." in {
    val input =
      """ProgramVariables.
        |R x.
        |R z.
        |R z_0.
        |End.
      """.stripMargin
    val decls = KeYmaeraXDeclarationsParser(KeYmaeraXLexer.inMode(input, ProblemFileMode()))._1
    decls.keySet.contains("x", None) shouldBe true
    decls.keySet.contains("z", None) shouldBe true
    decls.keySet.contains("z", Some(0)) shouldBe true
    decls.keys.toList.length shouldBe 3
  }

  it should "parse declarations of z, z_0 as two separate declarations" in {
    val input =
      """ProgramVariables.
        |R x.
        |R z.
        |R z_0.
        |R a.
        |End.
        |Problem.
        |x + z + z_0 = z_0 + z + x
        |End.
      """.stripMargin
    KeYmaeraXProblemParser(input)
  }

}
