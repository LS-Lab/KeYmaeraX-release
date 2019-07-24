package tools

import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tools.OrbitalAlgebraTool

/** Tests for OrbitalAlgebraTool
  */
class OrbitalAlgebraToolTests extends TacticTestBase  {

  "OrbitalAlgebraTool" should "compute groebner basis" in withMathematica { _ =>
    val x = "1+x*y^2+1+y^2+x*y+(x+y+3)^(2-1)".asTerm
    val y = "y+x*z*a+(a*b+1/3)^2".asTerm
    val tool = new OrbitalAlgebraTool()

    tool.groebnerBasis(List(x,y,Variable("z"))) shouldBe List("z", "5+y+y^2+x+x*y+x*y^2", "1/9+y+2/3*a*b+a^2*b^2").map(_.asTerm)
  }

  it should "compute polynomial remainder" in withMathematica { _ =>
    val x = "x^(2-1)+x+(x+y)^2+1/2".asTerm
    val y = "x+3+y".asTerm
    val tool = new OrbitalAlgebraTool()

    println(tool.polynomialReduce(x,List(y)))
  }

}
