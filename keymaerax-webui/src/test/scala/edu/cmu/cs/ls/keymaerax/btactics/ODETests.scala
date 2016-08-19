package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core._
import testHelper.KeYmaeraXTestTags.IgnoreInBuildTest

import scala.collection.immutable._
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXPrettyPrinter, KeYmaeraXProblemParser}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.{SummaryTest, UsualTest}
import edu.cmu.cs.ls.keymaerax.tools.ToolException
import testHelper.CustomAssertions._
import testHelper.KeYmaeraXTestTags

import scala.collection.immutable.IndexedSeq

/**
 * Tests automatic
 * [[edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary.ODE]] differential equations proving.
 */
@UsualTest
class ODETests extends TacticTestBase {
  "Auto ODE" should "prove x^2>5 -> [{x'=x^3+x^4}]x^2>5" in withMathematica { qeTool =>
    proveBy("x^2>5 -> [{x'=x^3+x^4}]x^2>5".asFormula, implyR(1) & ODE(1))
  }

  //@note: there's overlap as multiple methods are able to prove some of the following examples
  val list =
  // solvable cases
    "x>=0&v=1 -> [{x'=v}]x>=0" ::
      "x>=0&v=1&a=2 -> [{x'=v,v'=a}]x>=0" ::
      "x>0&v=1 -> [{x'=v}]x>0" ::
      "x>0&v=1&a=2 -> [{x'=v,v'=a}]x>0" ::
      "x>0&v=1&a=2 -> [{x'=v,v'=a&v>=0}](x>0&v>=0)" ::
      "x>1&v=10&a=-2 -> [{x'=v,v'=a&v>=0}](x>1&v>=0)" ::
      "x>=1&v=10&a=-2 -> [{x'=v,v'=a&v>=0}](x>=1&v>=0)" ::
      // open cases
      "x^2>5 -> [{x'=x^3}]x^2>5" ::
      "x^2<5 -> [{x'=x^3}]x^2<5" ::
      "x^2>5 -> [{x'=x^4}]x^2>5" ::
      "x^2<5 -> [{x'=x^4}]x^2<5" ::
      "x^2>5 -> [{x'=x^3+x^4}]x^2>5" ::
      "x^2<5 -> [{x'=x^3+x^4}]x^2<5" ::
      // split open cases
      "x^3>5 & y^4>2 -> [{x'=x^3+x^4,y'=5*y+y^2}](x^3>5&y^4>2)" ::
      // split cases
      "x>=1&y=10&a=-2 -> [{x'=y,y'=a+y^2-y&y>=0}](x>=1&y>=0)" ::
      // auto-ghost
      "x>0->[{x'=-x}]x>0" ::
      "x>0->[{x'=x}]x>0" ::
      "x>0->[{x'=-x+1}]x>0" ::
      "x>0&a<0&b>=0->[{x'=a*x+b}]x>0" ::
      "x>0&a>0&b>=0->[{x'=a*x+b}]x>0" ::
  // conserved quantity
      "x1^4*x2^2+x1^2*x2^4-3*x1^2*x2^2+1 <= c -> [{x1'=2*x1^4*x2+4*x1^2*x2^3-6*x1^2*x2, x2'=-4*x1^3*x2^2-2*x1*x2^4+6*x1*x2^2}] x1^4*x2^2+x1^2*x2^4-3*x1^2*x2^2+1 <= c" ::
      Nil


  it should "prove a list of ODEs" in withMathematica {implicit qeTool =>
    var fail: List[String] = Nil
    for (ex <- list) {
      val fml = ex.asFormula
      println("\nProving\n" + fml)
      val proof = TactixLibrary.proveBy(fml, implyR(1) & ODE(1))
      if (proof.isProved)
        println("\nProved: " + fml)
      else {
        println(proof)
        println("\nFailed: " + fml)
        fail = fail :+ ex
      }
    }
    if (fail.isEmpty)
      println("All examples proved successfully")
    else {
      println("\n\nFailures: " + fail.mkString("\n"))
      fail shouldBe 'empty
    }
  }
}
