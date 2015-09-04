/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/

import edu.cmu.cs.ls.keymaerax.tactics.{PosInExpr, Context, Position}
import edu.cmu.cs.ls.keymaerax.tools.KeYmaera

import scala.collection.immutable._
import edu.cmu.cs.ls.keymaerax.tactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser._
import org.scalatest.{PrivateMethodTester, Matchers, FlatSpec}

import test.RandomFormula

/**
 * Tests the context splitting on randomly generated formulas
 * @author Andre Platzer
 */
class RandomContextTests extends FlatSpec with Matchers {
  KeYmaera.init(Map.empty)
  val randomTrials = 40000
  val randomComplexity = 6
  val rand = new RandomFormula()


  def contextShouldBe[T<:Formula](origin: T, pos: PosInExpr): Boolean = {
    val (ctx,e) = try { origin.at(pos) } catch {case e: IllegalArgumentException => println("\nInput:      " + origin +
      "\nIllposition: " + pos); (Context(DotFormula), origin)}
      println("\n" +
        "\nInput:      " + origin +
        "\nPosition:   " + pos +
        "\nContext:    " + ctx +
        "\nArgument:   " + e +
        "\nReassemble: " + (if (e.isInstanceOf[Program]) "<program>" else ctx(e)) +
        "\nExpected:  " + origin)
    if (!e.isInstanceOf[Program] && !programCtx(ctx)) ctx(e) shouldBe origin
    true
  }

  private def programCtx(r:Context[Expression]): Boolean =
     StaticSemantics.signature(r.ctx).contains(noContext) || StaticSemantics.signature(r.ctx).contains(noContextD)

  //@todo DotProgram would in a sense be the appropriate context
  private val noContext = ProgramConst("noctx")
  private val noContextD = DifferentialProgramConst("noctxD")


  "The positioning" should "consistently split formulas" in {
    for (i <- 1 to randomTrials) {
      val f = rand.nextFormula(randomComplexity)
      val pos = rand.nextPosition(randomComplexity).inExpr
      try {
        contextShouldBe(f, pos)
      } catch {
        case e: SubstitutionClashException => println("Clashes can happen when reassembling ill-defined:\n" + e)
      }
      //@todo could reshuffle pos if location didn't work.
    }
  }

}
