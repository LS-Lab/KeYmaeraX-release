/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

import edu.cmu.cs.ls.keymaerax.{Configuration, FileConfiguration}
import edu.cmu.cs.ls.keymaerax.bellerophon.LazySequentialInterpreter
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.RandomFormula
import edu.cmu.cs.ls.keymaerax.tools.KeYmaeraXTool
import testHelper.KeYmaeraXTestTags.{CheckinTest, SlowTest, SummaryTest, UsualTest}

import scala.collection.immutable._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.{Context, PosInExpr}
import org.scalatest.{BeforeAndAfterAll, FlatSpec, Matchers}

/**
 * Tests the context splitting on randomly generated formulas
 * @author
 *   Andre Platzer
 */
class RandomContextTests extends FlatSpec with Matchers with BeforeAndAfterAll {
  private val randomTrials = 400
  private val randomReps = 10
  private val randomComplexity = 6
  private val rand = new RandomFormula()

  override def beforeAll(): Unit = {
    Configuration.setConfiguration(FileConfiguration)
    KeYmaeraXTool.init(Map(
      KeYmaeraXTool.INIT_DERIVATION_INFO_REGISTRY -> "false",
      KeYmaeraXTool.INTERPRETER -> LazySequentialInterpreter.getClass.getSimpleName,
    ))
  }

  override def afterAll(): Unit = { KeYmaeraXTool.shutdown() }

  private def contextShouldBe[T <: Formula](origin: T, pos: PosInExpr): Boolean = {
    if (
      pos != PosInExpr.HereP && pos.pos.last == 0 &&
      (origin.sub(pos.parent) match {
        // exempt those positions where DotTerm() makes no sense since restricted to variables
        case Some(Assign(_, _)) => true
        // case Some(DiffAssign(_,_)) => true
        case Some(AssignAny(_)) => true
        case Some(AtomicODE(_, _)) => true
        case None => true
        case Some(_) => false
      })
    ) return true
    val (ctx, e) =
      try { origin.at(pos) }
      catch {
        case _: IllegalArgumentException =>
          println("\nInput:      " + origin + "\nIllposition: " + pos); (Context(DotFormula), origin)
        case _: SubstitutionClashException =>
          println("\nInput:      " + origin + "\nIllposition: " + pos); (Context(DotFormula), origin)
      }
    println("\n" + "\nInput:      " + origin + "\nPosition:   " + pos + "\nContext:    " + ctx + "\nArgument:   " + e)
    val reassemble =
      try { Some(ctx(e)) }
      catch {
        case e: SubstitutionClashException => println("Clashes can happen when reassembling ill-defined:\n" + e); None
      }
    println("\nReassemble: " + reassemble.getOrElse(Variable("undefined")) + "\nExpected:  " + origin)
    if (reassemble.isDefined && e != Nothing && !noCtx(ctx)) reassemble.get shouldBe origin
    true
  }

  private def noCtx(r: Context[Expression]): Boolean = StaticSemantics.signature(r.ctx).contains(noContext) ||
    StaticSemantics.signature(r.ctx).contains(noContextD)

  // @todo DotProgram would in a sense be the appropriate context
  private val noContext = ProgramConst("noctx")
  private val noContextD = DifferentialProgramConst("noctxD", AnyArg)

  // @note these tests sometimes fails for too courageous DotTerm() occurrences in the wrong places caused by random positioning. For example left of assignment ...
  "The positioning" should "consistently split formulas (checkin)" taggedAs CheckinTest in { test(5, 2) }
  it should "consistently split formulas (summary)" taggedAs SummaryTest in { test(20, 8) }
  it should "consistently split formulas (usual)" taggedAs UsualTest in { test(50, 10) }
  it should "consistently split formulas (slow)" taggedAs SlowTest in { test() }

  private def test(
      randomTrials: Int = randomTrials,
      randomReps: Int = randomReps,
      randomComplexity: Int = randomComplexity,
  ): Unit = for (_ <- 1 to randomTrials) {
    val f = rand.nextFormula(randomComplexity)
    for (_ <- 1 to randomReps) {
      val pos = rand.nextPosition(randomComplexity).inExpr
      contextShouldBe(f, pos)
    }
  }

}
