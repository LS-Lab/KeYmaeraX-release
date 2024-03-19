/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

/**
 * Test refinement engine for testing whether given proof proves given formula
 * @author
 *   Brandon Bohrer
 */
package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase
import edu.cmu.cs.ls.keymaerax.core.{PrettyPrinter => _, _}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tagobjects.TodoTest
import org.scalatest.prop.TableDrivenPropertyChecks._

/**
 * @param name
 *   Human-readable short description, can contain spaces etc
 * @param proof
 *   Proof statement which is tested against game
 * @param game
 *   Game that is tested for refinement
 * @param shouldRefine
 *   Whether expected behavior is to refine succesfully vs fail
 */
case class RefinementTestCase(name: String, proof: Statement, game: Program, shouldRefine: Boolean) {
  def prettyString: String =
    s"$name, with expected ${if (shouldRefine) "refinement" else "non-refinement"} of:\nproof:\n" +
      s"${PrettyPrinter.short(proof)}\nvs. game: ${game.prettyString}"
}
object RefinementTestCase {
  def apply(name: String, proof: String, game: String, shouldRefine: Boolean = true): RefinementTestCase = {
    try {
      val pf = KaisarProgramParser.parseSingle(proof)
      val g = game.asProgram
      RefinementTestCase(name, pf, g, shouldRefine)
    } catch { case th: Throwable => throw new Exception("Parse error in test case: " + name, th) }
  }
}

class RefinementTests extends TacticTestBase {
  val trivAssign: RefinementTestCase = RefinementTestCase("Trivial assignment", "x:= 0;", "x:=0;")
  val ghostODE: RefinementTestCase =
    RefinementTestCase("Simple differential ghost proof", SharedModels.ghostODE, SharedModels.ghostODEProgram)
  val inverseGhostODE: RefinementTestCase = RefinementTestCase(
    "Simple inverse differential ghost proof",
    SharedModels.inverseGhostODE,
    SharedModels.inverseGhostODEProgram,
  )
  val demonLoop: RefinementTestCase =
    RefinementTestCase("Simple demonic increment loop", SharedModels.demonicLoop, SharedModels.demonicLoopProgram)
  val demonLoopGhostly: RefinementTestCase = RefinementTestCase(
    "Demonic increment loop with hidden induction proofs",
    SharedModels.demonicLoopGhostly,
    SharedModels.demonicLoopGhostlyProgram,
  )
  val assertBranchesNonzero: RefinementTestCase = RefinementTestCase(
    "Branching assert",
    SharedModels.assertBranchesNonzero,
    SharedModels.assertBranchesNonzeroProgram,
  )
  val switchLiterals: RefinementTestCase =
    RefinementTestCase("switch statement", SharedModels.switchLiterals, SharedModels.switchLiteralsProgram)
  val annotatedAssign: RefinementTestCase =
    RefinementTestCase("annotated assignment", SharedModels.annotatedAssign, SharedModels.annotatedAssignProgram)
  val annotatedAssignGame: RefinementTestCase =
    RefinementTestCase("annotated assignment game", SharedModels.annotatedAssign, SharedModels.annotatedAssignGame)
  val noteAnd: RefinementTestCase =
    RefinementTestCase("note example", SharedModels.noteAndFull, SharedModels.noteAndProgram)
  val basicForNoConv: RefinementTestCase =
    RefinementTestCase("for loop no-conv", SharedModels.basicForNoConv, SharedModels.basicForNoConvProg)
  val pldiModelSafeSimpleLets: RefinementTestCase =
    RefinementTestCase("simple lets", SharedModels.pldiModelSafeSimple, SharedModels.pldiModelSafeSimpleProgram)
  val pldiModelSafeFull: RefinementTestCase =
    RefinementTestCase("simple lets", SharedModels.pldiModelSafeFull, SharedModels.pldiModelSafeFullProgram)
  val allCases: List[RefinementTestCase] = List(
    trivAssign,
    demonLoop,
    demonLoopGhostly,
    ghostODE,
    inverseGhostODE,
    assertBranchesNonzero,
    switchLiterals,
    annotatedAssign,
    annotatedAssignGame, /*basicForNoConv,*/ pldiModelSafeSimpleLets,
    pldiModelSafeFull,
    noteAnd,
  )

  private def didRefine(pf: Statement, g: Program, name: String): Boolean = {
    val (outPf, ssaG) =
      try {
        val proofCon = Context.empty
        val (outPf, cncl) = Kaisar.result(proofCon, pf)
        val elabG = proofCon.elaborateFunctions(g, node = Triv())
        val ssaG = SSAPass(elabG)
        (outPf, ssaG)
      } catch {
        case th: Throwable =>
          val msg = "All Kaisar proofs in Refinement tests are supposed to succeed, but proof failed for case " + name
          throw new Exception(msg, th)
      }
    try {
      RefinementChecker(outPf, ssaG);
      true
    } catch { case _: RefinementFailure => false }
  }

  "Refinement checker" should "check all cases" in withMathematica { _ =>
    forEvery(Table("Test Case", allCases: _*))({ case rtc @ RefinementTestCase(name, proof, game, shouldRefine) =>
      println("Checking: " + name)
      didRefine(proof, game, name) shouldBe shouldRefine withClue s"in testcase ${rtc.prettyString}"
    })
  }

  it should "FEATURE_REQUEST: check specific cases" taggedAs TodoTest in withMathematica { _ =>
    // @note see SharedModels todo
    val chosenCases = List(basicForNoConv) // noteAnd basicForNoConv
    forEvery(Table("Test Case", chosenCases: _*))({ case rtc @ RefinementTestCase(name, proof, game, shouldRefine) =>
      println("Checking: " + name)
      didRefine(proof, game, name) shouldBe shouldRefine withClue s"in testcase ${rtc.prettyString}"
    })
    println("Finished checking chosen cases")
  }
}
