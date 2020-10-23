package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

/** @param name Human-readable short description, can contain spaces etc
  * @param proof Proof statement which is tested against game
  * @param game Game that is tested for refinement
  * @param shouldRefine  Whether expected behavior is to refine succesfully vs fail       */
case class RefinementTestCase(name: String, proof: Statement, game: Program, shouldRefine: Boolean) {
  def prettyString: String =
    s"$name, with expected ${if(shouldRefine) "refinement" else "non-refinement"} of:\nproof:\n"+
    s"${PrettyPrinter.short(proof)}\nvs. game: ${game.prettyString}"
}
object RefinementTestCase {
  def apply(name: String, proof: String, game: String, shouldRefine: Boolean = true): RefinementTestCase = {
    try {
      val pf = KaisarProgramParser.parseSingle(proof)
      val g = game.asProgram
      RefinementTestCase(name, pf, g, shouldRefine)
    } catch {
      case th: Throwable => throw new Exception("Parse error in test case: " + name, th)
    }
  }
}

class RefinementTests extends TacticTestBase {
  val trivAssign: RefinementTestCase = RefinementTestCase("Trivial assignment", "x:= 0;", "x:=0;")
  val ghostODE: RefinementTestCase = RefinementTestCase("Simple differential ghost proof", SharedModels.ghostODE, SharedModels.ghostODEProgram)
  val inverseGhostODE: RefinementTestCase = RefinementTestCase("Simple inverse differential ghost proof", SharedModels.inverseGhostODE, SharedModels.inverseGhostODEProgram)
  val demonLoop: RefinementTestCase = RefinementTestCase("Simple demonic increment loop", SharedModels.demonicLoop, SharedModels.demonicLoopProgram)
  val demonLoopGhostly: RefinementTestCase = RefinementTestCase("Demonic increment loop with hidden induction proofs", SharedModels.demonicLoopGhostly, SharedModels.demonicLoopGhostlyProgram)

  val allCases: List[RefinementTestCase] = List(trivAssign, demonLoop, demonLoopGhostly, ghostODE, inverseGhostODE)

  private def didRefine(pf: Statement, g: Program): Boolean = {
    try {
      RefinementChecker(pf, g);
      true
    } catch {
      case _: RefinementFailure => false
    }
  }

  "Refinement checker" should "check all cases" in {
    allCases.foreach(rtc =>
      didRefine(rtc.proof, rtc.game) shouldBe rtc.shouldRefine withClue s"in testcase ${rtc.prettyString}"
    )
  }

  it should "check specific cases" in {
    val chosenCases = List(inverseGhostODE)
    chosenCases.foreach(rtc => {
      println("Checking: " + rtc.name)
      didRefine(rtc.proof, rtc.game) shouldBe rtc.shouldRefine withClue s"in testcase ${rtc.prettyString}"
    })
    println("Finished checking chosen cases")
  }
}
