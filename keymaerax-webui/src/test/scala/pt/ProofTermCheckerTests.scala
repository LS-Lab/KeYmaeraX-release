package pt

import edu.cmu.cs.ls.keymaerax.core.Formula
import edu.cmu.cs.ls.keymaerax.pt._
import testHelper.TacticTestSuite
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

/**
 * Tests of the proof term checker from
 * "A Logic of Proofs for Differential Dynamic Logic: Twoard Independently Checkable Proof Certificates for Dynamic Logics"
 * Nathan Fulton and Andre Platzer
 * In Submission to CPP'16
 * @author Nathan Fulton
 */
class ProofTermCheckerTests extends TacticTestSuite {
  "\\FOLR Tautology checker" should "check j_{0=0} : 0=0" in {
    val zEz : Formula = "0=0".asFormula
    val certificate = ProofChecker(folrConstant(zEz), zEz)
    certificate.isDefined shouldBe true
    println(certificate.get.prettyString)
    certificate.get.isProved shouldBe true
  }

  it should "check j_{x^2 = 0 <-> x = 0} : x^2 = 0 <-> x = 0" in {
    val f = "x^2 = 0 <-> x = 0".asFormula
    val certificate = ProofChecker(folrConstant(f), f)
    certificate.isDefined shouldBe true
    certificate.get.isProved shouldBe true
  }

  "e ^ d term checker" should "check j_{0=0} ^ j_{1=1} : 0=0 & 1=1" in {
    val f = "0=0 & 1=1".asFormula
    val certificate = ProofChecker(AndTerm(folrConstant("0=0".asFormula), folrConstant("1=1".asFormula)), f)
    certificate.isDefined shouldBe true
    certificate.get.isProved shouldBe true 
  }
}
