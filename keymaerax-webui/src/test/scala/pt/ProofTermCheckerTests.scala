package pt

import edu.cmu.cs.ls.keymaerax.core
import edu.cmu.cs.ls.keymaerax.core.{Provable, Sequent, Imply, Formula}
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
  private def proves(cert : Provable, f : Formula) = {
    val s = cert.conclusion
    s.succ.length == 1 && s.ante.length == 0 && s.succ.last.equals(f) && cert.isProved
  }
  private def debugCert(cert: Provable) = println(cert.subgoals.mkString("\n --- \n"))

  "\\FOLR Tautology checker" should "check j_{0=0} : 0=0" in {
    val zEz : Formula = "0=0".asFormula
    val certificate = ProofChecker(folrConstant(zEz), zEz)
    certificate.isDefined shouldBe true
    proves(certificate.get, zEz) shouldBe true
  }

  it should "check j_{x^2 = 0 <-> x = 0} : x^2 = 0 <-> x = 0" in {
    val f = "x^2 = 0 <-> x = 0".asFormula
    val certificate = ProofChecker(folrConstant(f), f)
    certificate.isDefined shouldBe true
    proves(certificate.get, f) shouldBe true
  }

  "e ^ d term checker" should "check j_{0=0} ^ j_{1=1} : 0=0 & 1=1" in {
    val f = "0=0 & 1=1".asFormula
    val certificate = ProofChecker(AndTerm(folrConstant("0=0".asFormula), folrConstant("1=1".asFormula)), f)
    certificate.isDefined shouldBe true
    proves(certificate.get, f) shouldBe true
  }

  "e * d term checker" should "check j_{0=0 -> 1=1} * j_{0=0} : 1=1" in {
    val oEo      = "1=1".asFormula
    val zEz      = "0=0".asFormula
    val zEzTerm  = folrConstant(zEz)
    val implTerm = folrConstant(Imply(zEz, oEo))
    val certificate = ProofChecker(ApplicationTerm(implTerm, zEz, zEzTerm), oEo)
    certificate.isDefined shouldBe true
    proves(certificate.get, oEo) shouldBe true

  }

  "e *-> d term checker" should "check j_{1=1 <-> 0=0} *-> j_{0=0} : 1=1" in {
    val oEo      = "1=1".asFormula
    val zEz      = "0=0".asFormula
    val zEzTerm  = folrConstant(zEz)
    val equivTerm = folrConstant(core.Equiv(oEo, zEz))
    val certificate = ProofChecker(RightEquivalence(equivTerm, zEz, zEzTerm), oEo)
    certificate.isDefined shouldBe true
    debugCert(certificate.get)
    proves(certificate.get, oEo) shouldBe true

  }
}
