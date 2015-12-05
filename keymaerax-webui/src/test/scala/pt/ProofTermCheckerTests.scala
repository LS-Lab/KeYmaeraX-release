package pt

import edu.cmu.cs.ls.keymaerax.core
import edu.cmu.cs.ls.keymaerax.core._
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

  "Axiom checker" should "check i_{[:=] assign} : [v:=t();]p(v) <-> p(t())" in {
    val label = "[:=] assign"
    val f = "[v:=t();]p(v) <-> p(t())".asFormula
    val certificate = ProofChecker(dLConstant(label), f)
    certificate.isDefined shouldBe true
    proves(certificate.get, f) shouldBe true
  }

  "\\FOLR Tautology checker" should "check j_{0=0} : 0=0" in {
    val zEz : Formula = "0=0".asFormula
    val certificate = ProofChecker(FOLRConstant(zEz), zEz)
    certificate.isDefined shouldBe true
    proves(certificate.get, zEz) shouldBe true
  }

  it should "check j_{x^2 = 0 <-> x = 0} : x^2 = 0 <-> x = 0" in {
    val f = "x^2 = 0 <-> x = 0".asFormula
    val certificate = ProofChecker(FOLRConstant(f), f)
    certificate.isDefined shouldBe true
    proves(certificate.get, f) shouldBe true
  }

  "e ^ d term checker" should "check j_{0=0} ^ j_{1=1} : 0=0 & 1=1" in {
    val f = "0=0 & 1=1".asFormula
    val certificate = ProofChecker(AndTerm(FOLRConstant("0=0".asFormula), FOLRConstant("1=1".asFormula)), f)
    certificate.isDefined shouldBe true
    proves(certificate.get, f) shouldBe true
  }

  "e * d term checker" should "check j_{0=0 -> 1=1} * j_{0=0} : 1=1" in {
    val oEo      = "1=1".asFormula
    val zEz      = "0=0".asFormula
    val zEzTerm  = FOLRConstant(zEz)
    val implTerm = FOLRConstant(Imply(zEz, oEo))
    val certificate = ProofChecker(ApplicationTerm(implTerm, zEz, zEzTerm), oEo)
    certificate.isDefined shouldBe true
    proves(certificate.get, oEo) shouldBe true

  }

  "e *<- d term checker" should "check j_{1=1 <-> 0=0} *-> j_{0=0} : 1=1" in {
    val oEo      = "1=1".asFormula
    val zEz      = "0=0".asFormula
    val zEzTerm  = FOLRConstant(zEz)
    val equivTerm = FOLRConstant(core.Equiv(oEo, zEz))
    val certificate = ProofChecker(LeftEquivalence(equivTerm, zEz, zEzTerm), oEo)
    certificate.isDefined shouldBe true
    debugCert(certificate.get)
    proves(certificate.get, oEo) shouldBe true
  }

  "e *-> d term checker" should "check j_{1=1 <-> 0=0} *<- j_{1=1} : 0=0" in {
    val oEo      = "1=1".asFormula
    val zEz      = "0=0".asFormula
    val oEoTerm  = FOLRConstant(oEo)
    val equivTerm = FOLRConstant(core.Equiv(oEo, zEz))
    val certificate = ProofChecker(RightEquivalence(equivTerm, oEo, oEoTerm), zEz)
    certificate.isDefined shouldBe true
    debugCert(certificate.get)
    proves(certificate.get, zEz) shouldBe true
  }


  //[v:=t();]p(v) <-> p(t())
  "usubst term checker" should "check \\sigma i_{[:=] assign} : [v:=1;]v=v <-> 1=1 for appropriate usubst" in {
    val axiomName = "[:=] assign"
    val axiom = Axiom.axiom("[:=] assign").conclusion.succ.last
    val instance = "[v:=1;]v=v <-> 1=1".asFormula
    val usubst = USubst(
      SubstitutionPair("t()".asTerm, "1".asTerm) ::
      SubstitutionPair(PredOf(Function("p", None, Real, Bool), DotTerm), Equal(DotTerm, DotTerm)) ::
      Nil
    )

    val instanceTerm = dLConstant(axiomName)
    val sigma = USubst(SubstitutionPair("f()".asTerm, "1".asTerm) :: Nil)
    val certificate = ProofChecker(UsubstTerm(instanceTerm, axiom, usubst), instance)
    certificate shouldBe defined
    proves(certificate.get, instance) shouldBe true
  }

  "CT term checker" should "check CT_\\sigma 1+1+1 = 1+2" in {
    val goal = "1+1+1=2+1".asFormula

    val premise = Equal("1+1".asTerm, "2".asTerm)
    val premiseTerm = FOLRConstant(premise)

    val c = Function("ctx_", None, Real, Real)
    val cApp = FuncOf(c, DotTerm)
    val f = Function("f_", None, Real, Real)
    val fApp = FuncOf(f, Anything)
    val g = Function("g_", None, Real, Real)
    val gApp = FuncOf(g, Anything)

    val usubst = USubst(
      SubstitutionPair(fApp, "1+1".asTerm) ::
      SubstitutionPair(gApp, "2".asTerm) ::
      SubstitutionPair(cApp, Plus(DotTerm, Number(1))) ::
      Nil
    )

    val certificate = ProofChecker(CTTerm(premiseTerm, premise, usubst), goal)
    certificate shouldBe defined
    proves(certificate.get, goal) shouldBe true
  }
}
