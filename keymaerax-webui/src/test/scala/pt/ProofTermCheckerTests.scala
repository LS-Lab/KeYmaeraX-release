package pt

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleInterpreter, BelleProvable}
import edu.cmu.cs.ls.keymaerax.btactics.{TacticTestBase, TactixLibrary}
import edu.cmu.cs.ls.keymaerax.core
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.pt._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._

/**
 * Tests of the proof term checker <strike>from</strike> inspired by
 * Nathan Fulton and Andre Platzer, "A Logic of Proofs for Differential Dynamic Logic: Twoard Independently Checkable Proof Certificates for Dynamic Logics", CPP 16
 * @todo update description of proof terms.
 * @author Nathan Fulton
 */
class ProofTermCheckerTests extends TacticTestBase {
  private def proves(cert : ProvableSig, f : Formula) = {
    val s = cert.conclusion
    s.succ.length == 1 && s.ante.length == 0 && s.succ.last.equals(f) && cert.isProved
  }
  private def debugCert(cert: ProvableSig) = println(cert.subgoals.mkString("\n --- \n"))

  "Axiom checker" should "check i_{[:=] assign} : [v:=t();]p(v) <-> p(t())" in {
    val label = "[:=] assign"
    val f = "[x_:=f();]p(x_) <-> p(f())".asFormula
    val t = US(USubst.apply(scala.collection.immutable.Seq()), label)

    val proofTerm = AxiomTerm(label)

    //Get the certificate
    val checkResult = ProofChecker(proofTerm, f)
    checkResult.isDefined shouldBe true
    proves(checkResult.get, f) shouldBe true
  }

  "Belle interpreter" should "generate proof terms when supplied with the PTProvable as input" in {
    val label = "[:=] assign"
    val f = "[x_:=f();]p(x_) <-> p(f())".asFormula
    val t = US(USubst.apply(scala.collection.immutable.Seq()), label)

    val provable = PTProvable.startProof(f)
    val tacticResult = proveBy(provable, t)
    println(tacticResult.prettyString)
  }

  it should "work for prop tautologies" in withMathematica(_ => {
    val f = "A() -> A()".asFormula
    val provable = PTProvable.startProof(f)
    val t = TactixLibrary.implyR(1) & TactixLibrary.close(-1,1)

    val tacticResult = proveBy(provable, t)
    println(tacticResult)
  })

  "\\FOLR Tautology checker" should "check j_{0=0} : 0=0" ignore {
    val zEz : Formula = "0=0".asFormula
    val certificate = ProofChecker(FOLRConstant(zEz), zEz)
    certificate.isDefined shouldBe true
    proves(certificate.get, zEz) shouldBe true
  }

  it should "check j_{x^2 = 0 <-> x = 0} : x^2 = 0 <-> x = 0" ignore {
    val f = "x^2 = 0 <-> x = 0".asFormula
    val certificate = ProofChecker(FOLRConstant(f), f)
    certificate.isDefined shouldBe true
    proves(certificate.get, f) shouldBe true
  }


  //[v:=t();]p(v) <-> p(t())
  "usubst term checker" should "check \\sigma i_{[:=] assign} : [v:=1;]v=v <-> 1=1 for appropriate usubst" ignore {
    val axiomName = "[:=] assign"
    val axiom = ProvableSig.axiom("[:=] assign")
    val instance = "[v:=1;]v=v <-> 1=1".asFormula
    val usubst = USubst(
      SubstitutionPair("t()".asTerm, "1".asTerm) ::
      SubstitutionPair(PredOf(Function("p", None, Real, Bool), DotTerm()), Equal(DotTerm(), DotTerm())) ::
      Nil
    )

    val instanceTerm = AxiomTerm(axiomName)
    val sigma = USubst(SubstitutionPair("f()".asTerm, "1".asTerm) :: Nil)
    val certificate = ProofChecker(UsubstTerm(instanceTerm, axiom, usubst), instance)
    certificate shouldBe defined
    proves(certificate.get, instance) shouldBe true
  }
}
