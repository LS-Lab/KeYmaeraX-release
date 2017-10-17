package pt

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.core
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.pt._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._

import scala.collection.immutable

/**
 * Tests of the proof term checker <strike>from</strike> inspired by
 * Nathan Fulton and Andre Platzer, "A Logic of Proofs for Differential Dynamic Logic: Toward Independently Checkable Proof Certificates for Dynamic Logics", CPP 16
 * @todo update description of proof terms.
 * @author Nathan Fulton
 * @author Brandon Bohrer
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
    val checkResult = ProofChecker(proofTerm, Some(f))
    //checkResult.isDefined shouldBe true
    proves(checkResult, f) shouldBe true
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


  it should "work for Lab2 dI-ified proof version 1" in withMathematica (_ => {
    val lab2Fml ="velLead >= 0 & velCtrl >= 0 & A() > 0 & B() > 0 & (posLead - posCtrl)*B() >= velCtrl*velCtrl - velLead*velCtrl & posLead >= posCtrl & T() > 0\n->\n[{\n  SB := (velCtrl - velLead)*T()*2*B() + B()*(A() + B())*T()^2 + 2*(T()*(A()+B()) + velCtrl - velLead)*((velCtrl + T()*A()));\n    {{?2*B()*(posLead - posCtrl) > SB;\n     accCtrl := A(); }\n    ++\n    accCtrl := -B(); };\n    {accLead := A() ; ++ accLead := -B(); };\n    t := 0;\n    { velCtrl' = accCtrl, velLead' = accLead, posCtrl' = velCtrl, posLead' = velLead, t' = 1 & t < T() & velCtrl >= 0 & velLead >= 0} \n }*@invariant(velLead >= 0 & velCtrl >= 0 &  (posLead - posCtrl)*B() >= velCtrl*velCtrl - velLead*velCtrl & posLead >= posCtrl)\n]\nposLead >= posCtrl".asFormula
    val lab2Tac:BelleExpr = BelleParser("  implyR(1) ; andL(-1) ; andL(-2) ; andL(-3) ; andL(-4) ; andL(-5) ; andL(-6) ; loop({`velLead>=0&velCtrl>=0&(posLead-posCtrl)*B()>=velCtrl*velCtrl-velLead*velCtrl&posLead>=posCtrl`}, 1) ; <(\n  andR(1) ; <(\n    closeId,\n    andR(1) ; <(\n      closeId,\n      andR(1) ; <(\n        closeId,\n        closeId\n        )\n      )\n    ),\n  andL(-1) ; andL(-5) ; andL(-6) ; closeId,\n  composeb(1) ; assignb(1) ; composeb(1) ; choiceb(1) ; andR(1) ; <(\n    composeb(1) ; testb(1) ; implyR(1) ; assignb(1) ; composeb(1) ; choiceb(1) ; andR(1) ; <(\n      assignb(1) ; composeb(1) ; assignb(1) ; dC({`velCtrl=old(velCtrl)+A()*t`}, 1) ; <(\n        dC({`velLead=old(velLead)+A()*t`}, 1) ; <(\n          dC({`posCtrl=old(posCtrl)+old(velCtrl)*t+A()*t^2/2`}, 1) ; <(\n            dC({`posLead=old(posLead)+old(velLead)*t+A()*t^2/2`}, 1) ; <(\n              dC({`t>=0`}, 1) ; <(\n                dW(1) ; master,\n                dI(1)\n                ),\n              dI(1)\n              ),\n            dI(1)\n            ),\n          dI(1)\n          ),\n        andL(-1) ; andL(-8) ; andL(-9) ; dI(1)\n        ),\n      assignb(1) ; composeb(1) ; assignb(1) ; dC({`velCtrl=old(velCtrl)+A()*t`}, 1) ; <(\n        dC({`velLead=old(velLead)+-B()*t`}, 1) ; <(\n          dC({`posCtrl=old(posCtrl)+old(velCtrl)*t+A()*t^2/2`}, 1) ; <(\n            dC({`posLead=old(posLead)+old(velLead)*t-B()*t^2/2`}, 1) ; <(\n              dC({`t>=0`}, 1) ; <(\n                dC({`t<=old(velLead)/B()`}, 1) ; <(\n                  dW(1) ; master,\n                  ODE(1)\n                  ),\n                dI(1)\n                ),\n              dI(1)\n              ),\n            dI(1)\n            ),\n          dI(1)\n          ),\n        dI(1)\n        )\n      ),\n    assignb(1) ; composeb(1) ; choiceb(1) ; andR(1) ; <(\n      assignb(1) ; composeb(1) ; assignb(1) ; dC({`velCtrl=old(velCtrl)+-B()*t`}, 1) ; <(\n        dC({`velLead=old(velLead)+A()*t`}, 1) ; <(\n          dC({`posCtrl=old(posCtrl)+old(velCtrl)*t-B()*t^2/2`}, 1) ; <(\n            dC({`posLead=old(posLead)+old(velLead)*t+A()*t^2/2`}, 1) ; <(\n              dC({`t>=0`}, 1) ; <(\n                dW(1) ; master,\n                dI(1)\n                ),\n              dI(1)\n              ),\n            dI(1)\n            ),\n          dI(1)\n          ),\n        dI(1)\n        ),\n      assignb(1) ; composeb(1) ; assignb(1) ; dC({`velCtrl=old(velCtrl)+-B()*t`}, 1) ; <(\n        dC({`velLead=old(velLead)+-B()*t`}, 1) ; <(\n          dC({`posCtrl=old(posCtrl)+old(velCtrl)*t-B()*t^2/2`}, 1) ; <(\n            dC({`posLead=old(posLead)+old(velLead)*t-B()*t^2/2`}, 1) ; <(\n              dC({`t>=0`}, 1) ; <(\n                dW(1) ; master,\n                dI(1)\n                ),\n              dI(1)\n              ),\n            dI(1)\n            ),\n          dI(1)\n          ),\n        dI(1)\n        )\n      )\n    )\n  )")
    val provable = ProvableSig.startProof(lab2Fml)
    val tacticResult = proveBy(provable,lab2Tac)
    tacticResult match {
      case pr:PTProvable =>
        val size = pr.pt.numCons
        val bytes = pr.pt.bytesEstimate
        val axioms = pr.pt.axiomsUsed
        val rules = pr.pt.rulesUsed
        val goals = pr.pt.arithmeticGoals

        println("Size: " + size + "\n\n\n")
        println("Axioms: " + axioms + "\n\n\n")
        println("Rules: " + rules + "\n\n\n")
        println("Arithmetic Goals: " + goals + "\n\n\n")
        println("END OF STATS\n\n\n\n\n\n\n\n\n\n\n")
        val checkResult = ProofChecker(pr.pt, Some(lab2Fml))
        //checkResult.isDefined shouldBe true
        proves(checkResult, lab2Fml) shouldBe true
      case _ => ()
    }

    println(tacticResult)
  })

  "\\FOLR Tautology checker" should "check j_{0=0} : 0=0" in withMathematica (_ => {
    val zEz : Formula = "0=0".asFormula
    val certificate = ProofChecker(FOLRConstant(zEz), Some(zEz))
    //certificate.isDefined shouldBe true
    proves(certificate, zEz) shouldBe true
  })

  it should "check j_{x^2 = 0 <-> x = 0} : x^2 = 0 <-> x = 0" in withMathematica(_ => {
    val f = "x^2 = 0 <-> x = 0".asFormula
    val certificate = ProofChecker(FOLRConstant(f), Some(f))
    //certificate.isDefined shouldBe true
    proves(certificate, f) shouldBe true
  })


  //[v:=t();]p(v) <-> p(t())
  /*"usubst term checker" should "check \\sigma i_{[:=] assign} : [v:=1;]v=v <-> 1=1 for appropriate usubst" in {
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
  }*/
}
