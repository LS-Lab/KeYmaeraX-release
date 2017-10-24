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
    proves(checkResult, f) shouldBe true
  }

  private def checkIfPT(p:ProvableSig,f:Formula):Unit = {
    p match {
      case _ : NoProofTermProvable => ()
      case PTProvable(ps,pt) =>
        val checkResult = ProofChecker(pt)
        proves(checkResult, f) shouldBe true
    }
  }

  "Belle interpreter" should "generate proof terms when supplied with the PTProvable as input" in {
    val label = "[:=] assign"
    val f = "[x_:=f();]p(x_) <-> p(f())".asFormula
    val t = US(USubst.apply(scala.collection.immutable.Seq()), label)

    val provable = PTProvable.startProof(f)
    val tacticResult = proveBy(provable, t)
    println(tacticResult.prettyString)
    checkIfPT(tacticResult,f)
  }

  it should "work for prop tautologies" in withMathematica(_ => {
    val f = "A() -> A()".asFormula
    val provable = PTProvable.startProof(f)
    val t = TactixLibrary.implyR(1) & TactixLibrary.close(-1,1)

    val tacticResult = proveBy(provable, t)
    println(tacticResult)
    checkIfPT(tacticResult,f)
  })

  it should "work for ETCS dI-ified proof" in withMathematica (_ => {
    val fml = "    v^2<=2*b()*(m-x) & v>=0  & A()>=0 & b()>0-> [{{?(2*b()*(m-x) >= v^2+(A()+b())*(A()*ep()^2+2*ep()*v)); a:=A(); ++ a:=-b(); } t := 0;{x'=v, v'=a, t'=1 & v>=0 & t<=ep()}}*@invariant(v^2<=2*b()*(m-x))] x <= m".asFormula
    val tac = BelleParser("implyR(1) ; loop({`v^2<=2*b()*(m-x)`}, 1) ; <(closeId, QE,composeb(1) ; choiceb(1) ;andR(1) ; <(composeb(1) ; testb(1) ; implyR(1) ; assignb(1) ; composeb(1) ; assignb(1) ; dC({`2*b()*(m-x)>=v^2+(A()+b())*(A()*(ep()-t)^2+2*(ep()-t)*v)`}, 1) ; <(dW(1) ; QE,dI(1)), assignb(1) ; composeb(1) ; assignb(1) ; dI(1)))")
    val provable = ProvableSig.startProof(fml)
        val tacticResult = proveBy(provable,tac)
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
            checkIfPT(tacticResult,fml)
          case _ => ()
        }

        println(tacticResult)
  })

  "\\FOLR Tautology checker" should "check j_{0=0} : 0=0" in withMathematica (_ => {
    val zEz : Formula = "0=0".asFormula
    val certificate = ProofChecker(FOLRConstant(zEz), Some(zEz))
    proves(certificate, zEz) shouldBe true
  })

  it should "check j_{x^2 = 0 <-> x = 0} : x^2 = 0 <-> x = 0" in withMathematica(_ => {
    val f = "x^2 = 0 <-> x = 0".asFormula
    val certificate = ProofChecker(FOLRConstant(f), Some(f))
    proves(certificate, f) shouldBe true
  })

  "Isabelle converter" should "convert simple FOLR certificate" in withMathematica(_ => {
    val f = "x*x = 0 <-> x = 0".asFormula
    val pt = FOLRConstant(f)
    val conv = new IsabelleConverter(pt)
    val source = conv.scalaObjects("ProofTerm", "proofTerm", "GeneratedProofChecker")
    println(source)
  })

  it should "convert simple axiom usage" in withMathematica(_ => {
    val label = "[:=] assign"
    val f = "[x_:=f();]p(x_) <-> p(f())".asFormula
    val t = US(USubst.apply(scala.collection.immutable.Seq()), label)
    proveBy(ProvableSig.startProof(f), t) match {
      case ptp: PTProvable =>
        val conv = new IsabelleConverter(ptp.pt)
        val source = conv.scalaObjects("ProofTerm", "proofTerm", "GeneratedProofChecker")
        println(source)
      case _  =>
    }
  })

  it should "convert prop tautologies" in withMathematica(_ => {
    val f = "A() -> A()".asFormula
    val provable = PTProvable.startProof(f)
    val t = TactixLibrary.implyR(1) & TactixLibrary.close(-1,1)

    proveBy(provable, t) match {
      case ptp: PTProvable =>
        val conv = new IsabelleConverter(ptp.pt)
        val source = conv.scalaObjects("ProofTerm", "proofTerm", "GeneratedProofChecker")
        println(source)
      case _  =>
    }
  })

  it should "convert CPP'17 example" in withMathematica(_ => {
    val f = "A() >= 0 & v >= 0 -> [{v' = A(), x' = v & true}] v >= 0".asFormula
    val provable = PTProvable.startProof(f)
    val t = TactixLibrary.implyR(1) & andL(-1) & dI()(1)

    proveBy(provable, t) match {
      case ptp: PTProvable =>
        val size = ptp.pt.numCons
        val bytes = ptp.pt.bytesEstimate
        val axioms = ptp.pt.axiomsUsed
        val rules = ptp.pt.rulesUsed
        val goals = ptp.pt.arithmeticGoals

        println("Size: " + size + "\n\n\n")
        println("Axioms: " + axioms + "\n\n\n")
        println("Rules: " + rules + "\n\n\n")
        println("Arithmetic Goals: " + goals + "\n\n\n")
        println("END OF STATS\n\n\n\n\n\n\n\n\n\n\n")
        val conv = new IsabelleConverter(ptp.pt)
        val source = conv.scalaObjects("ProofTerm", "proofTerm", "GeneratedProofChecker")
        println(source)
      case _  =>
    }
  })

}
