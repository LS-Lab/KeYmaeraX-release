/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.pt

import java.io.PrintWriter
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.pt._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.parser.ArchiveParser
import edu.cmu.cs.ls.keymaerax.parser.ParsedArchiveEntry
import testHelper.KeYmaeraXTestTags.TodoTest

/**
 * Tests of the proof term checker <strike>from</strike> inspired by
 * Nathan Fulton and Andre Platzer, "A Logic of Proofs for Differential Dynamic Logic: Toward Independently Checkable Proof Certificates for Dynamic Logics", CPP 16
 * @todo update description of proof terms.
 * @author Nathan Fulton
 * @author Brandon Bohrer
 */
class ProofTermCheckerTests extends TacticTestBase {
  private def proves(cert: ProvableSig, f: Formula) = {
    val s = cert.conclusion
    s.succ.length == 1 && s.ante.isEmpty && s.succ.last.equals(f) && cert.isProved
  }

/*
  "Axiom checker" should "check i_{[:=] assign} : [v:=t();]p(v) <-> p(t())" in {
    val label = "[:=] assign"
    val f = "[x_:=f();]p(x_) <-> p(f())".asFormula
    val t = US(USubst.apply(scala.collection.immutable.Seq()), label)

    val proofTerm = AxiomTerm(label)

    //Get the certificate
    val checkResult = ProofChecker(proofTerm, Some(f))
    proves(checkResult, f) shouldBe true
  }
*/
  private def checkIfPT(p: ProvableSig, f: Formula): Unit = {
    p match {
      case _: ElidingProvable => ()
      case TermProvable(_, pt, _) =>
        val checkResult = ProofChecker(pt)
        proves(checkResult, f) shouldBe true
    }
  }

  "Belle interpreter" should "generate proof terms when supplied with the TermProvable as input" ignore {
    val label = "[:=] assign"
    val f = "[x_:=f();]p(x_) <-> p(f())".asFormula
    val t = ??? //US(USubst.apply(scala.collection.immutable.Seq()), label)

    val provable = TermProvable.startPlainProof(f)
    val tacticResult = proveBy(provable, t)
    println(tacticResult.prettyString)
    checkIfPT(tacticResult,f)
  }

  it should "work for prop tautologies with manual proof" in withTemporaryConfig(Map(Configuration.Keys.PROOF_TERM -> "true")) { withMathematica { _ =>
    val f = "A() -> A()".asFormula
    val provable = TermProvable.startPlainProof(f)
    val tacticResult = proveBy(provable, TactixLibrary.implyR(1) & TactixLibrary.close(-1,1))
    println(tacticResult)
    checkIfPT(tacticResult, f)
  }}

  it should "work for prop tautologies with propClose" in withTemporaryConfig(Map(Configuration.Keys.PROOF_TERM -> "true")) { withMathematica { _ =>
    val f = "A() -> A()".asFormula
    val provable = TermProvable.startPlainProof(f)
    val tacticResult = proveBy(provable, TactixLibrary.propClose)
    println(tacticResult)
    checkIfPT(tacticResult, f)
  }}

  it should "FEATURE_REQUEST: work for monoCars" taggedAs TodoTest in withTemporaryConfig(Map(Configuration.Keys.PROOF_TERM -> "true")) { withMathematica { _ =>
    val fml =
      """velLead >= velCtrl & velCtrl >= 0 &  A() > 0 &  B() > 0 &  posLead >= posCtrl & T() > 0
        |->
        |[{
        |  {   ?((velLead-velCtrl) >= T()*(A()+B())); accCtrl := A();
        |   ++ accCtrl:= -B();
        |  };
        |  {   accLead := A() ;
        |   ++ accLead := -B(); };
        |  t := 0;
        |  { velCtrl' = accCtrl, velLead' = accLead, posCtrl' = velCtrl, posLead' = velLead, t' = 1 & t < T() & velCtrl>= 0 & velLead >= 0}
        | }*@invariant(velLead >= velCtrl & velCtrl >= 0 & posLead >= posCtrl)
        |]posLead >= posCtrl
        |""".stripMargin.asFormula
    val tac = BelleParser(
      """unfold ; loop("velLead>=velCtrl&velCtrl>=0&posLead>=posCtrl", 1) ; <(
        |  propClose,
        |  propClose,
        |  unfold ; <(
        |    dC("velLead>=velCtrl", 1) ; <(
        |      dC("posLead>=posCtrl", 1) ; <(
        |        dW(1) ; propClose,
        |        dI(1)
        |        ),
        |      dI(1)
        |      ),
        |    dC("velLead>=velCtrl", 1) ; <(
        |      dC("posLead>=posCtrl", 1) ; <(
        |        dW(1) ; propClose,
        |        dI(1)
        |        ),
        |      dI(1)
        |      ),
        |    dC("velLead>=velCtrl", 1) ; <(
        |      dC("posLead>=posCtrl", 1) ; <(
        |        dW(1) ; propClose,
        |        dI(1)
        |        ),
        |      dI(1)
        |      ),
        |    dC("velLead-velCtrl>=(A()+B())*(T()-t)", 1) ; <(
        |      dC("posLead>=posCtrl", 1) ; <(
        |        dW(1) ; unfold ; QE,
        |        dI(1)
        |        ),
        |      dI(1)
        |      )
        |    )
        |  )
        |""".stripMargin)
    val provable = ProvableSig.startPlainProof(fml)
    val tacticResult = proveBy(provable,tac)
    println(tacticResult)
    tacticResult match {
      case pr:TermProvable =>
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

        //@todo uniform renaming in Isabelle
        val conv = new IsabelleConverter(pr.pt)
        //val source = conv.scalaObjects("ProofTerm", "proofTerm", "GeneratedProofChecker")
        val source = conv.sexp
        val writer = new PrintWriter("monocars.pt")
        writer.write(source)
        writer.close()
      case _ => ()
    }
  }}

  it should "FEATURE_REQUEST: work for double velCar" taggedAs TodoTest in withTemporaryConfig(Map(Configuration.Keys.PROOF_TERM -> "true")) { withMathematica { _ =>
    val velCar2Fml =
      """    xc<=xl & V>=0
        | -> [
        |      {
        |        {?(xl-xc)>=V*ep; vc:=V; ++ vc:=0;};
        |        {vl := V; ++ vl:=0;}
        |        t := 0;
        |        {xl'=vl, xc'=vc, t'=1 & t<=ep}
        |      }*@invariant(xc<=xl)
        |    ] xc <= xl
        |""".stripMargin.asFormula
    val tac = BelleParser(
      """unfold ; loop("xc<=xl", 1) ; <(
        |  propClose,
        |  propClose,
        |  unfold ; <(
        |    dI(1),
        |    dI(1),
        |    dI(1),
        |    dC("xl-xc>=V*(ep-t)", 1) ; <(
        |      dW(1) ; QE,
        |      dI(1)
        |      )
        |    )
        |  )
        |""".stripMargin)
    val provable = ProvableSig.startPlainProof(velCar2Fml)
    val tacticResult = proveBy(provable,tac)
    println(tacticResult)
    tacticResult match {
      case pr: TermProvable =>
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

        //@todo uniform renaming in Isabelle
        val conv = new IsabelleConverter(pr.pt)
        //val source = conv.scalaObjects("ProofTerm", "proofTerm", "GeneratedProofChecker")
        val source = conv.sexp
        val writer = new PrintWriter("doubleCar-dfunl.pt")
        writer.write(source)
        writer.close()
      case _ => ()
    }
  }}

  it should "FEATURE_REQUEST: work for ETCS dI-ified proof" taggedAs TodoTest in withMathematica (_ => {
    val fml = "    v^2<=2*b()*(m-x) & v>=0  & A()>=0 & b()>0-> [{{?(2*b()*(m-x) >= v^2+(A()+b())*(A()*ep()^2+2*ep()*v)); a:=A(); ++ a:=-b(); } t := 0;{x'=v, v'=a, t'=1 & v>=0 & t<=ep()}}*@invariant(v^2<=2*b()*(m-x))] x <= m".asFormula
    val tac = BelleParser("implyR(1) ; loop({`v^2<=2*b()*(m-x)`}, 1) ; <(closeId, QE,composeb(1) ; choiceb(1) ;andR(1) ; <(composeb(1) ; testb(1) ; implyR(1) ; assignb(1) ; composeb(1) ; assignb(1) ; dC({`2*b()*(m-x)>=v^2+(A()+b())*(A()*(ep()-t)^2+2*(ep()-t)*v)`}, 1) ; <(dW(1) ; QE,dI(1)), assignb(1) ; composeb(1) ; assignb(1) ; dI(1)))")
    val provable = ProvableSig.startPlainProof(fml)
        val tacticResult = proveBy(provable,tac)
        tacticResult match {
          case pr:TermProvable =>
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

  "\\FOLR Tautology checker" should "check j_{0=0} : 0=0" in withTemporaryConfig(Map(Configuration.Keys.PROOF_TERM -> "true")) { withMathematica { _ =>
    val zEz : Formula = "0=0".asFormula
    val certificate = ProofChecker(FOLRConstant(zEz), Some(zEz))
    proves(certificate, zEz) shouldBe true
  }}

  it should "check j_{x^2 = 0 <-> x = 0} : x^2 = 0 <-> x = 0" in withTemporaryConfig(Map(Configuration.Keys.PROOF_TERM -> "true")) { withMathematica { _ =>
    val f = "x^2 = 0 <-> x = 0".asFormula
    val certificate = ProofChecker(FOLRConstant(f), Some(f))
    proves(certificate, f) shouldBe true
  }}

  "Isabelle converter" should "convert simple FOLR certificate" in withTemporaryConfig(Map(Configuration.Keys.PROOF_TERM -> "true")) { withMathematica { _ =>
    val f = "x*x = 0 <-> x = 0".asFormula
    val pt = FOLRConstant(f)
    val conv = new IsabelleConverter(pt)
    val source = conv.scalaObjects("ProofTerm", "proofTerm", "GeneratedProofChecker")
    println(source)
  }}

  it should "convert simple axiom usage" ignore withMathematica(_ => {
    val label = "[:=] assign"
    val f = "[x_:=f();]p(x_) <-> p(f())".asFormula
    val t = ??? ///US(USubst.apply(scala.collection.immutable.Seq()), label)
    proveBy(ProvableSig.startPlainProof(f), t) match {
      case ptp: TermProvable =>
        val conv = new IsabelleConverter(ptp.pt)
        val source = conv.scalaObjects("ProofTerm", "proofTerm", "GeneratedProofChecker")
        println(source)
      case _  =>
    }
  })

  it should "convert prop tautologies" in withTemporaryConfig(Map(Configuration.Keys.PROOF_TERM -> "true")) { withMathematica { _ =>
    val f = "A() -> A()".asFormula
    val provable = TermProvable.startPlainProof(f)
    val t = TactixLibrary.implyR(1) & TactixLibrary.close(-1,1)

    proveBy(provable, t) match {
      case ptp: TermProvable =>
        val conv = new IsabelleConverter(ptp.pt)
        val source = conv.scalaObjects("ProofTerm", "proofTerm", "GeneratedProofChecker")
        println(source)
      case _  =>
    }
  }}

  it should "FEATURE_REQUEST: convert leaderfollower" taggedAs TodoTest in withMathematica(_ => {
    //@note TermProvable throws DebugMeException on unfold (swallowed by interpreter, since unfold executes optional chase steps)
    val archive = "SharedDefinitions.\n  R A.\n  R B.\n  R T.\n\n  R SB(R vl, R vf) = ( vf*vf - vl*vl + (A()+B())*(A()*T()*T() + 2*T()*vf) ).\n\n  /* predicates */\n  B bounds() <-> ( A()>=0 & B()>0 & T()>=0 ).\n  B loopinv(R vl, R pl, R vf, R pf) <-> ( vl>=0 & vf>=0 & (pl-pf)*2*B()>=vf*vf-vl*vl & pl>=pf ).\n\n  /* differential invariants */\n  B vinv(R v, R a, R t) <-> ( v=old(v)+a*t ).\n  B pinv(R p, R v, R a, R t) <-> ( p=old(p)+old(v)*t+a*t^2/2 ).\n\n  /* programs */\n  HP ctrl ::= {\n    {   ?(posLead - posCtrl)*2*B() >= SB(velLead, velCtrl); accCtrl := A();\n     ++ accCtrl := -B();\n    };\n    t := 0;\n  }.\n\n  HP plant ::= {\n       { velCtrl' = accCtrl, velLead' =  A(), posCtrl' = velCtrl, posLead' = velLead, t' = 1 & t <= T() & velCtrl >= 0 & velLead >= 0}\n    ++ { velCtrl' = accCtrl, velLead' = -B(), posCtrl' = velCtrl, posLead' = velLead, t' = 1 & t <= T() & velCtrl >= 0 & velLead >= 0}\n  }.\nEnd.\n\nLemma \"Leader-Follower Preserves Invariant\".\n\nProgramVariables.\n  R velLead.\n  R velCtrl.\n  R posLead.\n  R posCtrl.\n  R accCtrl.\n  R accLead.\n  R t.\nEnd.\n\nProblem.\nbounds() & loopinv(velLead, posLead, velCtrl, posCtrl)\n->\n[\n  ctrl;\n  plant;\n]\nloopinv(velLead, posLead, velCtrl, posCtrl)\nEnd.\n\n\nTactic \"Proof Leader-Follower Preserves Loop Invariant\".\nunfold ; <(\n  diffInvariant({`vinv(velCtrl, A(), t)`}, 1);\n  diffInvariant({`vinv(velLead, A(), t)`}, 1);\n  diffInvariant({`pinv(posCtrl, velCtrl, A(), t)`}, 1);\n  diffInvariant({`pinv(posLead, velLead, A(), t)`}, 1);\n  diffInvariant({`t>=0`}, 1);\n  dW(1);\n  implyR(1);\n  andL('L)*;\n  hideL(-3=={`(posLead_0-posCtrl_0)*2*B()>=velCtrl_0*velCtrl_0-velLead_0*velLead_0`});\n  print({`Transforming`});\n  cut({`(posLead_0-posCtrl_0)*2*B()>=velCtrl_0*velCtrl_0-velLead_0*velLead_0+(A()+B())*(A()*t*t+2*t*velCtrl_0)`}); <(\n    hideL(-7=={`(posLead_0-posCtrl_0)*2*B()>=velCtrl_0*velCtrl_0-velLead_0*velLead_0+(A()+B())*(A()*T()*T()+2*T()*velCtrl_0)`}),\n    hideR(1);\n    hideL('L=={`posLead=posLead_0+velLead_0*t+A()*t^2/2`});\n    hideL('L=={`posCtrl=posCtrl_0+velCtrl_0*t+A()*t^2/2`});\n    hideL('L=={`velLead=velLead_0+A()*t`});\n    hideL('L=={`velCtrl=velCtrl_0+A()*t`});\n    hideL('L=={`velCtrl>=0`});\n    hideL('L=={`velLead>=0`});\n    QE\n  );\n  hideL('L=={`T()>=0`});\n  hideL('L=={`t<=T()`});\n  print({`Lead=A(), Follow=A()`}); master; print({`...done`})\n  ,\n  diffInvariant({`vinv(velCtrl, -B(), t)`}, 1);\n  diffInvariant({`vinv(velLead, A(), t)`}, 1);\n  diffInvariant({`pinv(posCtrl, velCtrl, -B(), t)`}, 1);\n  diffInvariant({`pinv(posLead, velLead, A(), t)`}, 1);\n  diffInvariant({`t>=0`}, 1);\n  dW(1); print({`Lead=A(), Follow=-B()`}); master; print({`...done`})\n  ,\n  diffInvariant({`vinv(velCtrl, A(), t)`}, 1);\n  diffInvariant({`vinv(velLead, -B(), t)`}, 1);\n  diffInvariant({`pinv(posCtrl, velCtrl, A(), t)`}, 1);\n  diffInvariant({`pinv(posLead, velLead, -B(), t)`}, 1);\n  diffInvariant({`t>=0`}, 1);\n  dW(1);\n  implyR(1);\n  andL('L)*;\n  hideL(-3=={`(posLead_0-posCtrl_0)*2*B()>=velCtrl_0*velCtrl_0-velLead_0*velLead_0`});\n  print({`Transforming`});\n  cut({`(posLead_0-posCtrl_0)*2*B()>=velCtrl_0*velCtrl_0-velLead_0*velLead_0+(A()+B())*(A()*t*t+2*t*velCtrl_0)`}); <(\n    hideL(-7=={`(posLead_0-posCtrl_0)*2*B()>=velCtrl_0*velCtrl_0-velLead_0*velLead_0+(A()+B())*(A()*T()*T()+2*T()*velCtrl_0)`}),\n    hideR(1);\n    hideL('L=={`posLead=posLead_0+velLead_0*t+(-B())*t^2/2`});\n    hideL('L=={`posCtrl=posCtrl_0+velCtrl_0*t+A()*t^2/2`});\n    hideL('L=={`velLead=velLead_0+(-B())*t`});\n    hideL('L=={`velCtrl=velCtrl_0+A()*t`});\n    hideL('L=={`velCtrl>=0`});\n    hideL('L=={`velLead>=0`});\n    QE\n  );\n  hideL('L=={`T()>=0`});\n  hideL('L=={`t<=T()`});\n  print({`Lead=-B(), Follow=A()`}); master; print({`...done`})\n  ,\n  diffInvariant({`vinv(velCtrl, -B(), t)`}, 1);\n  diffInvariant({`vinv(velLead, -B(), t)`}, 1);\n  diffInvariant({`pinv(posCtrl, velCtrl, -B(), t)`}, 1);\n  diffInvariant({`pinv(posLead, velLead, -B(), t)`}, 1);\n  diffInvariant({`t>=0`}, 1);\n  dW(1); print({`Lead=-B(), Follow=-B()`}); master; print({`...done`})\n)\nEnd.\n\nEnd.\n\nTheorem \"Leader-Follower Safety\".\n\nProgramVariables.\n  R velLead.\n  R velCtrl.\n  R posLead.\n  R posCtrl.\n  R accCtrl.\n  R accLead.\n  R t.\nEnd.\n\nProblem.\nbounds() & velLead=0 & velCtrl=0 & posLead>=posCtrl\n->\n[{\n   ctrl;\n   plant;\n }*@invariant(loopinv(velLead, posLead, velCtrl, posCtrl))\n]\nposLead>=posCtrl\nEnd.\n\nTactic \"Proof Leader-Follower Safety\".\nimplyR(1); loop({`loopinv(velLead, posLead, velCtrl, posCtrl)`}, 1); <(\n  QE,\n  QE,\n  useLemma({`Leader-Follower Preserves Invariant`}, {`prop`})\n)\nEnd.\n\nEnd."
    val ParsedArchiveEntry(name, kind, modelText, _, _, formula, parsedTactics, _, _) = ArchiveParser.parse(archive).head
    val provable = TermProvable.startPlainProof(formula.asInstanceOf[Formula])
    proveBy(provable, parsedTactics.head._3) match {
      case ptp: TermProvable =>
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
        //val source = conv.scalaObjects("ProofTerm", "proofTerm", "GeneratedProofChecker")
        val source = conv.sexp
        val writer = new PrintWriter("TheLeadFollow.pt")
        writer.write(source)
        writer.close()
      //println(source)
    }})

  it should "FEATURE_REQUEST: convert VelocityCarDist" taggedAs TodoTest in withMathematica(_ => {
    val f = "(d>=0 & (V()>=0 & ep()>=0)) -> [{{{{?d>=V()*ep(); v:=*; ?0<=v&v<=V();} ++ v:=0;}t := 0;}{d'=-v, t'=1 & t<=ep()}}*@invariant(d>=0)] ( d>=0)".asFormula
    val t =
      implyR(1) &
        loop("d >= 0".asFormula)(1)  <(
          id,
          id,
          composeb(1) & composeb(1) & choiceb(1) & andR(1) <(
            composeb(1) & testb(1) & implyR(1) & composeb(1) & randomb(1) & allR(1) & testb(1) & implyR(1) &
              assignb(1) & dC("d>=V()*(ep()-t)".asFormula)(1) <(
              dW(1) & QE,
              dI()(1)
            ),
            assignb(1) & assignb(1) & dI()(1)
          )
        )
    val provable = TermProvable.startPlainProof(f)
    proveBy(provable, t) match {
      case ptp: TermProvable =>
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
        //val source = conv.scalaObjects("ProofTerm", "proofTerm", "GeneratedProofChecker")
        val source = conv.sexp
        val writer = new PrintWriter("velocityCar-dist.pt")
        writer.write(source)
        writer.close()
        //println(source)
    }})

  it should "convert CPP'17 example" ignore withMathematica(_ => {
    val f = "A() >= 0 & v >= 0 -> [{v' = A(), x' = v & true}] v >= 0".asFormula
    val provable = TermProvable.startPlainProof(f)
    val t = TactixLibrary.implyR(1) & andL(-1) & dI()(1)

    proveBy(provable, t) match {
      case ptp: TermProvable =>
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
        val is = collection.immutable.IndexedSeq
        /*val subPt =
          Sub(
            Sub(
              RuleApplication(
                RuleApplication(
                  StartProof(Sequent(is("A()>=0".asFormula, "v>=0".asFormula),is("(true->v>=0&[{v'=A(),x'=v&true}](v>=0)')->[{v'=A(),x'=v&true}]v>=0".asFormula))),
                  "CoHideRight",0,List(core.SuccPos(0)),List()),
                "Imply Right",0,List(core.SuccPos(0)),List()),
              StartProof(Sequent(is("true->v>=0&[{v'=A(),x'=v&true}](v>=0)'".asFormula), is("[{v'=A(),x'=v&true}]v>=0".asFormula))),0),
          Sub(RuleApplication(RuleApplication(RuleApplication(
                 StartProof(Sequent(is("true->v>=0&[{v'=A(),x'=v&true}](v>=0)'".asFormula),is("[{v'=A(),x'=v&true}]v>=0".asFormula))),
                   "cut Right",0,List(core.SuccPos(0)),List("true->v>=0&[{v'=A(),x'=v&true}](v>=0)'".asFormula))
              ,"Close",0,List(core.AntePos(0), core.SuccPos(0)),List()),"HideLeft",0,List(AntePos(0)),List()),
            StartProof(Sequent(is(),is("(true->v>=0&[{v'=A(),x'=v&true}](v>=0)')->[{v'=A(),x'=v&true}]v>=0".asFormula))),0),0)*/

        val recheck = ProofChecker(ptp.pt)
        val conv = new IsabelleConverter(ptp.pt)
        val source = conv.sexp//conv.scalaObjects("ProofTerm", "proofTerm", "GeneratedProofChecker")
        println(source)
      case _  =>
    }
  })

  it should "FEATURE_REQUEST: work for Lab2 dI-ified proof version 2" taggedAs TodoTest in withZ3 (_ => {
    val lab2Fml=
    ("( A()>=0 & B()>0 & T()>=0 ) &" +
        "( velLead>=0 & velCtrl>=0 & (posLead-posCtrl)*2*B()>=velCtrl*velCtrl-velLead*velLead & posLead>=posCtrl ) ->" +
        "[    {   ?(posLead - posCtrl)*2*B() >= ( velCtrl*velCtrl - velLead*velLead + (A()+B())*(A()*T()*T() + 2*T()*velCtrl) ); accCtrl := A();\n     ++ accCtrl := -B();\n    };\n    t := 0;" +
        "       {{ velCtrl' = accCtrl, velLead' =  A(), posCtrl' = velCtrl, posLead' = velLead, t' = 1 & t <= T() & velCtrl >= 0 & velLead >= 0}\n    ++ { velCtrl' = accCtrl, velLead' = -B(), posCtrl' = velCtrl, posLead' = velLead, t' = 1 & t <= T() & velCtrl >= 0 & velLead >= 0}}]" +
        "( velLead>=0 & velCtrl>=0 & (posLead-posCtrl)*2*B()>=velCtrl*velCtrl-velLead*velLead & posLead>=posCtrl )").asFormula

    /*val lab2Fml ="velLead >= 0 &\nvelCtrl >= 0 &\nA() > 0 & \nB() > 0 & \n(posLead - posCtrl)*B() >= velCtrl*velCtrl - velLead*velCtrl &\n posLead >= posCtrl &\n T() > 0\n->\n[{\n  SB := (velCtrl - velLead)*T()*2*B() + B()*(A() + B())*T()*T() + 2*(T()*(A()+B()) + velCtrl - velLead)*((velCtrl + T()*A()));\n {{?2*B()*(posLead - posCtrl) > SB;\n   accCtrl := A(); }\n ++\n   accCtrl := -B();};\n {accLead := A() ;++ accLead := -B(); };\n t := 0;\n { velCtrl' = accCtrl, velLead' = accLead, posCtrl' = velCtrl, posLead' = velLead, t' = 1 & t < T() & velCtrl >= 0 & velLead >= 0}\n}*@invariant(velLead >= 0 & velCtrl >= 0 &  (posLead - posCtrl)*B() >= velCtrl*velCtrl - velLead*velCtrl & posLead >= posCtrl)\n]posLead >= posCtrl".asFormula*/
    /*val lab2Tac:BelleExpr = BelleParser("unfold ; loop({`velLead>=0&velCtrl>=0&(posLead-posCtrl)*B()>=velCtrl*velCtrl-velLead*velCtrl&posLead>=posCtrl`}, 1) ; <(  unfold,  unfold,  unfold ; <(    dC({`velCtrl=old(velCtrl)+A()*t`}, 1) ; <(      dC({`velLead=old(velLead)+A()*t`}, 1) ; <(        dC({`posCtrl=old(posCtrl)+old(velCtrl)*t+A()*t*t*0.5`}, 1) ; <(          dC({`posLead=old(posLead)+old(velLead)*t+A()*t*t*0.5`}, 1) ; <(            dC({`t>=0`}, 1) ; <(              dW(1) ; master,              dI(1)              ),            dI(1)            ),          dI(1)          ),        dI(1)        ),      dI(1)      ),    dC({`velCtrl=old(velCtrl)+-B()*t`}, 1) ; <(      dC({`velLead=old(velLead)+A()*t`}, 1) ; <(        dC({`posCtrl=old(posCtrl)+old(velCtrl)*t-B()*t*t*0.5`}, 1) ; <(          dC({`posLead=old(posLead)+old(velLead)*t+A()*t*t*0.5`}, 1) ; <(            dC({`t>=0`}, 1) ; <(              dW(1) ; master,              dI(1)              ),            dI(1)            ),          dI(1)          ),        dI(1)        ),      dI(1)      ),    dC({`velCtrl=old(velCtrl)+A()*t`}, 1) ; <(      dC({`velLead=old(velLead)+-B()*t`}, 1) ; <(        dC({`posCtrl=old(posCtrl)+old(velCtrl)*t+A()*t*t*0.5`}, 1) ; <(          dC({`posLead=old(posLead)+old(velLead)*t-B()*t*t*0.5`}, 1) ; <(            dC({`t>=0`}, 1) ; <(              dC({`2*B()*(posLead-posCtrl)>(velCtrl-velLead)*(T()-t)*2*B()+B()*(A()+B())*(T()-t)*(T()-t)+2*((T()-t)*(A()+B())+velCtrl-velLead)*(velCtrl+(T()-t)*A())`}, 1) ; <(                dC({`B()*t<=old(velLead)`}, 1) ; <(                  dW(1) ; unfold ; <(                    QE,                    QE                    ),                  ODE(1)                  ),                dI(1)                ),              dI(1)              ),            dI(1)            ),          dI(1)          ),        dI(1)        ),      dI(1)      ),    dC({`velCtrl=old(velCtrl)+-B()*t`}, 1) ; <(      dC({`velLead=old(velLead)+-B()*t`}, 1) ; <(        dC({`posCtrl=old(posCtrl)+old(velCtrl)*t-B()*t*t*0.5`}, 1) ; <(          dC({`posLead=old(posLead)+old(velLead)*t-B()*t*t*0.5`}, 1) ; <(            dC({`t>=0`}, 1) ; <(              dW(1) ; master,              dI(1)              ),            dI(1)            ),          dI(1)          ),        dI(1)        ),      dI(1)      )    )  )")*/
    val lab2Tac = BelleParser("""unfold ; <(
                                |  diffInvariant({`velCtrl=old(velCtrl)+A()*t`}, 1);
                                |  diffInvariant({`velLead=old(velLead)+A()*t`}, 1);
                                |  diffInvariant({`posCtrl=old(posCtrl)+old(velCtrl)*t+A()*t*t*0.5`}, 1);
                                |  diffInvariant({`posLead=old(posLead)+old(velLead)*t+A()*t*t*0.5`}, 1);
                                |  diffInvariant({`t>=0`}, 1);
                                |  dW(1); print({`Lead=A(), Follow=A()`}); master; print({`...done`})
                                |  ,
                                |  diffInvariant({`velCtrl=old(velCtrl)-B()*t`}, 1);
                                |  diffInvariant({`velLead=old(velLead)+A()*t`}, 1);
                                |  diffInvariant({`posCtrl=old(posCtrl)+old(velCtrl)*t-B()*t*t*0.5`}, 1);
                                |  diffInvariant({`posLead=old(posLead)+old(velLead)*t+A()*t*t*0.5`}, 1);
                                |  diffInvariant({`t>=0`}, 1);
                                |  dW(1); print({`Lead=A(), Follow=-B()`}); master; print({`...done`})
                                |  ,
                                |
                                |  diffInvariant({`velCtrl=old(velCtrl)+A()*t`}, 1);
                                |  diffInvariant({`velLead=old(velLead)-B()*t`}, 1);
                                |  diffInvariant({`posCtrl=old(posCtrl)+old(velCtrl)*t+A()*t*t*0.5`}, 1);
                                |  diffInvariant({`posLead=old(posLead)+old(velLead)*t-B()*t*t*0.5`}, 1);
                                |  diffInvariant({`t>=0`}, 1);
                                |  dWplus(1);
                                |  implyR(1);
                                |  print({`Transforming`});
                                |  transform(
                                |    {`(posLead_0-posCtrl_0)*2*B()>=velCtrl_0*velCtrl_0-velLead_0*velLead_0+(A()+B())*(A()*t*t+2*t*velCtrl_0)`},
                                |    'L=={`(posLead_0-posCtrl_0)*2*B()>=velCtrl_0*velCtrl_0-velLead_0*velLead_0+(A()+B())*(A()*T()*T()+2*T()*velCtrl_0)`}
                                |  );
                                |  print({`Lead=-B(), Follow=A()`}); master; print({`...done`})
                                |  ,
                                |  diffInvariant({`velCtrl=old(velCtrl)-B()*t`}, 1);
                                |  diffInvariant({`velLead=old(velLead)-B()*t`}, 1);
                                |  diffInvariant({`posCtrl=old(posCtrl)+old(velCtrl)*t-B()*t*t*0.5`}, 1);
                                |  diffInvariant({`posLead=old(posLead)+old(velLead)*t-B()*t*t*0.5`}, 1);
                                |  diffInvariant({`t>=0`}, 1);
                                |  dW(1); print({`Lead=-B(), Follow=-B()`}); master; print({`...done`})
                                |)""".stripMargin)
    val provable = ProvableSig.startPlainProof(lab2Fml)
    val tacticResult = proveBy(provable,lab2Tac)
    tacticResult match {
      case pr:TermProvable =>
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
        val conv = new IsabelleConverter(pr.pt)
        //val source = conv.scalaObjects("ProofTerm", "proofTerm", "GeneratedProofChecker")
        val source = conv.sexp
        val writer = new PrintWriter("lab2.pt")
        writer.write(source)
        writer.close()
      case _ => ()
    }
    println(tacticResult)
  })


  import pt.lib.Sum_Type._
  import pt.lib.Scratch._
  import pt.lib.Syntax._
  import pt.lib.Nat._
  import pt.lib.Int._
  import pt.lib.Rat._
  import pt.lib.Real._
  import pt.lib.Proof_Checker._
  import pt.lib.Parser._

  "sexp parser" should "parse ids" in {
    val (i1(), 2) = mv("i1",0)
    val (i3(), 4) = mv("  i3) ",2)
  }

  it should "parse unit" in {
    val ((), 5) = unit("   ()",3)
    val ((), 5) = unit("   ())",3)
  }

  it should "parse sums" in {
    val (Inl(i1()), _) = sum(mv,mv)(" (Inl i1)", 1)
    val (Inr(()), _) = sum(mv,unit)(" (Inr ())", 1)
  }

  it should "parse options" in {
    val (None, 5) = option(mv)(" None", 1)
    val (Some(i1()), 9) = option(mv)("(Some i1)", 0)
  }

  it should "parse axioms" in {
    val (AdConst(), 9) = axiom("(AdConst)",0)
  }

  it should "parse axRules" in {
    val (CE(), 4) = axrule("(CE)",0)
  }

  it should "parse nats" in {
    val(pt.lib.Nat.Nata(n), 10) = nat("(Nata 100)",0)
    n.intValue shouldBe 100
  }

  it should "parse ints" in {
    val(pt.lib.Int.int_of_integer(n1), _) = int("(int_of_integer 123)",0)
    val(pt.lib.Int.int_of_integer(n2), _) = int("(int_of_integer -123)",0)
    n1.intValue shouldBe 123
    n2.intValue shouldBe -123
  }

  it should "parse rats" in {
    val(Frct((int_of_integer(den),int_of_integer(num))),_) = rat("(Frct ((int_of_integer 2) (int_of_integer 1)))",0)
    den.intValue shouldBe 2
    num.intValue shouldBe 1
  }

  it should "parse reals" in {
    val(Ratreal(Frct((int_of_integer(den),int_of_integer(num)))),_) = real("(Ratreal (Frct ((int_of_integer 2) (int_of_integer 1))))",0)
    den.intValue shouldBe 2
    num.intValue shouldBe 1
  }

  it should "parse terms" in {
    val (Const(Ratreal(Frct((int_of_integer(den1),int_of_integer(num1))))),_) = trm(mv)("(Const (Ratreal (Frct ((int_of_integer 2) (int_of_integer 1)))))", 0)
    den1.intValue shouldBe 2
    num1.intValue shouldBe 1
    val(Const(Ratreal(Frct((int_of_integer(den2),int_of_integer(num2))))),_) = trm(mv)("z", 0)
    den2.intValue shouldBe 0
    num2.intValue shouldBe 1
    val(Const(Ratreal(Frct((int_of_integer(den3),int_of_integer(num3))))),_) = trm(mv)("zst", 0)
    den3.intValue shouldBe 0
    num3.intValue shouldBe 1
    val(Var(i1()),_) = trm(mv)("(Var i1)",0)
    val(DiffVar(i1()),_) = trm(mv)("(DiffVar i1)",0)
    val(Function(Inr(i1()),emp),_) = trm(sum(mv,mv))("(Function (Inr i1) est)",0)
    enum_myvarsa.foreach(i => (emp(i) shouldBe Const(Ratreal(Frct((int_of_integer(0),int_of_integer(1)))))))
    val(Functional(Inr(i1())),_) = trm(sum(mv,mv))("(Functional (Inr i1))",0)
    val(Plus(Var(i1()),Var(i2())),_) = trm(mv)("(Plus (Var i1) (Var i2))",0)
    val(Times(Var(i1()),Var(i2())),_) = trm(mv)("(Times (Var i1) (Var i2))",0)
    val(Differential(Times(Var(i1()),Var(i2()))),_) = trm(mv)("(Differential (Times (Var i1) (Var i2)))",0)
  }

  it should "parse odes" in {
    val(OSing(i5(),Var(i4())),_) = ode(mv)("(OSing i5 (Var i4))",0)
    val(OProd(OSing(i4(),Function(i4(),emp)),OSing(i5(),Var(i4()))),_) = ode(mv)("(OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4)))",0)
    val(OVar(i1),_) = ode(mv)("(OVar i1)",0)
  }

  it should "parse formulas" in {
    val(Geq(_,_),_) = formula(mv,mv)("(Geq z z)",0)
    val(InContext(i2(),Geq(_,_)),_) = formula(mv,mv)("(InContext i2 (Geq z z))",0)
    val(Diamond(EvolveODE(OProd(OSing(i5(),Var(i4())),OSing(i4(),Function(i4(),_))),Geq(_,_)),Not(Not(Diamond(DiffAssign(i4(),Function(i4(),_)),Not(Geq(DiffVar(i4()),_)))))),_) =
      formula(mv,mv)("(Diamond (EvolveODE (OProd (OSing i5 (Var i4)) (OSing i4 (Function i4 e))) (Geq z z)) (Not (Not (Diamond (DiffAssign i4 (Function i4 e)) (Not (Geq (DiffVar i4) z))))))",0)
    val(Prop(i1(),args),_) = formula(mv,mv)("(Prop i1 (s (Function i1 e)))",0)
    args(i1()) match {case (Function(i1(),emp)) => enum_myvarsa.foreach(i => (if(true) {emp(i) shouldBe Const(Ratreal(Frct((int_of_integer(0),int_of_integer(1)))))}))}
    //"(Not (And (Not (And (Not (Diamond (EvolveODE (OProd (OSing i5 (Var i4)) (OSing i4 (Function i4 e))) (Geq z z)) (Not (Not (Diamond (DiffAssign i4 (Function i4 e)) (Not (Geq (DiffVar i4) z))))))) (Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Geq (DiffVar i4) z)))))) (Not (And (Not (Not (Diamond (EvolveODE (OProd (OSing i5 (Var i4)) (OSing i4 (Function i4 e))) (Geq z z)) (Not (Not (Diamond (DiffAssign i4 (Function i4 e)) (Not (Geq (DiffVar i4) z)))))))) (Not (Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Geq (DiffVar i4) z)))))))))"
  }

  it should "parse hps" in {
    val(EvolveODE(OProd(OSing(i5(),Var(i4())),OSing(i4(),Function(i4(),_))),Geq(_,_)),_) =
      hp(mv,mv)("(EvolveODE (OProd (OSing i5 (Var i4)) (OSing i4 (Function i4 e))) (Geq z z))",0)
    val(Pvar(i1()),_) = hp(mv,mv)("(Pvar i1)",0)
    val(Assign(i2(),Plus(Var(i1()),Var(i2()))),_) = hp(mv,mv)("(Assign i2 (Plus (Var i1) (Var i2)))",0)
    val(DiffAssign(i2(),Times(Var(i1()),Var(i2()))),_) = hp(mv,mv)("(DiffAssign i2 (Times (Var i1) (Var i2)))",0)
    val(Test(Geq(_,_)),_) = hp(mv,mv)("(Test (Geq z z))",0)
    val(Choice(Test(Geq(_,_)),Test(Geq(_,_))),_) = hp(mv,mv)("(Choice (Test (Geq z z)) (Test (Geq z z)))",0)
    val(Sequence(Test(Geq(_,_)),Test(Geq(_,_))),_) = hp(mv,mv)("(Sequence (Test (Geq z z)) (Test (Geq z z)))",0)
    val(Loop(Test(Geq(_,_))),_) = hp(mv,mv)("(Loop (Test (Geq z z)))",0)
  }

  it should "parse sequents" in {
    val((a,s),_) = sequent("(() ((Not (And (Not (And (Prop i1 (s (Function i1 e))) (Not (Diamond (DiffAssign i1 (Function i1 e)) (Not (Prop i1 (s (DiffVar i1)))))))) (Not (And (Not (Prop i1 (s (Function i1 e)))) (Not (Not (Diamond (DiffAssign i1 (Function i1 e)) (Not (Prop i1 (s (DiffVar i1)))))))))))))",0)
    a.length shouldBe 0
    s.length shouldBe 1
  }

  it should "parse substs" in {
    val(pt.lib.USubst.subst_exta(fun,funl,pred,con,prog,ode,_),_) = subst("(subst_exta ((Some (Var i4)) None None None None None None None None None None) ns ((Some (Not (Diamond (DiffAssign i4 (Function (Inl i4) est)) (Not (Geq (DiffVar i4) zst))))) None None None None None None None None None None) ns ns ns)", 0)
    fun(i1()) shouldBe Some(Var(i4()))
    fun(i2()) shouldBe None
    (pred(i1()) match {case Some (Not (Diamond (DiffAssign(i4(),Function(Inl(i4()),_)),Not(Geq(DiffVar(i4),_))))) => true case _ => false}) shouldBe true
  }

  it should "parse pts" in {
    val cpp = "(Sub (Sub (RuleApp (RuleApp (Sub (Sub (RuleApp (RuleApp (RuleApp (Start (() ((Not (And (Not (Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Geq (Var i4) z))))) (Not (Not (And (Geq (Function i4 e) z) (Geq (Var i4) z))))))))) (Rrule (ImplyR) (Nata 0)) (Nata 0)) (Lrule (AndL) (Nata 0)) (Nata 0)) (Rrule (CutRight (Not (And (Not (And (Geq (Var i4) z) (Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Geq (Differential (Var i4)) (Differential z))))))) (Not (Not (Geq z z)))))) (Nata 0)) (Nata 0)) (Start (((Geq (Function i4 e) z) (Geq (Var i4) z)) ((Not (And (Not (And (Geq (Var i4) z) (Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Geq (Differential (Var i4)) (Differential z))))))) (Not (Not (Geq z z)))))))) (Nata 0)) (Sub (Sub (Sub (RuleApp (RuleApp (Start (((Geq (Function i4 e) z) (Geq (Var i4) z)) ((Not (And (Not (Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Geq (Var i4) z))))) (Not (Not (Not (And (Not (And (Geq (Var i4) z) (Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Geq (Differential (Var i4)) (Differential z))))))) (Not (Not (Geq z z)))))))))))) (Rrule (CohideRR) (Nata 0)) (Nata 0)) (Rrule (ImplyR) (Nata 0)) (Nata 0)) (Start (((Not (And (Not (And (Geq (Var i4) z) (Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Geq (Differential (Var i4)) (Differential z))))))) (Not (Not (Geq z z)))))) ((Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Geq (Var i4) z))))))) (Nata 0)) (Sub (RuleApp (RuleApp (RuleApp (Start (((Not (And (Not (And (Geq (Var i4) z) (Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Geq (Differential (Var i4)) (Differential z))))))) (Not (Not (Geq z z)))))) ((Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Geq (Var i4) z))))))) (Rrule (CutRight (Not (And (Not (And (Geq (Var i4) z) (Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Geq (Differential (Var i4)) (Differential z))))))) (Not (Not (Geq z z)))))) (Nata 0)) (Nata 0)) (CloseId (Nata 0) (Nata 0)) (Nata 0)) (Lrule (HideL) (Nata 0)) (Nata 0)) (Start (() ((Not (And (Not (Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Geq (Var i4) z))))) (Not (Not (Not (And (Not (And (Geq (Var i4) z) (Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Geq (Differential (Var i4)) (Differential z))))))) (Not (Not (Geq z z)))))))))))) (Nata 0)) (Nata 0)) (PrUSubst (Ax (ADIGeq)) (subst_exta ns ((Some (Var i4)) (Some z) None None None None None None None None None) ns (None (Some (Geq z z)) None None None None None None None None None) ns ((Some (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4)))) None None None None None None None None None None))) (Nata 0)) (Nata 1)) (Rrule (ImplyR) (Nata 0)) (Nata 0)) (Rrule (AndR) (Nata 0)) (Nata 0)) (RuleApp (Start (((Geq (Function i4 e) z) (Geq (Var i4) z) (Geq z z)) ((Geq (Var i4) z)))) (CloseId (Nata 1) (Nata 0)) (Nata 0)) (Nata 0)) (RuleApp (Sub (Sub (Sub (Sub (RuleApp (Sub (Sub (RuleApp (Sub (Sub (RuleApp (Sub (Sub (RuleApp (Sub (Sub (RuleApp (Sub (Sub (RuleApp (Start (((Geq (Function i4 e) z) (Geq (Var i4) z) (Geq z z)) ((Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Geq (Differential (Var i4)) (Differential z)))))))) (Rrule (CutRight (Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Geq (DiffVar i4) z))))) (Nata 0)) (Nata 0)) (Start (((Geq (Function i4 e) z) (Geq (Var i4) z) (Geq z z)) ((Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Geq (DiffVar i4) z))))))) (Nata 0)) (Sub (Sub (RuleApp (RuleApp (Start (((Geq (Function i4 e) z) (Geq (Var i4) z) (Geq z z)) ((Not (And (Not (Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Geq (Differential (Var i4)) (Differential z)))))) (Not (Not (Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Geq (DiffVar i4) z))))))))))) (Rrule (CohideRR) (Nata 0)) (Nata 0)) (Rrule (EquivifyR) (Nata 0)) (Nata 0)) (PrUSubst (AxRule (CE)) (subst_exta ns ns ns ((Some (Geq (DiffVar i4) z)) (Some (Geq (Differential (Var i4)) (Differential z))) (Some (Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (InContext (Inr ()) (Geq z z)))))) None None None None None None None None) ns ns)) (Nata 0)) (Sub (Sub (RuleApp (Start (() ((Not (And (Not (And (Geq (DiffVar i4) z) (Geq (Differential (Var i4)) (Differential z)))) (Not (And (Not (Geq (DiffVar i4) z)) (Not (Geq (Differential (Var i4)) (Differential z)))))))))) (Rrule (CutRight (Not (And (Not (And (Geq (DiffVar i4) (Differential z)) (Geq (Differential (Var i4)) (Differential z)))) (Not (And (Not (Geq (DiffVar i4) (Differential z))) (Not (Geq (Differential (Var i4)) (Differential z)))))))) (Nata 0)) (Nata 0)) (FNC (FNC (Pro (PrUSubst (Ax (AdConst)) (subst_exta ((Some zst) None None None None None None None None None None) ns ns ns ns ns)) (PrUSubst (AxRule (CQ)) (subst_exta ns ((Some (Differential z)) (Some z) None None None None None None None None None) (None None (Some (Not (And (Not (And (Geq (DiffVar i4) (Function (Inr i1) est)) (Geq (Differential (Var i4)) (Differential zst)))) (Not (And (Not (Geq (DiffVar i4) (Function (Inr i1) est))) (Not (Geq (Differential (Var i4)) (Differential zst)))))))) None None None None None None None None) ns ns ns))) (() ((Not (And (Not (Not (And (Not (And (Geq (DiffVar i4) z) (Geq (Differential (Var i4)) (Differential z)))) (Not (And (Not (Geq (DiffVar i4) z)) (Not (Geq (Differential (Var i4)) (Differential z)))))))) (Not (Not (Not (And (Not (And (Geq (DiffVar i4) (Differential z)) (Geq (Differential (Var i4)) (Differential z)))) (Not (And (Not (Geq (DiffVar i4) (Differential z))) (Not (Geq (Differential (Var i4)) (Differential z))))))))))))) (Rrule (EquivifyR) (Nata 0))) (() ((Not (And (Not (Not (And (Not (And (Geq (DiffVar i4) z) (Geq (Differential (Var i4)) (Differential z)))) (Not (And (Not (Geq (DiffVar i4) z)) (Not (Geq (Differential (Var i4)) (Differential z)))))))) (Not (Not (Not (And (Not (And (Geq (DiffVar i4) (Differential z)) (Geq (Differential (Var i4)) (Differential z)))) (Not (And (Not (Geq (DiffVar i4) (Differential z))) (Not (Geq (Differential (Var i4)) (Differential z))))))))))))) (Rrule (CohideRR) (Nata 0))) (Nata 1)) (Sub (Sub (RuleApp (Start (() ((Not (And (Not (And (Geq (DiffVar i4) (Differential z)) (Geq (Differential (Var i4)) (Differential z)))) (Not (And (Not (Geq (DiffVar i4) (Differential z))) (Not (Geq (Differential (Var i4)) (Differential z)))))))))) (Rrule (CutRight (Not (And (Not (And (Geq (Differential (Var i4)) (Differential z)) (Geq (Differential (Var i4)) (Differential z)))) (Not (And (Not (Geq (Differential (Var i4)) (Differential z))) (Not (Geq (Differential (Var i4)) (Differential z)))))))) (Nata 0)) (Nata 0)) (FNC (FNC (Pro (FNC (PrUSubst (Ax (Advar)) (subst_exta ns ns ns ns ns ns)) (() ((And (Geq (Differential (Var i4)) (DiffVar i4)) (Geq (DiffVar i4) (Differential (Var i4)))))) (URename i1 i4)) (PrUSubst (AxRule (CQ)) (subst_exta ns ((Some (Differential (Var i4))) (Some (DiffVar i4)) None None None None None None None None None) (None None (Some (Not (And (Not (And (Geq (Function (Inr i1) est) (Differential zst)) (Geq (Differential (Var i4)) (Differential zst)))) (Not (And (Not (Geq (Function (Inr i1) est) (Differential zst))) (Not (Geq (Differential (Var i4)) (Differential zst)))))))) None None None None None None None None) ns ns ns))) (() ((Not (And (Not (Not (And (Not (And (Geq (DiffVar i4) (Differential z)) (Geq (Differential (Var i4)) (Differential z)))) (Not (And (Not (Geq (DiffVar i4) (Differential z))) (Not (Geq (Differential (Var i4)) (Differential z)))))))) (Not (Not (Not (And (Not (And (Geq (Differential (Var i4)) (Differential z)) (Geq (Differential (Var i4)) (Differential z)))) (Not (And (Not (Geq (Differential (Var i4)) (Differential z))) (Not (Geq (Differential (Var i4)) (Differential z))))))))))))) (Rrule (EquivifyR) (Nata 0))) (() ((Not (And (Not (Not (And (Not (And (Geq (DiffVar i4) (Differential z)) (Geq (Differential (Var i4)) (Differential z)))) (Not (And (Not (Geq (DiffVar i4) (Differential z))) (Not (Geq (Differential (Var i4)) (Differential z)))))))) (Not (Not (Not (And (Not (And (Geq (Differential (Var i4)) (Differential z)) (Geq (Differential (Var i4)) (Differential z)))) (Not (And (Not (Geq (Differential (Var i4)) (Differential z))) (Not (Geq (Differential (Var i4)) (Differential z))))))))))))) (Rrule (CohideRR) (Nata 0))) (Nata 1)) (Sub (Start (() ((Not (And (Not (And (Geq (Differential (Var i4)) (Differential z)) (Geq (Differential (Var i4)) (Differential z)))) (Not (And (Not (Geq (Differential (Var i4)) (Differential z))) (Not (Geq (Differential (Var i4)) (Differential z)))))))))) (PrUSubst (Ax (AEquivReflexive)) (subst_exta ns ns ((Some (Geq (Differential (Var i4)) (Differential zst))) None None None None None None None None None None) ns ns ns)) (Nata 0)) (Nata 0)) (Nata 0)) (Nata 0)) (Nata 1)) (Rrule (CutRight (Not (Diamond (EvolveODE (OProd (OSing i5 (Var i4)) (OSing i4 (Function i4 e))) (Geq z z)) (Not (Not (Diamond (DiffAssign i4 (Function i4 e)) (Not (Geq (DiffVar i4) z)))))))) (Nata 0)) (Nata 0)) (Start (((Geq (Function i4 e) z) (Geq (Var i4) z) (Geq z z)) ((Not (Diamond (EvolveODE (OProd (OSing i5 (Var i4)) (OSing i4 (Function i4 e))) (Geq z z)) (Not (Not (Diamond (DiffAssign i4 (Function i4 e)) (Not (Geq (DiffVar i4) z)))))))))) (Nata 0)) (Sub (RuleApp (RuleApp (Start (((Geq (Function i4 e) z) (Geq (Var i4) z) (Geq z z)) ((Not (And (Not (Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Geq (DiffVar i4) z))))) (Not (Not (Not (Diamond (EvolveODE (OProd (OSing i5 (Var i4)) (OSing i4 (Function i4 e))) (Geq z z)) (Not (Not (Diamond (DiffAssign i4 (Function i4 e)) (Not (Geq (DiffVar i4) z)))))))))))))) (Rrule (CohideRR) (Nata 0)) (Nata 0)) (Rrule (EquivifyR) (Nata 0)) (Nata 0)) (FNC (PrUSubst (Sub (RuleApp (Start (() ((Not (And (Not (And (Not (Diamond (EvolveODE (OProd (OVar i1) (OSing i1 (Functional i1))) (InContext i2 (Geq z z))) (Not (Not (Diamond (DiffAssign i1 (Functional i1)) (Not (InContext i1 (Geq z z)))))))) (Not (Diamond (EvolveODE (OProd (OSing i1 (Functional i1)) (OVar i1)) (InContext i2 (Geq z z))) (Not (InContext i1 (Geq z z))))))) (Not (And (Not (Not (Diamond (EvolveODE (OProd (OVar i1) (OSing i1 (Functional i1))) (InContext i2 (Geq z z))) (Not (Not (Diamond (DiffAssign i1 (Functional i1)) (Not (InContext i1 (Geq z z))))))))) (Not (Not (Diamond (EvolveODE (OProd (OSing i1 (Functional i1)) (OVar i1)) (InContext i2 (Geq z z))) (Not (InContext i1 (Geq z z))))))))))))) (Rrule (CommuteEquivR) (Nata 0)) (Nata 0)) (Ax (ADiffEffectSys)) (Nata 0)) (subst_exta ns ((Some (Function i4 e)) None None None None None None None None None None) ns ((Some (Geq (DiffVar i1) z)) (Some (Geq z z)) None None None None None None None None None) ns ((Some (OSing i5 (Var i1))) None None None None None None None None None None))) (() ((Not (And (Not (And (Not (Diamond (EvolveODE (OProd (OSing i5 (Var i4)) (OSing i4 (Function i4 e))) (Geq z z)) (Not (Not (Diamond (DiffAssign i4 (Function i4 e)) (Not (Geq (DiffVar i4) z))))))) (Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Geq (DiffVar i4) z)))))) (Not (And (Not (Not (Diamond (EvolveODE (OProd (OSing i5 (Var i4)) (OSing i4 (Function i4 e))) (Geq z z)) (Not (Not (Diamond (DiffAssign i4 (Function i4 e)) (Not (Geq (DiffVar i4) z)))))))) (Not (Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Geq (DiffVar i4) z))))))))))) (URename i1 i4)) (Nata 0)) (Nata 1)) (Rrule (CutRight (Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Not (Diamond (DiffAssign i5 (Var i4)) (Not (Not (Diamond (DiffAssign i4 (Function i4 e)) (Not (Geq (DiffVar i4) z))))))))))) (Nata 0)) (Nata 0)) (Start (((Geq (Function i4 e) z) (Geq (Var i4) z) (Geq z z)) ((Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Not (Diamond (DiffAssign i5 (Var i4)) (Not (Not (Diamond (DiffAssign i4 (Function i4 e)) (Not (Geq (DiffVar i4) z))))))))))))) (Nata 0)) (Sub (RuleApp (RuleApp (Start (((Geq (Function i4 e) z) (Geq (Var i4) z) (Geq z z)) ((Not (And (Not (Not (Diamond (EvolveODE (OProd (OSing i5 (Var i4)) (OSing i4 (Function i4 e))) (Geq z z)) (Not (Not (Diamond (DiffAssign i4 (Function i4 e)) (Not (Geq (DiffVar i4) z)))))))) (Not (Not (Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Not (Diamond (DiffAssign i5 (Var i4)) (Not (Not (Diamond (DiffAssign i4 (Function i4 e)) (Not (Geq (DiffVar i4) z))))))))))))))))) (Rrule (CohideRR) (Nata 0)) (Nata 0)) (Rrule (EquivifyR) (Nata 0)) (Nata 0)) (FNC (PrUSubst (Sub (RuleApp (Start (() ((Not (And (Not (And (Not (Diamond (EvolveODE (OProd (OVar i1) (OSing i1 (Functional i1))) (InContext i2 (Geq z z))) (Not (Not (Diamond (DiffAssign i1 (Functional i1)) (Not (InContext i1 (Geq z z)))))))) (Not (Diamond (EvolveODE (OProd (OSing i1 (Functional i1)) (OVar i1)) (InContext i2 (Geq z z))) (Not (InContext i1 (Geq z z))))))) (Not (And (Not (Not (Diamond (EvolveODE (OProd (OVar i1) (OSing i1 (Functional i1))) (InContext i2 (Geq z z))) (Not (Not (Diamond (DiffAssign i1 (Functional i1)) (Not (InContext i1 (Geq z z))))))))) (Not (Not (Diamond (EvolveODE (OProd (OSing i1 (Functional i1)) (OVar i1)) (InContext i2 (Geq z z))) (Not (InContext i1 (Geq z z))))))))))))) (Rrule (CommuteEquivR) (Nata 0)) (Nata 0)) (Ax (ADiffEffectSys)) (Nata 0)) (subst_exta ns ((Some (Var i4)) None None None None None None None None None None) ns ((Some (Not (Diamond (DiffAssign i4 (Function i4 e)) (Not (Geq (DiffVar i4) z))))) (Some (Geq z z)) None None None None None None None None None) ns ((Some (OSing i4 (Function i4 e))) None None None None None None None None None None))) (() ((Not (And (Not (And (Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Not (Diamond (DiffAssign i5 (Var i4)) (Not (Not (Diamond (DiffAssign i4 (Function i4 e)) (Not (Geq (DiffVar i4) z)))))))))) (Not (Diamond (EvolveODE (OProd (OSing i5 (Var i4)) (OSing i4 (Function i4 e))) (Geq z z)) (Not (Not (Diamond (DiffAssign i4 (Function i4 e)) (Not (Geq (DiffVar i4) z))))))))) (Not (And (Not (Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Not (Diamond (DiffAssign i5 (Var i4)) (Not (Not (Diamond (DiffAssign i4 (Function i4 e)) (Not (Geq (DiffVar i4) z))))))))))) (Not (Not (Diamond (EvolveODE (OProd (OSing i5 (Var i4)) (OSing i4 (Function i4 e))) (Geq z z)) (Not (Not (Diamond (DiffAssign i4 (Function i4 e)) (Not (Geq (DiffVar i4) z)))))))))))))) (URename i1 i5)) (Nata 0)) (Nata 1)) (Rrule (CutRight (Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Not (Diamond (DiffAssign i4 (Function i4 e)) (Not (Geq (DiffVar i4) z)))))))) (Nata 0)) (Nata 0)) (Start (((Geq (Function i4 e) z) (Geq (Var i4) z) (Geq z z)) ((Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Not (Diamond (DiffAssign i4 (Function i4 e)) (Not (Geq (DiffVar i4) z)))))))))) (Nata 0)) (Sub (Sub (RuleApp (RuleApp (Start (((Geq (Function i4 e) z) (Geq (Var i4) z) (Geq z z)) ((Not (And (Not (Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Not (Diamond (DiffAssign i5 (Var i4)) (Not (Not (Diamond (DiffAssign i4 (Function i4 e)) (Not (Geq (DiffVar i4) z))))))))))) (Not (Not (Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Not (Diamond (DiffAssign i4 (Function i4 e)) (Not (Geq (DiffVar i4) z)))))))))))))) (Rrule (CohideRR) (Nata 0)) (Nata 0)) (Rrule (EquivifyR) (Nata 0)) (Nata 0)) (PrUSubst (AxRule (CE)) (subst_exta ns ns ns ((Some (Not (Diamond (DiffAssign i4 (Function i4 e)) (Not (Geq (DiffVar i4) z))))) (Some (Not (Diamond (DiffAssign i5 (Var i4)) (Not (Not (Diamond (DiffAssign i4 (Function i4 e)) (Not (Geq (DiffVar i4) z)))))))) (Some (Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (InContext (Inr ()) (Geq z z)))))) None None None None None None None None) ns ns)) (Nata 0)) (FNC (PrUSubst (Sub (RuleApp (Start (() ((Not (And (Not (And (Prop i1 (s (Function i1 e))) (Not (Diamond (DiffAssign i1 (Function i1 e)) (Not (Prop i1 (s (DiffVar i1)))))))) (Not (And (Not (Prop i1 (s (Function i1 e)))) (Not (Not (Diamond (DiffAssign i1 (Function i1 e)) (Not (Prop i1 (s (DiffVar i1)))))))))))))) (Rrule (CommuteEquivR) (Nata 0)) (Nata 0)) (Ax (Adassign)) (Nata 0)) (subst_exta ((Some (Var i4)) None None None None None None None None None None) ns ((Some (Not (Diamond (DiffAssign i4 (Function (Inl i4) est)) (Not (Geq (DiffVar i4) zst))))) None None None None None None None None None None) ns ns ns)) (() ((Not (And (Not (And (Not (Diamond (DiffAssign i4 (Function i4 e)) (Not (Geq (DiffVar i4) z)))) (Not (Diamond (DiffAssign i5 (Var i4)) (Not (Not (Diamond (DiffAssign i4 (Function i4 e)) (Not (Geq (DiffVar i4) z))))))))) (Not (And (Not (Not (Diamond (DiffAssign i4 (Function i4 e)) (Not (Geq (DiffVar i4) z))))) (Not (Not (Diamond (DiffAssign i5 (Var i4)) (Not (Not (Diamond (DiffAssign i4 (Function i4 e)) (Not (Geq (DiffVar i4) z)))))))))))))) (URename i1 i5)) (Nata 0)) (Nata 1)) (Rrule (CutRight (Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Geq (Function i4 e) z))))) (Nata 0)) (Nata 0)) (Start (((Geq (Function i4 e) z) (Geq (Var i4) z) (Geq z z)) ((Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Geq (Function i4 e) z))))))) (Nata 0)) (Sub (Sub (RuleApp (RuleApp (Start (((Geq (Function i4 e) z) (Geq (Var i4) z) (Geq z z)) ((Not (And (Not (Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Not (Diamond (DiffAssign i4 (Function i4 e)) (Not (Geq (DiffVar i4) z)))))))) (Not (Not (Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Geq (Function i4 e) z))))))))))) (Rrule (CohideRR) (Nata 0)) (Nata 0)) (Rrule (EquivifyR) (Nata 0)) (Nata 0)) (PrUSubst (AxRule (CE)) (subst_exta ns ns ns ((Some (Geq (Function i4 e) z)) (Some (Not (Diamond (DiffAssign i4 (Function i4 e)) (Not (Geq (DiffVar i4) z))))) (Some (Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (InContext (Inr ()) (Geq z z)))))) None None None None None None None None) ns ns)) (Nata 0)) (FNC (PrUSubst (Sub (RuleApp (Start (() ((Not (And (Not (And (Prop i1 (s (Function i1 e))) (Not (Diamond (DiffAssign i1 (Function i1 e)) (Not (Prop i1 (s (DiffVar i1)))))))) (Not (And (Not (Prop i1 (s (Function i1 e)))) (Not (Not (Diamond (DiffAssign i1 (Function i1 e)) (Not (Prop i1 (s (DiffVar i1)))))))))))))) (Rrule (CommuteEquivR) (Nata 0)) (Nata 0)) (Ax (Adassign)) (Nata 0)) (subst_exta ((Some (Function (Inl i4) est)) None None None None None None None None None None) ns ((Some (Geq (Function (Inr i1) est) zst)) None None None None None None None None None None) ns ns ns)) (() ((Not (And (Not (And (Geq (Function i4 e) z) (Not (Diamond (DiffAssign i4 (Function i4 e)) (Not (Geq (DiffVar i4) z)))))) (Not (And (Not (Geq (Function i4 e) z)) (Not (Not (Diamond (DiffAssign i4 (Function i4 e)) (Not (Geq (DiffVar i4) z))))))))))) (URename i1 i4)) (Nata 0)) (Nata 1)) (Cut (Not (And (Not (Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Geq (Function i4 e) z))))) (Not (Not (Geq (Function i4 e) z)))))) (Nata 0)) (Start (((Geq (Function i4 e) z) (Geq (Var i4) z) (Geq z z) (Not (And (Not (Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Geq (Function i4 e) z))))) (Not (Not (Geq (Function i4 e) z)))))) ((Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Geq (Function i4 e) z))))))) (Nata 0)) (Start (((Geq (Function i4 e) z) (Geq (Var i4) z) (Geq z z)) ((Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Geq (Function i4 e) z)))) (Not (And (Not (Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Geq (Function i4 e) z))))) (Not (Not (Geq (Function i4 e) z)))))))) (Nata 1)) (Sub (Sub (RuleApp (Start (((Geq (Function i4 e) z) (Geq (Var i4) z) (Geq z z) (Not (And (Not (Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Geq (Function i4 e) z))))) (Not (Not (Geq (Function i4 e) z)))))) ((Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Geq (Function i4 e) z))))))) (Lrule (ImplyL) (Nata 3)) (Nata 0)) (RuleApp (Start (((Geq (Function i4 e) z) (Geq (Var i4) z) (Geq z z)) ((Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Geq (Function i4 e) z)))) (Geq (Function i4 e) z)))) (Rrule (HideR) (Nata 0)) (Nata 0)) (Nata 0)) (RuleApp (Start (((Geq (Function i4 e) z) (Geq (Var i4) z) (Geq z z) (Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Geq (Function i4 e) z))))) ((Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Geq (Function i4 e) z))))))) (CloseId (Nata 3) (Nata 0)) (Nata 0)) (Nata 1)) (Nata 0)) (RuleApp (Sub (Sub (Sub (Sub (RuleApp (RuleApp (Sub (Sub (RuleApp (RuleApp (Start (((Geq (Function i4 e) z) (Geq (Var i4) z) (Geq z z)) ((Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Geq (Function i4 e) z)))) (Not (And (Not (Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Geq (Function i4 e) z))))) (Not (Not (Geq (Function i4 e) z)))))))) (Rrule (CohideRR) (Nata 1)) (Nata 0)) (Rrule (ImplyR) (Nata 0)) (Nata 0)) (Start (((Geq (Function i4 e) z)) ((Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Geq (Function i4 e) z))))))) (Nata 0)) (Sub (RuleApp (RuleApp (RuleApp (Start (((Geq (Function i4 e) z)) ((Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Geq (Function i4 e) z))))))) (Rrule (CutRight (Geq (Function i4 e) z)) (Nata 0)) (Nata 0)) (CloseId (Nata 0) (Nata 0)) (Nata 0)) (Lrule (HideL) (Nata 0)) (Nata 0)) (Start (() ((Not (And (Not (Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Geq (Function i4 e) z))))) (Not (Not (Geq (Function i4 e) z)))))))) (Nata 0)) (Nata 0)) (Rrule (ImplyR) (Nata 0)) (Nata 0)) (Cut (Not (And (Not (Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Geq (Function i4 e) z))))) (Not (Not (Geq (Function i4 e) z)))))) (Nata 0)) (Start (((Geq (Function i4 e) z) (Not (And (Not (Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Geq (Function i4 e) z))))) (Not (Not (Geq (Function i4 e) z)))))) ((Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Geq (Function i4 e) z))))))) (Nata 0)) (Start (((Geq (Function i4 e) z)) ((Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Geq (Function i4 e) z)))) (Not (And (Not (Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Geq (Function i4 e) z))))) (Not (Not (Geq (Function i4 e) z)))))))) (Nata 1)) (Sub (Sub (RuleApp (Start (((Geq (Function i4 e) z) (Not (And (Not (Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Geq (Function i4 e) z))))) (Not (Not (Geq (Function i4 e) z)))))) ((Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Geq (Function i4 e) z))))))) (Lrule (ImplyL) (Nata 1)) (Nata 0)) (RuleApp (Start (((Geq (Function i4 e) z)) ((Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Geq (Function i4 e) z)))) (Geq (Function i4 e) z)))) (Rrule (HideR) (Nata 0)) (Nata 0)) (Nata 0)) (RuleApp (Sub (RuleApp (Start (((Geq (Function i4 e) z) (Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Geq (Function i4 e) z))))) ((Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Geq (Function i4 e) z))))))) (Cohide2 (Nata 1) (Nata 0)) (Nata 0)) (PrUSubst (AxRule (monb)) (subst_exta ns ns ns ((Some (Geq (Function i4 e) z)) (Some (Geq (Function i4 e) z)) None None None None None None None None None) ((Some (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z))) None None None None None None None None None None) ns)) (Nata 0)) (CloseId (Nata 0) (Nata 0)) (Nata 0)) (Nata 1)) (Nata 0)) (RuleApp (Sub (Sub (RuleApp (RuleApp (RuleApp (Start (((Geq (Function i4 e) z)) ((Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Geq (Function i4 e) z)))) (Not (And (Not (Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Geq (Function i4 e) z))))) (Not (Not (Geq (Function i4 e) z)))))))) (Rrule (HideR) (Nata 0)) (Nata 0)) (Rrule (ImplyR) (Nata 0)) (Nata 0)) (Rrule (CutRight (Geq (Function i4 e) z)) (Nata 0)) (Nata 0)) (Start (((Geq (Function i4 e) z) (Geq (Function i4 e) z)) ((Geq (Function i4 e) z)))) (Nata 0)) (Sub (Sub (Sub (RuleApp (RuleApp (Start (((Geq (Function i4 e) z) (Geq (Function i4 e) z)) ((Not (And (Not (Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Geq (Function i4 e) z))))) (Not (Not (Geq (Function i4 e) z)))))))) (Rrule (CohideRR) (Nata 0)) (Nata 0)) (Rrule (ImplyR) (Nata 0)) (Nata 0)) (Start (((Geq (Function i4 e) z)) ((Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Geq (Function i4 e) z))))))) (Nata 0)) (Sub (RuleApp (RuleApp (RuleApp (Start (((Geq (Function i4 e) z)) ((Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Geq (Function i4 e) z))))))) (Rrule (CutRight (Geq (Function i4 e) z)) (Nata 0)) (Nata 0)) (CloseId (Nata 0) (Nata 0)) (Nata 0)) (Lrule (HideL) (Nata 0)) (Nata 0)) (Start (() ((Not (And (Not (Not (Diamond (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z)) (Not (Geq (Function i4 e) z))))) (Not (Not (Geq (Function i4 e) z)))))))) (Nata 0)) (Nata 0)) (PrUSubst (Ax (AV)) (subst_exta ns ns ((Some (Geq (Function (Inl i4) est) zst)) None None None None None None None None None None) ns ((Some (EvolveODE (OProd (OSing i4 (Function i4 e)) (OSing i5 (Var i4))) (Geq z z))) None None None None None None None None None None) ns)) (Nata 0)) (Nata 1)) (CloseId (Nata 1) (Nata 0)) (Nata 0)) (Nata 1)) (CloseId (Nata 0) (Nata 0)) (Nata 0)) (Nata 1)) (CloseId (Nata 0) (Nata 0)) (Nata 0)) (Nata 0))"
    val start = System.currentTimeMillis()
    val (_,_) = proofTerm(cpp,0)
    val end = System.currentTimeMillis()
    println("Time taken(seconds): "+ (end-start)/1000.0)
  }
/*
  it should "parse velocityCar" in {
    val path = "/usr0/home/bbohrer/KeYmaeraX/velocityCar.pt"
    val str = Source.fromFile(path).mkString
    val start = System.currentTimeMillis()
    val (_,_) = proofTerm(str,0)
    val end = System.currentTimeMillis()
    println("Time taken(seconds): "+ (end-start)/1000.0)

  }*/
}
