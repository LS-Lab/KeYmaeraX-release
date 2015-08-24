/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tactics.Tactics.ApplyRule
import edu.cmu.cs.ls.keymaerax.tactics._
import edu.cmu.cs.ls.keymaerax.tactics.TacticLibrary.debugT
import edu.cmu.cs.ls.keymaerax.tactics.TactixLibrary.{assignb, closeId, composeb, cut, ls, onBranch}
import edu.cmu.cs.ls.keymaerax.tactics.BranchLabels._
import edu.cmu.cs.ls.keymaerax.tools.{ToolEvidence, Tool, Mathematica}
import testHelper.ProvabilityTestHelper

import org.scalatest.{BeforeAndAfterEach, Matchers, FlatSpec}

import scala.collection.immutable

/**
 * Created by smitsch on 3/5/15.
 * @author Stefan Mitsch
 */
class LemmaTests extends FlatSpec with Matchers with BeforeAndAfterEach {
  val helper = new ProvabilityTestHelper((x) => println(x))
  val mathematicaConfig: Map[String, String] = helper.mathematicaConfig
  var math: Tool with QETool = null

  override def beforeEach() = {
    math = new Mathematica
    math.init(mathematicaConfig)
    PrettyPrinter.setPrinter(edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter)
  }

  override def afterEach() = {
    math.shutdown()
    math = null
  }

  "Tactics (Lemma)" should "learn a lemma from (x > 0 & y > x) -> x >= 0" in {
    val f = TacticLibrary.universalClosure("(x > 0 & y > x) -> x >= 0".asFormula)
    val lemmaDB = new FileLemmaDB
    val res = RCF.proveArithmetic(math, f)
    val id = lemmaDB.add(res)

    (res.fact.conclusion.succ.head match {
      case Equiv(_, True) => true
      case _ => false
    }) shouldBe true
    val r = new RootNode(new Sequent(Nil, Vector(), Vector(res.fact.conclusion.succ.head)))
    val t = LookupLemma(lemmaDB, id)
    r.apply(t) shouldBe 'closed
  }

  it should "learn a lemma from (x > 0 & y = x+1 & y > x) -> (x >= 0 & y > 0)" in {
    val f = TacticLibrary.universalClosure("(x > 0 & y = x+1 & y > x) -> (x >= 0 & y > 0)".asFormula)
    val lemmaDB = new FileLemmaDB
    val res = RCF.proveArithmetic(math, f)
    val id = lemmaDB.add(res)

    (res.fact.conclusion.succ.head match {
          case Equiv(_, True) => true
          case _ => false
    }) shouldBe true
    val r = new RootNode(new Sequent(Nil, Vector(), Vector(res.fact.conclusion.succ.head)))
    val t = LookupLemma(lemmaDB, id)
    r.apply(t) shouldBe 'closed
  }

  it should "learn a lemma from (x > 0 & y = x+1 & y > x) -> (y > 0)" in {
    val f = TacticLibrary.universalClosure("(x > 0 & y = x+1 & y > x) -> (y > 0)".asFormula)
    val lemmaDB = new FileLemmaDB
    val res = RCF.proveArithmetic(math, f)
    val id = lemmaDB.add(res)

    (res.fact.conclusion.succ.head match {
        case Equiv(_, True) => true
        case _ => false
    }) shouldBe true
    val r = new RootNode(new Sequent(Nil, Vector(), Vector(res.fact.conclusion.succ.head)))
    val t = LookupLemma(lemmaDB, id)
    r.apply(t) shouldBe 'closed
  }

  it should "learn a lemma from (x > 0 & y = x+1 & x+1 > x) -> (x+1 > 0)" in {
    val f = TacticLibrary.universalClosure("(x > 0 & y = x+1 & x+1 > x) -> (x+1 > 0)".asFormula)
    val lemmaDB = new FileLemmaDB
    val res = RCF.proveArithmetic(math, f)
    val id = lemmaDB.add(res)

    (res.fact.conclusion.succ.head match {
          case Equiv(_, True) => true
          case _ => false
    }) shouldBe true
    val r = new RootNode(new Sequent(Nil, Vector(), Vector(res.fact.conclusion.succ.head)))
    val t = LookupLemma(lemmaDB, id)
    r.apply(t) shouldBe 'closed
  }

  "A lemma" should "be learned and used" in {
    val lemmaDB = new FileLemmaDB

    val f = "[x:=2;]x=2".asFormula
    val s = Sequent(Nil, immutable.IndexedSeq(), immutable.IndexedSeq(f))
    val r1 = helper.runTactic(debugT("msg") & ls(assignb) & debugT("msg") & closeId, new RootNode(s))
    //val r1 = helper.runTactic(ls(assignb) & closeId, new RootNode(s))
    r1 shouldBe 'closed
    // create evidence (traces input into tool and output from tool)
    val evidence = new ToolEvidence(immutable.Map("input" -> f.prettyString, "output" -> "true")) :: Nil
    // cannot use lemma names for testing, because running the test multiple times results in duplicate lemmas
    val lemma = Lemma(r1.provableWitness, evidence /*, Some("My first lemma")*/)
    // add lemma into DB, which creates an ID for it. use the ID to apply the lemma
    val lemmaID = lemmaDB.add(lemma)

    val h = "[y:=3; x:=2;]x=2".asFormula
    val t = Sequent(Nil, immutable.IndexedSeq(), immutable.IndexedSeq(h))
    val applyLemma = new ApplyRule(LookupLemma(lemmaDB, lemmaID)) {
      override def applicable(node: ProofNode): Boolean = node.sequent.sameSequentAs(s)
    }
    val r2 = helper.runTactic(
      ls(composeb) & ls(assignb) &
      // cut in exact shape of lemma
      cut("[x:=2;]x=2".asFormula) & onBranch(
        (cutShowLbl,
          // hide everything exact lemma shape, then apply lemma
          SearchTacticsImpl.lastSucc(PropositionalTacticsImpl.cohideT) & applyLemma),
        (cutUseLbl, closeId)
      ), new RootNode(t))
    r2 shouldBe 'closed
  }
}
