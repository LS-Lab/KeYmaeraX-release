/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.parser

import org.keymaerax.Configuration
import org.keymaerax.btactics.TacticTestBase
import org.keymaerax.core._
import org.keymaerax.hydra.SQLite
import org.keymaerax.info.{Version, VersionNumber}
import org.keymaerax.lemma.{Lemma, LemmaDB, LemmaDBFactory}
import org.keymaerax.parser.StringConverter._
import org.keymaerax.pt.ProvableSig
import org.keymaerax.tools.ToolEvidence
import org.scalatest.Inside._
import org.scalatest.LoneElement._

/** @author Nathan Fulton */
class ExtendedLemmaParserTests extends TacticTestBase {

  "Extended Lemma Parser" should "work" in {
    val sequent = Sequent(IndexedSeq("1=1".asFormula, "3=3".asFormula), IndexedSeq("2=2".asFormula, "5=5".asFormula))
    val storedProvable = Provable.toStorageString(Provable.startProof(sequent))
    val tool = ToolEvidence(List("input" -> "", "output" -> ""))
    val kyxversion = ToolEvidence(List("kyxversion" -> Version.toString))

    val lemmaFile = {
      s"""Lemma "MyLemma".
         |"$storedProvable"
         |End.
         |$tool
         |$kyxversion""".stripMargin
    }
    val parseResult = KeYmaeraXExtendedLemmaParser(lemmaFile)

    parseResult._1.get shouldBe "MyLemma"
    parseResult._2.subgoals.loneElement shouldBe sequent
    parseResult._2.conclusion shouldBe sequent

    Lemma.fromString(lemmaFile)
  }

  it should "be backwards-compatible" in {
    val sequent = Sequent(IndexedSeq("1=1".asFormula, "3=3".asFormula), IndexedSeq("2=2".asFormula, "5=5".asFormula))
    val storedProvable = Provable.toStorageString(Provable.startProof(sequent))
    val tool = "input \"\"\"\" \"\"\"\"\noutput \"\"\"\" \"\"\"\""
    val kyxversion = "kyxversion \"\"\"\"" + Version.toString + "\"\"\"\""

    val lemmaFile = {
      s"""Lemma "MyLemma".
         |"$storedProvable"
         |End.
         |Tool. $tool End.
         |Tool. $kyxversion End.""".stripMargin
    }
    val parseResult = KeYmaeraXExtendedLemmaParser(lemmaFile)

    parseResult._1.get shouldBe "MyLemma"
    parseResult._2.subgoals.loneElement shouldBe sequent
    parseResult._2.conclusion shouldBe sequent

    Lemma.fromString(lemmaFile)
  }

  it should "be backwards-compatible but is allowed to change explicit spaces of evidence store with old versions" in {
    val sequent = Sequent(IndexedSeq("1=1".asFormula, "3=3".asFormula), IndexedSeq("2=2".asFormula, "5=5".asFormula))
    val storedProvable = Provable.toStorageString(Provable.startProof(sequent))
    val toolValue = "  this h a d   awkward space s"
    val tool = "input \"\"\"\"" + toolValue + "\"\"\"\""
    val kyxversion = "kyxversion \"\"\"\"" + Version.toString + "\"\"\"\""

    val lemmaFile = {
      s"""Lemma "MyLemma".
         |"$storedProvable"
         |End.
         |Tool. $tool End.
         |Tool. $kyxversion End.""".stripMargin
    }
    val parseResult = KeYmaeraXExtendedLemmaParser(lemmaFile)

    parseResult._1.get shouldBe "MyLemma"
    parseResult._2.subgoals.loneElement shouldBe sequent
    parseResult._2.conclusion shouldBe sequent

    Lemma.fromString(lemmaFile) match {
      case Lemma(_, (e: ToolEvidence) :: _ :: Nil, _) => e.info should contain theSameElementsAs
          List("input" -> toolValue.stripPrefix(" ").stripSuffix(" "))
    }
  }

  it should "work with no subgoals" in {
    val sequent = Sequent(IndexedSeq("p()".asFormula), IndexedSeq("p()".asFormula))
    val closedProvable = ProvableSig.startPlainProof(sequent).apply(Close(AntePos(0), SuccPos(0)), 0)
    val kyxversion = ToolEvidence(List("kyxversion" -> Version.toString))
    val lemmaFile = {
      s"""Lemma "MyLemma".
         |"${Provable.toStorageString(closedProvable.underlyingProvable)}"
         |End.
         |$kyxversion""".stripMargin
    }
    val parseResult = KeYmaeraXExtendedLemmaParser(lemmaFile)

    parseResult._1.get shouldBe "MyLemma"
    parseResult._2.subgoals shouldBe empty
    parseResult._2.conclusion shouldBe sequent

    Lemma.fromString(lemmaFile)
  }

  it should "work with sequents that don't have antes" in {
    val sequent = Sequent(IndexedSeq(), IndexedSeq("2=2".asFormula, "5=5".asFormula))
    val provable = ProvableSig.startPlainProof(sequent)
    val tool = ToolEvidence(List("input" -> "", "output" -> ""))
    val kyxversion = ToolEvidence(List("kyxversion" -> Version.toString))

    val lemmaFile = {
      s"""Lemma "MyLemma".
         |"${Provable.toStorageString(provable.underlyingProvable)}"
         |End.
         |$tool
         |$kyxversion""".stripMargin
    }
    val parseResult = KeYmaeraXExtendedLemmaParser(lemmaFile)

    parseResult._1.get shouldBe "MyLemma"
    parseResult._2.subgoals.loneElement shouldBe sequent
    parseResult._2.conclusion shouldBe sequent

    Lemma.fromString(lemmaFile)
  }

  it should "work with sequents that don't have succs" in {
    val sequent = Sequent(IndexedSeq("1=1".asFormula, "3=3".asFormula), IndexedSeq())
    val provable = ProvableSig.startPlainProof(sequent)
    val tool = ToolEvidence(List("input" -> "", "output" -> ""))
    val kyxversion = ToolEvidence(List("kyxversion" -> Version.toString))

    val lemmaFile = {
      s"""Lemma "MyLemma".
         |"${Provable.toStorageString(provable.underlyingProvable)}"
         |End.
         |$tool
         |$kyxversion""".stripMargin
    }
    val parseResult = KeYmaeraXExtendedLemmaParser(lemmaFile)

    parseResult._1.get shouldBe "MyLemma"
    parseResult._2.subgoals.loneElement shouldBe sequent
    parseResult._2.conclusion shouldBe sequent

    Lemma.fromString(lemmaFile)
  }

  it should "parse multi-evidence lemma correctly in backwards-compatibility" in {
    val sequent = "1=1, 2=2 ==> 3=3, 4=4".asSequent
    val tool = "input \"\"\"\" \"\"\"\"\noutput \"\"\"\" \"\"\"\""
    val lemmaFile = {
      s"""Lemma "MyLemma".
         |"${Provable.toStorageString(Provable.startProof(sequent))}"
         |End.
         |Tool.
         |$tool
         |End.
         |Tool.
         |$tool
         |End.
      """.stripMargin
    }

    val parseResult = KeYmaeraXExtendedLemmaParser(lemmaFile)

    parseResult._1 shouldBe Some("MyLemma")
    parseResult._2.subgoals.loneElement shouldBe sequent
    parseResult._2.conclusion shouldBe sequent
    parseResult._3.length shouldBe 2
  }

  it should "parse multi-evidence lemma correctly" in {
    val sequent = "1=1, 2=2 ==> 3=3, 4=4".asSequent
    val tool = ToolEvidence(List("input" -> "", "output" -> ""))
    val lemmaFile = {
      s"""Lemma "MyLemma".
         |"${Provable.toStorageString(Provable.startProof(sequent))}"
         |End.
         |$tool
         |$tool""".stripMargin
    }

    val parseResult = KeYmaeraXExtendedLemmaParser(lemmaFile)

    parseResult._1 shouldBe Some("MyLemma")
    parseResult._2.subgoals.loneElement shouldBe sequent
    parseResult._2.conclusion shouldBe sequent
    parseResult._3.length shouldBe 2
  }

  it should "parse lemma without evidence correctly in compatibility mode" in {
    withTemporaryConfig(Map(Configuration.Keys.LEMMA_COMPATIBILITY -> "true")) {
      // reinitialize [[Lemma.LEMMA_COMPAT_MODE]] from changed configuration
      val c = Lemma.getClass.getDeclaredConstructor()
      c.setAccessible(true)
      c.newInstance()

      val lemmaFile = {
        s"""Lemma "MyLemma".
           |"${Provable.toStorageString(Provable.startProof("1=1".asFormula))}"
           |End.
        """.stripMargin
      }

      val parseResult = KeYmaeraXExtendedLemmaParser(lemmaFile)

      parseResult._1 shouldBe Some("MyLemma")
      parseResult._2.conclusion shouldBe "==> 1=1".asSequent
      parseResult._3 shouldBe empty
    }
  }

  it should "automatically add a version to all lemmas" in {
    val tool = ToolEvidence(List("input" -> "", "output" -> ""))
    val lemmaFile = {
      s"""Lemma "MyLemma".
         |"${Provable.toStorageString(Provable.startProof("1=1".asFormula))}"
         |End.
         |$tool""".stripMargin
    }
    val parseResult = KeYmaeraXExtendedLemmaParser(lemmaFile)
    parseResult
      ._3
      .filter(x => x.isInstanceOf[ToolEvidence])
      .exists(x => x.asInstanceOf[ToolEvidence].info.exists(p => p._1 == "kyxversion"))
  }

  it should "add to sql db" ignore { addTo(SQLite.cachedSQLiteLemmaDB(SQLite.TestDB)) }

  it should "add to file db" in { addTo(LemmaDBFactory.lemmaDB) }

  // This test is ignored because reinitialization of Lemma.LEMMA_COMPAT_MODE using reflection no longer works.
  // Once config handling is changed, we can fix this without performance impact
  // by looking up Lemma.LEMMA_COMPAT_MODE in the config every time.
  // Alternatively, we break backwards compatibility for KeYmaera X 6.0.0
  // and get rid of the whole compatibility mode stuff.
  it should "not create a lemma without evidence in strict mode" ignore {
    val name = "blah"
    val p = ProvableSig.startPlainProof("1=1".asFormula)
    val c = Lemma.getClass.getDeclaredConstructor()
    c.setAccessible(true)
    withTemporaryConfig(Map(Configuration.Keys.LEMMA_COMPATIBILITY -> "false")) {
      c.newInstance() // reinitialize [[Lemma.LEMMA_COMPAT_MODE]] from the changed configuration
      (the[AssertionError] thrownBy Lemma(p, ToolEvidence(("a", "a") :: Nil) :: Nil, Some(name))).getMessage should
        include("assertion failed: Lemma should have kyxversion (unless compatibility mode, which is false)")
    }
    withTemporaryConfig(Map(Configuration.Keys.LEMMA_COMPATIBILITY -> "true")) {
      c.newInstance() // reinitialize [[Lemma.LEMMA_COMPAT_MODE]] from the changed configuration
      Lemma(p, ToolEvidence(("a", "a") :: Nil) :: Nil, Some(name))
    }
  }

  it should "not drop evidence" in {
    val q = "\"\"\"\""
    val content = {
      s"""Lemma "user/TheLemma".
         |"  ==>  (S(x))->([?(!(S(x)));](P(x)))
         |\\qed::b626db1b63039b1010d137dcb515214d"
         |End.
         |Tool.
         |  tool $q KeYmaera X $q
         |  model $q "Lemma "TheLemma"
         |  Definitions     /* constants, functions, properties, programs */
         |    Bool S(Real x);
         |    Bool P(Real x);
         |  End.
         |  ProgramVariables Real x; End.        /* variables */
         |  Problem  S(x) -> [?!S(x);]P(x) End.  /* specification in dL */
         |End. $q
         |  tactic $q implyR(1) ; testb(1) ; implyR(1) ; notL(-2) ; id using "S(x) :: nil" $q
         | End.
         |
         | Tool.
         | kyxversion $q 4.9.3 $q
         | End.""".stripMargin
    }

    val (name, p, evidence) = KeYmaeraXExtendedLemmaParser(content)
    name should contain("user/TheLemma")
    p.conclusion shouldBe "==> S(x) -> [?!S(x);]P(x)".asSequent
    evidence should have size 2
    inside(evidence) { case ToolEvidence(t) :: ToolEvidence(v) :: Nil =>
      t.toMap.keySet should contain theSameElementsAs List("tool", "model", "tactic")
      v should contain theSameElementsAs List("kyxversion" -> "4.9.3")
    }
  }

  "Evidence" should "print space before/after quadruple quotes" in {
    val e1 = ToolEvidence(List("key" -> "value"))
    e1.toString shouldBe "Tool.\n  key \"\"\"\" value \"\"\"\"\nEnd."
    val e2 = ToolEvidence(List("k1" -> "\"v1\"", "k2" -> "\"v2\""))
    e2.toString shouldBe "Tool.\n  k1 \"\"\"\" \"v1\" \"\"\"\"\n  k2 \"\"\"\" \"v2\" \"\"\"\"\nEnd."

    val (ev, Token(EOF, _) :: Nil) = KeYmaeraXExtendedLemmaParser
      .parseAllEvidence(KeYmaeraXLexer.inMode(e1.toString + "\n" + e2.toString, LemmaFileMode))
    ev should contain theSameElementsInOrderAs List(e1, e2)
  }

  private def addTo(db: LemmaDB): Unit = {
    var name = "1111112"
    while (db.contains(name)) name = name + "1"

    val p = ProvableSig.startPlainProof("1=1".asFormula)

    try {
      db.add(new Lemma(p, Lemma.requiredEvidence(p, ToolEvidence(("a", "a") :: Nil) :: Nil), Some(name)))
      val reloadedLemma = db.get(name)
      reloadedLemma
        .get
        .evidence
        .find({
          case ToolEvidence(("kyxversion", _) :: Nil) => true
          case _ => false
        }) match {
        case Some(ToolEvidence((_, version) :: Nil)) => VersionNumber.parse(version) shouldBe Version
        case None => throw new Exception(s"Expected some version evidence in ${db.get(name).get.toString}")
      }
      db.remove(name)
    } catch {
      case e: Throwable =>
        db.remove(name)
        throw e // still fail but don't leave clutter around
    }
  }

}
