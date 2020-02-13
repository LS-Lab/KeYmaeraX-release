package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.hydra.SQLite
import edu.cmu.cs.ls.keymaerax.lemma.{Lemma, LemmaDB, LemmaDBFactory}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tools.ToolEvidence

import scala.collection.immutable.IndexedSeq

import org.scalatest.LoneElement._

/**
  * @author Nathan Fulton
  */
class ExtendedLemmaParserTests extends TacticTestBase {

  "Extended Lemma Parser" should "work" in {
    val sequent = Sequent(IndexedSeq("1=1".asFormula, "3=3".asFormula), IndexedSeq("2=2".asFormula, "5=5".asFormula))
    val storedProvable = Provable.toStorageString(Provable.startProof(sequent))

    val tool = "input \"\"\"\" \"\"\"\"\noutput \"\"\"\" \"\"\"\""
    val kyxversion = "kyxversion \"\"\"\"" + edu.cmu.cs.ls.keymaerax.core.VERSION + "\"\"\"\""

    val lemmaFile =
      s"""Lemma "MyLemma".
          |"$storedProvable"
          |End.
          |Tool.
          |$tool
          |End.
          |Tool.
          |$kyxversion
          |End.
      """.stripMargin
    val parseResult = KeYmaeraXExtendedLemmaParser(lemmaFile)

    parseResult._1.get shouldBe "MyLemma"
    parseResult._2.subgoals.loneElement shouldBe sequent
    parseResult._2.conclusion shouldBe sequent

    Lemma.fromString(lemmaFile)
  }

  it should "work with no subgoals" in {
    val sequent = Sequent(IndexedSeq("p()".asFormula), IndexedSeq("p()".asFormula))
    val closedProvable = ProvableSig.startProof(sequent).apply(Close(AntePos(0), SuccPos(0)), 0)
    val kyxversion = "kyxversion \"\"\"\"" + edu.cmu.cs.ls.keymaerax.core.VERSION + "\"\"\"\""
    val lemmaFile =
      s"""Lemma "MyLemma".
          |"${Provable.toStorageString(closedProvable.underlyingProvable)}"
          |End.
          |Tool.
          |$kyxversion
          |End.
      """.stripMargin
    val parseResult = KeYmaeraXExtendedLemmaParser(lemmaFile)

    parseResult._1.get shouldBe "MyLemma"
    parseResult._2.subgoals shouldBe empty
    parseResult._2.conclusion shouldBe sequent

    Lemma.fromString(lemmaFile)
  }

  it should "work with sequents that don't have antes" in {
    val sequent = Sequent(IndexedSeq(), IndexedSeq("2=2".asFormula, "5=5".asFormula))
    val provable = ProvableSig.startProof(sequent)
    val tool = "input \"\"\"\" \"\"\"\"\noutput \"\"\"\" \"\"\"\""
    val kyxversion = "kyxversion \"\"\"\"" + edu.cmu.cs.ls.keymaerax.core.VERSION + "\"\"\"\""

    val lemmaFile =
      s"""Lemma "MyLemma".
          |"${Provable.toStorageString(provable.underlyingProvable)}"
          |End.
          |Tool.
          |$tool
          |End.
          |Tool.
          |$kyxversion
          |End.
      """.stripMargin
    val parseResult = KeYmaeraXExtendedLemmaParser(lemmaFile)

    parseResult._1.get shouldBe "MyLemma"
    parseResult._2.subgoals.loneElement shouldBe sequent
    parseResult._2.conclusion shouldBe sequent

    Lemma.fromString(lemmaFile)
  }

  it should "work with sequents that don't have succs" in {
    val sequent = Sequent(IndexedSeq("1=1".asFormula, "3=3".asFormula), IndexedSeq())
    val provable = ProvableSig.startProof(sequent)
    val tool = "input \"\"\"\" \"\"\"\"\noutput \"\"\"\" \"\"\"\""
    val kyxversion = "kyxversion \"\"\"\"" + edu.cmu.cs.ls.keymaerax.core.VERSION + "\"\"\"\""

    val lemmaFile =
      s"""Lemma "MyLemma".
          |"${Provable.toStorageString(provable.underlyingProvable)}"
          |End.
          |Tool.
          |$tool
          |End.
          |Tool.
          |$kyxversion
          |End.
      """.stripMargin
    val parseResult = KeYmaeraXExtendedLemmaParser(lemmaFile)

    parseResult._1.get shouldBe "MyLemma"
    parseResult._2.subgoals.loneElement shouldBe sequent
    parseResult._2.conclusion shouldBe sequent

    Lemma.fromString(lemmaFile)
  }

  it should "parse multi-evidence lemma correctly" in {
    val sequent = "1=1, 2=2 ==> 3=3, 4=4".asSequent
    val tool = "input \"\"\"\" \"\"\"\"\noutput \"\"\"\" \"\"\"\""
    val lemmaFile =
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

      val lemmaFile =
        s"""Lemma "MyLemma".
           |"${Provable.toStorageString(Provable.startProof("1=1".asFormula))}"
           |End.
        """.stripMargin

      val parseResult = KeYmaeraXExtendedLemmaParser(lemmaFile)

      parseResult._1 shouldBe Some("MyLemma")
      parseResult._2.conclusion shouldBe "==> 1=1".asSequent
      parseResult._3 shouldBe empty
    }
  }

  it should "automatically add a version to all lemmas" in {
    val tool: String = "input \"\"\"\"" + "output" + "\"\"\"\"\n"
    val lemmaFile =
      s"""Lemma "MyLemma".
          |"${Provable.toStorageString(Provable.startProof("1=1".asFormula))}"
          |End.
          |Tool.
          |$tool
          |End.
      """.stripMargin
    val parseResult = KeYmaeraXExtendedLemmaParser(lemmaFile)
    parseResult._3.filter(x => x.isInstanceOf[ToolEvidence]).exists(x => x.asInstanceOf[ToolEvidence].info.exists(p => p._1 == "kyxversion"))
  }

  it should "add to sql db" ignore {
    addTo(SQLite.cachedSQLiteLemmaDB(SQLite.TestDB), remove=true)
  }

  it should "add to file db" in {
    addTo(LemmaDBFactory.lemmaDB, remove=true)
  }

  it should "not create a lemma without evidence in strict mode" in {
    val name ="blah"
    val p = ProvableSig.startProof("1=1".asFormula)
    val c = Lemma.getClass.getDeclaredConstructor()
    c.setAccessible(true)
    withTemporaryConfig(Map(Configuration.Keys.LEMMA_COMPATIBILITY -> "false")) {
      c.newInstance() // reinitialize [[Lemma.LEMMA_COMPAT_MODE]] from the changed configuration
      (the [AssertionError] thrownBy Lemma(p, ToolEvidence(("a", "a") :: Nil) :: Nil, Some(name))).getMessage should
        include ("assertion failed: Lemma should have kyxversion (unless compatibility mode, which is false)")
    }
    withTemporaryConfig(Map(Configuration.Keys.LEMMA_COMPATIBILITY -> "true")) {
      c.newInstance() // reinitialize [[Lemma.LEMMA_COMPAT_MODE]] from the changed configuration
      Lemma(p, ToolEvidence(("a", "a") :: Nil) :: Nil, Some(name))
    }
  }

  private def addTo(db: LemmaDB, remove: Boolean=true): Unit = {
    var name = "1111112"
    while (db.contains(name)) name = name + "1"

    val p = ProvableSig.startProof("1=1".asFormula)

    try {
      db.add(new Lemma(p, Lemma.requiredEvidence(p, ToolEvidence(("a", "a")::Nil)::Nil), Some(name)))
      val reloadedLemma = db.get(name)
      reloadedLemma.get.evidence.find({ case ToolEvidence(("kyxversion", _) :: Nil) => true case _ => false }) match {
        case Some(ToolEvidence((_, version) :: Nil)) => version shouldBe VERSION
        case None => throw new Exception(s"Expected some version evidence in ${db.get(name).get.toString}")
      }
      if (remove) db.remove(name)
    } catch {
      case e: Throwable =>
        if (remove) db.remove(name)
        throw e //still fail but don't leave clutter around
    }
  }

}
