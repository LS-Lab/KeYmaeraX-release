package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.hydra.SQLite
import edu.cmu.cs.ls.keymaerax.lemma.{LemmaDB, LemmaDBFactory}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tools.{HashEvidence, ToolEvidence}

import scala.collection.immutable.IndexedSeq

/**
  * @author Nathan Fulton
  */
class ExtendedLemmaParserTests extends TacticTestBase {

  "Extended Lemma Parser" should "work" in {
    val sequent = Sequent(IndexedSeq("1=1".asFormula, "3=3".asFormula), IndexedSeq("2=2".asFormula, "5=5".asFormula))

    val tool = "input \"\"\"\" \"\"\"\"\noutput \"\"\"\" \"\"\"\""
    val hash = "\"\"\"\"" + Lemma.checksum(ProvableSig.startProof(sequent)) + "\"\"\"\""
    val kyxversion = "kyxversion \"\"\"\"" + edu.cmu.cs.ls.keymaerax.core.VERSION + "\"\"\"\""

    val lemmaFile =
      s"""Lemma "MyLemma".
          |Sequent.
          |Formula: 1=1
          |Formula: 3=3
          |==>
          |Formula: 2=2
          |Formula: 5=5
          |Sequent.
          |Formula: 1=1
          |Formula: 3=3
          |==>
          |Formula: 2=2
          |Formula: 5=5
          |End.
          |Tool.
          |$tool
          |End.
          |Hash.
          |  hash $hash
          |End.
          |Tool.
          |$kyxversion
          |End.
      """.stripMargin
    val parseResult = KeYmaeraXExtendedLemmaParser(lemmaFile)

    parseResult._1.get shouldBe "MyLemma"
    parseResult._2.length shouldBe 2
    parseResult._2.head shouldBe sequent

    Lemma.fromString(lemmaFile)
  }

  it should "work with no subgoals" in {
    val sequent = Sequent(IndexedSeq("p()".asFormula), IndexedSeq("p()".asFormula))
    val closedProvable = ProvableSig.startProof(sequent).apply(Close(AntePos(0), SuccPos(0)), 0)
    val hash = "\"\"\"\"" + Lemma.checksum(closedProvable) + "\"\"\"\""
    val kyxversion = "kyxversion \"\"\"\"" + edu.cmu.cs.ls.keymaerax.core.VERSION + "\"\"\"\""

    val tool = "input \"\"\"\" \"\"\"\"\noutput \"\"\"\" \"\"\"\""
    val lemmaFile =
      s"""Lemma "MyLemma".
          |Sequent.
          |Formula: p()
          |==>
          |Formula: p()
          |End.
          |Tool.
          |$tool
          |End.
          |Hash.
          |  hash $hash
          |End.
          |Tool.
          |$kyxversion
          |End.
      """.stripMargin
    val parseResult = KeYmaeraXExtendedLemmaParser(lemmaFile)

    parseResult._1.get shouldBe "MyLemma"
    parseResult._2.length shouldBe 1
    parseResult._2.head shouldBe sequent

    Lemma.fromString(lemmaFile)
  }

  it should "work with sequents that don't have antes" in {
    val sequent = Sequent(IndexedSeq(), IndexedSeq("2=2".asFormula, "5=5".asFormula))

    val tool = "input \"\"\"\" \"\"\"\"\noutput \"\"\"\" \"\"\"\""
    val hash = "\"\"\"\"" + Lemma.checksum(ProvableSig.startProof(sequent)) + "\"\"\"\""
    val kyxversion = "kyxversion \"\"\"\"" + edu.cmu.cs.ls.keymaerax.core.VERSION + "\"\"\"\""

    val lemmaFile =
      s"""Lemma "MyLemma".
          |Sequent.
          |==>
          |Formula: 2=2
          |Formula: 5=5
          |Sequent.
          |==>
          |Formula: 2=2
          |Formula: 5=5
          |End.
          |Tool.
          |$tool
          |End.
          |Hash.
          |  hash $hash
          |End.
          |Tool.
          |$kyxversion
          |End.
      """.stripMargin
    val parseResult = KeYmaeraXExtendedLemmaParser(lemmaFile)

    parseResult._1.get shouldBe "MyLemma"
    parseResult._2.length shouldBe 2
    parseResult._2.head shouldBe sequent

    Lemma.fromString(lemmaFile)
  }

  it should "work with sequents that don't have succs" in {
    val sequent = Sequent(IndexedSeq("1=1".asFormula, "3=3".asFormula), IndexedSeq())

    val tool = "input \"\"\"\" \"\"\"\"\noutput \"\"\"\" \"\"\"\""
    val hash = "\"\"\"\"" + Lemma.checksum(ProvableSig.startProof(sequent)) + "\"\"\"\""
    val kyxversion = "kyxversion \"\"\"\"" + edu.cmu.cs.ls.keymaerax.core.VERSION + "\"\"\"\""

    val lemmaFile =
      s"""Lemma "MyLemma".
          |Sequent.
          |Formula: 1=1
          |Formula: 3=3
          |==>
          |Sequent.
          |Formula: 1=1
          |Formula: 3=3
          |==>
          |End.
          |Tool.
          |$tool
          |End.
          |Hash.
          |  hash $hash
          |End.
          |Tool.
          |$kyxversion
          |End.
      """.stripMargin
    val parseResult = KeYmaeraXExtendedLemmaParser(lemmaFile)

    parseResult._1.get shouldBe "MyLemma"
    parseResult._2.length shouldBe 2
    parseResult._2.head shouldBe sequent

    Lemma.fromString(lemmaFile)
  }

  it should "parse multi-evidence lemma correctly" in {
    val tool = "input \"\"\"\" \"\"\"\"\noutput \"\"\"\" \"\"\"\""
    val lemmaFile =
      s"""Lemma "MyLemma".
          |Sequent.
          |Formula: 1=1
          |Formula: 2=2
          |==>
          |Formula: 3=3
          |Formula: 4=4
          |Sequent.
          |Formula: 5=5
          |==>
          |Formula: 6=6
          |Sequent.
          |Formula: 7=7
          |==>
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
    parseResult._2.length shouldBe 3
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
           |Sequent.
           |==>
           |Formula: 1=1
           |End.
        """.stripMargin

      val parseResult = KeYmaeraXExtendedLemmaParser(lemmaFile)

      parseResult._1 shouldBe Some("MyLemma")
      parseResult._2.length shouldBe 1
      parseResult._3 shouldBe empty
    }
  }

  it should "automatically add a version to all lemmas" in {
    val tool: String = "input \"\"\"\"" + "output" + "\"\"\"\"\n"
    val lemmaFile =
      s"""Lemma "MyLemma".
          |Sequent.
          |Formula: 1=1
          |Formula: 2=2
          |==>
          |Formula: 3=3
          |Formula: 4=4
          |Sequent.
          |Formula: 5=5
          |==>
          |Formula: 6=6
          |Sequent.
          |Formula: 7=7
          |==>
          |End.
          |Tool.
          |$tool
          |End.
      """.stripMargin
    val parseResult = KeYmaeraXExtendedLemmaParser(lemmaFile)
    parseResult._3.filter(x => x.isInstanceOf[ToolEvidence]).exists(x => x.asInstanceOf[ToolEvidence].info.exists(p => p._1 == "kyxversion"))
  }

  it should "add to sql db" ignore {
    addTo(SQLite.SQLiteLemmaDB(SQLite.TestDB), remove=true)
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
        include ("assertion failed: Lemma should have kyxversion and checksum stamps (unless compatibility mode, which is false)")
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
      reloadedLemma.get.evidence.find(_.isInstanceOf[HashEvidence]) match {
        case Some(HashEvidence(h)) => h == Lemma.checksum(p)
          //h == (reloadedLemma.get invokePrivate md5Generator(reloadedLemma.get invokePrivate sequentsToString(p.conclusion :: Nil)))
        case None => throw new Exception(s"Expected some hash evidence in ${db.get(name).get.toString}")
      }
      if (remove) db.remove(name)
    } catch {
      case e: Throwable =>
        if (remove) db.remove(name)
        throw e //stil fail but don't leave clutter around.
    }
  }

}
