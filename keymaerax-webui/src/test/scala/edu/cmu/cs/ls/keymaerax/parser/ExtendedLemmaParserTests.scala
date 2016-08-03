package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.core.{Lemma, Provable, Sequent}
import edu.cmu.cs.ls.keymaerax.hydra.SQLite
import edu.cmu.cs.ls.keymaerax.lemma.{LemmaDB, LemmaDBFactory}
import org.scalatest.{FlatSpec, Matchers, PrivateMethodTester}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tools.{HashEvidence, ToolEvidence}

import scala.collection.immutable.IndexedSeq
/**
  * Created by nfulton on 12/16/15.
  */
class ExtendedLemmaParserTests extends FlatSpec with Matchers with PrivateMethodTester {
  private val md5Generator = PrivateMethod[String]('md5)
  private val sequentsToString = PrivateMethod[String]('sequentsToString)

  "Extended Lemma Parser" should "work" in {
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
          |Formula: 8=8
          |End.
          |Tool.
          |${tool}
          |End.
      """.stripMargin
    val parseResult = KeYmaeraXExtendedLemmaParser(lemmaFile)

    parseResult._1.get shouldBe "MyLemma"
    parseResult._2.length shouldBe 3
    parseResult._2.head shouldBe new Sequent(IndexedSeq("1=1".asFormula, "2=2".asFormula), IndexedSeq("3=3".asFormula, "4=4".asFormula))

    Lemma.fromString(lemmaFile)
  }

  it should "work with no subgoals" in {
    val tool = "input \"\"\"\" \"\"\"\"\noutput \"\"\"\" \"\"\"\""
    val lemmaFile =
      s"""Lemma "MyLemma".
          |Sequent.
          |Formula: 1=1
          |Formula: 2=2
          |==>
          |Formula: 3=3
          |Formula: 4=4
          |End.
          |Tool.
          |${tool}
          |End.
      """.stripMargin
    val parseResult = KeYmaeraXExtendedLemmaParser(lemmaFile)

    parseResult._1.get shouldBe "MyLemma"
    parseResult._2.length shouldBe 1
    parseResult._2.head shouldBe new Sequent(IndexedSeq("1=1".asFormula, "2=2".asFormula), IndexedSeq("3=3".asFormula, "4=4".asFormula))

    Lemma.fromString(lemmaFile)
  }

  it should "work with sequents that don't have antes" in {
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
          |==>
          |Formula: 6=6
          |Sequent.
          |Formula: 7=7
          |==>
          |Formula: 8=8
          |End.
          |Tool.
          |${tool}
          |End.
      """.stripMargin
    val parseResult = KeYmaeraXExtendedLemmaParser(lemmaFile)

    parseResult._1.get shouldBe "MyLemma"
    parseResult._2.length shouldBe 3
    parseResult._2.head shouldBe new Sequent(IndexedSeq("1=1".asFormula, "2=2".asFormula), IndexedSeq("3=3".asFormula, "4=4".asFormula))

    Lemma.fromString(lemmaFile)
  }

  it should "work with sequents that don't have succs" in {
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
          |${tool}
          |End.
      """.stripMargin
    val parseResult = KeYmaeraXExtendedLemmaParser(lemmaFile)

    parseResult._1.get shouldBe "MyLemma"
    parseResult._2.length shouldBe 3
    parseResult._2.head shouldBe new Sequent(IndexedSeq("1=1".asFormula, "2=2".asFormula), IndexedSeq("3=3".asFormula, "4=4".asFormula))

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
          |${tool}
          |End.
          |Tool.
          |${tool}
          |End.
      """.stripMargin

    val parseResult = KeYmaeraXExtendedLemmaParser(lemmaFile)

    parseResult._1 shouldBe Some("MyLemma")
    parseResult._2.length shouldBe 3
    parseResult._3.length shouldBe 2
  }

  it should "parse a lemma with a hash" in {
    val md5 = Lemma(null, null) invokePrivate md5Generator("asdf")
    val tool: String = "hash \"\"\"\"" + md5 + "\"\"\"\"\n"
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
          |Hash.
          |${tool}
          |End.
      """.stripMargin
    val parseResult = KeYmaeraXExtendedLemmaParser(lemmaFile)
    parseResult._3.head.asInstanceOf[HashEvidence].h shouldBe md5
  }

  it should "add a lemma" in {
    addTo(LemmaDBFactory.lemmaDB, true)
  }

  it should "add a sql lemma" in {
    addTo(new SQLite.SQLiteLemmaDB(SQLite.TestDB), false /*@todo b/c .remove currently unsupported for sql lemma db*/)
  }


  private def addTo(db:LemmaDB, remove:Boolean=true) = {
    var name = "111111"
    while(db.contains(name)) {
      name = name + "1"
    }

    val p = Provable.startProof("1=1".asFormula)

    try {
      db.add(new Lemma(p, ToolEvidence(("a", "a") :: Nil) :: Nil, Some(name)))
      val reloadedLemma = db.get(name)
      reloadedLemma.get.evidence.find(_.isInstanceOf[HashEvidence]) match {
        case Some(HashEvidence(h)) => h == (reloadedLemma.get invokePrivate md5Generator(reloadedLemma.get invokePrivate sequentsToString(p.conclusion :: Nil)))
        case None => throw new Exception(s"Expected some hash evidence in ${db.get(name).get.toString}")
      }
      if(remove) db.remove(name)
    }
    catch {
      case e: Throwable => {
        if(remove) db.remove(name)
        throw e //stil fail but don't leave clutter around.
      }
    }
  }

}
