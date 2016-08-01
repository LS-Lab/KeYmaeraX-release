package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.core.{Lemma, Sequent}
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXExtendedLemmaParser
import org.scalatest.{FlatSpec, Matchers}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tools.{HashEvidence, HashEvidenceHelper}

import scala.collection.immutable.IndexedSeq
/**
  * Created by nfulton on 12/16/15.
  */
class ExtendedLemmaParserTests extends FlatSpec with Matchers {
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
    val tool: String = "hash \"\"\"\"" + HashEvidenceHelper.md5("asdf") + "\"\"\"\"\n"
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
    parseResult._3.head.asInstanceOf[HashEvidence].h shouldBe HashEvidenceHelper.md5("asdf")
  }

}
