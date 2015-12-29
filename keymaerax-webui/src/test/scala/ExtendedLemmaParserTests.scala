import edu.cmu.cs.ls.keymaerax.core.{Lemma, Sequent}
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXExtendedLemmaParser
import org.scalatest.{Matchers, FlatSpec}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import scala.collection.immutable.IndexedSeq
/**
  * Created by nfulton on 12/16/15.
  */
class ExtendedLemmaParserTests extends FlatSpec with Matchers {
  "Extended Lemma Parser" should "work, hopefully" in {
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
    parseResult._2.head shouldBe new Sequent(Nil, IndexedSeq("1=1".asFormula, "2=2".asFormula), IndexedSeq("3=3".asFormula, "4=4".asFormula))

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
    parseResult._2.head shouldBe new Sequent(Nil, IndexedSeq("1=1".asFormula, "2=2".asFormula), IndexedSeq("3=3".asFormula, "4=4".asFormula))

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
    parseResult._2.head shouldBe new Sequent(Nil, IndexedSeq("1=1".asFormula, "2=2".asFormula), IndexedSeq("3=3".asFormula, "4=4".asFormula))

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
    parseResult._2.head shouldBe new Sequent(Nil, IndexedSeq("1=1".asFormula, "2=2".asFormula), IndexedSeq("3=3".asFormula, "4=4".asFormula))

    Lemma.fromString(lemmaFile)
  }
}
