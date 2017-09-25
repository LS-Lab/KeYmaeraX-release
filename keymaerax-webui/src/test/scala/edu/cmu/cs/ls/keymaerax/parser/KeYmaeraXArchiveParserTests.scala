/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/

package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.btactics.{TacticTestBase, TactixLibrary}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXArchiveParser.ParsedArchiveEntry
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import org.scalatest.LoneElement._

/**
  * Tests the archive parser.
  * Created by smitsch on 12/29/16.
  */
class KeYmaeraXArchiveParserTests extends TacticTestBase {

  "Archive parser" should "parse a model only entry" in {
    val input =
      """
        |ArchiveEntry "Entry 1".
        | ProgramVariables. R x. R y. End.
        | Problem. x>y -> x>=y End.
        |End.
      """.stripMargin
    val entries = KeYmaeraXArchiveParser.parse(input)
    entries should have size 1
    entries.head shouldBe ParsedArchiveEntry(
      "Entry 1",
      "theorem",
      """ProgramVariables. R x. R y. End.
        | Problem. x>y -> x>=y End.""".stripMargin,
      "x>y -> x>=y".asFormula,
      Nil
    )
  }

  it should "detect duplicate variable definitions" in {
    val input =
      """
        |ArchiveEntry "Entry 1".
        | ProgramVariables. R x. R x. R y. End.
        | Problem. x>y -> x>=y End.
        |End.
      """.stripMargin
    val ex = the [ParseException] thrownBy KeYmaeraXArchiveParser.parse(input)
    ex.msg should include ("Duplicate symbol 'x'")
  }

  it should "detect duplicate function names" in {
    val input =
      """
        |ArchiveEntry "Entry 1".
        | Definitions. R f() = (1). R f() = (2). End.
        | ProgramVariables. R x. R y. End.
        | Problem. x>y -> x>=y End.
        |End.
      """.stripMargin
    val ex = the [ParseException] thrownBy KeYmaeraXArchiveParser.parse(input)
    ex.msg should include ("Duplicate symbol 'f'")
  }

  it should "detect duplicate predicate names" in {
    val input =
      """
        |ArchiveEntry "Entry 1".
        | Definitions. B p() <-> (1>0). B p() <-> (2>1). End.
        | ProgramVariables. R x. R y. End.
        | Problem. p() -> x>=y End.
        |End.
      """.stripMargin
    val ex = the [ParseException] thrownBy KeYmaeraXArchiveParser.parse(input)
    ex.msg should include ("Duplicate symbol 'p'")
  }

  it should "detect duplicate program names" in {
    val input =
      """
        |ArchiveEntry "Entry 1".
        | Definitions. HP a ::= { ?true; }. HP a ::= { ?false; }.. End.
        | ProgramVariables. R x. R y. End.
        | Problem. [a;]true End.
        |End.
      """.stripMargin
    val ex = the [ParseException] thrownBy KeYmaeraXArchiveParser.parse(input)
    ex.msg should include ("Duplicate symbol 'a'")
  }

  it should "parse a model and tactic entry" in withQE { _ =>
    val input =
      """
        |ArchiveEntry "Entry 1".
        | ProgramVariables. R x. R y. End.
        | Problem. x>y -> x>=y End.
        | Tactic "Proof 1". implyR(1) & QE End.
        |End.
      """.stripMargin
    val entries = KeYmaeraXArchiveParser.parse(input)
    entries should have size 1
    entries.head shouldBe ParsedArchiveEntry(
      "Entry 1",
      "theorem",
      """ProgramVariables. R x. R y. End.
        | Problem. x>y -> x>=y End.""".stripMargin,
      "x>y -> x>=y".asFormula,
      ("Proof 1", implyR(1) & QE) :: Nil
    )
  }

  it should "parse a model with several tactics" in withQE { _ =>
    val input =
      """
        |ArchiveEntry "Entry 1".
        | ProgramVariables. R x. R y. End.
        | Problem. x>y -> x>=y End.
        | Tactic "Proof 1". implyR(1) & QE End.
        | Tactic "Proof 2". implyR('R) End.
        |End.
      """.stripMargin
    val entries = KeYmaeraXArchiveParser.parse(input)
    entries.loneElement shouldBe ParsedArchiveEntry(
      "Entry 1",
      "theorem",
      """ProgramVariables. R x. R y. End.
        | Problem. x>y -> x>=y End.""".stripMargin,
      "x>y -> x>=y".asFormula,
      ("Proof 1", implyR(1) & QE) :: ("Proof 2", implyR('R)) :: Nil
    )
  }

  it should "parse a list of model and tactic entries" in {
    val input =
      """ArchiveEntry "Entry 1".
        | ProgramVariables. R x. R y. End.
        | Problem. x>y -> x>=y End.
        |End.
        |
        |ArchiveEntry "Entry 2".
        |  Functions. R x(). End.
        |  ProgramVariables R y. End.
        |  Problem. x()>=y -> x()>=y End.
        |  Tactic "Prop Proof". prop End.
        |End.
      """.stripMargin
    val entries = KeYmaeraXArchiveParser.parse(input)
    entries should have size 2
    entries.head shouldBe ParsedArchiveEntry(
      "Entry 1",
      "theorem",
      """ProgramVariables. R x. R y. End.
        | Problem. x>y -> x>=y End.""".stripMargin,
      "x>y -> x>=y".asFormula,
      Nil
    )
    entries.last shouldBe ParsedArchiveEntry(
      "Entry 2",
      "theorem",
      """Functions. R x(). End.
        |  ProgramVariables R y. End.
        |  Problem. x()>=y -> x()>=y End.""".stripMargin,
      "x()>=y -> x()>=y".asFormula,
      ("Prop Proof", prop) :: Nil
    )
  }

  it should "parse a list of mixed entries, lemmas, and theorems" in {
    val input =
      """ArchiveEntry "Entry 1".
        | ProgramVariables. R x. R y. End.
        | Problem. x>y -> x>=y End.
        |End.
        |
        |Lemma "Entry 2".
        |  Functions. R x(). End.
        |  ProgramVariables R y. End.
        |  Problem. x()>=y -> x()>=y End.
        |  Tactic "Prop Proof". prop End.
        |End.
        |
        |Theorem "Entry 3".
        |  ProgramVariables. R x. End.
        |  Problem. x>3 -> x>=3 End.
        |End.
        |
        |ArchiveEntry "Entry 4".
        |  ProgramVariables. R x. End.
        |  Problem. x>4 -> x>=4 End.
        |End.
      """.stripMargin
    val entries = KeYmaeraXArchiveParser.parse(input)
    entries should have size 4
    entries should contain theSameElementsInOrderAs
      ParsedArchiveEntry(
        "Entry 1",
        "theorem",
        """ProgramVariables. R x. R y. End.
          | Problem. x>y -> x>=y End.""".stripMargin,
        "x>y -> x>=y".asFormula,
        Nil
      ) ::
      ParsedArchiveEntry(
        "Entry 2",
        "lemma",
        """Functions. R x(). End.
          |  ProgramVariables R y. End.
          |  Problem. x()>=y -> x()>=y End.""".stripMargin,
        "x()>=y -> x()>=y".asFormula,
        ("Prop Proof", prop) :: Nil
      ) ::
      ParsedArchiveEntry(
        "Entry 3",
        "theorem",
        """ProgramVariables. R x. End.
          |  Problem. x>3 -> x>=3 End.""".stripMargin,
        "x>3 -> x>=3".asFormula,
        Nil
      ) ::
      ParsedArchiveEntry(
        "Entry 4",
        "theorem",
        """ProgramVariables. R x. End.
          |  Problem. x>4 -> x>=4 End.""".stripMargin,
        "x>4 -> x>=4".asFormula,
        Nil
      ) :: Nil
  }

  it should "parse a list of mixed entries, lemmas, and theorems, whose names are again entry/lemma/theorem" in {
    val input =
      """ArchiveEntry "Entry 1".
        | ProgramVariables. R x. R y. End.
        | Problem. x>y -> x>=y End.
        |End.
        |
        |Lemma "Lemma 2: Some Entry".
        |  Functions. R x(). End.
        |  ProgramVariables R y. End.
        |  Problem. x()>=y -> x()>=y End.
        |  Tactic "Prop Proof of Lemma 2". prop End.
        |End.
        |
        |Theorem "Theorem 1: Some Entry".
        |  ProgramVariables. R x. End.
        |  Problem. x>3 -> x>=3 End.
        |End.
        |
        |ArchiveEntry "ArchiveEntry 4: Name".
        |  ProgramVariables. R x. End.
        |  Problem. x>4 -> x>=4 End.
        |End.
      """.stripMargin
    val entries = KeYmaeraXArchiveParser.parse(input)
    entries should have size 4
    entries should contain theSameElementsInOrderAs
      ParsedArchiveEntry(
        "Entry 1",
        "theorem",
        """ProgramVariables. R x. R y. End.
          | Problem. x>y -> x>=y End.""".stripMargin,
        "x>y -> x>=y".asFormula,
        Nil
      ) ::
        ParsedArchiveEntry(
          "Lemma 2: Some Entry",
          "lemma",
          """Functions. R x(). End.
            |  ProgramVariables R y. End.
            |  Problem. x()>=y -> x()>=y End.""".stripMargin,
          "x()>=y -> x()>=y".asFormula,
          ("Prop Proof of Lemma 2", prop) :: Nil
        ) ::
        ParsedArchiveEntry(
          "Theorem 1: Some Entry",
          "theorem",
          """ProgramVariables. R x. End.
            |  Problem. x>3 -> x>=3 End.""".stripMargin,
          "x>3 -> x>=3".asFormula,
          Nil
        ) ::
        ParsedArchiveEntry(
          "ArchiveEntry 4: Name",
          "theorem",
          """ProgramVariables. R x. End.
            |  Problem. x>4 -> x>=4 End.""".stripMargin,
          "x>4 -> x>=4".asFormula,
          Nil
        ) :: Nil
  }

  it should "parse a lemma entry" in {
    val input =
      """
        |Lemma "Entry 1".
        | ProgramVariables. R x. R y. End.
        | Problem. x>y -> x>=y End.
        |End.
      """.stripMargin
    val entries = KeYmaeraXArchiveParser.parse(input)
    entries.loneElement shouldBe ParsedArchiveEntry(
      "Entry 1",
      "lemma",
      """ProgramVariables. R x. R y. End.
        | Problem. x>y -> x>=y End.""".stripMargin,
      "x>y -> x>=y".asFormula,
      Nil
    )
  }

  it should "parse a theorem entry" in {
    val input =
      """
        |Theorem "Entry 1".
        | ProgramVariables. R x. R y. End.
        | Problem. x>y -> x>=y End.
        |End.
      """.stripMargin
    val entries = KeYmaeraXArchiveParser.parse(input)
    entries.loneElement shouldBe ParsedArchiveEntry(
      "Entry 1",
      "theorem",
      """ProgramVariables. R x. R y. End.
        | Problem. x>y -> x>=y End.""".stripMargin,
      "x>y -> x>=y".asFormula,
      Nil
    )
  }

  it should "split blocks by whole word only (lemma used in tactic)" in {
    val input =
      """
        |Lemma "Entry 1".
        | ProgramVariables. R x. R y. End.
        | Problem. x>y -> x>=y End.
        |End.
        |
        |Theorem "Entry 2".
        | ProgramVariables. R x. R y. End.
        | Problem. x>y -> x>=y End.
        | Tactic "Proof Entry 2". useLemma({`Entry 1`}) End.
        |End.
      """.stripMargin
    val entries = KeYmaeraXArchiveParser.parse(input)
    entries should have size 2
    entries.head shouldBe ParsedArchiveEntry(
      "Entry 1",
      "lemma",
      """ProgramVariables. R x. R y. End.
        | Problem. x>y -> x>=y End.""".stripMargin,
      "x>y -> x>=y".asFormula,
      Nil
    )
    entries(1) shouldBe ParsedArchiveEntry(
      "Entry 2",
      "theorem",
      """ProgramVariables. R x. R y. End.
        | Problem. x>y -> x>=y End.""".stripMargin,
      "x>y -> x>=y".asFormula,
      ("Proof Entry 2", TactixLibrary.useLemma("Entry 1", None))::Nil
    )
  }

  "Global definitions" should "be added to all entries" in {
    val input =
      """
        |SharedDefinitions.
        | B gt(R,R) <-> ( ._0 > ._1 ).
        |End.
        |
        |Lemma "Entry 1".
        | ProgramVariables. R x. R y. End.
        | Problem. gt(x,y) -> x>=y End.
        |End.
        |
        |Theorem "Entry 2".
        | Definitions. B geq(R,R) <-> ( ._0 >= ._1 ). End.
        | ProgramVariables. R x. R y. End.
        | Problem. gt(x,y) -> geq(x,y) End.
        | Tactic "Proof Entry 2". useLemma({`Entry 1`}) End.
        |End.
      """.stripMargin
    val entries = KeYmaeraXArchiveParser.parse(input)
    entries should have size 2
    entries.head shouldBe ParsedArchiveEntry(
      "Entry 1",
      "lemma",
      """Definitions.
        |B gt(R,R) <-> ( ._0 > ._1 ).
        |End.
        |ProgramVariables. R x. R y. End.
        | Problem. gt(x,y) -> x>=y End.""".stripMargin,
      "x>y -> x>=y".asFormula,
      Nil
    )
    entries(1) shouldBe ParsedArchiveEntry(
      "Entry 2",
      "theorem",
      """Definitions.
        |B gt(R,R) <-> ( ._0 > ._1 ).
        | B geq(R,R) <-> ( ._0 >= ._1 ). End.
        | ProgramVariables. R x. R y. End.
        | Problem. gt(x,y) -> geq(x,y) End.""".stripMargin,
      "x>y -> x>=y".asFormula,
      ("Proof Entry 2", TactixLibrary.useLemma("Entry 1", None))::Nil
    )
  }

  it should "not allow duplicates with local definitions" in {
    val input =
      """
        |SharedDefinitions.
        | B gt(R,R) <-> ( ._0 > ._1 ).
        |End.
        |
        |Lemma "Entry 1".
        | Definitions. B gt(R,R) <-> ( ._0 + 0 > ._1 ). End.
        | ProgramVariables. R x. R y. End.
        | Problem. gt(x,y) -> x>=y End.
        |End.
      """.stripMargin
    val ex = the [ParseException] thrownBy KeYmaeraXArchiveParser.parse(input)
    ex.msg should include ("Duplicate symbol 'gt'")
  }

  it should "not allow duplicates with local definitions even with different sorts" in {
    val input =
      """
        |SharedDefinitions.
        | B gt(R,R) <-> ( ._0 > ._1 ).
        |End.
        |
        |Lemma "Entry 1".
        | Definitions. R gt(R) = ( ._0 * 3 ). End.
        | ProgramVariables. R x. R y. End.
        | Problem. gt(x,y) -> x>=y End.
        |End.
      """.stripMargin
    val ex = the [ParseException] thrownBy KeYmaeraXArchiveParser.parse(input)
    ex.msg should include ("Duplicate symbol 'gt'")
  }

  it should "not swallow backslashes, for example \\exists" in {
    val input =
      """
        |SharedDefinitions.
        | B gt(R,R) <-> ( \exists t (t=1 & ._0*t > ._1) ).
        |End.
        |
        |Lemma "Entry 1".
        | Definitions. B geq(R,R) <-> ( ._0 >= ._1 ). End.
        | ProgramVariables. R x. R y. End.
        | Problem. gt(x,y) -> geq(x,y) End.
        |End.
      """.stripMargin
    val entries = KeYmaeraXArchiveParser.parse(input)
    entries.loneElement shouldBe ParsedArchiveEntry(
      "Entry 1",
      "lemma",
      """Definitions.
        |B gt(R,R) <-> ( \exists t (t=1 & ._0*t > ._1) ).
        | B geq(R,R) <-> ( ._0 >= ._1 ). End.
        | ProgramVariables. R x. R y. End.
        | Problem. gt(x,y) -> geq(x,y) End.""".stripMargin,
      "\\exists t (t=1 & x*t>y) -> x>=y".asFormula,
      Nil
    )
  }

}
