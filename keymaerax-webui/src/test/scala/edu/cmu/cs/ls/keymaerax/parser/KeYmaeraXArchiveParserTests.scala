/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/

package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase
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
      """ProgramVariables. R x. R y. End.
        | Problem. x>y -> x>=y End.""".stripMargin,
      "theorem",
      "x>y -> x>=y".asFormula,
      Nil
    )
  }

  it should "parse a model and tactic entry" in withMathematica { tool =>
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
      """ProgramVariables. R x. R y. End.
        | Problem. x>y -> x>=y End.""".stripMargin,
      "theorem",
      "x>y -> x>=y".asFormula,
      ("Proof 1", implyR(1) & QE) :: Nil
    )
  }

  it should "parse a model with several tactics" in withMathematica { tool =>
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
      """ProgramVariables. R x. R y. End.
        | Problem. x>y -> x>=y End.""".stripMargin,
      "theorem",
      "x>y -> x>=y".asFormula,
      ("Proof 1", implyR(1) & QE) :: ("Proof 2", implyR('R)) :: Nil
    )
  }

  it should "parse a list of model and tactic entries" in withMathematica { tool =>
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
      """ProgramVariables. R x. R y. End.
        | Problem. x>y -> x>=y End.""".stripMargin,
      "theorem",
      "x>y -> x>=y".asFormula,
      Nil
    )
    entries.last shouldBe ParsedArchiveEntry(
      "Entry 2",
      """Functions. R x(). End.
        |  ProgramVariables R y. End.
        |  Problem. x()>=y -> x()>=y End.""".stripMargin,
      "theorem",
      "x()>=y -> x()>=y".asFormula,
      ("Prop Proof", prop) :: Nil
    )
  }

  it should "parse a list of mixed entries, lemmas, and theorems" in withMathematica { tool =>
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
        """ProgramVariables. R x. R y. End.
          | Problem. x>y -> x>=y End.""".stripMargin,
        "theorem",
        "x>y -> x>=y".asFormula,
        Nil
      ) ::
      ParsedArchiveEntry(
        "Entry 2",
        """Functions. R x(). End.
          |  ProgramVariables R y. End.
          |  Problem. x()>=y -> x()>=y End.""".stripMargin,
        "lemma",
        "x()>=y -> x()>=y".asFormula,
        ("Prop Proof", prop) :: Nil
      ) ::
      ParsedArchiveEntry(
        "Entry 3",
        """ProgramVariables. R x. End.
          |  Problem. x>3 -> x>=3 End.""".stripMargin,
        "theorem",
        "x>3 -> x>=3".asFormula,
        Nil
      ) ::
      ParsedArchiveEntry(
        "Entry 4",
        """ProgramVariables. R x. End.
          |  Problem. x>4 -> x>=4 End.""".stripMargin,
        "theorem",
        "x>4 -> x>=4".asFormula,
        Nil
      ) :: Nil
  }

  it should "parse a list of mixed entries, lemmas, and theorems, whose names are again entry/lemma/theorem" in withMathematica { tool =>
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
        |  Tactic "Prop Proof". prop End.
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
        """ProgramVariables. R x. R y. End.
          | Problem. x>y -> x>=y End.""".stripMargin,
        "theorem",
        "x>y -> x>=y".asFormula,
        Nil
      ) ::
        ParsedArchiveEntry(
          "Lemma 2: Some Entry",
          """Functions. R x(). End.
            |  ProgramVariables R y. End.
            |  Problem. x()>=y -> x()>=y End.""".stripMargin,
          "lemma",
          "x()>=y -> x()>=y".asFormula,
          ("Prop Proof", prop) :: Nil
        ) ::
        ParsedArchiveEntry(
          "Theorem 1: Some Entry",
          """ProgramVariables. R x. End.
            |  Problem. x>3 -> x>=3 End.""".stripMargin,
          "theorem",
          "x>3 -> x>=3".asFormula,
          Nil
        ) ::
        ParsedArchiveEntry(
          "ArchiveEntry 4: Name",
          """ProgramVariables. R x. End.
            |  Problem. x>4 -> x>=4 End.""".stripMargin,
          "theorem",
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
      """ProgramVariables. R x. R y. End.
        | Problem. x>y -> x>=y End.""".stripMargin,
      "lemma",
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
      """ProgramVariables. R x. R y. End.
        | Problem. x>y -> x>=y End.""".stripMargin,
      "theorem",
      "x>y -> x>=y".asFormula,
      Nil
    )
  }

}
