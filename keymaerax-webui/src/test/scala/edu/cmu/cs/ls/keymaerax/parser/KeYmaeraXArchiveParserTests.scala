/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/

package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

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
    entries.head shouldBe (
      "Entry 1",
      """ProgramVariables. R x. R y. End.
        | Problem. x>y -> x>=y End.""".stripMargin,
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
    entries.head shouldBe (
      "Entry 1",
      """ProgramVariables. R x. R y. End.
        | Problem. x>y -> x>=y End.""".stripMargin,
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
    entries should have size 1
    entries.head shouldBe (
      "Entry 1",
      """ProgramVariables. R x. R y. End.
        | Problem. x>y -> x>=y End.""".stripMargin,
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
    entries.head shouldBe (
      "Entry 1",
      """ProgramVariables. R x. R y. End.
        | Problem. x>y -> x>=y End.""".stripMargin,
      "x>y -> x>=y".asFormula,
      Nil
    )
    entries.last shouldBe (
      "Entry 2",
      """Functions. R x(). End.
        |  ProgramVariables R y. End.
        |  Problem. x()>=y -> x()>=y End.""".stripMargin,
      "x()>=y -> x()>=y".asFormula,
      ("Prop Proof", prop) :: Nil
    )
  }

}
