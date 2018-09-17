/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/

package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.btactics.{TacticTestBase, TactixLibrary}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core.{Bool, Expression, Real, Sort, Trafo, Tuple, Unit}
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXArchiveParser.Declaration
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import org.scalatest.LoneElement._
import org.scalatest.matchers.{MatchResult, Matcher}

/**
  * Tests the archive parser.
  * Created by smitsch on 12/29/16.
  */
class KeYmaeraXArchiveParserTests extends TacticTestBase {

  private def beDecl(right: Declaration) =
    new Matcher[Declaration] {
      def apply(left: Declaration): MatchResult =
        MatchResult(
          //compare without locations
          left.decls.map(v => v._1 -> (v._2._1, v._2._2, v._2._3)) == right.decls.map(v => v._1 -> (v._2._1, v._2._2, v._2._3)),
          left + " was not " + right,
          left + " was " + right
        )
    }

  "Archive parser" should "parse a model only entry" in {
    val input =
      """ArchiveEntry "Entry 1".
        | ProgramVariables. R x. R y. End.
        | Problem. x>y -> x>=y End.
        |End.""".stripMargin
    val entry = KeYmaeraXArchiveParser.parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "theorem"
    entry.fileContent shouldBe input
    entry.defs should beDecl(
      Declaration(Map(
        ("x", None) -> (None, Real, None, UnknownLocation),
        ("y", None) -> (None, Real, None, UnknownLocation)
      )))
    entry.model shouldBe "x>y -> x>=y".asFormula
    entry.tactics shouldBe empty
    entry.info shouldBe empty
  }

  it should "parse definitions before variables" in {
    val input =
      """
        |ArchiveEntry "Entry 1".
        | Definitions. R f() = (1). B p(R x) <-> (x>1). B q(R x, R y, R z) <-> (x+y>z). HP a ::= { ?p(x); }. End.
        | ProgramVariables. R x. R y. End.
        | Problem. p(x) & y>=0 -> q(x,y,f()) & [a;]p(x) End.
        |End.
      """.stripMargin
    val entry = KeYmaeraXArchiveParser.parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "theorem"
    entry.fileContent shouldBe input.trim()
    entry.defs should beDecl(
      Declaration(Map(
        ("f", None) -> (Some(Unit), Real, Some("1".asTerm), UnknownLocation),
        ("p", None) -> (Some(Real), Bool, Some(".>1".asFormula), UnknownLocation),
        ("q", None) -> (Some(Tuple(Real, Tuple(Real, Real))), Bool, Some("._0+._1>._2".asFormula), UnknownLocation),
        ("a", None) -> (Some(Unit), Trafo, Some("?p(x);".asProgram), UnknownLocation),
        ("x", None) -> (None, Real, None, UnknownLocation),
        ("y", None) -> (None, Real, None, UnknownLocation)
      )))
    entry.model shouldBe "x>1 & y>=0 -> x+y>1 & [?x>1;]x>1".asFormula
    entry.tactics shouldBe empty
    entry.info shouldBe empty
  }

  it should "parse definitions after variables" in {
    val input =
      """
        |ArchiveEntry "Entry 1".
        | ProgramVariables. R x. R y. End.
        | Definitions. R f() = (1). B p(R x) <-> (x>1). B q(R x, R y, R z) <-> (x+y>z). HP a ::= { ?p(x); }. End.
        | Problem. p(x) & y>=0 -> q(x,y,f()) & [a;]p(x) End.
        |End.
      """.stripMargin
    val entry = KeYmaeraXArchiveParser.parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "theorem"
    entry.fileContent shouldBe input.trim()
    entry.defs should beDecl(
      Declaration(Map(
        ("f", None) -> (Some(Unit), Real, Some("1".asTerm), UnknownLocation),
        ("p", None) -> (Some(Real), Bool, Some(".>1".asFormula), UnknownLocation),
        ("q", None) -> (Some(Tuple(Real, Tuple(Real, Real))), Bool, Some("._0+._1>._2".asFormula), UnknownLocation),
        ("a", None) -> (Some(Unit), Trafo, Some("?p(x);".asProgram), UnknownLocation),
        ("x", None) -> (None, Real, None, UnknownLocation),
        ("y", None) -> (None, Real, None, UnknownLocation)
      )))
    entry.model shouldBe "x>1 & y>=0 -> x+y>1 & [?x>1;]x>1".asFormula
    entry.tactics shouldBe empty
    entry.info shouldBe empty
  }

  it should "parse definitions with dot arguments" in {
    val input =
      """ArchiveEntry "Entry 1".
        | Definitions. R f(R). R g(R,R). R h(R) = (.+2). End.
        | ProgramVariables. R x. R y. End.
        | Problem. f(x)>g(x,y) & h(x)>5 End.
        |End.""".stripMargin
    val entry = KeYmaeraXArchiveParser.parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "theorem"
    entry.fileContent shouldBe input.trim()
    entry.defs should beDecl(
      Declaration(Map(
        ("f", None) -> (Some(Real), Real, None, UnknownLocation),
        ("g", None) -> (Some(Tuple(Real, Real)), Real, None, UnknownLocation),
        ("h", None) -> (Some(Real), Real, Some(".+2".asTerm), UnknownLocation),
        ("x", None) -> (None, Real, None, UnknownLocation),
        ("y", None) -> (None, Real, None, UnknownLocation)
      )))
    entry.model shouldBe "f(x)>g(x,y) & x+2>5".asFormula
    entry.tactics shouldBe empty
    entry.info shouldBe empty
  }

  it should "parse definitions without parentheses" in {
    val input = """ArchiveEntry "Entry 1".
                  | Definitions Real f() = 5; Bool p(R x) <-> x>0; End.
                  | Problem p(f()) End.
                  |End.""".stripMargin
    val entry = KeYmaeraXArchiveParser.parse(input).loneElement

    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "theorem"
    entry.fileContent shouldBe input.trim()
    entry.defs should beDecl(
      Declaration(Map(
        ("f", None) -> (Some(Unit), Real, Some("5".asTerm), UnknownLocation),
        ("p", None) -> (Some(Real), Bool, Some(".>0".asFormula), UnknownLocation)
      )))
    entry.model shouldBe "5>0".asFormula
    entry.tactics shouldBe empty
    entry.info shouldBe empty
  }

  it should "parse a problem without variables" in {
    val input =
      """ArchiveEntry "Entry 1".
        | Definitions. R f(). End.
        | Problem. f()>0 End.
        |End.""".stripMargin
    val entry = KeYmaeraXArchiveParser.parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "theorem"
    entry.fileContent shouldBe input.trim()
    entry.defs should beDecl(
      Declaration(Map(
        ("f", None) -> (Some(Unit), Real, None, UnknownLocation)
      )))
    entry.model shouldBe "f()>0".asFormula
    entry.tactics shouldBe empty
    entry.info shouldBe empty
  }

  it should "parse a problem that uses the allowed interpreted functions" in {
    val input =
      """ArchiveEntry "Entry 1".
        | Problem. abs(-5)>0 End.
        |End.""".stripMargin
    val entry = KeYmaeraXArchiveParser.parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "theorem"
    entry.fileContent shouldBe input.trim()
    entry.defs.decls shouldBe empty
    entry.model shouldBe "abs(-5)>0".asFormula
    entry.tactics shouldBe empty
    entry.info shouldBe empty
  }

  it should "parse a problem with neither definitions nor variables" in {
    val input =
      """ArchiveEntry "Entry 1".
        | Problem. false -> true End.
        |End.""".stripMargin
    val entry = KeYmaeraXArchiveParser.parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "theorem"
    entry.fileContent shouldBe input.trim()
    entry.defs.decls shouldBe empty
    entry.model shouldBe "false -> true".asFormula
    entry.tactics shouldBe empty
    entry.info shouldBe empty
  }

  it should "parse a plain problem format" in {
    val input =
      """ProgramVariables. R x. R y. End.
        |Problem. x>y -> x>=y End.
      """.stripMargin
    val entry = KeYmaeraXArchiveParser.parse(input).loneElement
    entry.name shouldBe "Unnamed"
    entry.kind shouldBe "theorem"
    entry.fileContent shouldBe input
    entry.defs should beDecl(
      Declaration(Map(
        ("x", None) -> (None, Real, None, UnknownLocation),
        ("y", None) -> (None, Real, None, UnknownLocation)
      )))
    entry.model shouldBe "x>y -> x>=y".asFormula
    entry.tactics shouldBe empty
    entry.info shouldBe empty
  }

  it should "refuse mixed plain and named entries" in {
    val input =
      """ProgramVariables. R x. R y. End.
        |Problem. x>y -> x>=y End.
        |
        |ArchiveEntry "Entry 2".
        |  ProgramVariables. R x. End.
        |  Problem. x>0 End.
        |End.
      """.stripMargin
    val ex = the [ParseException] thrownBy KeYmaeraXArchiveParser.parse(input)
    ex.msg should include ("Archives that start with an anonymous entry may not contain any other entries, but found ArchiveEntry")
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
    ex.msg should include ("Duplicate variable 'x'")
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
        | Definitions. HP a ::= { ?true; }. HP a ::= { ?false; }. End.
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
    val entry = KeYmaeraXArchiveParser.parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "theorem"
    entry.fileContent shouldBe input.trim()
    entry.defs should beDecl(
      Declaration(Map(
        ("x", None) -> (None, Real, None, UnknownLocation),
        ("y", None) -> (None, Real, None, UnknownLocation)
      )))
    entry.model shouldBe "x>y -> x>=y".asFormula
    entry.tactics shouldBe ("Proof 1", "implyR(1) & QE", implyR(1) & QE) :: Nil
    entry.info shouldBe empty
  }

  it should "parse a tactic without name" in withQE { _ =>
    val input =
      """
        |ArchiveEntry "Entry 1".
        | ProgramVariables. R x. R y. End.
        | Problem. x>y -> x>=y End.
        | Tactic. implyR(1) & QE End.
        |End.
      """.stripMargin
    val entry = KeYmaeraXArchiveParser.parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "theorem"
    entry.fileContent shouldBe input.trim()
    entry.defs should beDecl(
      Declaration(Map(
        ("x", None) -> (None, Real, None, UnknownLocation),
        ("y", None) -> (None, Real, None, UnknownLocation)
      )))
    entry.model shouldBe "x>y -> x>=y".asFormula
    entry.tactics shouldBe ("Unnamed", "implyR(1) & QE", implyR(1) & QE) :: Nil
    entry.info shouldBe empty
  }

  it should "parse a tactic with a comment in the beginning" in withQE { _ =>
    val input =
      """
        |ArchiveEntry "Entry 1".
        | ProgramVariables. R x. R y. End.
        | Problem. x>y -> x>=y End.
        | Tactic "Empty". /* a comment */ nil partial End.
        |End.
      """.stripMargin
    val entry = KeYmaeraXArchiveParser.parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "theorem"
    entry.fileContent shouldBe input.trim()
    entry.defs should beDecl(
      Declaration(Map(
        ("x", None) -> (None, Real, None, UnknownLocation),
        ("y", None) -> (None, Real, None, UnknownLocation)
      )))
    entry.model shouldBe "x>y -> x>=y".asFormula
    entry.tactics shouldBe ("Empty", "nil partial", nil partial) :: Nil
    entry.info shouldBe empty
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
    val entry = KeYmaeraXArchiveParser.parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "theorem"
    entry.fileContent shouldBe input.trim()
    entry.defs should beDecl(
      Declaration(Map(
        ("x", None) -> (None, Real, None, UnknownLocation),
        ("y", None) -> (None, Real, None, UnknownLocation)
      )))
    entry.model shouldBe "x>y -> x>=y".asFormula
    entry.tactics shouldBe ("Proof 1", "implyR(1) & QE", implyR(1) & QE) :: ("Proof 2", "implyR('R)", implyR('R)) :: Nil
    entry.info shouldBe empty
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
    val entry1 = entries.head
    entry1.name shouldBe "Entry 1"
    entry1.kind shouldBe "theorem"
    entry1.fileContent shouldBe """ArchiveEntry "Entry 1".
                                  | ProgramVariables. R x. R y. End.
                                  | Problem. x>y -> x>=y End.
                                  |End.""".stripMargin
    entry1.defs should beDecl(
      Declaration(Map(
        ("x", None) -> (None, Real, None, UnknownLocation),
        ("y", None) -> (None, Real, None, UnknownLocation)
      )))
    entry1.model shouldBe "x>y -> x>=y".asFormula
    entry1.tactics shouldBe empty
    entry1.info shouldBe empty

    val entry2 = entries.last
    entry2.name shouldBe "Entry 2"
    entry2.kind shouldBe "theorem"
    entry2.fileContent shouldBe """ArchiveEntry "Entry 2".
                                  |  Functions. R x(). End.
                                  |  ProgramVariables R y. End.
                                  |  Problem. x()>=y -> x()>=y End.
                                  |  Tactic "Prop Proof". prop End.
                                  |End.""".stripMargin
    entry2.defs should beDecl(
      Declaration(Map(
        ("x", None) -> (Some(Unit), Real, None, UnknownLocation),
        ("y", None) -> (None, Real, None, UnknownLocation)
      )))
    entry2.model shouldBe "x()>=y -> x()>=y".asFormula
    entry2.tactics shouldBe ("Prop Proof", "prop", prop) :: Nil
    entry2.info shouldBe empty
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

    val entry1 = entries.head
    entry1.name shouldBe "Entry 1"
    entry1.kind shouldBe "theorem"
    entry1.fileContent shouldBe """ArchiveEntry "Entry 1".
                                  | ProgramVariables. R x. R y. End.
                                  | Problem. x>y -> x>=y End.
                                  |End.""".stripMargin
    entry1.defs should beDecl(
      Declaration(Map(
        ("x", None) -> (None, Real, None, UnknownLocation),
        ("y", None) -> (None, Real, None, UnknownLocation)
      )))
    entry1.model shouldBe "x>y -> x>=y".asFormula
    entry1.tactics shouldBe empty
    entry1.info shouldBe empty

    val entry2 = entries(1)
    entry2.name shouldBe "Entry 2"
    entry2.kind shouldBe "lemma"
    entry2.fileContent shouldBe """Lemma "Entry 2".
                                  |  Functions. R x(). End.
                                  |  ProgramVariables R y. End.
                                  |  Problem. x()>=y -> x()>=y End.
                                  |  Tactic "Prop Proof". prop End.
                                  |End.""".stripMargin
    entry2.defs should beDecl(
      Declaration(Map(
        ("x", None) -> (Some(Unit), Real, None, UnknownLocation),
        ("y", None) -> (None, Real, None, UnknownLocation)
      )))
    entry2.model shouldBe "x()>=y -> x()>=y".asFormula
    entry2.tactics shouldBe ("Prop Proof", "prop", prop) :: Nil
    entry2.info shouldBe empty

    val entry3 = entries(2)
    entry3.name shouldBe "Entry 3"
    entry3.kind shouldBe "theorem"
    entry3.fileContent shouldBe """Theorem "Entry 3".
                                  |  ProgramVariables. R x. End.
                                  |  Problem. x>3 -> x>=3 End.
                                  |End.""".stripMargin
    entry3.defs should beDecl(
      Declaration(Map(
        ("x", None) -> (None, Real, None, UnknownLocation)
      )))
    entry3.model shouldBe "x>3 -> x>=3".asFormula
    entry3.tactics shouldBe empty
    entry3.info shouldBe empty

    val entry4 = entries(3)
    entry4.name shouldBe "Entry 4"
    entry4.kind shouldBe "theorem"
    entry4.fileContent shouldBe """ArchiveEntry "Entry 4".
                                  |  ProgramVariables. R x. End.
                                  |  Problem. x>4 -> x>=4 End.
                                  |End.""".stripMargin
    entry4.defs should beDecl(
      Declaration(Map(
        ("x", None) -> (None, Real, None, UnknownLocation)
      )))
    entry4.model shouldBe "x>4 -> x>=4".asFormula
    entry4.tactics shouldBe empty
    entry4.info shouldBe empty
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

    val entry1 = entries.head
    entry1.name shouldBe "Entry 1"
    entry1.kind shouldBe "theorem"
    entry1.fileContent shouldBe """ArchiveEntry "Entry 1".
                                  | ProgramVariables. R x. R y. End.
                                  | Problem. x>y -> x>=y End.
                                  |End.""".stripMargin
    entry1.defs should beDecl(
      Declaration(Map(
        ("x", None) -> (None, Real, None, UnknownLocation),
        ("y", None) -> (None, Real, None, UnknownLocation)
      )))
    entry1.model shouldBe "x>y -> x>=y".asFormula
    entry1.tactics shouldBe empty
    entry1.info shouldBe empty

    val entry2 = entries(1)
    entry2.name shouldBe "Lemma 2: Some Entry"
    entry2.kind shouldBe "lemma"
    entry2.fileContent shouldBe """Lemma "Lemma 2: Some Entry".
                                  |  Functions. R x(). End.
                                  |  ProgramVariables R y. End.
                                  |  Problem. x()>=y -> x()>=y End.
                                  |  Tactic "Prop Proof of Lemma 2". prop End.
                                  |End.""".stripMargin
    entry2.defs should beDecl(
      Declaration(Map(
        ("x", None) -> (Some(Unit), Real, None, UnknownLocation),
        ("y", None) -> (None, Real, None, UnknownLocation)
      )))
    entry2.model shouldBe "x()>=y -> x()>=y".asFormula
    entry2.tactics shouldBe ("Prop Proof of Lemma 2", "prop", prop) :: Nil
    entry2.info shouldBe empty

    val entry3 = entries(2)
    entry3.name shouldBe "Theorem 1: Some Entry"
    entry3.kind shouldBe "theorem"
    entry3.fileContent shouldBe """Theorem "Theorem 1: Some Entry".
                                  |  ProgramVariables. R x. End.
                                  |  Problem. x>3 -> x>=3 End.
                                  |End.""".stripMargin
    entry3.defs should beDecl(
      Declaration(Map(
        ("x", None) -> (None, Real, None, UnknownLocation)
      )))
    entry3.model shouldBe "x>3 -> x>=3".asFormula
    entry3.tactics shouldBe empty
    entry3.info shouldBe empty

    val entry4 = entries(3)
    entry4.name shouldBe "ArchiveEntry 4: Name"
    entry4.kind shouldBe "theorem"
    entry4.fileContent shouldBe """ArchiveEntry "ArchiveEntry 4: Name".
                                  |  ProgramVariables. R x. End.
                                  |  Problem. x>4 -> x>=4 End.
                                  |End.""".stripMargin
    entry4.defs should beDecl(
      Declaration(Map(
        ("x", None) -> (None, Real, None, UnknownLocation)
      )))
    entry4.model shouldBe "x>4 -> x>=4".asFormula
    entry4.tactics shouldBe empty
    entry4.info shouldBe empty
  }

  it should "parse a lemma entry" in {
    val input =
      """
        |Lemma "Entry 1".
        | ProgramVariables. R x. R y. End.
        | Problem. x>y -> x>=y End.
        |End.
      """.stripMargin
    val entry = KeYmaeraXArchiveParser.parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "lemma"
    entry.fileContent shouldBe input.trim()
    entry.defs should beDecl(
      Declaration(Map(
        ("x", None) -> (None, Real, None, UnknownLocation),
        ("y", None) -> (None, Real, None, UnknownLocation)
      )))
    entry.model shouldBe "x>y -> x>=y".asFormula
    entry.tactics shouldBe empty
    entry.info shouldBe empty
  }

  it should "parse a theorem entry" in {
    val input =
      """
        |Theorem "Entry 1".
        | ProgramVariables. R x. R y. End.
        | Problem. x>y -> x>=y End.
        |End.
      """.stripMargin
    val entry = KeYmaeraXArchiveParser.parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "theorem"
    entry.fileContent shouldBe input.trim
    entry.defs should beDecl(
      Declaration(Map(
        ("x", None) -> (None, Real, None, UnknownLocation),
        ("y", None) -> (None, Real, None, UnknownLocation)
      )))
    entry.model shouldBe "x>y -> x>=y".asFormula
    entry.tactics shouldBe empty
    entry.info shouldBe empty
  }

  it should "split blocks by whole word only (lemma used in tactic)" in {
    val input =
      """Lemma "Entry 1".
        | ProgramVariables. R x. R y. End.
        | Problem. x>y -> x>=y End.
        |End.
        |
        |Theorem "Entry 2".
        | ProgramVariables. R x. R y. End.
        | Problem. x>y -> x>=y End.
        | Tactic "Proof Entry 2". useLemma({`Entry 1`}) End.
        |End.""".stripMargin
    val entries = KeYmaeraXArchiveParser.parse(input)
    entries should have size 2

    val entry1 = entries.head
    entry1.name shouldBe "Entry 1"
    entry1.kind shouldBe "lemma"
    entry1.fileContent shouldBe
      """Lemma "Entry 1".
        | ProgramVariables. R x. R y. End.
        | Problem. x>y -> x>=y End.
        |End.""".stripMargin
    entry1.defs should beDecl(
      Declaration(Map(
        ("x", None) -> (None, Real, None, UnknownLocation),
        ("y", None) -> (None, Real, None, UnknownLocation)
      )))
    entry1.model shouldBe "x>y -> x>=y".asFormula
    entry1.tactics shouldBe empty
    entry1.info shouldBe empty

    val entry2 = entries(1)
    entry2.name shouldBe "Entry 2"
    entry2.kind shouldBe "theorem"
    entry2.fileContent shouldBe
      """Theorem "Entry 2".
        | ProgramVariables. R x. R y. End.
        | Problem. x>y -> x>=y End.
        | Tactic "Proof Entry 2". useLemma({`Entry 1`}) End.
        |End.""".stripMargin
    entry2.defs should beDecl(
      Declaration(Map(
        ("x", None) -> (None, Real, None, UnknownLocation),
        ("y", None) -> (None, Real, None, UnknownLocation)
      )))
    entry2.model shouldBe "x>y -> x>=y".asFormula
    entry2.tactics shouldBe ("Proof Entry 2", "useLemma({`Entry 1`})", TactixLibrary.useLemma("Entry 1", None))::Nil
    entry2.info shouldBe empty
  }

  it should "parse meta information" in {
    val input =
      """Lemma "Entry 1".
        | Description "The description of entry 1".
        | Title "A short entry 1 title".
        | Link "http://web.keymaerax.org/show/entry1".
        | ProgramVariables. R x. R y. End.
        | Problem. x>y -> y<x End.
        |End.""".stripMargin
    val entry = KeYmaeraXArchiveParser.parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "lemma"
    entry.fileContent shouldBe
      """Lemma "Entry 1".
        | Description "The description of entry 1".
        | Title "A short entry 1 title".
        | Link "http://web.keymaerax.org/show/entry1".
        | ProgramVariables. R x. R y. End.
        | Problem. x>y -> y<x End.
        |End.""".stripMargin
    entry.defs should beDecl(
      Declaration(Map(
        ("x", None) -> (None, Real, None, UnknownLocation),
        ("y", None) -> (None, Real, None, UnknownLocation)
      )))
    entry.model shouldBe "x>y -> y<x".asFormula
    entry.tactics shouldBe empty
    entry.info shouldBe Map(
      "Description" -> "The description of entry 1",
      "Title" -> "A short entry 1 title",
      "Link" -> "http://web.keymaerax.org/show/entry1")
  }

  "Global definitions" should "be added to all entries" in {
    val input =
      """SharedDefinitions.
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
        |End.""".stripMargin
    val entries = KeYmaeraXArchiveParser.parse(input)
    entries should have size 2

    val entry1 = entries.head
    entry1.name shouldBe "Entry 1"
    entry1.kind shouldBe "lemma"
    entry1.fileContent shouldBe
      """SharedDefinitions.
        |B gt(R,R) <-> ( ._0 > ._1 ).
        |End.
        |Lemma "Entry 1".
        | ProgramVariables. R x. R y. End.
        | Problem. gt(x,y) -> x>=y End.
        |End.""".stripMargin
    entry1.defs should beDecl(
      Declaration(Map(
        ("gt", None) -> (Some(Tuple(Real, Real)), Bool, Some("._0>._1".asFormula), UnknownLocation),
        ("x", None) -> (None, Real, None, UnknownLocation),
        ("y", None) -> (None, Real, None, UnknownLocation)
      )))
    entry1.model shouldBe "x>y -> x>=y".asFormula
    entry1.tactics shouldBe empty
    entry1.info shouldBe empty

    val entry2 = entries(1)
    entry2.name shouldBe "Entry 2"
    entry2.kind shouldBe "theorem"
    entry2.fileContent shouldBe
      """SharedDefinitions.
        |B gt(R,R) <-> ( ._0 > ._1 ).
        |End.
        |Theorem "Entry 2".
        | Definitions. B geq(R,R) <-> ( ._0 >= ._1 ). End.
        | ProgramVariables. R x. R y. End.
        | Problem. gt(x,y) -> geq(x,y) End.
        | Tactic "Proof Entry 2". useLemma({`Entry 1`}) End.
        |End.""".stripMargin
    entry2.defs should beDecl(
      Declaration(Map(
        ("gt", None) -> (Some(Tuple(Real, Real)), Bool, Some("._0 > ._1".asFormula), UnknownLocation),
        ("geq", None) -> (Some(Tuple(Real, Real)), Bool, Some("._0 >= ._1".asFormula), UnknownLocation),
        ("x", None) -> (None, Real, None, UnknownLocation),
        ("y", None) -> (None, Real, None, UnknownLocation)
      )))
    entry2.model shouldBe "x>y -> x>=y".asFormula
    entry2.tactics shouldBe ("Proof Entry 2", "useLemma({`Entry 1`})", TactixLibrary.useLemma("Entry 1", None))::Nil
    entry2.info shouldBe empty
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
    ex.msg should include ("Symbol 'gt' overrides inherited definition; must declare override")
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
    ex.msg should include ("Symbol 'gt' overrides inherited definition; must declare override")
  }

  it should "not swallow backslashes, for example \\exists" in {
    val input =
      """SharedDefinitions.
        | B gt(R,R) <-> ( \exists t (t=1 & ._0*t > ._1) ).
        |End.
        |
        |Lemma "Entry 1".
        | Definitions. B geq(R,R) <-> ( ._0 >= ._1 ). End.
        | ProgramVariables. R x. R y. End.
        | Problem. gt(x,y) -> geq(x,y) End.
        |End.""".stripMargin
    val entry = KeYmaeraXArchiveParser.parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "lemma"
    entry.fileContent shouldBe
      """SharedDefinitions.
        |B gt(R,R) <-> ( \exists t (t=1 & ._0*t > ._1) ).
        |End.
        |Lemma "Entry 1".
        | Definitions. B geq(R,R) <-> ( ._0 >= ._1 ). End.
        | ProgramVariables. R x. R y. End.
        | Problem. gt(x,y) -> geq(x,y) End.
        |End.""".stripMargin
    entry.defs should beDecl(
      Declaration(Map(
        ("gt", None) -> (Some(Tuple(Real, Real)), Bool, Some("\\exists t (t=1 & ._0*t > ._1)".asFormula), UnknownLocation),
        ("geq", None) -> (Some(Tuple(Real, Real)), Bool, Some("._0 >= ._1".asFormula), UnknownLocation),
        ("x", None) -> (None, Real, None, UnknownLocation),
        ("y", None) -> (None, Real, None, UnknownLocation)
      )))
    entry.model shouldBe "\\exists t (t=1 & x*t>y) -> x>=y".asFormula
    entry.tactics shouldBe empty
    entry.info shouldBe empty
  }

  "Archive parser error message" should "report an invalid meta info key" in {
    the [ParseException] thrownBy KeYmaeraXArchiveParser.parse(
      """ArchiveEntry "Entry 1".
        | MetaInfo "Invalid key".
        | ProgramVariables. R x. End.
        | Problem. x>0 End.
        |End.""".stripMargin
    ) should have message """2:2 Invalid meta info key 'MetaInfo'
                            |Found:    MetaInfo (ID("MetaInfo")) at 2:2 to 2:9
                            |Expected: Link,Citation,Title,Description,Author,See""".stripMargin
  }

  it should "report invalid meta info value" in {
    the [ParseException] thrownBy KeYmaeraXArchiveParser.parse(
      """ArchiveEntry "Entry 1"
        | Title InvalidValue.
        | ProgramVariables R x. End.
        | Problem x>0 End.
        |End.""".stripMargin
    ) should have message """2:8 Invalid meta info value
                            |Found:    InvalidValue (ID("InvalidValue")) at 2:8 to 2:19
                            |Expected: <string> (DOUBLE_QUOTES_STRING)""".stripMargin
  }

  it should "report missing meta info delimiter" in {
    the [ParseException] thrownBy KeYmaeraXArchiveParser.parse(
      """ArchiveEntry "Entry 1".
        | Title "A title"
        | ProgramVariables. R x. End.
        | Problem. x>0 End.
        |End.""".stripMargin
    ) should have message """3:2 Missing meta info delimiter
                            |Found:    ProgramVariables (PROGRAM_VARIABLES_BLOCK$) at 3:2 to 3:17
                            |Expected: . (PERIOD$)
                            |      or: ; (SEMI$)""".stripMargin
  }

  it should "report missing or misplaced problem blocks" in {
    the [ParseException] thrownBy KeYmaeraXArchiveParser.parse(
      """ArchiveEntry "Entry 1".
        | ProgramVariables. R x. End.
        |End.""".stripMargin
    ) should have message """3:1 Missing problem block
                            |Found:    End. (END_BLOCK$) at 3:1 to 3:4
                            |Expected: Problem""".stripMargin

    the [ParseException] thrownBy KeYmaeraXArchiveParser.parse(
      """ArchiveEntry "Entry 1".
        | ProgramVariables. R x. End.
        | Tactic "Proof". implyR(1) End.
        |End.""".stripMargin
    ) should have message """3:2 Missing problem block
                           |Found:    Tactic (TACTIC_BLOCK$) at 3:2 to 3:7
                           |Expected: Problem""".stripMargin

    the [ParseException] thrownBy KeYmaeraXArchiveParser.parse(
      """ArchiveEntry "Entry 1".
        | ProgramVariables. R x. End.
        | Tactic "Proof". implyR(1) End.
        | Problem. x>0 End.
        |End.""".stripMargin
    ) should have message """3:2 Misplaced problem block: problem expected before tactics
                           |Found:    Tactic (TACTIC_BLOCK$) at 3:2 to 3:7
                           |Expected: Problem""".stripMargin
  }

  it should "report misplaced variables or definitions" in {
    the [ParseException] thrownBy KeYmaeraXArchiveParser.parse(
      """ArchiveEntry "Entry 1".
        | Problem. x>0 End.
        | ProgramVariables. R x. End.
        |End.""".stripMargin
    ) should have message """2:2 Misplaced definitions/program variables: expected before problem
                            |Found:    Problem (PROBLEM_BLOCK$) at 2:2 to 2:8
                            |Expected: ProgramVariables""".stripMargin

    the [ParseException] thrownBy KeYmaeraXArchiveParser.parse(
      """ArchiveEntry "Entry 1".
        | Problem. x>0 End.
        | Definitions. R f(). End.
        |End.""".stripMargin
    ) should have message """2:2 Misplaced definitions/program variables: expected before problem
                            |Found:    Problem (PROBLEM_BLOCK$) at 2:2 to 2:8
                            |Expected: Definitions""".stripMargin

    the [ParseException] thrownBy KeYmaeraXArchiveParser.parse(
      """ArchiveEntry "Entry 1".
        | Problem. x>0 End.
        | ProgramVariables. R x. End.
        | Definitions. R f(). End.
        |End.""".stripMargin
    ) should have message """2:2 Misplaced definitions/program variables: expected before problem
                           |Found:    Problem (PROBLEM_BLOCK$) at 2:2 to 2:8
                           |Expected: ProgramVariables""".stripMargin
  }

  it should "report missing archive names" in {
    the [ParseException] thrownBy KeYmaeraXArchiveParser.parse(
      """ArchiveEntry.
        | ProgramVariables. R x. End.
        | Problem. x>0 End.
        |End.""".stripMargin
    ) should have message """1:13 Missing archive name
                            |Found:    . (PERIOD$) at 1:13
                            |Expected: "<string>"""".stripMargin
  }

  it should "report a missing archive entry delimiter" in {
    the [ParseException] thrownBy KeYmaeraXArchiveParser.parse(
      """ArchiveEntry "Entry 1".
        | Problem. true End.""".stripMargin
    ) should have message """2:20 Missing entry delimiter
                            |Found:    <EOF> (EOF$) at 2:20 to EOF$
                            |Expected: End.""".stripMargin

    the [ParseException] thrownBy KeYmaeraXArchiveParser.parse(
      """ArchiveEntry "Entry 1".
        | Problem. true End.
        |Theorem "Entry 2".
        | Problem. false->true End.
        |End.""".stripMargin
    ) should have message """3:1 Missing entry delimiter
                           |Found:    ArchiveEntry|Lemma|Theorem|Exercise (Theorem) at 3:1 to 3:7
                           |Expected: End.""".stripMargin
  }

  it should "report a missing definitions delimiter" in {
    the [ParseException] thrownBy KeYmaeraXArchiveParser.parse(
      """ArchiveEntry "Entry 1".
        | Definitions. R f().
        | Problem. true End.
        |End.""".stripMargin
    ) should have message """3:2 Missing definitions delimiter
                            |Found:    Problem (PROBLEM_BLOCK$) at 3:2 to 3:8
                            |Expected: End.""".stripMargin
  }

  it should "report a missing program variables delimiter" in {
    the [ParseException] thrownBy KeYmaeraXArchiveParser.parse(
      """ArchiveEntry "Entry 1".
        | ProgramVariables R x.
        | Problem. true End.
        |End.""".stripMargin
    ) should have message """3:2 Missing program variables delimiter
                            |Found:    Problem (PROBLEM_BLOCK$) at 3:2 to 3:8
                            |Expected: End.""".stripMargin
  }

  it should "report a missing problem delimiter" in {
    the [ParseException] thrownBy KeYmaeraXArchiveParser.parse(
      """ArchiveEntry "Entry 1".
        | Problem. true
        | Tactic "Proof". close End.
        |End.""".stripMargin
    ) should have message """3:2 Missing problem delimiter
                            |Found:    Tactic (TACTIC_BLOCK$) at 3:2 to 3:7
                            |Expected: End.""".stripMargin

    the [ParseException] thrownBy KeYmaeraXArchiveParser.parse(
      """ArchiveEntry "Entry 1".
        | Problem. true""".stripMargin
    ) should have message """2:15 Missing problem delimiter
                           |Found:    <EOF> (EOF$) at 2:15 to EOF$
                           |Expected: End.""".stripMargin
  }

  it should "report misplaced function, predicate, or program definitions" in {
    the [ParseException] thrownBy KeYmaeraXArchiveParser.parse(
      """ArchiveEntry "Entry 1".
        | ProgramVariables R f(). End.
        | Problem. true End.
        |End.""".stripMargin
    ) should have message """2:22 Function definition only allowed in Definitions block
                            |Found:    ( (LPAREN$) at 2:22
                            |Expected: ; or ,""".stripMargin

    the [ParseException] thrownBy KeYmaeraXArchiveParser.parse(
      """ArchiveEntry "Entry 1".
        | ProgramVariables B p(). End.
        | Problem. true End.
        |End.""".stripMargin
    ) should have message """2:19 Predicate and program definitions only allowed in Definitions block
                            |Found:    B (ID("B")) at 2:19
                            |Expected: Real""".stripMargin

    the [ParseException] thrownBy KeYmaeraXArchiveParser.parse(
      """ArchiveEntry "Entry 1".
        | ProgramVariables HP a. End.
        | Problem. true End.
        |End.""".stripMargin
    ) should have message """2:19 Predicate and program definitions only allowed in Definitions block
                           |Found:    HP (ID("HP")) at 2:19 to 2:20
                           |Expected: Real""".stripMargin

    the [ParseException] thrownBy KeYmaeraXArchiveParser.parse(
      """ArchiveEntry "Entry 1".
        | ProgramVariables R x &. End.
        | Problem. true End.
        |End.""".stripMargin
    ) should have message """2:23 Unexpected token in ProgramVariables block
                           |Found:    & (AMP$) at 2:23
                           |Expected: ; or ,""".stripMargin
  }

  it should "report function definition errors" in {
    the [ParseException] thrownBy KeYmaeraXArchiveParser.parse(
      """ArchiveEntry "Entry 1".
        | Definitions R f() & . End.
        | Problem. true End.
        |End.""".stripMargin
    ) should have message """2:20 Unexpected token in function definition
                            |Found:    & (AMP$) at 2:20
                            |Expected: = (EQ$)
                            |      or: ; (SEMI$)""".stripMargin

    the [ParseException] thrownBy KeYmaeraXArchiveParser.parse(
      """ArchiveEntry "Entry 1".
        | Definitions R f() <-> 5; End.
        | Problem. true End.
        |End.""".stripMargin
    ) should have message """2:20 Function must be defined by equality
                            |Found:    <-> (EQUIV$) at 2:20 to 2:22
                            |Expected: =""".stripMargin

    the [ParseException] thrownBy KeYmaeraXArchiveParser.parse(
      """ArchiveEntry "Entry 1".
        | Definitions R f() = 5!=7; End.
        | Problem. true End.
        |End.""".stripMargin
    ) should have message """2:22 Function definition expects a Term
                            |Found:    5!=7 at 2:22 to 2:25
                            |Expected: Term""".stripMargin
  }

  it should "report predicate definition errors" in {
    the [ParseException] thrownBy KeYmaeraXArchiveParser.parse(
      """ArchiveEntry "Entry 1".
        | Definitions B p() & . End.
        | Problem. true End.
        |End.""".stripMargin
    ) should have message """2:20 Unexpected token in predicate definition
                            |Found:    & (AMP$) at 2:20
                            |Expected: <->""".stripMargin

    the [ParseException] thrownBy KeYmaeraXArchiveParser.parse(
      """ArchiveEntry "Entry 1".
        | Definitions B p() = 5>0; End.
        | Problem. true End.
        |End.""".stripMargin
    ) should have message """2:20 Predicate must be defined by equivalence
                            |Found:    = (EQ$) at 2:20
                            |Expected: <->""".stripMargin

    the [ParseException] thrownBy KeYmaeraXArchiveParser.parse(
      """ArchiveEntry "Entry 1".
        | Definitions B p() <-> 5+7; End.
        | Problem. true End.
        |End.""".stripMargin
    ) should have message """2:24 Predicate definition expects a Formula
                            |Found:    5+7 at 2:24 to 2:26
                            |Expected: Formula""".stripMargin
  }
}
