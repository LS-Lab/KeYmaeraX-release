/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/

package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.bellerophon.parser.{BellePrettyPrinter, DLBelleParser}
import edu.cmu.cs.ls.keymaerax.bellerophon.{Expand, ExpandAll, ReflectiveExpressionBuilder, SeqTactic}
import edu.cmu.cs.ls.keymaerax.btactics.{DebuggingTactics, FixedGenerator, TacticTestBase, TactixLibrary}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core.{Assign, Bool, DotTerm, Function, Greater, Number, Pair, Plus, PredOf, Real, SubstitutionPair, Trafo, Tuple, Unit, Variable}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import org.scalatest.Inside.inside
import org.scalatest.LoneElement._
import org.scalatest.PrivateMethodTester
import org.scalatest.matchers.{MatchResult, Matcher}
import testHelper.KeYmaeraXTestTags.TodoTest

/**
  * Tests the archive parser.
  * Created by smitsch on 12/29/16.
  * @author Stefan Mitsch
  * @author Andre Platzer
  */
class KeYmaeraXArchiveParserTests extends TacticTestBase with PrivateMethodTester {
  private val parser = new DLArchiveParser(new DLBelleParser(BellePrettyPrinter, ReflectiveExpressionBuilder(_, _, Some(FixedGenerator(List.empty)), _)))

  private def parse(input: String): List[ParsedArchiveEntry] =
    parser.parse(input)

  private def beDecl(right: Declaration) =
    new Matcher[Declaration] {
      def apply(left: Declaration): MatchResult =
        MatchResult(
          //compare without locations
          left.decls.map(v => v._1 -> v._2.copy(loc = UnknownLocation)) == right.decls.map(v => v._1 -> v._2.copy(loc = UnknownLocation)),
          left + " was not " + right,
          left + " was " + right
        )
    }

  "Archive parser" should "parse a model only entry" in {
    val input =
      """ArchiveEntry "Entry 1"
        | ProgramVariables Real x; Real y; End.
        | Problem x>y -> x>=y End.
        |End.""".stripMargin
    val entry = parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "theorem"
    entry.problemContent shouldBe input
    entry.defs should beDecl(
      Declaration(Map(
        Name("x", None) -> Signature(None, Real, None, None, UnknownLocation),
        Name("y", None) -> Signature(None, Real, None, None, UnknownLocation)
      )))
    entry.model shouldBe "x>y -> x>=y".asFormula
    entry.tactics shouldBe empty
    entry.info shouldBe empty
    entry.fileContent shouldBe input
  }

  it should "parse a model with entry ID" in {
    val input =
      """ArchiveEntry b01_8entry1_and_more_underscores : "Entry 1"
        | ProgramVariables Real x; Real y; End.
        | Problem x>y -> x>=y End.
        |End.""".stripMargin
    val entry = parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "theorem"
    entry.defs should beDecl(
      Declaration(Map(
        Name("x", None) -> Signature(None, Real, None, None, UnknownLocation),
        Name("y", None) -> Signature(None, Real, None, None, UnknownLocation)
      )))
    entry.model shouldBe "x>y -> x>=y".asFormula
    entry.tactics shouldBe empty
    entry.info shouldBe Map("id" -> "b01_8entry1_and_more_underscores")
    entry.fileContent shouldBe input
  }

  it should "parse a model with entry ID repeated at end" in {
    val input =
      """ArchiveEntry b01_entry1 : "Entry 1"
        | ProgramVariables Real x; Real y; End.
        | Problem x>y -> x>=y End.
        |End b01_entry1.""".stripMargin
    val entry = parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "theorem"
    entry.defs should beDecl(
      Declaration(Map(
        Name("x", None) -> Signature(None, Real, None, None, UnknownLocation),
        Name("y", None) -> Signature(None, Real, None, None, UnknownLocation)
      )))
    entry.model shouldBe "x>y -> x>=y".asFormula
    entry.tactics shouldBe empty
    entry.info shouldBe Map("id" -> "b01_entry1")
    entry.fileContent shouldBe input
  }

  it should "parse simple function declaration" in {
    val input =
      """
        |ArchiveEntry "Entry 1"
        | Definitions Real f(); End.
        | ProgramVariables Real x; End.
        | Problem x>=0 -> f()>0 End.
        |End.
      """.stripMargin
    val entry = parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "theorem"
    entry.defs should beDecl(
      Declaration(Map(
        Name("f", None) -> Signature(Some(Unit), Real, Some(Nil), None, UnknownLocation),
        Name("x", None) -> Signature(None, Real, None, None, UnknownLocation),
      )))
    entry.model shouldBe "x>=0 -> f()>0".asFormula
    entry.expandedModel shouldBe "x>=0 -> f()>0".asFormula
    entry.tactics shouldBe empty
    entry.info shouldBe empty
    entry.fileContent shouldBe input.trim()
  }

  it should "parse simple function definition" in {
    val input =
      """
        |ArchiveEntry "Entry 1"
        | Definitions Real f() = (1); End.
        | ProgramVariables Real x; End.
        | Problem x>=0 -> f()>0 End.
        |End.
      """.stripMargin
    val entry = parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "theorem"
    entry.defs should beDecl(
      Declaration(Map(
        Name("f", None) -> Signature(Some(Unit), Real, Some(Nil), Some("1".asTerm), UnknownLocation),
        Name("x", None) -> Signature(None, Real, None, None, UnknownLocation),
      )))
    entry.model shouldBe "x>=0 -> f()>0".asFormula
    entry.expandedModel shouldBe "x>=0 -> 1>0".asFormula
    entry.tactics shouldBe empty
    entry.info shouldBe empty
    entry.fileContent shouldBe input.trim()
  }

  it should "FEATURE_REQUEST: parse simple predicate declaration" taggedAs TodoTest in {
    val input =
      """
        |ArchiveEntry "Entry 1"
        | Definitions Bool p(Real x); End.
        | ProgramVariables Real x; End.
        | Problem p(x) & x>0 -> [x:=x+1;]p(x) End.
        |End.
      """.stripMargin
    val entry = parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "theorem"
    entry.defs should beDecl(
      Declaration(Map(
        Name("p", None) -> Signature(Some(Real), Bool, Some((Name("x", None), Real) :: Nil), None, UnknownLocation),
        Name("x", None) -> Signature(None, Real, None, None, UnknownLocation)
      )))
    entry.model shouldBe "p(x) & x>0 -> [x:=x+1;]p(x)".asFormula
    entry.expandedModel shouldBe "p(x) & x>0 -> [x:=x+1;]p(x)".asFormula
    entry.tactics shouldBe empty
    entry.info shouldBe empty
    entry.fileContent shouldBe input.trim()
  }

  it should "parse simple nullary predicate definition" in {
    val input =
      """
        |ArchiveEntry "Entry 1"
        | Definitions Bool p() <-> (2>1); End.
        | ProgramVariables Real x; End.
        | Problem p() & x>0 -> [x:=x+1;]p() End.
        |End.
      """.stripMargin
    val entry = parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "theorem"
    entry.defs should beDecl(
      Declaration(Map(
        Name("p", None) -> Signature(Some(Unit), Bool, Some(Nil), Some("2>1".asFormula), UnknownLocation),
        Name("x", None) -> Signature(None, Real, None, None, UnknownLocation)
      )))
    entry.model shouldBe "p() & x>0 -> [x:=x+1;]p()".asFormula
    entry.expandedModel shouldBe "2>1 & x>0 -> [x:=x+1;]2>1".asFormula
    entry.tactics shouldBe empty
    entry.info shouldBe empty
    entry.fileContent shouldBe input.trim()
  }

  it should "parse simple nullary predicate definition with multiple variables" in {
    val input =
      """
        |ArchiveEntry "Entry 1"
        | Definitions Bool p() <-> (2>1); End.
        | ProgramVariables Real x; Real y; End.
        | Problem p() & x>0 -> [x:=x+y;]p() End.
        |End.
      """.stripMargin
    val entry = parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "theorem"
    entry.defs should beDecl(
      Declaration(Map(
        Name("p", None) -> Signature(Some(Unit), Bool, Some(Nil), Some("2>1".asFormula), UnknownLocation),
        Name("x", None) -> Signature(None, Real, None, None, UnknownLocation),
        Name("y", None) -> Signature(None, Real, None, None, UnknownLocation)
      )))
    entry.model shouldBe "p() & x>0 -> [x:=x+y;]p()".asFormula
    entry.expandedModel shouldBe "2>1 & x>0 -> [x:=x+y;]2>1".asFormula
    entry.tactics shouldBe empty
    entry.info shouldBe empty
    entry.fileContent shouldBe input.trim()
  }

  it should "FEATURE_REQUEST: parse simple unary predicate definition" taggedAs TodoTest in {
    val input =
      """
        |ArchiveEntry "Entry 1"
        | Definitions Bool p(Real x) <-> (x>1); End.
        | ProgramVariables Real x; End.
        | Problem p(x) & x>0 -> [x:=x+1;]p(x) End.
        |End.
      """.stripMargin
    val entry = parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "theorem"
    entry.defs should beDecl(
      Declaration(Map(
        Name("p", None) -> Signature(Some(Real), Bool, Some((Name("x", None), Real) :: Nil), Some(".>1".asFormula), UnknownLocation),
        Name("x", None) -> Signature(None, Real, None, None, UnknownLocation)
      )))
    entry.model shouldBe "p(x) & x>0 -> [x:=x+1;]p(x)".asFormula
    entry.expandedModel shouldBe "x>1 & x>0 -> [x:=x+1;]x>1".asFormula
    entry.tactics shouldBe empty
    entry.info shouldBe empty
    entry.fileContent shouldBe input.trim()
  }

  it should "FEATURE_REQUEST: parse simple program declaration before variables" taggedAs TodoTest in {
    val input =
      """
        |ArchiveEntry "Entry 1"
        | Definitions HP a; End.
        | ProgramVariables Real x; End.
        | Problem x!=0 -> [a;]x>1 End.
        |End.
      """.stripMargin
    val entry = parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "theorem"
    entry.defs should beDecl(
      Declaration(Map(
        Name("a", None) -> Signature(Some(Unit), Trafo, None, None, UnknownLocation),
        Name("x", None) -> Signature(None, Real, None, None, UnknownLocation)
      )))
    entry.model shouldBe "x!=0 -> [a;]x>1".asFormula
    entry.expandedModel shouldBe "x!=0 -> [a;]x>1".asFormula
    entry.tactics shouldBe empty
    entry.info shouldBe empty
    entry.fileContent shouldBe input.trim()
  }

  it should "parse an isolated simple definition assignment" in {
    DLParser.programParser("x:=x+1;") shouldBe Assign(Variable("x"),Plus(Variable("x"),Number(BigDecimal(1))))
    DLParser.programParser("{ x:=x+1; }") shouldBe DLParser.programParser("x:=x+1;")
    val archiveParser = new DLArchiveParser(new DLBelleParser(BellePrettyPrinter, ReflectiveExpressionBuilder(_, _, Some(FixedGenerator(List.empty)), _)))
    DLParser.parseValue( "HP a ::= { x:=x+1; };", archiveParser.progDef(_)) shouldBe (Name("a", None), Signature(Some(Unit), Trafo, None, Some("x:=x+1;".asProgram), UnknownLocation))
    DLParser.parseValue( "Definitions HP a ::= { x:=x+1; }; End.", archiveParser.definitions(_)) shouldBe Declaration(Map(Name("a", None) -> Signature(Some(Unit), Trafo, None, Some("x:=x+1;".asProgram), UnknownLocation)))
    val input =
      """
        |ArchiveEntry "Entry 1"
        | Definitions HP a ::= { x:=x+1; }; End.
        | ProgramVariables Real x; End.
        | Problem x!=0 -> [a;]x>1 End.
        |End.
      """.stripMargin
    val entry = parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "theorem"
    entry.defs should beDecl(
      Declaration(Map(
        Name("a", None) -> Signature(Some(Unit), Trafo, None, Some("x:=x+1;".asProgram), UnknownLocation),
        Name("x", None) -> Signature(None, Real, None, None, UnknownLocation)
      )))
    entry.model shouldBe "x!=0 -> [a{|^@|};]x>1".asFormula
    entry.expandedModel shouldBe "x!=0 -> [x:=x+1;]x>1".asFormula
    entry.tactics shouldBe empty
    entry.info shouldBe empty
    entry.fileContent shouldBe input.trim()
  }

  it should "parse simple program definition assignment before variables" in {
    val input =
      """
        |ArchiveEntry "Entry 1"
        | Definitions HP a ::= { x:=x+1; }; End.
        | ProgramVariables Real x; End.
        | Problem x!=0 -> [a;]x>1 End.
        |End.
      """.stripMargin
    val entry = parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "theorem"
    entry.defs should beDecl(
      Declaration(Map(
        Name("a", None) -> Signature(Some(Unit), Trafo, None, Some("x:=x+1;".asProgram), UnknownLocation),
        Name("x", None) -> Signature(None, Real, None, None, UnknownLocation)
      )))
    entry.model shouldBe "x!=0 -> [a{|^@|};]x>1".asFormula
    entry.expandedModel shouldBe "x!=0 -> [x:=x+1;]x>1".asFormula
    entry.tactics shouldBe empty
    entry.info shouldBe empty
    entry.fileContent shouldBe input.trim()
  }

  it should "parse simple program definition test before variables" in {
    val input =
      """
        |ArchiveEntry "Entry 1"
        | Definitions HP a ::= { ?x>1; }; End.
        | ProgramVariables Real x; End.
        | Problem x!=0 -> [a;]x>1 End.
        |End.
      """.stripMargin
    val entry = parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "theorem"
    entry.defs should beDecl(
      Declaration(Map(
        Name("a", None) -> Signature(Some(Unit), Trafo, None, Some("?x>1;".asProgram), UnknownLocation),
        Name("x", None) -> Signature(None, Real, None, None, UnknownLocation)
      )))
    entry.model shouldBe "x!=0 -> [a{|^@|};]x>1".asFormula
    entry.expandedModel shouldBe "x!=0 -> [?x>1;]x>1".asFormula
    entry.tactics shouldBe empty
    entry.info shouldBe empty
    entry.fileContent shouldBe input.trim()
  }

  it should "parse simple program definition ODE before variables" in {
    val input =
      """
        |ArchiveEntry "Entry 1"
        | Definitions HP a ::= { {x'=5} }; End.
        | ProgramVariables Real x; End.
        | Problem x!=0 -> [a;]x>1 End.
        |End.
      """.stripMargin
    val entry = parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "theorem"
    entry.defs should beDecl(
      Declaration(Map(
        Name("a", None) -> Signature(Some(Unit), Trafo, None, Some("{x'=5}".asProgram), UnknownLocation),
        Name("x", None) -> Signature(None, Real, None, None, UnknownLocation)
      )))
    entry.model shouldBe "x!=0 -> [a{|^@|};]x>1".asFormula
    entry.expandedModel shouldBe "x!=0 -> [{x'=5}]x>1".asFormula
    entry.tactics shouldBe empty
    entry.info shouldBe empty
    entry.fileContent shouldBe input.trim()
  }

  it should "parse simple program definition compose assign before variables" in {
    val input =
      """
        |ArchiveEntry "Entry 1"
        | Definitions HP a ::= { x:=x+1;?x>1; }; End.
        | ProgramVariables Real x; End.
        | Problem x!=0 -> [a;]x>1 End.
        |End.
      """.stripMargin
    val entry = parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "theorem"
    entry.defs should beDecl(
      Declaration(Map(
        Name("a", None) -> Signature(Some(Unit), Trafo, None, Some("x:=x+1;?x>1;".asProgram), UnknownLocation),
        Name("x", None) -> Signature(None, Real, None, None, UnknownLocation)
      )))
    entry.model shouldBe "x!=0 -> [a{|^@|};]x>1".asFormula
    entry.expandedModel shouldBe "x!=0 -> [x:=x+1;?x>1;]x>1".asFormula
    entry.tactics shouldBe empty
    entry.info shouldBe empty
    entry.fileContent shouldBe input.trim()
  }

  it should "parse simple program definition compose before variables" in {
    val input =
      """
        |ArchiveEntry "Entry 1"
        | Definitions HP a ::= { ?x>1;x:=x+1; }; End.
        | ProgramVariables Real x; End.
        | Problem x!=0 -> [a;]x>1 End.
        |End.
      """.stripMargin
    val entry = parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "theorem"
    entry.defs should beDecl(
      Declaration(Map(
        Name("a", None) -> Signature(Some(Unit), Trafo, None, Some("?x>1;x:=x+1;".asProgram), UnknownLocation),
        Name("x", None) -> Signature(None, Real, None, None, UnknownLocation)
      )))
    entry.model shouldBe "x!=0 -> [a{|^@|};]x>1".asFormula
    entry.expandedModel shouldBe "x!=0 -> [?x>1;x:=x+1;]x>1".asFormula
    entry.tactics shouldBe empty
    entry.info shouldBe empty
    entry.fileContent shouldBe input.trim()
  }

  it should "FEATURE_REQUEST: parse lots of definitions before variables" taggedAs TodoTest in {
    val input =
      """
        |ArchiveEntry "Entry 1"
        | Definitions Real f() = (1); Bool p(Real x) <-> (x>1); Bool q(Real x, Real y, Real z) <-> (x+y>z); HP a ::= { ?p(x); }; End.
        | ProgramVariables Real x; Real y; End.
        | Problem p(x) & y>=0 -> q(x,y,f()) & [a;]p(x) End.
        |End.
      """.stripMargin
    val entry = parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "theorem"
    entry.defs should beDecl(
      Declaration(Map(
        Name("f", None) -> Signature(Some(Unit), Real, Some(Nil), Some("1".asTerm), UnknownLocation),
        Name("p", None) -> Signature(Some(Real), Bool, Some((Name("x", None), Real) :: Nil), Some(".>1".asFormula), UnknownLocation),
        Name("q", None) -> Signature(Some(Tuple(Real, Tuple(Real, Real))), Bool, Some((Name("x", None), Real) :: (Name("y", None), Real) :: (Name("z", None), Real) :: Nil), Some("._0+._1>._2".asFormula), UnknownLocation),
        Name("a", None) -> Signature(Some(Unit), Trafo, None, Some("?p(x);".asProgram), UnknownLocation),
        Name("x", None) -> Signature(None, Real, None, None, UnknownLocation),
        Name("y", None) -> Signature(None, Real, None, None, UnknownLocation)
      )))
    entry.model shouldBe "p(x) & y>=0 -> q(x,y,f()) & [a{|^@|};]p(x)".asFormula
    entry.expandedModel shouldBe "x>1 & y>=0 -> x+y>1 & [?x>1;]x>1".asFormula
    entry.tactics shouldBe empty
    entry.info shouldBe empty
    entry.fileContent shouldBe input.trim()
  }

  it should "complain when variable and function have same name" in {
    val input =
      """ArchiveEntry "Entry 1"
        | Definitions Real x() = 2; End.
        | ProgramVariables Real x; End.
        | Problem x=1 -> x<=x() End.
        |End.""".stripMargin
    the [ParseException] thrownBy parse(input) should have message
      """<somewhere> Semantic analysis error
        |semantics: Expect unique names_index that identify a unique type.
        |ambiguous: x:Unit->Real and x:Real
        |symbols:   x, x
        |Found:    <unknown> at <somewhere>
        |Expected: <unknown>""".stripMargin
  }

  it should "parse simple definitions after variables" in {
    val input =
      """
        |ArchiveEntry "Entry 1"
        | ProgramVariables Real x; End.
        | Definitions Real f() = (1); End.
        | Problem f()>0 & x>=0 -> [x:=x+1;]f()>0 End.
        |End.
      """.stripMargin
    val entry = parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "theorem"
    entry.defs should beDecl(
      Declaration(Map(
        Name("f", None) -> Signature(Some(Unit), Real, Some(Nil), Some("1".asTerm), UnknownLocation),
        Name("x", None) -> Signature(None, Real, None, None, UnknownLocation),
      )))
    entry.model shouldBe "f()>0 & x>=0 -> [x:=x+1;]f()>0".asFormula
    entry.expandedModel shouldBe "1>0 & x>=0 -> [x:=x+1;]1>0".asFormula
    entry.tactics shouldBe empty
    entry.info shouldBe empty
    entry.fileContent shouldBe input.trim()
  }

  it should "FEATURE_REQUEST: parse lots of definitions after variables" taggedAs TodoTest in {
    val input =
      """
        |ArchiveEntry "Entry 1"
        | ProgramVariables Real x; Real y; End.
        | Definitions Real f() = (1); Bool p(Real x) <-> (x>1); Bool q(Real x, Real y, Real z) <-> (x+y>z); HP a ::= { ?p(x); }; End.
        | Problem p(x) & y>=0 -> q(x,y,f()) & [a;]p(x) End.
        |End.
      """.stripMargin
    val entry = parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "theorem"
    entry.defs should beDecl(
      Declaration(Map(
        Name("f", None) -> Signature(Some(Unit), Real, Some(Nil), Some("1".asTerm), UnknownLocation),
        Name("p", None) -> Signature(Some(Real), Bool, Some((Name("x", None), Real) :: Nil), Some(".>1".asFormula), UnknownLocation),
        Name("q", None) -> Signature(Some(Tuple(Real, Tuple(Real, Real))), Bool, Some((Name("x", None), Real) :: (Name("y", None), Real) :: (Name("z", None), Real) :: Nil), Some("._0+._1>._2".asFormula), UnknownLocation),
        Name("a", None) -> Signature(Some(Unit), Trafo, None, Some("?p(x);".asProgram), UnknownLocation),
        Name("x", None) -> Signature(None, Real, None, None, UnknownLocation),
        Name("y", None) -> Signature(None, Real, None, None, UnknownLocation)
      )))
    entry.model shouldBe "p(x) & y>=0 -> q(x,y,f()) & [a{|^@|};]p(x)".asFormula
    entry.expandedModel shouldBe "x>1 & y>=0 -> x+y>1 & [?x>1;]x>1".asFormula
    entry.tactics shouldBe empty
    entry.info shouldBe empty
    entry.fileContent shouldBe input.trim()
  }

  it should "accept ODEs without extra braces" in {
    val input =
      """
        |ArchiveEntry "Entry 1"
        | ProgramVariables Real x; Real t; End.
        | Definitions HP a ::= { x'=x, t'=1 & x<=2 }; End.
        | Problem [a;]x<=2 End.
        |End.
      """.stripMargin
    val entry = parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "theorem"
    entry.defs should beDecl(
      Declaration(Map(
        Name("a", None) -> Signature(Some(Unit), Trafo, None, Some("{ x'=x, t'=1 & x<=2 }".asProgram), UnknownLocation),
        Name("t", None) -> Signature(None, Real, None, None, UnknownLocation),
        Name("x", None) -> Signature(None, Real, None, None, UnknownLocation)
      )))
    entry.model shouldBe "[a{|^@|};]x<=2".asFormula
    entry.expandedModel shouldBe "[{x'=x, t'=1 & x<=2}]x<=2".asFormula
    entry.tactics shouldBe empty
    entry.info shouldBe empty
    entry.fileContent shouldBe input.trim()
  }

  it should "FEATURE_REQUEST: parse definitions with dot arguments" taggedAs TodoTest in {
    val input =
      """ArchiveEntry "Entry 1"
        | Definitions Real f(Real); Real g(Real,Real); Real h(Real) = (.+2); End.
        | ProgramVariables Real x; Real y; End.
        | Problem f(x)>g(x,y) & h(x)>5 End.
        |End.""".stripMargin
    val entry = parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "theorem"
    entry.defs should beDecl(
      Declaration(Map(
        Name("f", None) -> Signature(Some(Real), Real, Some((Name("\\cdot", Some(0)), Real) :: Nil), None, UnknownLocation),
        Name("g", None) -> Signature(Some(Tuple(Real, Real)), Real, Some((Name("\\cdot", Some(0)), Real) :: (Name("\\cdot", Some(1)), Real) :: Nil), None, UnknownLocation),
        Name("h", None) -> Signature(Some(Real), Real, Some((Name("\\cdot", Some(0)), Real) :: Nil), Some(".+2".asTerm), UnknownLocation),
        Name("x", None) -> Signature(None, Real, None, None, UnknownLocation),
        Name("y", None) -> Signature(None, Real, None, None, UnknownLocation)
      )))
    entry.model shouldBe "f(x)>g(x,y) & h(x)>5".asFormula
    entry.expandedModel shouldBe "f(x)>g(x,y) & x+2>5".asFormula
    entry.tactics shouldBe empty
    entry.info shouldBe empty
    entry.fileContent shouldBe input.trim()
  }

  it should "FEATURE_REQUEST: parse definitions without parentheses" taggedAs TodoTest in {
    val input = """ArchiveEntry "Entry 1"
                  | Definitions Real f() = 5; Bool p(Real x) <-> x>0; End.
                  | Problem p(f()) End.
                  |End.""".stripMargin
    val entry = parse(input).loneElement

    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "theorem"
    entry.defs should beDecl(
      Declaration(Map(
        Name("f", None) -> Signature(Some(Unit), Real, Some(Nil), Some("5".asTerm), UnknownLocation),
        Name("p", None) -> Signature(Some(Real), Bool, Some((Name("x", None), Real) :: Nil), Some(".>0".asFormula), UnknownLocation)
      )))
    entry.model shouldBe "p(f())".asFormula
    entry.expandedModel shouldBe "5>0".asFormula
    entry.tactics shouldBe empty
    entry.info shouldBe empty
    entry.fileContent shouldBe input.trim()
  }

  it should "parse comma-separated variable declarations" in {
    val input =
      """ArchiveEntry "Entry 1"
        | ProgramVariables Real x, y; End.
        | Problem x>y -> x>=y End.
        |End.""".stripMargin
    val entry = parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "theorem"
    entry.problemContent shouldBe input
    entry.defs should beDecl(
      Declaration(Map(
        Name("x", None) -> Signature(None, Real, None, None, UnknownLocation),
        Name("y", None) -> Signature(None, Real, None, None, UnknownLocation)
      )))
    entry.model shouldBe "x>y -> x>=y".asFormula
    entry.tactics shouldBe empty
    entry.info shouldBe empty
    entry.fileContent shouldBe input.trim()
  }

  it should "accept reserved identifiers" in {
    parse(
      """ArchiveEntry "Entry 1"
        | ProgramVariables Real Real; End.
        | Problem true End.
        |End.""".stripMargin
    ).loneElement.defs should beDecl(
      Declaration(Map(
        Name("Real", None) -> Signature(None, Real, None, None, UnknownLocation)
      ))
    )

    parse(
      """ArchiveEntry "Entry 1"
        | ProgramVariables Real R; End.
        | Problem true End.
        |End.""".stripMargin
    ).loneElement.defs  should beDecl(
      Declaration(Map(
        Name("R", None) -> Signature(None, Real, None, None, UnknownLocation)
      ))
    )

    parse(
      """ArchiveEntry "Entry 1"
        | ProgramVariables Real Bool; End.
        | Problem true End.
        |End.""".stripMargin
    ).loneElement.defs  should beDecl(
      Declaration(Map(
        Name("Bool", None) -> Signature(None, Real, None, None, UnknownLocation)
      ))
    )

    parse(
      """ArchiveEntry "Entry 1"
        | ProgramVariables Real HP; End.
        | Problem true End.
        |End.""".stripMargin
    ).loneElement.defs  should beDecl(
      Declaration(Map(
        Name("HP", None) -> Signature(None, Real, None, None, UnknownLocation)
      ))
    )
  }

  it should "parse a problem without variables" in {
    val input =
      """ArchiveEntry "Entry 1"
        | Definitions Real f(); End.
        | Problem f()>0 End.
        |End.""".stripMargin
    val entry = parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "theorem"
    entry.defs should beDecl(
      Declaration(Map(
        Name("f", None) -> Signature(Some(Unit), Real, Some(Nil), None, UnknownLocation)
      )))
    entry.model shouldBe "f()>0".asFormula
    entry.tactics shouldBe empty
    entry.info shouldBe empty
    entry.fileContent shouldBe input.trim()
  }

  it should "FEATURE_REQUEST: allow comma-separated simple function definitions" taggedAs TodoTest in {
    val input =
      """ArchiveEntry "Entry 1"
        | Definitions Real f(), g; End.
        | Problem f()>g() End.
        |End.""".stripMargin
    val entry = parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "theorem"
    entry.defs should beDecl(
      Declaration(Map(
        Name("f", None) -> Signature(Some(Unit), Real, Some(Nil), None, UnknownLocation),
        Name("g", None) -> Signature(Some(Unit), Real, Some(Nil), None, UnknownLocation)
      )))
    entry.model shouldBe "f()>g()".asFormula
    entry.tactics shouldBe empty
    entry.info shouldBe empty
    entry.fileContent shouldBe input.trim()
  }

  it should "allow comma-separated simple predicate definitions" in {
    val input =
      """ArchiveEntry "Entry 1"
        | Definitions Bool p(), q(); End.
        | Problem p() & q() End.
        |End.""".stripMargin
    val entry = parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "theorem"
    entry.defs should beDecl(
      Declaration(Map(
        Name("p", None) -> Signature(Some(Unit), Bool, Some(Nil), None, UnknownLocation),
        Name("q", None) -> Signature(Some(Unit), Bool, Some(Nil), None, UnknownLocation)
      )))
    entry.model shouldBe "p() & q()".asFormula
    entry.tactics shouldBe empty
    entry.info shouldBe empty
    entry.fileContent shouldBe input.trim()
  }

  it should "FEATURE_REQUEST: parse a problem that uses the allowed interpreted functions" taggedAs TodoTest in {
    val input =
      """ArchiveEntry "Entry 1"
        | Problem abs(-5)>0 End.
        |End.""".stripMargin
    val entry = parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "theorem"
    entry.defs.decls shouldBe Map(Name("abs", None) -> (Some(Real), Real, None, None, UnknownLocation))
    entry.model shouldBe "abs(-5)>0".asFormula
    entry.tactics shouldBe empty
    entry.info shouldBe empty
    entry.fileContent shouldBe input.trim()
  }

  it should "parse an annotation that uses the reserved function symbol old" in {
    val input =
      """ArchiveEntry "Entry 1"
        | ProgramVariables Real x; End.
        | Problem [{x:=x;}*@invariant(old(x)=x)]x=x End.
        |End.""".stripMargin
    val entry = parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "theorem"
    entry.defs should beDecl(
      Declaration(Map(
        Name("x", None) -> Signature(None, Real, None, None, UnknownLocation)
      )))
    entry.model shouldBe "[{x:=x;}*]x=x".asFormula
    entry.tactics shouldBe empty
    entry.info shouldBe empty
    entry.fileContent shouldBe input.trim()
  }

  it should "parse a problem with neither definitions nor variables" in {
    val input =
      """ArchiveEntry "Entry 1"
        | Problem false -> true End.
        |End.""".stripMargin
    val entry = parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "theorem"
    entry.defs.decls shouldBe empty
    entry.model shouldBe "false -> true".asFormula
    entry.tactics shouldBe empty
    entry.info shouldBe empty
    entry.fileContent shouldBe input.trim()
  }

  it should "FEATURE_REQUEST: parse a plain problem format" taggedAs TodoTest in {
    val input =
      """ProgramVariables Real x; Real y; End.
        |Problem x>y -> x>=y End.
      """.stripMargin
    val entry = parse(input).loneElement
    entry.name shouldBe "<undefined>"
    entry.kind shouldBe "theorem"
    entry.problemContent shouldBe input.trim()
    entry.defs should beDecl(
      Declaration(Map(
        Name("x", None) -> Signature(None, Real, None, None, UnknownLocation),
        Name("y", None) -> Signature(None, Real, None, None, UnknownLocation)
      )))
    entry.model shouldBe "x>y -> x>=y".asFormula
    entry.tactics shouldBe empty
    entry.info shouldBe empty
    entry.fileContent shouldBe input.trim()
  }

  it should "FEATURE_REQUEST: parse a problem without declarations" taggedAs TodoTest in {
    val input = "ArchiveEntry \"Test\" Problem x>y -> x>=y End. End."
    val entry = parse(input).loneElement
    entry.name shouldBe "Test"
    entry.kind shouldBe "theorem"
    entry.defs should beDecl(
      Declaration(Map(
        Name("x", None) -> Signature(None, Real, None, None, UnknownLocation),
        Name("y", None) -> Signature(None, Real, None, None, UnknownLocation)
      )))
    entry.model shouldBe "x>y -> x>=y".asFormula
    entry.tactics shouldBe empty
    entry.info shouldBe empty
    entry.fileContent shouldBe input.trim()
  }


  it should "FEATURE_REQUEST: refuse mixed plain and named entries" taggedAs TodoTest in {
    val input =
      """ProgramVariables Real x; Real y; End.
        |Problem x>y -> x>=y End.
        |
        |ArchiveEntry "Entry 2"
        |  ProgramVariables Real x; End.
        |  Problem x>0 End.
        |End.
      """.stripMargin
    val ex = the [ParseException] thrownBy parse(input)
    ex.msg should include ("Archives that start with an anonymous entry may not contain any other entries, but found ArchiveEntry")
  }

  it should "FEATURE_REQUEST: detect duplicate variable definitions" taggedAs TodoTest in {
    val input =
      """
        |ArchiveEntry "Entry 1"
        | ProgramVariables Real x; Real x; Real y; End.
        | Problem x>y -> x>=y End.
        |End.
      """.stripMargin
    val ex = the [ParseException] thrownBy parse(input)
    ex.msg should include ("Duplicate variable 'x'")
  }

  it should "FEATURE_REQUEST: detect duplicate function names" taggedAs TodoTest in {
    val input =
      """
        |ArchiveEntry "Entry 1"
        | Definitions Real f() = (1); Real f() = (2); End.
        | ProgramVariables Real x; Real y; End.
        | Problem x>y -> x>=y End.
        |End.
      """.stripMargin
    val ex = the [ParseException] thrownBy parse(input)
    ex.msg should include ("Duplicate symbol 'f'")
  }

  it should "FEATURE_REQUEST: detect duplicate predicate names" taggedAs TodoTest in {
    val input =
      """
        |ArchiveEntry "Entry 1"
        | Definitions Bool p() <-> (1>0). Bool p() <-> (2>1); End.
        | ProgramVariables Real x; Real y; End.
        | Problem p() -> x>=y End.
        |End.
      """.stripMargin
    val ex = the [ParseException] thrownBy parse(input)
    ex.msg should include ("Duplicate symbol 'p'")
  }

  it should "FEATURE_REQUEST: detect duplicate program names" taggedAs TodoTest in {
    val input =
      """
        |ArchiveEntry "Entry 1"
        | Definitions HP a ::= { ?true; }. HP a ::= { ?false; }; End.
        | ProgramVariables Real x; Real y; End.
        | Problem [a;]true End.
        |End.
      """.stripMargin
    val ex = the [ParseException] thrownBy parse(input)
    ex.msg should include ("Duplicate symbol 'a'")
  }

  it should "FEATURE_REQUEST: parse a model and tactic entry" taggedAs TodoTest in withTactics {
    val input =
      """
        |ArchiveEntry "Entry 1"
        | ProgramVariables Real x; Real y; End.
        | Problem x>y -> x>=y End.
        | Tactic "Proof 1" implyR(1) ; QE End.
        |End.
      """.stripMargin
    val entry = parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "theorem"
    entry.defs should beDecl(
      Declaration(Map(
        Name("x", None) -> Signature(None, Real, None, None, UnknownLocation),
        Name("y", None) -> Signature(None, Real, None, None, UnknownLocation)
      )))
    entry.model shouldBe "x>y -> x>=y".asFormula
    entry.tactics shouldBe ("Proof 1", "implyR(1) ; QE", implyR(1) & QE) :: Nil
    entry.info shouldBe empty
    entry.fileContent shouldBe input.trim()
    entry.problemContent shouldBe """ArchiveEntry "Entry 1"
                                    | ProgramVariables Real x; Real y; End.
                                    | Problem x>y -> x>=y End.
                                    |End.""".stripMargin.trim()
  }

  it should "FEATURE_REQUEST: parse a tactic without name" taggedAs TodoTest in withTactics {
    val input =
      """
        |ArchiveEntry "Entry 1"
        | ProgramVariables Real x; Real y; End.
        | Problem x>y -> x>=y End.
        | Tactic implyR(1) ; QE End.
        |End.
      """.stripMargin
    val entry = parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "theorem"
    entry.defs should beDecl(
      Declaration(Map(
        Name("x", None) -> Signature(None, Real, None, None, UnknownLocation),
        Name("y", None) -> Signature(None, Real, None, None, UnknownLocation)
      )))
    entry.model shouldBe "x>y -> x>=y".asFormula
    entry.tactics shouldBe ("<undefined>", "implyR(1) & QE", implyR(1) & QE) :: Nil
    entry.info shouldBe empty
    entry.fileContent shouldBe input.trim()
    entry.problemContent shouldBe
      """ArchiveEntry "Entry 1"
        | ProgramVariables Real x; Real y; End.
        | Problem x>y -> x>=y End.
        |End.""".stripMargin
  }

  it should "FEATURE_REQUEST: parse a tactic with a comment in the beginning" taggedAs TodoTest in withTactics {
    val input =
      """
        |ArchiveEntry "Entry 1"
        | ProgramVariables Real x; Real y; End.
        | Problem x>y -> x>=y End.
        | Tactic "Empty" /* a comment */ nil End.
        |End.
      """.stripMargin
    val entry = parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "theorem"
    entry.defs should beDecl(
      Declaration(Map(
        Name("x", None) -> Signature(None, Real, None, None, UnknownLocation),
        Name("y", None) -> Signature(None, Real, None, None, UnknownLocation)
      )))
    entry.model shouldBe "x>y -> x>=y".asFormula
    entry.tactics shouldBe ("Empty", "/* a comment */ nil", nil) :: Nil
    entry.info shouldBe empty
    entry.fileContent shouldBe input.trim()
  }

  it should "FEATURE_REQUEST: parse a pending tactic" taggedAs TodoTest in withTactics {
    val input =
      """
        |ArchiveEntry "Entry 1"
        | ProgramVariables Real x; Real y; End.
        | Problem x>y -> x>=y End.
        | Tactic "Pending" implyR(1) ; pending({`QE`}) End.
        |End.
      """.stripMargin
    val entry = parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "theorem"
    entry.defs should beDecl(
      Declaration(Map(
        Name("x", None) -> Signature(None, Real, None, None, UnknownLocation),
        Name("y", None) -> Signature(None, Real, None, None, UnknownLocation)
      )))
    entry.model shouldBe "x>y -> x>=y".asFormula
    entry.tactics shouldBe ("Pending", "implyR(1) ; pending({`QE`})", implyR(1) & DebuggingTactics.pending("QE")) :: Nil
    entry.info shouldBe empty
    entry.fileContent shouldBe input.trim()
  }

  it should "FEATURE_REQUEST: parse a pending tactic with arguments" taggedAs TodoTest in withTactics {
    val input =
      """
        |ArchiveEntry "Entry 1"
        | ProgramVariables Real x; Real y; End.
        | Problem x>y -> x>=y End.
        | Tactic "Pending" implyR(1) ; pending({`QE({`Mathematica`}) | QE({`Z3`})`}) End.
        |End.
      """.stripMargin
    val entry = parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "theorem"
    entry.defs should beDecl(
      Declaration(Map(
        Name("x", None) -> Signature(None, Real, None, None, UnknownLocation),
        Name("y", None) -> Signature(None, Real, None, None, UnknownLocation)
      )))
    entry.model shouldBe "x>y -> x>=y".asFormula
    entry.tactics shouldBe ("Pending", "implyR(1) ; pending({`QE({`Mathematica`}) | QE({`Z3`})`})", implyR(1) & DebuggingTactics.pending("QE({`Mathematica`}) | QE({`Z3`})")) :: Nil
    entry.info shouldBe empty
    entry.fileContent shouldBe input.trim()
  }

  it should "FEATURE_REQUEST: parse a tactic with arguments in new syntax" taggedAs TodoTest in withTactics {
    val input =
      """
        |ArchiveEntry "Entry 1"
        | ProgramVariables Real x; Real y; End.
        | Problem x>y -> [{x'=1}]x>=y End.
        | Tactic "Simple" implyR(1) ; dC("x>=old(x)", 1) End.
        |End.
      """.stripMargin
    val entry = parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "theorem"
    entry.defs should beDecl(
      Declaration(Map(
        Name("x", None) -> Signature(None, Real, None, None, UnknownLocation),
        Name("y", None) -> Signature(None, Real, None, None, UnknownLocation)
      )))
    entry.model shouldBe "x>y -> [{x'=1}]x>=y".asFormula
    entry.tactics shouldBe ("Simple", "implyR(1) ; dC(\"x>=old(x)\", 1)", implyR(1) & dC("x>=old(x)".asFormula)(1)) :: Nil
    entry.info shouldBe empty
    entry.fileContent shouldBe input.trim()
  }

  it should "FEATURE_REQUEST: elaborate to functions when parsing a tactic" taggedAs TodoTest in withTactics {
    val input =
      """
        |ArchiveEntry "Entry 1"
        | Definitions Real y; End.
        | ProgramVariables Real x; End.
        | Problem x>y -> [{x'=1}]x>=y End.
        | Tactic "Simple" implyR(1) ; dC("y=old(y)", 1) End.
        |End.
      """.stripMargin
    val entry = parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "theorem"
    entry.defs should beDecl(
      Declaration(Map(
        Name("x", None) -> Signature(None, Real, None, None, UnknownLocation),
        Name("y", None) -> Signature(Some(Unit), Real, Some(Nil), None, UnknownLocation)
      )))
    entry.model shouldBe "x>y() -> [{x'=1}]x>=y()".asFormula
    entry.tactics shouldBe ("Simple", "implyR(1) ; dC(\"y=old(y)\", 1)", implyR(1) & dC("y()=old(y())".asFormula)(1)) :: Nil
    entry.info shouldBe empty
    entry.fileContent shouldBe input.trim()
  }

  it should "FEATURE_REQUEST: elaborate to functions in the presence of program constants" taggedAs TodoTest in withTactics {
    val input =
      """
        |ArchiveEntry "Entry 1"
        | Definitions Real y; End.
        | ProgramVariables Real x; End.
        | Problem x>y -> [ctrl;]x>=y End.
        | Tactic "Simple" implyR(1) ; dC("y=old(y)", 1) End.
        |End.
      """.stripMargin
    val entry = parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "theorem"
    entry.defs should beDecl(
      Declaration(Map(
        Name("x", None) -> Signature(None, Real, None, None, UnknownLocation),
        Name("y", None) -> Signature(Some(Unit), Real, Some(Nil), None, UnknownLocation)
      )))
    entry.model shouldBe "x>y() -> [ctrl;]x>=y()".asFormula
    entry.tactics shouldBe ("Simple", "implyR(1) ; dC(\"y=old(y)\", 1)", implyR(1) & dC("y()=old(y())".asFormula)(1)) :: Nil
    entry.info shouldBe empty
    entry.fileContent shouldBe input.trim()
  }

  it should "FEATURE_REQUEST: sort definitions correctly when parsing expandAllDefs" taggedAs TodoTest in withTactics {
    val input =
      """
        |ArchiveEntry "Entry 1"
        | Definitions Real b = 3*y; Real y = 4; Real z(Real a) = a*b*y; End.
        | ProgramVariables Real x; End.
        | Problem x>y -> [ctrl;]x>=y End.
        | Tactic "Expand" expandAllDefs End.
        |End.
      """.stripMargin
    val entry = parse(input).loneElement
    entry.defs.substs shouldBe List("z(.) ~> .*b()*y()".asSubstitutionPair, "b()~>3*y()".asSubstitutionPair, "y() ~> 4".asSubstitutionPair)
    inside (entry.tactics) {
      case (_, _, ExpandAll(defs)) :: Nil => defs shouldBe entry.defs.substs
    }
  }

  it should "not elaborate to program constants when definitions contain duals" in {
    val input =
      """
        |ArchiveEntry "Entry 1"
        | Definitions Real y(); HP ctrl ::= { x:=x+1;^@ }; End.
        | ProgramVariables Real x; End.
        | Problem x>y -> [ctrl;]x>=y End.
        |End.
      """.stripMargin
    val entry = parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "theorem"
    entry.defs should beDecl(
      Declaration(Map(
        Name("x", None) -> Signature(None, Real, None, None, UnknownLocation),
        Name("y", None) -> Signature(Some(Unit), Real, Some(Nil), None, UnknownLocation),
        Name("ctrl", None) -> Signature(Some(Unit), Trafo, None, Some("x:=x+1;^@".asProgram), UnknownLocation)
      )))
    entry.model shouldBe "x>y() -> [ctrl;]x>=y()".asFormula
    entry.tactics shouldBe empty
    entry.info shouldBe empty
    entry.fileContent shouldBe input.trim()
  }

  it should "FEATURE_REQUEST: parse a pending tactic with arguments in new syntax" taggedAs TodoTest in withTactics {
    val input =
      """
        |ArchiveEntry "Entry 1"
        | ProgramVariables Real x; Real y; End.
        | Problem x>y -> [{x'=1}]x>=y End.
        | Tactic "Simple" implyR(1) ; pending("dC(\"x>=old(x)\", 1)") End.
        |End.
      """.stripMargin
    val entry = parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "theorem"
    entry.defs should beDecl(
      Declaration(Map(
        Name("x", None) -> Signature(None, Real, None, None, UnknownLocation),
        Name("y", None) -> Signature(None, Real, None, None, UnknownLocation)
      )))
    entry.model shouldBe "x>y -> [{x'=1}]x>=y".asFormula
    entry.tactics shouldBe ("Simple", "implyR(1) ; pending(\"dC(\\\"x>=old(x)\\\", 1)\")", implyR(1) & DebuggingTactics.pending("dC(\\\"x>=old(x)\\\", 1)")) :: Nil
    entry.info shouldBe empty
    entry.fileContent shouldBe input.trim()
  }

  it should "FEATURE_REQUEST: parse a model with several tactics" taggedAs TodoTest in withQE { _ =>
    val input =
      """
        |ArchiveEntry "Entry 1"
        | ProgramVariables Real x; Real y; End.
        | Problem x>y -> x>=y End.
        | Tactic "Proof 1" implyR(1) & QE End.
        | Tactic "Proof 2" implyR('R) End.
        |End.
      """.stripMargin
    val entry = parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "theorem"
    entry.defs should beDecl(
      Declaration(Map(
        Name("x", None) -> Signature(None, Real, None, None, UnknownLocation),
        Name("y", None) -> Signature(None, Real, None, None, UnknownLocation)
      )))
    entry.model shouldBe "x>y -> x>=y".asFormula
    entry.tactics shouldBe ("Proof 1", "implyR(1) & QE", implyR(1) & QE) :: ("Proof 2", "implyR('R)", implyR('R)) :: Nil
    entry.info shouldBe empty
    entry.fileContent shouldBe input.trim()
    entry.problemContent shouldBe
      """ArchiveEntry "Entry 1"
        | ProgramVariables Real x; Real y; End.
        | Problem x>y -> x>=y End.
        |End.""".stripMargin
  }

  it should "FEATURE_REQUEST: parse a list of model and tactic entries" taggedAs TodoTest in {
    val input =
      """ArchiveEntry "Entry 1"
        | ProgramVariables Real x; Real y; End.
        | Problem x>y -> x>=y End.
        |End.
        |
        |ArchiveEntry "Entry 2"
        |  Definitions Real x(); End.
        |  ProgramVariables Real y; End.
        |  Problem x()>=y -> x()>=y End.
        |  Tactic "Prop Proof" prop End.
        |End.
      """.stripMargin
    val entries = parse(input)
    entries should have size 2
    val entry1 = entries.head
    entry1.name shouldBe "Entry 1"
    entry1.kind shouldBe "theorem"
    entry1.defs should beDecl(
      Declaration(Map(
        Name("x", None) -> Signature(None, Real, None, None, UnknownLocation),
        Name("y", None) -> Signature(None, Real, None, None, UnknownLocation)
      )))
    entry1.model shouldBe "x>y -> x>=y".asFormula
    entry1.tactics shouldBe empty
    entry1.info shouldBe empty
    entry1.fileContent shouldBe """ArchiveEntry "Entry 1"
                                  | ProgramVariables Real x; Real y; End.
                                  | Problem x>y -> x>=y End.
                                  |End.""".stripMargin

    val entry2 = entries.last
    entry2.name shouldBe "Entry 2"
    entry2.kind shouldBe "theorem"
    entry2.defs should beDecl(
      Declaration(Map(
        Name("x", None) -> Signature(Some(Unit), Real, Some(Nil), None, UnknownLocation),
        Name("y", None) -> Signature(None, Real, None, None, UnknownLocation)
      )))
    entry2.model shouldBe "x()>=y -> x()>=y".asFormula
    entry2.tactics shouldBe ("Prop Proof", "prop", prop) :: Nil
    entry2.info shouldBe empty
    entry2.fileContent shouldBe """ArchiveEntry "Entry 2"
                                  |  Definitions Real x(); End.
                                  |  ProgramVariables Real y; End.
                                  |  Problem x()>=y -> x()>=y End.
                                  |  Tactic "Prop Proof" prop End.
                                  |End.""".stripMargin
  }

  it should "FEATURE_REQUEST: parse a list of mixed entries, lemmas, and theorems" taggedAs TodoTest in {
    val input =
      """ArchiveEntry "Entry 1"
        | ProgramVariables Real x; Real y; End.
        | Problem x>y -> x>=y End.
        |End.
        |
        |Lemma "Entry 2"
        |  Definitions Real x(); End.
        |  ProgramVariables Real y; End.
        |  Problem x()>=y -> x()>=y End.
        |  Tactic "Prop Proof" prop End.
        |End.
        |
        |Theorem "Entry 3"
        |  ProgramVariables Real x; End.
        |  Problem x>3 -> x>=3 End.
        |End.
        |
        |ArchiveEntry "Entry 4"
        |  ProgramVariables Real x; End.
        |  Problem x>4 -> x>=4 End.
        |End.
      """.stripMargin
    val entries = parse(input)
    entries should have size 4

    val entry1 = entries.head
    entry1.name shouldBe "Entry 1"
    entry1.kind shouldBe "theorem"
    entry1.defs should beDecl(
      Declaration(Map(
        Name("x", None) -> Signature(None, Real, None, None, UnknownLocation),
        Name("y", None) -> Signature(None, Real, None, None, UnknownLocation)
      )))
    entry1.model shouldBe "x>y -> x>=y".asFormula
    entry1.tactics shouldBe empty
    entry1.info shouldBe empty
    entry1.fileContent shouldBe """ArchiveEntry "Entry 1"
                                  | ProgramVariables Real x; Real y; End.
                                  | Problem x>y -> x>=y End.
                                  |End.""".stripMargin

    val entry2 = entries(1)
    entry2.name shouldBe "Entry 2"
    entry2.kind shouldBe "lemma"
    entry2.defs should beDecl(
      Declaration(Map(
        Name("x", None) -> Signature(Some(Unit), Real, Some(Nil), None, UnknownLocation),
        Name("y", None) -> Signature(None, Real, None, None, UnknownLocation)
      )))
    entry2.model shouldBe "x()>=y -> x()>=y".asFormula
    entry2.tactics shouldBe ("Prop Proof", "prop", prop) :: Nil
    entry2.info shouldBe empty
    entry2.fileContent shouldBe """Lemma "Entry 2"
                                  |  Definitions Real x(); End.
                                  |  ProgramVariables Real y; End.
                                  |  Problem x()>=y -> x()>=y End.
                                  |  Tactic "Prop Proof" prop End.
                                  |End.""".stripMargin

    val entry3 = entries(2)
    entry3.name shouldBe "Entry 3"
    entry3.kind shouldBe "theorem"
    entry3.defs should beDecl(
      Declaration(Map(
        Name("x", None) -> Signature(None, Real, None, None, UnknownLocation)
      )))
    entry3.model shouldBe "x>3 -> x>=3".asFormula
    entry3.tactics shouldBe empty
    entry3.info shouldBe empty
    entry3.fileContent shouldBe """Theorem "Entry 3"
                                  |  ProgramVariables Real x; End.
                                  |  Problem x>3 -> x>=3 End.
                                  |End.""".stripMargin

    val entry4 = entries(3)
    entry4.name shouldBe "Entry 4"
    entry4.kind shouldBe "theorem"
    entry4.defs should beDecl(
      Declaration(Map(
        Name("x", None) -> Signature(None, Real, None, None, UnknownLocation)
      )))
    entry4.model shouldBe "x>4 -> x>=4".asFormula
    entry4.tactics shouldBe empty
    entry4.info shouldBe empty
    entry4.fileContent shouldBe """ArchiveEntry "Entry 4"
                                  |  ProgramVariables Real x; End.
                                  |  Problem x>4 -> x>=4 End.
                                  |End.""".stripMargin
  }

  it should "FEATURE_REQUEST: parse a list of mixed entries, lemmas, and theorems, whose names are again entry/lemma/theorem" taggedAs TodoTest in {
    val input =
      """ArchiveEntry "Entry 1"
        | ProgramVariables Real x; Real y; End.
        | Problem x>y -> x>=y End.
        |End.
        |
        |Lemma "Lemma 2: Some Entry"
        |  Definitions Real x(); End.
        |  ProgramVariables Real y; End.
        |  Problem x()>=y -> x()>=y End.
        |  Tactic "Prop Proof of Lemma 2" prop End.
        |End.
        |
        |Theorem "Theorem 1: Some Entry"
        |  ProgramVariables Real x; End.
        |  Problem x>3 -> x>=3 End.
        |End.
        |
        |ArchiveEntry "ArchiveEntry 4: Name"
        |  ProgramVariables Real x; End.
        |  Problem x>4 -> x>=4 End.
        |End.
      """.stripMargin
    val entries = parse(input)
    entries should have size 4

    val entry1 = entries.head
    entry1.name shouldBe "Entry 1"
    entry1.kind shouldBe "theorem"
    entry1.defs should beDecl(
      Declaration(Map(
        Name("x", None) -> Signature(None, Real, None, None, UnknownLocation),
        Name("y", None) -> Signature(None, Real, None, None, UnknownLocation)
      )))
    entry1.model shouldBe "x>y -> x>=y".asFormula
    entry1.tactics shouldBe empty
    entry1.info shouldBe empty
    entry1.fileContent shouldBe """ArchiveEntry "Entry 1"
                                  | ProgramVariables Real x; Real y; End.
                                  | Problem x>y -> x>=y End.
                                  |End.""".stripMargin

    val entry2 = entries(1)
    entry2.name shouldBe "Lemma 2: Some Entry"
    entry2.kind shouldBe "lemma"
    entry2.defs should beDecl(
      Declaration(Map(
        Name("x", None) -> Signature(Some(Unit), Real, Some(Nil), None, UnknownLocation),
        Name("y", None) -> Signature(None, Real, None, None, UnknownLocation)
      )))
    entry2.model shouldBe "x()>=y -> x()>=y".asFormula
    entry2.tactics shouldBe ("Prop Proof of Lemma 2", "prop", prop) :: Nil
    entry2.info shouldBe empty
    entry2.fileContent shouldBe """Lemma "Lemma 2: Some Entry"
                                  |  Definitions Real x(); End.
                                  |  ProgramVariables Real y; End.
                                  |  Problem x()>=y -> x()>=y End.
                                  |  Tactic "Prop Proof of Lemma 2" prop End.
                                  |End.""".stripMargin

    val entry3 = entries(2)
    entry3.name shouldBe "Theorem 1: Some Entry"
    entry3.kind shouldBe "theorem"
    entry3.defs should beDecl(
      Declaration(Map(
        Name("x", None) -> Signature(None, Real, None, None, UnknownLocation)
      )))
    entry3.model shouldBe "x>3 -> x>=3".asFormula
    entry3.tactics shouldBe empty
    entry3.info shouldBe empty
    entry3.fileContent shouldBe """Theorem "Theorem 1: Some Entry"
                                  |  ProgramVariables Real x; End.
                                  |  Problem x>3 -> x>=3 End.
                                  |End.""".stripMargin

    val entry4 = entries(3)
    entry4.name shouldBe "ArchiveEntry 4: Name"
    entry4.kind shouldBe "theorem"
    entry4.defs should beDecl(
      Declaration(Map(
        Name("x", None) -> Signature(None, Real, None, None, UnknownLocation)
      )))
    entry4.model shouldBe "x>4 -> x>=4".asFormula
    entry4.tactics shouldBe empty
    entry4.info shouldBe empty
    entry4.fileContent shouldBe """ArchiveEntry "ArchiveEntry 4: Name"
                                  |  ProgramVariables Real x; End.
                                  |  Problem x>4 -> x>=4 End.
                                  |End.""".stripMargin
  }

  it should "parse a lemma entry" in {
    val input =
      """
        |Lemma "Entry 1"
        | ProgramVariables Real x; Real y; End.
        | Problem x>y -> x>=y End.
        |End.
      """.stripMargin
    val entry = parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "lemma"
    entry.defs should beDecl(
      Declaration(Map(
        Name("x", None) -> Signature(None, Real, None, None, UnknownLocation),
        Name("y", None) -> Signature(None, Real, None, None, UnknownLocation)
      )))
    entry.model shouldBe "x>y -> x>=y".asFormula
    entry.tactics shouldBe empty
    entry.info shouldBe empty
    entry.fileContent shouldBe input.trim()
  }

  it should "parse a theorem entry" in {
    val input =
      """
        |Theorem "Entry 1"
        | ProgramVariables Real x; Real y; End.
        | Problem x>y -> x>=y End.
        |End.
      """.stripMargin
    val entry = parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "theorem"
    entry.defs should beDecl(
      Declaration(Map(
        Name("x", None) -> Signature(None, Real, None, None, UnknownLocation),
        Name("y", None) -> Signature(None, Real, None, None, UnknownLocation)
      )))
    entry.model shouldBe "x>y -> x>=y".asFormula
    entry.tactics shouldBe empty
    entry.info shouldBe empty
    entry.fileContent shouldBe input.trim
  }

  it should "FEATURE_REQUEST: split blocks by whole word only (lemma used in tactic)" taggedAs TodoTest in {
    val input =
      """Lemma "Entry 1"
        | ProgramVariables Real x; Real y; End.
        | Problem x>y -> x>=y End.
        |End.
        |
        |Theorem "Entry 2"
        | ProgramVariables Real x; Real y; End.
        | Problem x>y -> x>=y End.
        | Tactic "Proof Entry 2" useLemma({`Entry 1`}) End.
        |End.""".stripMargin
    val entries = parse(input)
    entries should have size 2

    val entry1 = entries.head
    entry1.name shouldBe "Entry 1"
    entry1.kind shouldBe "lemma"
    entry1.defs should beDecl(
      Declaration(Map(
        Name("x", None) -> Signature(None, Real, None, None, UnknownLocation),
        Name("y", None) -> Signature(None, Real, None, None, UnknownLocation)
      )))
    entry1.model shouldBe "x>y -> x>=y".asFormula
    entry1.tactics shouldBe empty
    entry1.info shouldBe empty
    entry1.fileContent shouldBe
      """Lemma "Entry 1"
        | ProgramVariables Real x; Real y; End.
        | Problem x>y -> x>=y End.
        |End.""".stripMargin

    val entry2 = entries(1)
    entry2.name shouldBe "Entry 2"
    entry2.kind shouldBe "theorem"
    entry2.defs should beDecl(
      Declaration(Map(
        Name("x", None) -> Signature(None, Real, None, None, UnknownLocation),
        Name("y", None) -> Signature(None, Real, None, None, UnknownLocation)
      )))
    entry2.model shouldBe "x>y -> x>=y".asFormula
    entry2.tactics shouldBe ("Proof Entry 2", "useLemma({`Entry 1`})", TactixLibrary.useLemmaX("Entry 1", None))::Nil
    entry2.info shouldBe empty
    entry2.fileContent shouldBe
      """Theorem "Entry 2"
        | ProgramVariables Real x; Real y; End.
        | Problem x>y -> x>=y End.
        | Tactic "Proof Entry 2" useLemma({`Entry 1`}) End.
        |End.""".stripMargin
  }

  it should "parse meta information" in {
    val input =
      """Lemma "Entry 1"
        | Description "The description of entry 1".
        | Title "A short entry 1 title".
        | Link "http://web.keymaerax.org/show/entry1".
        | ProgramVariables Real x; Real y; End.
        | Problem x>y -> y<x End.
        |End.""".stripMargin
    val entry = parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "lemma"
    entry.defs should beDecl(
      Declaration(Map(
        Name("x", None) -> Signature(None, Real, None, None, UnknownLocation),
        Name("y", None) -> Signature(None, Real, None, None, UnknownLocation)
      )))
    entry.model shouldBe "x>y -> y<x".asFormula
    entry.tactics shouldBe empty
    entry.info shouldBe Map(
      "Description" -> "The description of entry 1",
      "Title" -> "A short entry 1 title",
      "Link" -> "http://web.keymaerax.org/show/entry1")
    entry.fileContent shouldBe
      """Lemma "Entry 1"
        | Description "The description of entry 1".
        | Title "A short entry 1 title".
        | Link "http://web.keymaerax.org/show/entry1".
        | ProgramVariables Real x; Real y; End.
        | Problem x>y -> y<x End.
        |End.""".stripMargin
  }

  it should "FEATURE_REQUEST: parse meta information at any position" taggedAs TodoTest in {
    val input =
      """Lemma "Entry 1"
        | Description "The description of entry 1".
        | ProgramVariables Real x; Real y; End.
        | Link "http://web.keymaerax.org/show/entry1".
        | Problem x>y -> y<x End.
        | Title "A short entry 1 title".
        | Illustration "https://lfcps.org/example.png".
        |End.""".stripMargin
    val entry = parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "lemma"
    entry.defs should beDecl(
      Declaration(Map(
        Name("x", None) -> Signature(None, Real, None, None, UnknownLocation),
        Name("y", None) -> Signature(None, Real, None, None, UnknownLocation)
      )))
    entry.model shouldBe "x>y -> y<x".asFormula
    entry.tactics shouldBe empty
    entry.info shouldBe Map(
      "Description" -> "The description of entry 1",
      "Title" -> "A short entry 1 title",
      "Link" -> "http://web.keymaerax.org/show/entry1",
      "Illustration" -> "https://lfcps.org/example.png"
    )
    entry.fileContent shouldBe
      """Lemma "Entry 1"
        | Description "The description of entry 1".
        | ProgramVariables Real x; Real y; End.
        | Link "http://web.keymaerax.org/show/entry1".
        | Problem x>y -> y<x End.
        | Title "A short entry 1 title".
        | Illustration "https://lfcps.org/example.png".
        |End.""".stripMargin
  }

  it should "FEATURE_REQUEST: replace tabs with spaces" taggedAs TodoTest in withTactics {
    // tabs throw off the position computation in the lexer. in archives, this leads to faulty tactic extraction.
    val entry = parse("ArchiveEntry \"Replace tabs\"\nProgramVariables\n\tReal x;\nEnd.\nProblem\n\tx>0\nEnd.\nTactic \"Proof\" auto End. End.").loneElement
    entry.name shouldBe "Replace tabs"
    entry.kind shouldBe "theorem"
    entry.defs should beDecl(
      Declaration(Map(
        Name("x", None) -> Signature(None, Real, None, None, UnknownLocation)
      )))
    entry.model shouldBe "x>0".asFormula
    entry.tactics shouldBe ("Proof", "auto", TactixLibrary.auto(TactixLibrary.invGenerator, None)) :: Nil
    entry.info shouldBe empty
    entry.fileContent shouldBe
      """ArchiveEntry "Replace tabs"
        |ProgramVariables
        |  Real x;
        |End.
        |Problem
        |  x>0
        |End.
        |Tactic "Proof" auto End. End.""".stripMargin
  }

  it should "FEATURE_REQUEST: replace tabs with spaces in model-only entry" taggedAs TodoTest in {
    // tabs throw off the position computation in the lexer (especially before \n). in archives without tactics, this leads to faulty model extraction.
    val entry = parse("ArchiveEntry \"Replace tabs\"\nProgramVariables\t\nReal x;\nEnd.\nProblem\nx>0 End. End.").loneElement
    entry.name shouldBe "Replace tabs"
    entry.kind shouldBe "theorem"
    entry.defs should beDecl(
      Declaration(Map(
        Name("x", None) -> Signature(None, Real, None, None, UnknownLocation)
      )))
    entry.model shouldBe "x>0".asFormula
    entry.tactics shouldBe empty
    entry.info shouldBe empty
    entry.fileContent shouldBe
      s"""ArchiveEntry "Replace tabs"
         |ProgramVariables${"  "}
         |Real x;
         |End.
         |Problem
         |x>0 End. End.""".stripMargin
  }

  it should "FEATURE_REQUEST: double-check extracted artifact strings" taggedAs TodoTest in {
    val text = """ArchiveEntry "Entry 1"
                 |ProgramVariables
                 |  Real x;
                 |End.
                 |Problem
                 |  x>0 End. End.""".stripMargin
    val tokens = KeYmaeraXLexer.inMode(text, ProblemFileMode)
    // temper with positioning
    val problemIdx = tokens.indexWhere(_.tok.img == "Problem")
    val (correctPosTokens, wrongPosTokens) = tokens.splitAt(problemIdx)
    val wrongTokens: KeYmaeraXLexer.TokenStream = correctPosTokens ++ wrongPosTokens.map(t => Token(t.tok, t.loc match {
      case Region(l, c, el, ec) => Region(l-1, c, el-1, ec)
      case l => l
    }))

    val parse = PrivateMethod[List[ParsedArchiveEntry]]('parse)
    parser invokePrivate parse(tokens, text, true) // should not fail
    the [ParseException] thrownBy (parser invokePrivate parse(wrongTokens, text, true)) should
      have message """<somewhere> Even though archive parses, extracted problem does not parse (try reformatting):
                     |ArchiveEntry "Entry 1"
                     |ProgramVariables
                     |  Real x;
                     |End.
                     |Problem
                     |Found:    <unknown> at <somewhere>
                     |Expected: <unknown>""".stripMargin
  }

  "Global definitions" should "FEATURE_REQUEST: be added to all entries" taggedAs TodoTest in withTactics {
    val input =
      """SharedDefinitions
        | Bool gt(Real,Real) <-> ( ._0 > ._1 ).
        |End.
        |
        |Lemma "Entry 1"
        | ProgramVariables Real x; Real y; End.
        | Problem gt(x,y) -> x>=y End.
        |End.
        |
        |Theorem "Entry 2"
        | Definitions Bool geq(Real,Real) <-> ( ._0 >= ._1 ); End.
        | ProgramVariables Real x; Real y; End.
        | Problem gt(x,y) -> geq(x,y) End.
        | Tactic "Proof Entry 2" useLemma({`Entry 1`}) End.
        |End.""".stripMargin
    val entries = parse(input)
    entries should have size 2

    val entry1 = entries.head
    entry1.name shouldBe "Entry 1"
    entry1.kind shouldBe "lemma"
    entry1.defs should beDecl(
      Declaration(Map(
        Name("gt", None) -> Signature(Some(Tuple(Real, Real)), Bool, Some((Name("\\cdot", Some(0)), Real) :: (Name("\\cdot", Some(1)), Real) :: Nil), Some("._0>._1".asFormula), UnknownLocation),
        Name("x", None) -> Signature(None, Real, None, None, UnknownLocation),
        Name("y", None) -> Signature(None, Real, None, None, UnknownLocation)
      )))
    entry1.model shouldBe "gt(x,y) -> x>=y".asFormula
    entry1.expandedModel shouldBe "x>y -> x>=y".asFormula
    entry1.tactics shouldBe empty
    entry1.info shouldBe empty
    entry1.fileContent shouldBe
      """SharedDefinitions
        |Bool gt(Real,Real) <-> ( ._0 > ._1 ).
        |End.
        |Lemma "Entry 1"
        | ProgramVariables Real x; Real y; End.
        | Problem gt(x,y) -> x>=y End.
        |End.""".stripMargin
    entry1.problemContent shouldBe
      """SharedDefinitions
        |Bool gt(Real,Real) <-> ( ._0 > ._1 ).
        |End.
        |Lemma "Entry 1"
        | ProgramVariables Real x; Real y; End.
        | Problem gt(x,y) -> x>=y End.
        |End.""".stripMargin

    val entry2 = entries(1)
    entry2.name shouldBe "Entry 2"
    entry2.kind shouldBe "theorem"
    entry2.defs should beDecl(
      Declaration(Map(
        Name("gt", None) -> Signature(Some(Tuple(Real, Real)), Bool, Some((Name("\\cdot", Some(0)), Real) :: (Name("\\cdot", Some(1)), Real) :: Nil), Some("._0 > ._1".asFormula), UnknownLocation),
        Name("geq", None) -> Signature(Some(Tuple(Real, Real)), Bool, Some((Name("\\cdot", Some(0)), Real) :: (Name("\\cdot", Some(1)), Real) :: Nil), Some("._0 >= ._1".asFormula), UnknownLocation),
        Name("x", None) -> Signature(None, Real, None, None, UnknownLocation),
        Name("y", None) -> Signature(None, Real, None, None, UnknownLocation)
      )))
    entry2.model shouldBe "gt(x,y) -> geq(x,y)".asFormula
    entry2.expandedModel shouldBe "x>y -> x>=y".asFormula
    inside (entry2.tactics) {
      case (name, text, SeqTactic(ExpandAll(substs) :: lemma :: Nil)) :: Nil =>
        name shouldBe "Proof Entry 2"
        text shouldBe "useLemma({`Entry 1`})"
        substs should contain theSameElementsAs entry2.defs.substs
        lemma shouldBe TactixLibrary.useLemmaX("Entry 1", None)
    }
    entry2.info shouldBe empty
    entry2.fileContent shouldBe
      """SharedDefinitions
        |Bool gt(Real,Real) <-> ( ._0 > ._1 ).
        |End.
        |Theorem "Entry 2"
        | Definitions Bool geq(Real,Real) <-> ( ._0 >= ._1 ); End.
        | ProgramVariables Real x; Real y; End.
        | Problem gt(x,y) -> geq(x,y) End.
        | Tactic "Proof Entry 2" useLemma({`Entry 1`}) End.
        |End.""".stripMargin
  }

  it should "FEATURE_REQUEST: add to all entries but not auto-expand if tactic expands" taggedAs TodoTest in withTactics {
    val input =
      """SharedDefinitions
        | Bool gt(Real,Real) <-> ( ._0 > ._1 ).
        |End.
        |
        |Lemma "Entry 1"
        | ProgramVariables Real x; Real y; End.
        | Problem gt(x,y) -> x>=y End.
        |End.
        |
        |Theorem "Entry 2"
        | Definitions Bool geq(Real,Real) <-> ( ._0 >= ._1 ); End.
        | ProgramVariables Real x; Real y; End.
        | Problem gt(x,y) -> geq(x,y) End.
        | Tactic "Proof Entry 2" expand "gt" ; useLemma({`Entry 1`}) End.
        |End.""".stripMargin
    val entries = parse(input)
    entries should have size 2

    val entry1 = entries.head
    entry1.name shouldBe "Entry 1"
    entry1.kind shouldBe "lemma"
    entry1.defs should beDecl(
      Declaration(Map(
        Name("gt", None) -> Signature(Some(Tuple(Real, Real)), Bool, Some((Name("\\cdot", Some(0)), Real) :: (Name("\\cdot", Some(1)), Real) :: Nil), Some("._0>._1".asFormula), UnknownLocation),
        Name("x", None) -> Signature(None, Real, None, None, UnknownLocation),
        Name("y", None) -> Signature(None, Real, None, None, UnknownLocation)
      )))
    entry1.model shouldBe "gt(x,y) -> x>=y".asFormula
    entry1.expandedModel shouldBe "x>y -> x>=y".asFormula
    entry1.tactics shouldBe empty
    entry1.info shouldBe empty
    entry1.fileContent shouldBe
      """SharedDefinitions
        |Bool gt(Real,Real) <-> ( ._0 > ._1 ).
        |End.
        |Lemma "Entry 1"
        | ProgramVariables Real x; Real y; End.
        | Problem gt(x,y) -> x>=y End.
        |End.""".stripMargin
    entry1.problemContent shouldBe
      """SharedDefinitions
        |Bool gt(Real,Real) <-> ( ._0 > ._1 ).
        |End.
        |Lemma "Entry 1"
        | ProgramVariables Real x; Real y; End.
        | Problem gt(x,y) -> x>=y End.
        |End.""".stripMargin

    val entry2 = entries(1)
    entry2.name shouldBe "Entry 2"
    entry2.kind shouldBe "theorem"
    entry2.defs should beDecl(
      Declaration(Map(
        Name("gt", None) -> Signature(Some(Tuple(Real, Real)), Bool, Some((Name("\\cdot", Some(0)), Real) :: (Name("\\cdot", Some(1)), Real) :: Nil), Some("._0 > ._1".asFormula), UnknownLocation),
        Name("geq", None) -> Signature(Some(Tuple(Real, Real)), Bool, Some((Name("\\cdot", Some(0)), Real) :: (Name("\\cdot", Some(1)), Real) :: Nil), Some("._0 >= ._1".asFormula), UnknownLocation),
        Name("x", None) -> Signature(None, Real, None, None, UnknownLocation),
        Name("y", None) -> Signature(None, Real, None, None, UnknownLocation)
      )))
    entry2.model shouldBe "gt(x,y) -> geq(x,y)".asFormula
    entry2.expandedModel shouldBe "x>y -> x>=y".asFormula
    entry2.tactics shouldBe ("Proof Entry 2", """expand "gt" ; useLemma({`Entry 1`})""",
      Expand("gt".asNamedSymbol, SubstitutionPair(
        PredOf(Function("gt", None, Tuple(Real, Real), Bool, interpreted=false), Pair(DotTerm(Real, Some(0)), DotTerm(Real, Some(1)))),
        Greater(DotTerm(Real, Some(0)), DotTerm(Real, Some(1))))
      ) & TactixLibrary.useLemmaX("Entry 1", None))::Nil
    entry2.info shouldBe empty
    entry2.fileContent shouldBe
      """SharedDefinitions
        |Bool gt(Real,Real) <-> ( ._0 > ._1 ).
        |End.
        |Theorem "Entry 2"
        | Definitions Bool geq(Real,Real) <-> ( ._0 >= ._1 ); End.
        | ProgramVariables Real x; Real y; End.
        | Problem gt(x,y) -> geq(x,y) End.
        | Tactic "Proof Entry 2" expand "gt" ; useLemma({`Entry 1`}) End.
        |End.""".stripMargin
  }

  it should "FEATURE_REQUEST: add to all entries but not auto-expand if tactic uses US to expand" taggedAs TodoTest in withTactics {
    val input =
      """SharedDefinitions
        | Bool gt(Real x, Real y) <-> x > y;
        |End.
        |
        |Lemma "Entry 1"
        | ProgramVariables Real x; Real y; End.
        | Problem gt(x,y) -> x>=y End.
        |End.
        |
        |Theorem "Entry 2"
        | Definitions Bool geq(Real x, Real y) <-> x >= y; End.
        | ProgramVariables Real x; Real y; End.
        | Problem gt(x,y) -> geq(x,y) End.
        | Tactic "Proof Entry 2" US("gt(x,y) ~> x>y") ; useLemma("Entry 1") End.
        |End.""".stripMargin
    val entries = parse(input)
    entries should have size 2

    val entry1 = entries.head
    entry1.name shouldBe "Entry 1"
    entry1.kind shouldBe "lemma"
    entry1.defs should beDecl(
      Declaration(Map(
        Name("gt", None) -> Signature(Some(Tuple(Real, Real)), Bool, Some((Name("x", None), Real) :: (Name("y", None), Real) :: Nil), Some("._0>._1".asFormula), UnknownLocation),
        Name("x", None) -> Signature(None, Real, None, None, UnknownLocation),
        Name("y", None) -> Signature(None, Real, None, None, UnknownLocation)
      )))
    entry1.model shouldBe "gt(x,y) -> x>=y".asFormula
    entry1.expandedModel shouldBe "x>y -> x>=y".asFormula
    entry1.tactics shouldBe empty
    entry1.info shouldBe empty
    entry1.fileContent shouldBe
      """SharedDefinitions
        |Bool gt(Real x, Real y) <-> x > y;
        |End.
        |Lemma "Entry 1"
        | ProgramVariables Real x; Real y; End.
        | Problem gt(x,y) -> x>=y End.
        |End.""".stripMargin
    entry1.problemContent shouldBe
      """SharedDefinitions
        |Bool gt(Real x, Real y) <-> x > y;
        |End.
        |Lemma "Entry 1"
        | ProgramVariables Real x; Real y; End.
        | Problem gt(x,y) -> x>=y End.
        |End.""".stripMargin

    val entry2 = entries(1)
    entry2.name shouldBe "Entry 2"
    entry2.kind shouldBe "theorem"
    entry2.defs should beDecl(
      Declaration(Map(
        Name("gt", None) -> Signature(Some(Tuple(Real, Real)), Bool, Some((Name("x", None), Real) :: (Name("y", None), Real) :: Nil), Some("._0 > ._1".asFormula), UnknownLocation),
        Name("geq", None) -> Signature(Some(Tuple(Real, Real)), Bool, Some((Name("x", None), Real) :: (Name("y", None), Real) :: Nil), Some("._0 >= ._1".asFormula), UnknownLocation),
        Name("x", None) -> Signature(None, Real, None, None, UnknownLocation),
        Name("y", None) -> Signature(None, Real, None, None, UnknownLocation)
      )))
    entry2.model shouldBe "gt(x,y) -> geq(x,y)".asFormula
    entry2.expandedModel shouldBe "x>y -> x>=y".asFormula
    entry2.tactics shouldBe ("Proof Entry 2", """US("gt(x,y) ~> x>y") ; useLemma("Entry 1")""",
      TactixLibrary.USX(SubstitutionPair(
        PredOf(Function("gt", None, Tuple(Real, Real), Bool, interpreted=false), Pair(DotTerm(Real, Some(0)), DotTerm(Real, Some(1)))),
        Greater(DotTerm(Real, Some(0)), DotTerm(Real, Some(1)))) :: Nil
      ) & TactixLibrary.useLemmaX("Entry 1", None))::Nil
    entry2.info shouldBe empty
    entry2.fileContent shouldBe
      """SharedDefinitions
        |Bool gt(Real x, Real y) <-> x > y;
        |End.
        |Theorem "Entry 2"
        | Definitions Bool geq(Real x, Real y) <-> x >= y; End.
        | ProgramVariables Real x; Real y; End.
        | Problem gt(x,y) -> geq(x,y) End.
        | Tactic "Proof Entry 2" US("gt(x,y) ~> x>y") ; useLemma("Entry 1") End.
        |End.""".stripMargin
  }

  it should "FEATURE_REQUEST: not allow duplicates with local definitions" taggedAs TodoTest in {
    val input =
      """
        |SharedDefinitions
        | Bool gt(Real,Real) <-> ( ._0 > ._1 ).
        |End.
        |
        |Lemma "Entry 1"
        | Definitions Bool gt(Real,Real) <-> ( ._0 + 0 > ._1 ); End.
        | ProgramVariables Real x; Real y; End.
        | Problem gt(x,y) -> x>=y End.
        |End.
      """.stripMargin
    val ex = the [ParseException] thrownBy parse(input)
    ex.msg should include ("Symbol 'gt' overrides inherited definition; must declare override")
  }

  it should "FEATURE_REQUEST: not allow duplicates with local definitions even with different sorts" taggedAs TodoTest in {
    val input =
      """
        |SharedDefinitions
        | Bool gt(Real,Real) <-> ( ._0 > ._1 ).
        |End.
        |
        |Lemma "Entry 1"
        | Definitions Real gt(Real) = ( ._0 * 3 ); End.
        | ProgramVariables Real x; Real y; End.
        | Problem gt(x,y) -> x>=y End.
        |End.
      """.stripMargin
    val ex = the [ParseException] thrownBy parse(input)
    ex.msg should include ("Symbol 'gt' overrides inherited definition; must declare override")
  }

  it should "FEATURE_REQUEST: not swallow backslashes, for example \\exists" taggedAs TodoTest in {
    val input =
      """SharedDefinitions
        | Bool gt(Real,Real) <-> ( \exists t (t=1 & ._0*t > ._1) ).
        |End.
        |
        |Lemma "Entry 1"
        | Definitions Bool geq(Real,Real) <-> ( ._0 >= ._1 ); End.
        | ProgramVariables Real x; Real y; End.
        | Problem gt(x,y) -> geq(x,y) End.
        |End.""".stripMargin
    val entry = parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "lemma"
    entry.defs should beDecl(
      Declaration(Map(
        Name("gt", None) -> Signature(Some(Tuple(Real, Real)), Bool, Some((Name("\\cdot", Some(0)), Real) :: (Name("\\cdot", Some(1)), Real) :: Nil), Some("\\exists t (t=1 & ._0*t > ._1)".asFormula), UnknownLocation),
        Name("geq", None) -> Signature(Some(Tuple(Real, Real)), Bool, Some((Name("\\cdot", Some(0)), Real) :: (Name("\\cdot", Some(1)), Real) :: Nil), Some("._0 >= ._1".asFormula), UnknownLocation),
        Name("x", None) -> Signature(None, Real, None, None, UnknownLocation),
        Name("y", None) -> Signature(None, Real, None, None, UnknownLocation)
      )))
    entry.model shouldBe "gt(x,y) -> geq(x,y)".asFormula
    entry.expandedModel shouldBe "\\exists t (t=1 & x*t>y) -> x>=y".asFormula
    entry.tactics shouldBe empty
    entry.info shouldBe empty
    entry.fileContent shouldBe
      """SharedDefinitions
        |Bool gt(Real,Real) <-> ( \exists t (t=1 & ._0*t > ._1) ).
        |End.
        |Lemma "Entry 1"
        | Definitions Bool geq(Real,Real) <-> ( ._0 >= ._1 ); End.
        | ProgramVariables Real x; Real y; End.
        | Problem gt(x,y) -> geq(x,y) End.
        |End.""".stripMargin
  }

  it should "FEATURE_REQUEST: accept exercises" taggedAs TodoTest in {
    val input =
      """Exercise "Exercise 1"
        | Definitions Bool geq(Real a, Real b) <-> ( a >= b ); End.
        | ProgramVariables Real x, y; End.
        | Problem __________ -> geq(x,y) End.
        |End.""".stripMargin
    val entry = parse(input).loneElement
    entry.name shouldBe "Exercise 1"
    entry.kind shouldBe "exercise"
    entry.defs should beDecl(
      Declaration(Map(
        Name("geq", None) -> Signature(Some(Tuple(Real, Real)), Bool, Some((Name("a", None), Real) :: (Name("b", None), Real) :: Nil), Some("._0 >= ._1".asFormula), UnknownLocation),
        Name("x", None) -> Signature(None, Real, None, None, UnknownLocation),
        Name("y", None) -> Signature(None, Real, None, None, UnknownLocation)
      )))
    entry.model shouldBe "false".asFormula
    entry.tactics shouldBe empty
    entry.info shouldBe empty
    entry.fileContent shouldBe
      """Exercise "Exercise 1"
        | Definitions Bool geq(Real a, Real b) <-> ( a >= b ); End.
        | ProgramVariables Real x, y; End.
        | Problem __________ -> geq(x,y) End.
        |End.""".stripMargin
  }

  it should "FEATURE_REQUEST: accept exercises in definitions" taggedAs TodoTest in {
    val input =
      """Exercise "Exercise 1"
        | Definitions Bool geq(Real a, Real b) <-> ( __________ ); End.
        | ProgramVariables Real x, y; End.
        | Problem __________ -> geq(x,y) End.
        |End.""".stripMargin
    val entry = parse(input).loneElement
    entry.name shouldBe "Exercise 1"
    entry.kind shouldBe "exercise"
    entry.defs should beDecl(
      Declaration(Map(
        Name("geq", None) -> Signature(Some(Tuple(Real, Real)), Bool, Some((Name("a", None), Real) :: (Name("b", None), Real) :: Nil), None, UnknownLocation),
        Name("x", None) -> Signature(None, Real, None, None, UnknownLocation),
        Name("y", None) -> Signature(None, Real, None, None, UnknownLocation)
      )))
    entry.model shouldBe "false".asFormula
    entry.tactics shouldBe empty
    entry.info shouldBe empty
    entry.fileContent shouldBe
      """Exercise "Exercise 1"
        | Definitions Bool geq(Real a, Real b) <-> ( __________ ); End.
        | ProgramVariables Real x, y; End.
        | Problem __________ -> geq(x,y) End.
        |End.""".stripMargin
  }

  "Archive parser error message" should "FEATURE_REQUEST: report an invalid meta info key" taggedAs TodoTest in {
    the [ParseException] thrownBy parse(
      """ArchiveEntry "Entry 1"
        | MetaInfo "Invalid key".
        | ProgramVariables Real x; End.
        | Problem x>0 End.
        |End.""".stripMargin
    ) should have message """2:2 Invalid meta info key 'MetaInfo'
                            |Found:    MetaInfo at 2:2 to 2:9
                            |Expected: Link,Citation,Title,Description,Author,See,Illustration""".stripMargin
  }

  it should "FEATURE_REQUEST: report invalid meta info value" taggedAs TodoTest in {
    the [ParseException] thrownBy parse(
      """ArchiveEntry "Entry 1"
        | Title InvalidValue.
        | ProgramVariables Real x; End.
        | Problem x>0 End.
        |End.""".stripMargin
    ) should have message """2:8 Invalid meta info value
                            |Found:    InvalidValue at 2:8 to 2:19
                            |Expected: <string>""".stripMargin
  }

  it should "FEATURE_REQUEST: report missing meta info delimiter" taggedAs TodoTest in {
    the [ParseException] thrownBy parse(
      """ArchiveEntry "Entry 1"
        | Title "A title"
        | ProgramVariables Real x; End.
        | Problem x>0 End.
        |End.""".stripMargin
    ) should have message """3:2 Missing meta info delimiter
                            |Found:    ProgramVariables at 3:2 to 3:17
                            |Expected: .
                            |      or: ;""".stripMargin
  }

  it should "FEATURE_REQUEST: report missing or misplaced problem blocks" taggedAs TodoTest in {
    the [ParseException] thrownBy parse(
      """ArchiveEntry "Entry 1"
        | ProgramVariables Real x; End.
        |End.""".stripMargin
    ) should have message """3:1 Missing problem block
                            |Found:    End at 3:1 to 3:3
                            |Expected: Problem""".stripMargin

    the [ParseException] thrownBy parse(
      """ArchiveEntry "Entry 1"
        | ProgramVariables Real x; End.
        | Tactic "Proof". implyR(1) End.
        |End.""".stripMargin
    ) should have message """3:2 Missing problem block
                           |Found:    Tactic at 3:2 to 3:7
                           |Expected: Problem""".stripMargin

    the [ParseException] thrownBy parse(
      """ArchiveEntry "Entry 1"
        | ProgramVariables Real x; End.
        | Tactic "Proof". implyR(1) End.
        | Problem x>0 End.
        |End.""".stripMargin
    ) should have message """3:2 Misplaced problem block: problem expected before tactics
                           |Found:    Tactic at 3:2 to 3:7
                           |Expected: Problem""".stripMargin
  }

  it should "FEATURE_REQUEST: report misplaced variables or definitions" taggedAs TodoTest in {
    the [ParseException] thrownBy parse(
      """ArchiveEntry "Entry 1"
        | Problem x>0 End.
        | ProgramVariables Real x; End.
        |End.""".stripMargin
    ) should have message """2:2 Misplaced definitions/program variables: expected before problem
                            |Found:    Problem at 2:2 to 2:8
                            |Expected: ProgramVariables""".stripMargin

    the [ParseException] thrownBy parse(
      """ArchiveEntry "Entry 1"
        | Problem x>0 End.
        | Definitions Real f(); End.
        |End.""".stripMargin
    ) should have message """2:2 Misplaced definitions/program variables: expected before problem
                            |Found:    Problem at 2:2 to 2:8
                            |Expected: Definitions""".stripMargin

    the [ParseException] thrownBy parse(
      """ArchiveEntry "Entry 1"
        | Problem x>0 End.
        | ProgramVariables Real x; End.
        | Definitions Real f(); End.
        |End.""".stripMargin
    ) should have message """2:2 Misplaced definitions/program variables: expected before problem
                           |Found:    Problem at 2:2 to 2:8
                           |Expected: ProgramVariables""".stripMargin
  }

  it should "FEATURE_REQUEST: report missing archive names" taggedAs TodoTest in {
    the [ParseException] thrownBy parse(
      """ArchiveEntry.
        | ProgramVariables Real x; End.
        | Problem x>0 End.
        |End.""".stripMargin
    ) should have message """1:13 Missing archive name
                            |Found:    . at 1:13
                            |Expected: "<string>"""".stripMargin
  }

  it should "FEATURE_REQUEST: report a missing archive entry delimiter" taggedAs TodoTest in {
    the [ParseException] thrownBy parse(
      """ArchiveEntry "Entry 1"
        | Problem true End.""".stripMargin
    ) should have message """2:19 ArchiveEntry has no matching End.
                            |unmatched: ArchiveEntry|Lemma|Theorem|Exercise at 1:1 to 1:12--2:19 to EOF$
                            |Found:    EOF$ at 2:19 to EOF$
                            |Expected: End.
                            |Hint: Every entry (including ArchiveEntry, Problem, Lemma, Theorem, and Exercise) needs its own End. delimiter.""".stripMargin

    the [ParseException] thrownBy parse(
      """ArchiveEntry "Entry 1"
        | Problem true End.
        |Theorem "Entry 2"
        | Problem false->true End.
        |End.""".stripMargin
    ) should have message """3:1 ArchiveEntry has no matching End.
                            |unmatched: ArchiveEntry|Lemma|Theorem|Exercise at 1:1 to 1:12--3:1 to 3:7
                            |Found:    Theorem at 3:1 to 3:7
                            |Expected: End.
                            |Hint: Every entry (including ArchiveEntry, Problem, Lemma, Theorem, and Exercise) needs its own End. delimiter.""".stripMargin
  }

  it should "FEATURE_REQUEST: report a missing definitions delimiter" taggedAs TodoTest in {
    the [ParseException] thrownBy parse(
      """ArchiveEntry "Entry 1"
        | Definitions Real f().
        | Problem true End.
        |End.""".stripMargin
    ) should have message """3:2 Unexpected definition
                            |Found:    Problem at 3:2 to 3:8
                            |Expected: End
                            |      or: Real
                            |      or: Bool
                            |      or: HP""".stripMargin
  }

  it should "FEATURE_REQUEST: report a missing program variables delimiter" taggedAs TodoTest in {
    the [ParseException] thrownBy parse(
      """ArchiveEntry "Entry 1"
        | ProgramVariables Real x.
        | Problem true End.
        |End.""".stripMargin
    ) should have message """3:2 Unexpected program variable definition
                            |Found:    Problem at 3:2 to 3:8
                            |Expected: End
                            |      or: Real""".stripMargin
  }

  it should "FEATURE_REQUEST: report a missing problem delimiter" taggedAs TodoTest in {
    the [ParseException] thrownBy parse(
      """ArchiveEntry "Entry 1"
        | Problem true
        | Tactic "Proof" close End.
        |End.""".stripMargin
    ) should have message """3:2 Missing problem delimiter
                            |Found:    Tactic at 3:2 to 3:7
                            |Expected: End""".stripMargin

    the [ParseException] thrownBy parse(
      """ArchiveEntry "Entry 1"
        | Problem true""".stripMargin
    ) should have message """2:14 Missing problem delimiter
                           |Found:    <EOF> at 2:14 to EOF$
                           |Expected: End""".stripMargin

    the [ParseException] thrownBy parse(
      """ArchiveEntry "Entry 1"
        | Problem true End""".stripMargin
    ) should have message """2:18 Missing . after delimiter End
                            |Found:    <EOF> at 2:18 to EOF$
                            |Expected: .
                            |Hint: ParseState( :+ ArchiveEntry :+ DOUBLE_QUOTES_STRING :+ MetaInfo(Map()) :+ Definitions(List(),List())  <|>  PROBLEM_BLOCK$, TRUE$, END_BLOCK$, EOF$)""".stripMargin

    the [ParseException] thrownBy parse(
      """ArchiveEntry "Entry 1"
        | Problem true End
        |Tactic "My tactic" closeTrue End. """.stripMargin
    ) should have message """3:1 Missing . after delimiter End
                            |Found:    Tactic at 3:1 to 3:6
                            |Expected: .
                            |Hint: ParseState( :+ ArchiveEntry :+ DOUBLE_QUOTES_STRING :+ MetaInfo(Map()) :+ Definitions(List(),List())  <|>  PROBLEM_BLOCK$, TRUE$, END_BLOCK$, TACTIC_BLOCK$, DOUBLE_QUOTES_STRING, ID("closeTrue"), END_BLOCK$, PERIOD$, EOF$)""".stripMargin
  }

  it should "FEATURE_REQUEST: report parse errors in function definitions" taggedAs TodoTest in {
    the [ParseException] thrownBy parse(
      """ArchiveEntry "Entry 1"
        | Definitions Real f() = 5*g() + *h(); End.
        | Problem true End.
        |End.""".stripMargin
    ) should have message """2:33 Unexpected token cannot be parsed
                            |Found:    * at 2:33
                            |Expected: <BeginningOfExpression>""".stripMargin
  }

  it should "FEATURE_REQUEST: report parse errors in predicate definitions" taggedAs TodoTest in {
    the [ParseException] thrownBy parse(
      """ArchiveEntry "Entry 1"
        | Definitions Bool p() <-> f()+5^ > g(); End.
        | Problem true End.
        |End.""".stripMargin
    ) should have message """2:34 Unexpected token cannot be parsed
                            |Found:    > at 2:34
                            |Expected: <BeginningOfExpression>""".stripMargin
  }

  it should "FEATURE_REQUEST: report parse errors in program definitions" taggedAs TodoTest in {
    the [ParseException] thrownBy parse(
      """ArchiveEntry "Entry 1"
        | Definitions HP acc ::= { a:=* }; End.
        | Problem true End.
        |End.""".stripMargin
    ) should have message """2:32 Unexpected token cannot be parsed
                            |Found:    } at 2:32
                            |Expected: ;""".stripMargin

    the [ParseException] thrownBy parse(
      """ArchiveEntry "Entry 1"
        | Definitions HP acc ::= { x'= }; End.
        | Problem true End.
        |End.""".stripMargin
    ) should have message """2:31 Missing right-hand side x'=
                            |Found:    } at 2:31
                            |Expected: $$$T""".stripMargin

    the [ParseException] thrownBy parse(
      """ArchiveEntry "Entry 1"
        | Definitions HP acc ::= { x'=7* }; End.
        | Problem true End.
        |End.""".stripMargin
    ) should have message """2:33 Unexpected token cannot be parsed
                            |Found:    } at 2:33
                            |Expected: <BeginningOfTerm>""".stripMargin

    the [ParseException] thrownBy parse(
      """ArchiveEntry "Entry 1"
        | Definitions HP acc ::= { x'=x, t'= }; End.
        | Problem true End.
        |End.""".stripMargin
    ) should have message """2:37 Missing right-hand side t'=
                            |Found:    } at 2:37
                            |Expected: $$$T""".stripMargin
  }



  it should "FEATURE_REQUEST: report misplaced function, predicate, or program definitions" taggedAs TodoTest in {
    the [ParseException] thrownBy parse(
      """ArchiveEntry "Entry 1"
        | ProgramVariables Real f(); End.
        | Problem true End.
        |End.""".stripMargin
    ) should have message """2:25 Function definition only allowed in Definitions block
                            |Found:    ( at 2:25
                            |Expected: ;
                            |      or: ,""".stripMargin

    the [ParseException] thrownBy parse(
      """ArchiveEntry "Entry 1"
        | ProgramVariables Bool p(); End.
        | Problem true End.
        |End.""".stripMargin
    ) should have message """2:19 Predicate and program definitions only allowed in Definitions block
                            |Found:    Bool at 2:19 to 2:22
                            |Expected: Real""".stripMargin

    the [ParseException] thrownBy parse(
      """ArchiveEntry "Entry 1"
        | ProgramVariables HP a; End.
        | Problem true End.
        |End.""".stripMargin
    ) should have message """2:19 Predicate and program definitions only allowed in Definitions block
                           |Found:    HP at 2:19 to 2:20
                           |Expected: Real""".stripMargin

    the [ParseException] thrownBy parse(
      """ArchiveEntry "Entry 1"
        | ProgramVariables Real x &; End.
        | Problem true End.
        |End.""".stripMargin
    ) should have message """2:26 Unexpected token in ProgramVariables block
                            |Found:    & at 2:26
                            |Expected: ;
                            |      or: ,""".stripMargin

    the [ParseException] thrownBy parse(
      """ArchiveEntry "Entry 1"
        | ProgramVariables Real x Real y; End.
        | Problem true End.
        |End.""".stripMargin
    ) should have message """2:26 Missing variable declaration delimiter
                            |Found:    Real at 2:26 to 2:29
                            |Expected: ;""".stripMargin
  }

  it should "FEATURE_REQUEST: report function definition errors" taggedAs TodoTest in {
    the [ParseException] thrownBy parse(
      """ArchiveEntry "Entry 1"
        | Definitions Real f() & ; End.
        | Problem true End.
        |End.""".stripMargin
    ) should have message """2:23 Unexpected token in function definition
                            |Found:    & at 2:23
                            |Expected: =
                            |      or: ;""".stripMargin

    the [ParseException] thrownBy parse(
      """ArchiveEntry "Entry 1"
        | Definitions Real f() <-> 5; End.
        | Problem true End.
        |End.""".stripMargin
    ) should have message """2:23 Function must be defined by equality
                            |Found:    <-> at 2:23 to 2:25
                            |Expected: =""".stripMargin

    the [ParseException] thrownBy parse(
      """ArchiveEntry "Entry 1"
        | Definitions Real f() = 5!=7; End.
        | Problem true End.
        |End.""".stripMargin
    ) should have message """2:25 Impossible elaboration: Operator PSEUDO$ expects a Term as argument but got the Formula 5!=7
                            |Found:    5!=7 at 2:25 to 2:28
                            |Expected: Term""".stripMargin
  }

  it should "FEATURE_REQUEST: report predicate definition errors" taggedAs TodoTest in {
    the [ParseException] thrownBy parse(
      """ArchiveEntry "Entry 1"
        | Definitions Bool p() & ; End.
        | Problem true End.
        |End.""".stripMargin
    ) should have message """2:23 Unexpected token in predicate definition
                            |Found:    & at 2:23
                            |Expected: <->""".stripMargin

    the [ParseException] thrownBy parse(
      """ArchiveEntry "Entry 1"
        | Definitions Bool p() = 5>0; End.
        | Problem true End.
        |End.""".stripMargin
    ) should have message """2:23 Predicate must be defined by equivalence
                            |Found:    = at 2:23
                            |Expected: <->""".stripMargin

    the [ParseException] thrownBy parse(
      """ArchiveEntry "Entry 1"
        | Definitions Bool p() <-> 5+7; End.
        | Problem true End.
        |End.""".stripMargin
    ) should have message """2:27 Impossible elaboration: Operator PSEUDO$ expects a Formula as argument but got the Term 5+7
                            |Found:    5+7 at 2:27 to 2:29
                            |Expected: Formula""".stripMargin
  }

  it should "FEATURE_REQUEST: report substitution errors" taggedAs TodoTest in {
    val entries = parse(
      """ArchiveEntry "Entry 1"
        | Definitions Bool p() <-> y>=0; End.
        | ProgramVariables Real y; End.
        | Problem [y:=0;]p() End.
        |End.""".stripMargin
    )
    the [ParseException] thrownBy entries.loneElement.expandedModel should have message
      """<somewhere> Definition p() as y>=0 must declare arguments {y}
        |Found:    <unknown> at <somewhere>
        |Expected: <unknown>""".stripMargin
  }

  it should "FEATURE_REQUEST: report imbalanced parentheses in predicate definitions" taggedAs TodoTest in {
    the [ParseException] thrownBy parse(
      """ArchiveEntry "Entry 1"
        | Definitions Bool p() <-> ( true; End.
        | Problem true End.
        |End.""".stripMargin
    ) should have message """2:27 Unmatched opening parenthesis in predicate definition
                            |unmatched: LPAREN$ at 2:27--2:29 to 2:32
                            |Found:    TRUE$ at 2:27 to 2:32
                            |Expected: )""".stripMargin

    the [ParseException] thrownBy parse(
      """ArchiveEntry "Entry 1"
        | Definitions Bool p() <-> ( (true) | false; End.
        | Problem true End.
        |End.""".stripMargin
    ) should have message """2:27 Unmatched opening parenthesis in predicate definition
                            |unmatched: LPAREN$ at 2:27--2:29
                            |Found:    LPAREN$ at 2:27 to 2:29
                            |Expected: )""".stripMargin
  }

  it should "FEATURE_REQUEST: report tactic errors at the correct location" taggedAs TodoTest in {
    the [ParseException] thrownBy parse(
      """ArchiveEntry "Entry 1"
        | ProgramVariables Real x; Real y; End.
        | Problem x>y -> x>=y End.
        | Tactic "Proof 1". implyR(1) ; End.
        |End.""".stripMargin
    ) should have message """4:31 A combinator should be followed by a full tactic expression
                            |Found:    Some(BelleToken(EOF$,4:31 to EOF$)) at 4:31 to EOF$
                            |Expected: """.stripMargin
  }

  it should "FEATURE_REQUEST: report a missing entry ID separator" taggedAs TodoTest in {
    the [ParseException] thrownBy parse(
      """ArchiveEntry entry1 "Entry 1"
        | ProgramVariables Real x; Real y; End.
        | Problem x>y -> x>=y End.
        |End.""".stripMargin
    ) should have message """1:21 Missing entry ID separator
                            |Found:    <string> at 1:21 to 1:29
                            |Expected: :""".stripMargin

    the [ParseException] thrownBy parse(
      """ArchiveEntry entry1
        | ProgramVariables Real x; Real y; End.
        | Problem x>y -> x>=y End.
        |End.""".stripMargin
    ) should have message """2:2 Missing entry ID separator
                            |Found:    ProgramVariables at 2:2 to 2:17
                            |Expected: :""".stripMargin
  }

  it should "FEATURE_REQUEST: report a missing entry title" taggedAs TodoTest in {
    the [ParseException] thrownBy parse(
      """ArchiveEntry entry1 :
        | ProgramVariables Real x; Real y; End.
        | Problem x>y -> x>=y End.
        |End.""".stripMargin
    ) should have message """2:2 Missing entry title
                            |Found:    ProgramVariables at 2:2 to 2:17
                            |Expected: <string>""".stripMargin
  }

  it should "FEATURE_REQUEST: report undefined entry IDs" taggedAs TodoTest in {
    the [ParseException] thrownBy parse(
      """ArchiveEntry "Entry 1"
        | ProgramVariables Real x; Real y; End.
        | Problem x>y -> x>=y End.
        |End entry1.""".stripMargin
    ) should have message """4:5 Archive entry ends with undefined ID entry1; define ID at entry start with ArchiveEntry entry1 : "Entry 1"
                            |Found:    <unknown> at 4:5 to 4:10
                            |Expected: <unknown>""".stripMargin

    the [ParseException] thrownBy parse(
      """ArchiveEntry entry1 : "Entry 1"
        | ProgramVariables Real x; Real y; End.
        | Problem x>y -> x>=y End.
        |End entry2.""".stripMargin
    ) should have message """4:5 Archive entry ends with ID entry2 but entry start defined entry1
                            |Found:    <unknown> at 4:5 to 4:10
                            |Expected: <unknown>""".stripMargin
  }

  it should "FEATURE_REQUEST: report sort identifier mismatches" taggedAs TodoTest in {
    the [ParseException] thrownBy parse(
      """ProgramVariables
        |  Real x;
        |  Rea y;
        |End.
        |Problem x>y -> x>=y End.""".stripMargin
    ) should have message """3:3 Unexpected program variable definition
                            |Found:    Rea at 3:3 to 3:5
                            |Expected: End
                            |      or: Real""".stripMargin

    the [ParseException] thrownBy parse(
      """ProgramVariables
        |  Real x;
        |  Bool y;
        |End.
        |Problem x>y -> x>=y End.""".stripMargin
    ) should have message """3:3 Predicate and program definitions only allowed in Definitions block
                            |Found:    Bool at 3:3 to 3:6
                            |Expected: Real""".stripMargin
  }

  it should "FEATURE_REQUEST: type-analyze annotations" taggedAs TodoTest in {
    the [ParseException] thrownBy parse(
      """Definitions
        |  Real f;
        |  Real g;
        |End.
        |
        |Problem
        |  [{?true;}*@invariant(fg > 0)]true
        |End.""".stripMargin
    ) should have message """<somewhere> type analysis: <undefined>: undefined symbol fg with index None
                            |Found:    undefined symbol at <somewhere>
                            |Expected: BaseVariable of sort Real
                            |Hint: Make sure to declare all variables in ProgramVariable and all symbols in Definitions block.""".stripMargin
  }

  it should "FEATURE_REQUEST: report program constant and differential program constant mismatches" taggedAs TodoTest in {
    the [ParseException] thrownBy parse(
      """ProgramVariables Real x; End.
        |Definitions HP inc ::= { x:=x+1; }; End.
        |Problem x>=0 -> [{inc}]x>=0 End.
      """.stripMargin
    ) should have message
      """<somewhere> All definitions and uses must match, but found the following mismatches:
        |Symbol 'inc{|^@|};' defined as Program, but used as DifferentialProgram in {inc}
        |Found:    {inc} at <somewhere>
        |Expected: inc{|^@|};""".stripMargin

    the [ParseException] thrownBy parse(
      """ProgramVariables Real x; End.
        |Definitions
        |  HP inc ::= { x:=x+1; };
        |  HP useInc ::= { {inc} };
        |End.
        |Problem x>=0 -> [useInc;]x>=0 End.
      """.stripMargin
    ) should have message
      """<somewhere> All definitions and uses must match, but found the following mismatches:
        |Symbol 'inc{|^@|};' defined as Program, but used as DifferentialProgram in {inc}
        |Found:    {inc} at <somewhere>
        |Expected: inc{|^@|};""".stripMargin
  }

  it should "FEATURE_REQUEST: report illegal name overloading" taggedAs TodoTest in {
    the [ParseException] thrownBy parse(
      """ArchiveEntry "Entry 1"
        | Definitions Real f(Real x) = x+1; Real f(Real x, Real y) = x+y; Bool f(Real x) <-> x>0; End.
        | Problem f(f(f(2,3))) End.
        |End.""".stripMargin
    ) should have message
      """2:66 Duplicate symbol 'f'
        |Found:    <unknown> at 2:66 to 2:88
        |Expected: <unknown>""".stripMargin

    the [ParseException] thrownBy parse(
      """ArchiveEntry "Entry 1"
        | Definitions HP inc ::= { x:=x+1;}; HP inc ::= { {x'=1} }; End.
        | ProgramVariables Real x; End.
        | Problem x>0 -> [inc;]x>0 End.
        |End.""".stripMargin
    ) should have message
      """2:37 Duplicate symbol 'inc'
        |Found:    <unknown> at 2:37 to 2:58
        |Expected: <unknown>""".stripMargin
  }

  it should "FEATURE_REQUEST: report variables used as functions" taggedAs TodoTest in {
    the [ParseException] thrownBy parse(
      """ArchiveEntry "Entry 1"
        | ProgramVariables Real x; End.
        | Problem x()>0 End.
        |End.""".stripMargin
    ) should have message
      """2:19 type analysis: Entry 1: x declared as a variable of sort Real but used as a function with arguments.
        |Found:    no arguments at 2:19 to 2:22
        |Expected: function with arguments""".stripMargin
  }


}
