/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/

package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.bellerophon.parser.{BellePrettyPrinter, DLBelleParser}
import edu.cmu.cs.ls.keymaerax.bellerophon.{ApplyDefTactic, DefTactic, OnAll, ReflectiveExpressionBuilder, Using}
import edu.cmu.cs.ls.keymaerax.btactics.{FixedGenerator, TacticTestBase, TactixLibrary}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core.{Assign, Bool, Box, DotTerm, Equal, FuncOf, GreaterEqual, Imply, Number, Plus, Power, PredOf, Real, Trafo, Tuple, Unit, Variable}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import org.scalatest.LoneElement._
import org.scalatest.matchers.{MatchResult, Matcher}
import testHelper.KeYmaeraXTestTags.TodoTest

/**
  * Tests the DL archive parser.
  * @author Stefan Mitsch
  * @author Andre Platzer
  * @author James Gallicchio
  */
class DLArchiveParserTests extends TacticTestBase {

  override def afterEach(): Unit = { Parser.parser.setAnnotationListener((_, _) => {}) }

  private def parse(input: String): List[ParsedArchiveEntry] =
    ArchiveParser.parse(input)

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

  it should "parse simple predicate declaration" taggedAs TodoTest in {
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

  it should "give a readable error message on unsupported unicode characters" in {
    val input =
      """
        |ArchiveEntry "Entry 1"
        | Description "Unicode is allowed in strings: ü, é, ∇, ©, ↩︎"
        | Definitions Bool p(Real x, Real y) <-> x >= -2 & x <= -1 & y >= −3 /* the last minus is not ASCII */; End.
        | ProgramVariables Real x; End.
        | Problem p(x,5) -> [x:=x+1;]p(x-1,5) End.
        |End.
      """.stripMargin
    the [ParseException] thrownBy parse(input).loneElement should have message
      """3:65 Unsupported Unicode character '−', please try ASCII
        |Found:    − at 3:65
        |Expected: ASCII character""".stripMargin
  }

  it should "give a readable error message on unsupported unicode characters in multiline strings" in {
    val input =
      """
        |ArchiveEntry "Entry 1"
        | Description "Unicode is allowed in strings: ü,
        |              é, ∇,
        |              ©, ↩︎"
        | Definitions Bool p(Real x, Real y) <-> x >= -2 & x <= -1 & y >= −3 /* the last minus is not ASCII */; End.
        | ProgramVariables Real x; End.
        | Problem p(x,5) -> [x:=x+1;]p(x-1,5) End.
        |End.
      """.stripMargin
    the [ParseException] thrownBy parse(input) should have message
      """3:65 Unsupported Unicode character '−', please try ASCII
        |Found:    − at 3:65
        |Expected: ASCII character""".stripMargin
  }

  it should "detect a missing tactic name" in {
    val input =
      """ArchiveEntry "Test"
        |Problem 1+1=2 End.
        |Tactic notatactic End.
        |End.""".stripMargin
    the [ParseException] thrownBy parse(input) should have message
      """3:8 Error parsing baseTac at 3:8
        |Found:    "notatactic" at 3:8
        |Expected: (string | "?" | <(tactic,tactic,...) | (tactic) | "doall" | "partial" | "let" | "tactic" | "USMatch" | atomicTactic | tactic(...))
        |Hint: Try ("\"" | "?" | "<" | "(" | "doall" | "partial" | "let" | "tactic" | "USMatch")""".stripMargin
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

  it should "parse simple unary predicate definition" taggedAs TodoTest in {
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
    DLParser.parseValue( "Definitions HP a ::= { x:=x+1; }; End.", archiveParser.definitions(Declaration(Map.empty))(_)) shouldBe Declaration(Map(Name("a", None) -> Signature(Some(Unit), Trafo, None, Some("x:=x+1;".asProgram), UnknownLocation)))
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

  it should "parse lots of definitions before variables" in {
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
    the [ParseException] thrownBy parse(input) should (have message
      """<somewhere> Semantic analysis error
        |semantics: Expect unique names_index that identify a unique type.
        |ambiguous: x:Unit->Real and x:Real
        |symbols:   x, x
        |Found:    <unknown> at <somewhere>
        |Expected: <unknown>""".stripMargin
      or have message
      """3:27 Error parsing programVariables at 3:2
        |Found:    "End." at 3:27
        |Expected: Unique name (x not unique)
        |Hint: Try ("Real" | "Bool" | "HP" | "HG" | Unique name (x not unique))""".stripMargin)
  }

  it should "give useful error messages on semantic analysis" in {
    val input =
      """ArchiveEntry "Test"
        |Definitions Real one = 1; End.
        |ProgramVariables /* Real x; */ End.
        |Problem x>0 -> [x:=x+1;]x>1 End.
        |End.""".stripMargin
    the [ParseException] thrownBy parse(input) should have message
      """<somewhere> type analysis: Test: undefined symbol x
        |Found:    undefined symbol x at <somewhere>
        |Expected: Real x
        |Hint: Add "Real x;" to the ProgramVariables block""".stripMargin
  }

  it should "give useful error messages on semantic analysis (2)" in {
    val input =
      """ArchiveEntry "Test"
        |Definitions Real f; End.
        |ProgramVariables Real x,y; End.
        |Problem x -> [x:=1+f;]x>f End. /* uses x as predicate and variable */
        |End.""".stripMargin
    the [ParseException] thrownBy parse(input) should have message
      """<somewhere> Semantic analysis error
        |semantics: Expect unique names_index that identify a unique type.
        |ambiguous: x:Unit->Bool and x:Real
        |Found:    x:Unit->Bool and x:Real at <somewhere>
        |Expected: unambiguous type""".stripMargin
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

  it should "parse lots of definitions after variables" in {
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

  it should "parse definitions without parentheses" in {
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

  it should "not accept reserved identifiers" in {
    the [ParseException] thrownBy parse(
      """ArchiveEntry "Entry 1"
        | ProgramVariables Real Real; End.
        | Problem true End.
        |End.""".stripMargin
    ) should have message
      """2:24 Error parsing ident at 2:24
        |Found:    "Real; End." at 2:24
        |Expected: ident
        |Hint: Try ()""".stripMargin

    the [ParseException] thrownBy parse(
      """ArchiveEntry "Entry 1"
        | ProgramVariables Real Bool; End.
        | Problem true End.
        |End.""".stripMargin
    ) should have message
      """2:24 Error parsing ident at 2:24
        |Found:    "Bool; End." at 2:24
        |Expected: ident
        |Hint: Try ()""".stripMargin

    the [ParseException] thrownBy parse(
      """ArchiveEntry "Entry 1"
        | ProgramVariables Real HP; End.
        | Problem true End.
        |End.""".stripMargin
    ) should have message
      """2:24 Error parsing ident at 2:24
        |Found:    "HP; End." at 2:24
        |Expected: ident
        |Hint: Try ()""".stripMargin
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

  it should "allow comma-separated simple function definitions" in {
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

  it should "parse a problem that uses the built-in interpreted functions" taggedAs TodoTest in {
    val input =
      """ArchiveEntry "Entry 1"
        | Problem abs(-5)>0 End.
        |End.""".stripMargin
    val entry = parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "theorem"
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

  it should "not parse a plain problem format" in {
    val input =
      """ProgramVariables Real x; Real y; End.
        |Problem x>y -> x>=y End.
      """.stripMargin
    the [ParseException] thrownBy parse(input).loneElement should have message
      """1:1 Error parsing archiveStart at 1:1
        |Found:    "ProgramVar" at 1:1
        |Expected: ("ArchiveEntry" | "Lemma" | "Theorem" | "Exercise")
        |Hint: Try ("SharedDefinitions" | "ArchiveEntry" | "Lemma" | "Theorem" | "Exercise")""".stripMargin
  }

  it should "parse a problem without declarations" in {
    val input = "ArchiveEntry \"Test\" Problem x>y -> x>=y End. End."
    val entry = parse(input).loneElement
    entry.name shouldBe "Test"
    entry.kind shouldBe "theorem"
    entry.defs.decls shouldBe 'empty
    entry.model shouldBe "x>y -> x>=y".asFormula
    entry.tactics shouldBe empty
    entry.info shouldBe empty
    entry.fileContent shouldBe input.trim()
  }


  it should "refuse mixed plain and named entries" in {
    val input =
      """ProgramVariables Real x; Real y; End.
        |Problem x>y -> x>=y End.
        |
        |ArchiveEntry "Entry 2"
        |  ProgramVariables Real x; End.
        |  Problem x>0 End.
        |End.
      """.stripMargin
    the [ParseException] thrownBy parse(input) should have message
      """1:1 Error parsing archiveStart at 1:1
        |Found:    "ProgramVar" at 1:1
        |Expected: ("ArchiveEntry" | "Lemma" | "Theorem" | "Exercise")
        |Hint: Try ("SharedDefinitions" | "ArchiveEntry" | "Lemma" | "Theorem" | "Exercise")""".stripMargin
  }

  it should "detect duplicate variable definitions" in {
    val input =
      """
        |ArchiveEntry "Entry 1"
        | ProgramVariables Real x; Real x; Real y; End.
        | Problem x>y -> x>=y End.
        |End.
      """.stripMargin
    the [ParseException] thrownBy parse(input) should have message
      """3:43 Error parsing programVariables at 3:2
        |Found:    "End." at 3:43
        |Expected: Unique name (x not unique)
        |Hint: Try ("Real" | "Bool" | "HP" | "HG" | Unique name (x not unique))""".stripMargin
  }

  it should "detect duplicate function names" in {
    val input =
      """
        |ArchiveEntry "Entry 1"
        | Definitions Real f() = 1; Real f() = 2; End.
        | ProgramVariables Real x; Real y; End.
        | Problem x>y -> x>=y End.
        |End.
      """.stripMargin
    the [ParseException] thrownBy parse(input) should have message
      """3:42 Error parsing definitions at 3:2
        |Found:    "End." at 3:42
        |Expected: Unique name (f not unique)
        |Hint: Try Unique name (f not unique)""".stripMargin
  }

  it should "detect duplicate predicate names" in {
    val input =
      """
        |ArchiveEntry "Entry 1"
        | Definitions Bool p() <-> 1>0; Bool p() <-> 2>1; End.
        | ProgramVariables Real x; Real y; End.
        | Problem p() -> x>=y End.
        |End.
      """.stripMargin
    the [ParseException] thrownBy parse(input) should have message
      """3:50 Error parsing definitions at 3:2
        |Found:    "End." at 3:50
        |Expected: Unique name (p not unique)
        |Hint: Try Unique name (p not unique)""".stripMargin
  }

  it should "detect duplicate program names" in {
    val input =
      """
        |ArchiveEntry "Entry 1"
        | Definitions HP a ::= { ?true; }; HP a ::= { ?false; }; End.
        | ProgramVariables Real x; Real y; End.
        | Problem [a;]true End.
        |End.
      """.stripMargin
    the [ParseException] thrownBy parse(input) should have message
      """3:57 Error parsing definitions at 3:2
        |Found:    "End." at 3:57
        |Expected: Unique name (a not unique)
        |Hint: Try Unique name (a not unique)""".stripMargin
  }

  it should "detect duplicate definitions (1)" in {
    val input =
      """ArchiveEntry "Entry 1"
        | Definitions Real x; End.
        | ProgramVariables Real x; End.
        | Problem x^2>=0 End.
        |End.
      """.stripMargin
    the [ParseException] thrownBy parse(input) should have message
      """3:27 Error parsing programVariables at 3:2
        |Found:    "End." at 3:27
        |Expected: Unique name (x not unique)
        |Hint: Try ("Real" | "Bool" | "HP" | "HG" | Unique name (x not unique))""".stripMargin
  }

  it should "detect duplicate definitions (2)" in {
    val input =
      """ArchiveEntry "Entry 1"
        | Definitions Real x; End.
        | ProgramVariables Real y; End.
        | Definitions Real z; End.
        | ProgramVariables Real x; End.
        | Problem x^2>=0 End.
        |End.
      """.stripMargin
    the [ParseException] thrownBy parse(input) should have message
      """5:27 Error parsing programVariables at 5:2
        |Found:    "End." at 5:27
        |Expected: Unique name (x not unique)
        |Hint: Try ("Real" | "Bool" | "HP" | "HG" | Unique name (x not unique))""".stripMargin
  }

  it should "detect duplicate definitions (3)" in {
    val input =
      """ArchiveEntry "Entry 1"
        | Definitions Real x; End.
        | ProgramVariables Real y; End.
        | Definitions Real y; End.
        | Problem x^2>=0 End.
        |End.
      """.stripMargin
    the [ParseException] thrownBy parse(input) should have message
      """4:22 Error parsing definitions at 4:2
        |Found:    "End." at 4:22
        |Expected: Unique name (y not unique)
        |Hint: Try Unique name (y not unique)""".stripMargin
  }

  it should "detect duplicate definitions (4)" in {
    val input =
      """ArchiveEntry "Entry 1"
        | Definitions Real x; End.
        | ProgramVariables Real y; End.
        | Definitions Real x; End.
        | Problem x^2>=0 End.
        |End.
      """.stripMargin
    the [ParseException] thrownBy parse(input) should have message
      """4:22 Error parsing definitions at 4:2
        |Found:    "End." at 4:22
        |Expected: Unique name (x not unique)
        |Hint: Try Unique name (x not unique)""".stripMargin
  }

  it should "detect duplicate definitions (5)" in {
    val input =
      """ArchiveEntry "Entry 1"
        | ProgramVariables Real x; End.
        | ProgramVariables Real x; End.
        | Problem x^2>=0 End.
        |End.
      """.stripMargin
    the [ParseException] thrownBy parse(input) should have message
      """3:27 Error parsing programVariables at 3:2
        |Found:    "End." at 3:27
        |Expected: Unique name (x not unique)
        |Hint: Try ("Real" | "Bool" | "HP" | "HG" | Unique name (x not unique))""".stripMargin
  }

  it should "not complain about undeclared variables in unused program definitions" in {
    val input =
      """ArchiveEntry "Test"
        |Definitions HP a ::= { y:=y+1; }; End.
        |ProgramVariables Real x; End.
        |Problem [x:=1;]x>=0 End.
        |End.
        |""".stripMargin
      parse(input).head.model shouldBe Box(Assign(Variable("x"), Number(1)), GreaterEqual(Variable("x"), Number(0)))
  }

  it should "complain about undeclared variables in unused function definitions" in {
    val input =
      """ArchiveEntry "Test"
        |Definitions Real f() = y+1; End.
        |ProgramVariables Real x; End.
        |Problem [x:=1;]x>=0 End.
        |End.
        |""".stripMargin
    the [ParseException] thrownBy parse(input) should have message
      """<somewhere> Definition f uses undefined symbol(s) y. Please add arguments or define as functions/predicates/programs
        |Found:    <unknown> at <somewhere>
        |Expected: <unknown>""".stripMargin
  }

  it should "not elaborate in unused program definitions" in {
    val input =
      """SharedDefinitions HP a ::= { y:=y+1; }; End.
        |ArchiveEntry "Test"
        |Definitions Real y; End.
        |ProgramVariables Real x; End.
        |Problem y=1 -> [x:=y;]x>=0 End.
        |End.
        |""".stripMargin
    parse(input).head.model shouldBe "y()=1 -> [x:=y();]x>=0".asFormula
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

  it should "parse a list of model and tactic entries" in withTactics {
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

  it should "parse a list of mixed entries, lemmas, and theorems" in withTactics {
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

  it should "parse a list of mixed entries, lemmas, and theorems, whose names are again entry/lemma/theorem" in withTactics {
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

  it should "split blocks by whole word only (lemma used in tactic)" in withTactics {
    val input =
      """Lemma "Entry 1"
        | ProgramVariables Real x; Real y; End.
        | Problem x>y -> x>=y End.
        |End.
        |
        |Theorem "Entry 2"
        | ProgramVariables Real x; Real y; End.
        | Problem x>y -> x>=y End.
        | Tactic "Proof Entry 2" useLemma("Entry 1") End.
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
    entry2.tactics shouldBe ("Proof Entry 2", "useLemma(\"Entry 1\")", TactixLibrary.useLemmaX("Entry 1", None))::Nil
    entry2.info shouldBe empty
    entry2.fileContent shouldBe
      """Theorem "Entry 2"
        | ProgramVariables Real x; Real y; End.
        | Problem x>y -> x>=y End.
        | Tactic "Proof Entry 2" useLemma("Entry 1") End.
        |End.""".stripMargin
  }

  it should "parse meta information" in {
    val input =
      """Lemma "Entry 1"
        | Description "The description of entry 1".
        | Title "A short entry 1 title".
        | Link "https://web.keymaerax.org/show/entry1".
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
      "Link" -> "https://web.keymaerax.org/show/entry1")
    entry.fileContent shouldBe
      """Lemma "Entry 1"
        | Description "The description of entry 1".
        | Title "A short entry 1 title".
        | Link "https://web.keymaerax.org/show/entry1".
        | ProgramVariables Real x; Real y; End.
        | Problem x>y -> y<x End.
        |End.""".stripMargin
  }

  it should "parse meta information at beginning or end" in {
    val input =
      """Lemma "Entry 1"
        | Description "The description of entry 1".
        | Link "https://web.keymaerax.org/show/entry1".
        | ProgramVariables Real x; Real y; End.
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
      "Link" -> "https://web.keymaerax.org/show/entry1",
      "Illustration" -> "https://lfcps.org/example.png"
    )
    entry.fileContent shouldBe
      """Lemma "Entry 1"
        | Description "The description of entry 1".
        | Link "https://web.keymaerax.org/show/entry1".
        | ProgramVariables Real x; Real y; End.
        | Problem x>y -> y<x End.
        | Title "A short entry 1 title".
        | Illustration "https://lfcps.org/example.png".
        |End.""".stripMargin
  }

  "implicit definitions" should "parse implicit ODE function definition" in {
    val (sin1, cos1) = {
      val fns = ODEToInterpreted.fromProgram(
        Parser.parser.programParser("{{sin1:=0;cos1:=1;t:=0;}; {t'=1, sin1'=cos1, cos1'=-sin1}}"), "t".asVariable)
      (fns(0), fns(1))
    }

    val tanh = {
      val fns = ODEToInterpreted.fromProgram(
        Parser.parser.programParser("{{tanh:=0; x:=0;}; {tanh'=1-tanh^2,x'=1}}"), "x".asVariable)
      fns(0)
    }


    val input =
      """
        |ArchiveEntry "Entry 1"
        | Definitions
        |   implicit Real sin1(Real t), cos1(Real t) =
        |     {{sin1:=0; t:=0; cos1:=1;}; {t'=1, sin1'=cos1, cos1'=-sin1}};
        |   implicit Real tanh(Real x) =
        |     {{tanh:=0;}; {tanh'=1-tanh^2}};
        | End.
        | ProgramVariables Real y; End.
        | Problem (sin1(y))^2 + (cos1(y))^2 = 1 End.
        |End.
      """.stripMargin
    val entry = parse(input).loneElement
    entry.name shouldBe "Entry 1"
    entry.kind shouldBe "theorem"
    entry.defs should beDecl(
      Declaration(Map(
        Name("cos1", None) -> Signature(Some(Real), Real, Some(List((Name("t",None),Real))), Some(FuncOf(cos1, DotTerm())), UnknownLocation),
        Name("sin1", None) -> Signature(Some(Real), Real, Some(List((Name("t",None),Real))), Some(FuncOf(sin1, DotTerm())), UnknownLocation),
        Name("tanh", None) -> Signature(Some(Real), Real, Some(List((Name("x",None),Real))), Some(FuncOf(tanh, DotTerm())), UnknownLocation),
        Name("y", None) -> Signature(None, Real, None, None, UnknownLocation)
      )))
    entry.model shouldBe (
      Equal(
        Plus(
          Power(FuncOf(sin1, "y".asVariable), Number(2)),
          Power(FuncOf(cos1, "y".asVariable), Number(2))
        ),
        Number(1)
      ))
    entry.tactics shouldBe empty
    entry.info shouldBe empty
    entry.fileContent shouldBe input.trim()
  }

  it should "disallow redefinition of builtins" in {
    val input =
      """
        |ArchiveEntry "Entry"
        | Definitions
        |   implicit Real exp(Real t) =
        |     {{exp:=1;}; {exp'=exp}};
        | End.
        | ProgramVariables Real y; End.
        | Problem exp(y) > 0 End.
        |End.
      """.stripMargin
    the [ParseException] thrownBy parse(input) should have message
      """5:29 Error parsing implicitDef at 4:4
        |Found:    ";" at 5:29
        |Expected: Not redefining builtin symbols (exp redefined)
        |Hint: Try Not redefining builtin symbols (exp redefined)""".stripMargin
  }

  it should "allow explicit initial times" in {

    val exp1 = {
      val fns = ODEToInterpreted.fromProgram(
        Parser.parser.programParser("{{s:=-2;exp1:=1;}; {s'=1,exp1'=exp1}}"), "s".asVariable)
      fns(0)
    }

    val input =
      """
        |ArchiveEntry "Entry"
        | Definitions
        |   implicit Real exp1(Real s) =
        |     {{s:=-2;exp1:=1;}; {s'=1,exp1'=exp1}};
        | End.
        | ProgramVariables Real y; End.
        | Problem exp1(y) > 0 End.
        |End.
      """.stripMargin

    val entry = parse(input).loneElement
    println(entry.defs)
    entry.defs should beDecl(
      Declaration(Map(
        Name("exp1",None) ->
          Signature(Some(Real),Real,Some(List((Name("s",None),Real))), Some("exp1<< <{exp1:=._0;s:=._1;}{{exp1'=-exp1,s'=-(1)}++{exp1'=exp1,s'=1}}>(exp1=1&s=-(2)) >>(.)".asTerm), UnknownLocation),
        Name("y", None) -> Signature(None, Real, None, None, UnknownLocation)
      )))
  }

  it should "parse in order" in {

    val input =
      """
        |ArchiveEntry "Entry"
        | Definitions
        |   implicit Real exp1(Real s) =
        |     {{s:=0;exp1:=exp(1);}; {s'=1,exp1'=exp1}};
        |   Real foo = 5;
        |   implicit Real exp2(Real s) =
        |     {{s:=exp1(foo);exp2:=0;}; {s'=1,exp2'=exp1(s)+exp2}};
        |
        | End.
        | ProgramVariables Real y; End.
        | Problem exp2(y) > 0 End.
        |End.
      """.stripMargin

    val entry = parse(input).loneElement
    println(entry.defs)
    entry.defs should beDecl(
      Declaration(Map(
        Name("exp1",None) -> Signature(Some(Real),Real,Some(List((Name("s",None),Real))),Some("exp1<< <{exp1:=._0;s:=._1;}{{exp1'=-exp1,s'=-(1)}++{exp1'=exp1,s'=1}}>(exp1=exp<< <{exp:=._0;t:=._1;}{{exp'=-exp,t'=-(1)}++{exp'=exp,t'=1}}>(exp=1&t=0) >>(1)&s=0) >>(.)".asTerm), UnknownLocation),
        Name("foo",None) -> Signature(Some(Unit),Real,Some(List()),Some(Number(5)), UnknownLocation),
        Name("exp2",None) -> Signature(Some(Real),Real,Some(List((Name("s",None),Real))),Some("exp2<< <{exp2:=._0;s:=._1;}{{exp2'=-(exp1<< <{exp1:=._0;s:=._1;}{{exp1'=-exp1,s'=-(1)}++{exp1'=exp1,s'=1}}>(exp1=exp<< <{exp:=._0;t:=._1;}{{exp'=-exp,t'=-(1)}++{exp'=exp,t'=1}}>(exp=1&t=0) >>(1)&s=0) >>(s)+exp2),s'=-(1)}++{exp2'=exp1<< <{exp1:=._0;s:=._1;}{{exp1'=-exp1,s'=-(1)}++{exp1'=exp1,s'=1}}>(exp1=exp<< <{exp:=._0;t:=._1;}{{exp'=-exp,t'=-(1)}++{exp'=exp,t'=1}}>(exp=1&t=0) >>(1)&s=0) >>(s)+exp2,s'=1}}>(exp2=0&s=exp1<< <{exp1:=._0;s:=._1;}{{exp1'=-exp1,s'=-(1)}++{exp1'=exp1,s'=1}}>(exp1=exp<< <{exp:=._0;t:=._1;}{{exp'=-exp,t'=-(1)}++{exp'=exp,t'=1}}>(exp=1&t=0) >>(1)&s=0) >>(5)) >>(.)".asTerm), UnknownLocation),
        Name("y",None) -> Signature(None,Real,None,None, UnknownLocation)))
    )
  }

  it should "parse expanded" in {

    val input =
      """
        |ArchiveEntry "Entry"
        | Definitions
        |   implicit Real exp1(Real s) =
        |     {{s:=0;exp1:=1;}; {s'=1,exp1'=exp1}};
        | End.
        | ProgramVariables Real y; End.
        | Problem exp1(y) > 0 End.
        |End.
      """.stripMargin

    val entry = parse(input).loneElement

    entry.model shouldBe "exp1<< <{exp1:=._0;s:=._1;}{{exp1'=-exp1,s'=-(1)}++{exp1'=exp1,s'=1}}>(exp1=1&s=0) >>(y)>0".asFormula
  }

  it should "fail to parse implicit function multi-variate definitions" in {
    val input =
      """
        |ArchiveEntry "Entry 1"
        | Definitions
        |   implicit Real saddle(Real x, Real y) = {saddle:=0;x:=0;y:=0;}{x'=1,y'=1,saddle=2x-2y};
        | End.
        | ProgramVariables Real x; End.
        | Problem saddle(0,0) = 0 -> saddle(x,0) = x*x End.
        |End.
      """.stripMargin
    assertThrows[ParseException](parse(input))
  }

  "Examples" should "parse example archive LFCPS 05: Short Bouncing Ball" in {
    val parsed = ArchiveParser.parser.parse(
      raw"""
         |ArchiveEntry "05: Short Bouncing Ball: single hop"
         |Description "5.4: A Proof of a Short Bouncing Ball single-hop without loop".
         |
         |Definitions      /* function symbols cannot change their value */
         |  Real H;        /* initial height */
         |  Real g;        /* gravity */
         |  Real c;        /* damping coefficient */
         |End.
         |
         |ProgramVariables /* program variables may change their value over time */
         |  Real x, v;     /* height and velocity */
         |End.
         |
         |Problem
         |  x>=0 & x=H
         |  & v=0 & g>0 & 1>=c&c>=0
         | ->
         |  [
         |      {x'=v,v'=-g}
         |      {?x=0; v:=-c*v;  ++  ?x>=0;}
         |  ] (x>=0 & x<=H)
         |End.
         |
         |Tactic "05: Short Bouncing Ball: single hop: Proof named"
         |    implyR('R=="x>=0&x=H()&v=0&g()>0&1>=c()&c()>=0->[{x'=v,v'=-g()}{?x=0;v:=-c()*v;++?x>=0;}](x>=0&x<=H())");
         |    composeb('R=="[{x'=v,v'=-g()}{?x=0;v:=-c()*v;++?x>=0;}](x>=0&x<=H())");
         |    choiceb('R=="[{x'=v,v'=-g()}]#[?x=0;v:=-c()*v;++?x>=0;](x>=0&x<=H())#");
         |    composeb('R=="[{x'=v,v'=-g()}](#[?x=0;v:=-c()*v;](x>=0&x<=H())#&[?x>=0;](x>=0&x<=H()))");
         |    testb('R=="[{x'=v,v'=-g()}](#[?x=0;][v:=-c()*v;](x>=0&x<=H())#&[?x>=0;](x>=0&x<=H()))");
         |    testb('R=="[{x'=v,v'=-g()}]((x=0->[v:=-c()*v;](x>=0&x<=H()))&#[?x>=0;](x>=0&x<=H())#)");
         |    assignb('R=="[{x'=v,v'=-g()}]((x=0->#[v:=-c()*v;](x>=0&x<=H())#)&(x>=0->x>=0&x<=H()))");
         |    solve('R=="[{x'=v,v'=-g()}]((x=0->x>=0&x<=H())&(x>=0->x>=0&x<=H()))");
         |    QE
         |End.
         |
         |Tactic "05: Short Bouncing Ball: single hop: Proof positionally"
         |  implyR(1) ; composeb(1) ; choiceb(1.1) ; composeb(1.1.0) ; testb(1.1.0) ; testb(1.1.1) ; assignb(1.1.0.1) ; solve(1) ; QE
         |End.
         |
         |Tactic "05: Short Bouncing Ball: single hop: Proof auto"
         |  auto
         |End.
         |
         |Illustration "https://lfcps.org/info/fig-bouncing-ball-dark1ghost.png".
         |End.
      """.stripMargin
    ).loneElement
    //TODO: shouldBes
    parsed.name shouldBe ("05: Short Bouncing Ball: single hop")
  }

  it should "parse example archive LFCPS 07: Bouncing Ball" in {
    val parsed = ArchiveParser.parser.parse(
      raw"""ArchiveEntry "07: Bouncing Ball"
         |Description "7.4: Acrophobic Bouncing Ball".
         |
         |Definitions      /* function symbols cannot change their value */
         |  Real H;        /* initial height */
         |  Real g;        /* gravity */
         |  Real c;        /* damping coefficient */
         |End.
         |
         |ProgramVariables /* program variables may change their value over time */
         |  Real x, v;     /* height and vertical velocity */
         |End.
         |
         |Problem
         |  (x>=0 & x=H & v=0) &
         |  (g>0 & 1=c&c>=0)
         | ->
         |  [
         |    {
         |      {x'=v,v'=-g&x>=0}
         |      {?x=0; v:=-c*v;  ++  ?x!=0;}
         |    }* @invariant(2*g*x=2*g*H-v^2 & x>=0)
         |  ] (x>=0 & x<=H)
         |End.
         |
         |Tactic "07: Bouncing Ball: generalizing as in book: positional"
         |  implyR(1) ; loop("2*g*x=2*g*H-v^2&x>=0", 1) ; <(
         |  "Init": QE,
         |  "Post": QE,
         |  "Step": composeb(1) ; MR("2*g*x=2*g*H-v^2&x>=0&c=1&g>0", 1) ; <(
         |    "Use Q->P": solve(1) ; QE,
         |    "Show [a]Q": choiceb(1) ; andR(1) ; <(
         |      composeb(1) ; testb(1) ; implyR(1) ; assignb(1) ; QE,
         |        testb(1) ; prop
         |      )
         |    )
         |)
         |End.
         |
         |Tactic "07: Bouncing Ball: generalizing as in book: named"
         |  implyR('R=="(x>=0&x=H()&v=0)&g()>0&1=c()&c()>=0->[{{x'=v,v'=-g()&x>=0}{?x=0;v:=-c()*v;++?x!=0;}}*](x>=0&x<=H())");
         |  loop("2*g()*x=2*g()*H()-v^2&x>=0", 'R=="[{{x'=v,v'=-g()&x>=0}{?x=0;v:=-c()*v;++?x!=0;}}*](x>=0&x<=H())"); <(
         |    "Init":
         |      QE,
         |    "Post":
         |      QE,
         |    "Step":
         |      composeb('R=="[{x'=v,v'=-g()&x>=0}{?x=0;v:=-c()*v;++?x!=0;}](2*g()*x=2*g()*H()-v^2&x>=0)");
         |      MR("2*g()*x=2*g()*H()-v^2&x>=0&c()=1&g()>0", 'R=="[{x'=v,v'=-g()&x>=0}][?x=0;v:=-c()*v;++?x!=0;](2*g()*x=2*g()*H()-v^2&x>=0)"); <(
         |        "Use Q->P":
         |          solve('R=="[{x'=v,v'=-g()&x>=0}](2*g()*x=2*g()*H()-v^2&x>=0&c()=1&g()>0)");
         |          QE,
         |        "Show [a]Q":
         |          choiceb('R=="[?x=0;v:=-c()*v;++?x!=0;](2*g()*x=2*g()*H()-v^2&x>=0)");
         |          andR('R=="[?x=0;v:=-c()*v;](2*g()*x=2*g()*H()-v^2&x>=0)&[?x!=0;](2*g()*x=2*g()*H()-v^2&x>=0)"); <(
         |            "[?x=0;v:=-c()*v;](2*g()*x=2*g()*H()-v^2&x>=0)":
         |              composeb('R=="[?x=0;v:=-c()*v;](2*g()*x=2*g()*H()-v^2&x>=0)");
         |              testb('R=="[?x=0;][v:=-c()*v;](2*g()*x=2*g()*H()-v^2&x>=0)");
         |              implyR('R=="x=0->[v:=-c()*v;](2*g()*x=2*g()*H()-v^2&x>=0)");
         |              assignb('R=="[v:=-c()*v;](2*g()*x=2*g()*H()-v^2&x>=0)");
         |              QE,
         |            "[?x!=0;](2*g()*x=2*g()*H()-v^2&x>=0)":
         |              testb('R=="[?x!=0;](2*g()*x=2*g()*H()-v^2&x>=0)");
         |              propClose
         |          )
         |      )
         |  )
         |End.
         |
         |Tactic "07: Bouncing Ball: top-level: positional"
         |  implyR(1) ; loop("2*g*x=2*g*H-v^2&x>=0", 1) ; <(
         |  "Init": QE,
         |  "Post": QE,
         |  "Step": composeb(1) ; solve(1) ; allR(1) ; implyR(1) ; implyR(1) ; allL("t_", -6) ; allR(1) ; implyR(1) ; choiceb(1) ; andR(1) ; <(
         |    composeb(1) ; testb(1) ; implyR(1) ; assignb(1) ; QE,
         |    testb(1) ; implyR(1) ; QE
         |)
         |)
         |End.
         |
         |Tactic "07: Bouncing Ball: top-level: named"
         |implyR('R=="(x>=0&x=H()&v=0)&g()>0&1=c()&c()>=0->[{{x'=v,v'=-g()&x>=0}{?x=0;v:=-c()*v;++?x!=0;}}*](x>=0&x<=H())");
         |loop("2*g()*x=2*g()*H()-v^2&x>=0", 'R=="[{{x'=v,v'=-g()&x>=0}{?x=0;v:=-c()*v;++?x!=0;}}*](x>=0&x<=H())"); <(
         |  "Init":
         |    QE,
         |  "Post":
         |    QE,
         |  "Step":
         |    composeb('R=="[{x'=v,v'=-g()&x>=0}{?x=0;v:=-c()*v;++?x!=0;}](2*g()*x=2*g()*H()-v^2&x>=0)");
         |    solve('R=="[{x'=v,v'=-g()&x>=0}][?x=0;v:=-c()*v;++?x!=0;](2*g()*x=2*g()*H()-v^2&x>=0)");
         |    allR('R=="\forall t_ (t_>=0->\forall s_ (0<=s_&s_<=t_->(-g())*(s_^2/2)+v_1*s_+x>=0)->\forall v (v=(-g())*t_+v_1->[?(-g())*((0+1*t_-0)^2/2)+v_1*(0+1*t_-0)+x=0;v:=-c()*v;++?(-g())*((0+1*t_-0)^2/2)+v_1*(0+1*t_-0)+x!=0;](2*g()*((-g())*(t_^2/2)+v_1*t_+x)=2*g()*H()-v^2&(-g())*(t_^2/2)+v_1*t_+x>=0)))");
         |    implyR('R=="t_>=0->\forall s_ (0<=s_&s_<=t_->(-g())*(s_^2/2)+v_1*s_+x>=0)->\forall v (v=(-g())*t_+v_1->[?(-g())*((0+1*t_-0)^2/2)+v_1*(0+1*t_-0)+x=0;v:=-c()*v;++?(-g())*((0+1*t_-0)^2/2)+v_1*(0+1*t_-0)+x!=0;](2*g()*((-g())*(t_^2/2)+v_1*t_+x)=2*g()*H()-v^2&(-g())*(t_^2/2)+v_1*t_+x>=0))");
         |    implyR('R=="\forall s_ (0<=s_&s_<=t_->(-g())*(s_^2/2)+v_1*s_+x>=0)->\forall v (v=(-g())*t_+v_1->[?(-g())*((0+1*t_-0)^2/2)+v_1*(0+1*t_-0)+x=0;v:=-c()*v;++?(-g())*((0+1*t_-0)^2/2)+v_1*(0+1*t_-0)+x!=0;](2*g()*((-g())*(t_^2/2)+v_1*t_+x)=2*g()*H()-v^2&(-g())*(t_^2/2)+v_1*t_+x>=0))");
         |    allL("t_", 'L=="\forall s_ (0<=s_&s_<=t_->(-g())*(s_^2/2)+v_1*s_+x>=0)");
         |    allR('R=="\forall v (v=(-g())*t_+v_1->[?(-g())*((0+1*t_-0)^2/2)+v_1*(0+1*t_-0)+x=0;v:=-c()*v;++?(-g())*((0+1*t_-0)^2/2)+v_1*(0+1*t_-0)+x!=0;](2*g()*((-g())*(t_^2/2)+v_1*t_+x)=2*g()*H()-v^2&(-g())*(t_^2/2)+v_1*t_+x>=0))");
         |    implyR('R=="v=(-g())*t_+v_1->[?(-g())*((0+1*t_-0)^2/2)+v_1*(0+1*t_-0)+x=0;v:=-c()*v;++?(-g())*((0+1*t_-0)^2/2)+v_1*(0+1*t_-0)+x!=0;](2*g()*((-g())*(t_^2/2)+v_1*t_+x)=2*g()*H()-v^2&(-g())*(t_^2/2)+v_1*t_+x>=0)");
         |    choiceb('R=="[?(-g())*((0+1*t_-0)^2/2)+v_1*(0+1*t_-0)+x=0;v:=-c()*v;++?(-g())*((0+1*t_-0)^2/2)+v_1*(0+1*t_-0)+x!=0;](2*g()*((-g())*(t_^2/2)+v_1*t_+x)=2*g()*H()-v^2&(-g())*(t_^2/2)+v_1*t_+x>=0)");
         |    andR('R=="[?(-g())*((0+1*t_-0)^2/2)+v_1*(0+1*t_-0)+x=0;v:=-c()*v;](2*g()*((-g())*(t_^2/2)+v_1*t_+x)=2*g()*H()-v^2&(-g())*(t_^2/2)+v_1*t_+x>=0)&[?(-g())*((0+1*t_-0)^2/2)+v_1*(0+1*t_-0)+x!=0;](2*g()*((-g())*(t_^2/2)+v_1*t_+x)=2*g()*H()-v^2&(-g())*(t_^2/2)+v_1*t_+x>=0)"); <(
         |      "[?(-g())*((0+1*t_-0)^2/2)+v_1*(0+1*t_-0)+x=0;v:=-c()*v;](2*g()*((-g())*(t_^2/2)+v_1*t_+x)=2*g()*H()-v^2&(-g())*(t_^2/2)+v_1*t_+x>=0)":
         |        composeb('R=="[?(-g())*((0+1*t_-0)^2/2)+v_1*(0+1*t_-0)+x=0;v:=-c()*v;](2*g()*((-g())*(t_^2/2)+v_1*t_+x)=2*g()*H()-v^2&(-g())*(t_^2/2)+v_1*t_+x>=0)");
         |        testb('R=="[?(-g())*((0+1*t_-0)^2/2)+v_1*(0+1*t_-0)+x=0;][v:=-c()*v;](2*g()*((-g())*(t_^2/2)+v_1*t_+x)=2*g()*H()-v^2&(-g())*(t_^2/2)+v_1*t_+x>=0)");
         |        implyR('R=="(-g())*((0+1*t_-0)^2/2)+v_1*(0+1*t_-0)+x=0->[v:=-c()*v;](2*g()*((-g())*(t_^2/2)+v_1*t_+x)=2*g()*H()-v^2&(-g())*(t_^2/2)+v_1*t_+x>=0)");
         |        assignb('R=="[v:=-c()*v;](2*g()*((-g())*(t_^2/2)+v_1*t_+x)=2*g()*H()-v^2&(-g())*(t_^2/2)+v_1*t_+x>=0)");
         |        QE,
         |      "[?(-g())*((0+1*t_-0)^2/2)+v_1*(0+1*t_-0)+x!=0;](2*g()*((-g())*(t_^2/2)+v_1*t_+x)=2*g()*H()-v^2&(-g())*(t_^2/2)+v_1*t_+x>=0)":
         |        testb('R=="[?(-g())*((0+1*t_-0)^2/2)+v_1*(0+1*t_-0)+x!=0;](2*g()*((-g())*(t_^2/2)+v_1*t_+x)=2*g()*H()-v^2&(-g())*(t_^2/2)+v_1*t_+x>=0)");
         |        implyR('R=="(-g())*((0+1*t_-0)^2/2)+v_1*(0+1*t_-0)+x!=0->2*g()*((-g())*(t_^2/2)+v_1*t_+x)=2*g()*H()-v^2&(-g())*(t_^2/2)+v_1*t_+x>=0");
         |        QE
         |    )
         |)End.
         |
         |Tactic "07: Bouncing Ball: in-place proof: positional"
         |  implyR(1) ; loop("2*g*x=2*g*H-v^2&x>=0", 1) ; <(
         |    "Init": QE,
         |    "Post": QE,
         |    "Step": composeb(1) ; choiceb(1.1) ; composeb(1.1.0) ; testb(1.1.0) ; assignb(1.1.0.1) ; testb(1.1.1) ; solve(1) ; QE
         |)
         |End.
         |
         |Tactic "07: Bouncing Ball: in-place proof: named"
         |  implyR('R=="(x>=0&x=H()&v=0)&g()>0&1=c()&c()>=0->[{{x'=v,v'=-g()&x>=0}{?x=0;v:=-c()*v;++?x!=0;}}*](x>=0&x<=H())");
         |  loop("2*g()*x=2*g()*H()-v^2&x>=0", 'R=="[{{x'=v,v'=-g()&x>=0}{?x=0;v:=-c()*v;++?x!=0;}}*](x>=0&x<=H())"); <(
         |    "Init":
         |      QE,
         |    "Post":
         |      QE,
         |    "Step":
         |      composeb('R=="[{x'=v,v'=-g()&x>=0}{?x=0;v:=-c()*v;++?x!=0;}](2*g()*x=2*g()*H()-v^2&x>=0)");
         |      choiceb('R=="[{x'=v,v'=-g()&x>=0}]#[?x=0;v:=-c()*v;++?x!=0;](2*g()*x=2*g()*H()-v^2&x>=0)#");
         |      composeb('R=="[{x'=v,v'=-g()&x>=0}](#[?x=0;v:=-c()*v;](2*g()*x=2*g()*H()-v^2&x>=0)#&[?x!=0;](2*g()*x=2*g()*H()-v^2&x>=0))");
         |      testb('R=="[{x'=v,v'=-g()&x>=0}](#[?x=0;][v:=-c()*v;](2*g()*x=2*g()*H()-v^2&x>=0)#&[?x!=0;](2*g()*x=2*g()*H()-v^2&x>=0))");
         |      assignb('R=="[{x'=v,v'=-g()&x>=0}]((x=0->#[v:=-c()*v;](2*g()*x=2*g()*H()-v^2&x>=0)#)&[?x!=0;](2*g()*x=2*g()*H()-v^2&x>=0))");
         |      testb('R=="[{x'=v,v'=-g()&x>=0}]((x=0->2*g()*x=2*g()*H()-(-c()*v)^2&x>=0)&#[?x!=0;](2*g()*x=2*g()*H()-v^2&x>=0)#)");
         |      solve('R=="[{x'=v,v'=-g()&x>=0}]((x=0->2*g()*x=2*g()*H()-(-c()*v)^2&x>=0)&(x!=0->2*g()*x=2*g()*H()-v^2&x>=0))");
         |      QE
         |  )
         |End.
         |
         |Tactic "07: Bouncing Ball: automatic"
         |  auto
         |End.
         |
         |Illustration "https://lfcps.org/info/fig-bouncing-ball-dark-trace.png".
         |End.""".stripMargin
    ).loneElement
    //TODO: shouldBes
  }

  it should "parse iteratedexp.kyx from implicit functions paper" in {
    val parsed = ArchiveParser.parser.parse(
      raw"""Theorem "double iterated exponential"
         |
         |Definitions
         |  implicit Real exp1(Real t) = {{exp1:=1;}; {exp1'=exp1}};
         |  Real E = exp1(1);
         |  implicit Real exp2(Real t) = {{exp2:=E;t:=0;}; {exp2'=exp1(t)*exp2,t'=1}};
         |  Real x;
         |End.
         |
         |Problem
         |  exp2(x) = exp(exp(x))
         |End.
         |
         |Tactic "double iterated exponential: Proof"
         |cut("exp(exp(x()))=exp1(exp1(x()))"); <(
         |  "Use":
         |    allL2R('L=="exp(exp(x()))=exp1(exp1(x()))");
         |    hideL('L=="exp(exp(x()))=exp1(exp1(x()))");
         |    expand("exp2");
         |    expand("exp1");
         |    diffUnfold("x()", "0", 'R=="exp2(x())=exp1(exp1(x()))"); <(
         |      "Init":
         |        QE,
         |      "[{v'=1&v<=x()}]exp2(v)=exp1(exp1(v))":
         |        ODE('R=="[{v'=1&v<=x()}]exp2(v)=exp1(exp1(v))"),
         |      "[{v'=(-1)&x()<=v}]exp2(v)=exp1(exp1(v))":
         |        ODE('R=="[{v'=(-1)&x()<=v}]exp2(v)=exp1(exp1(v))")
         |    ),
         |  "Show":
         |    hideR('R=="exp2(x())=exp(exp(x()))");
         |    expand("exp1");
         |    cut("\forall y exp(y)=exp1(y)"); <(
         |      "Use":
         |        allLkeep("x()", 'L=="\forall y exp(y)=exp1(y)");
         |        allL2R('L=="exp(x())=exp1(x())");
         |        hideL('L=="exp(x())=exp1(x())");
         |        allL("exp1(x())", 'L=="\forall y exp(y)=exp1(y)");
         |        expand("exp1");
         |        propClose,
         |      "Show":
         |        hideR('R=="exp(exp(x()))=exp1(exp1(x()))");
         |        allR('R=="\forall y exp(y)=exp1(y)");
         |        expand("exp1");
         |        diffUnfold("y", "0", 'R=="exp(y)=exp1(y)"); <(
         |          "Init":
         |            QE,
         |          "[{v'=1&v<=y}]exp(v)=exp1(v)":
         |            ODE('R=="[{v'=1&v<=y}]exp(v)=exp1(v)"),
         |          "[{v'=(-1)&y<=v}]exp(v)=exp1(v)":
         |            ODE('R=="[{v'=(-1)&y<=v}]exp(v)=exp1(v)")
         |        )
         |    )
         |)
         |End.
         |
         |End.""".stripMargin
    ).loneElement
    //TODO: shouldBe
  }

  it should "parse FIDE21/01 exponential decay" in {
    val parsed = ArchiveParser.parser.parse(
      raw"""Lemma "FIDE21/01-Exponential decay"
           |  ProgramVariables
           |    Real x;
           |  End.
           |
           |  Problem
           |    x>=0 -> [{x'=-x}]x>=0
           |  End.
           |
           |  Tactic "Interactive proof"
           |    implyR('R=="x>=0->[{x'=-x}]x>=0");
           |    ODE('R=="[{x'=-x}]x>=0");
           |    done
           |  End.
           |
           |  Tactic "Automated proof"
           |    autoClose
           |  End.
           |
           |End.
           |
           |
           |Lemma "FIDE21/02-Unsatisfied control guard"
           |  Definitions     /* constants, functions, properties, programs */
           |    Bool S(Real x);
           |    Bool P(Real x);
           |  End.
           |
           |  ProgramVariables                     /* variables */
           |    Real x;
           |  End.
           |
           |  Problem                              /* specification in dL */
           |    S(x) -> [?!S(x);]P(x)
           |  End.
           |
           |  Tactic "Interactive proof"
           |    implyR('R=="S(x)->[?!S(x);]P(x)");
           |    testb('R=="[?!S(x);]P(x)");
           |    implyR('R=="!S(x)->P(x)");
           |    notL('L=="!S(x)");
           |    id using "S(x)";
           |    done
           |  End.
           |
           |  Tactic "Automated proof"
           |    autoClose
           |  End.
           |
           |End.
           |
           |Lemma "FIDE21/03-Induction step"
           |
           |  Definitions
           |    Bool S(Real x) <-> x>=0;
           |    HP ctrl ::= { if (S(x)) { x:=2*x; } };
           |    HP ode ::= { {x'=-x} };
           |  End.
           |
           |  ProgramVariables
           |    Real x;
           |  End.
           |
           |  Problem
           |    S(x) -> [ctrl;ode;]S(x)
           |  End.
           |
           |  Tactic "Interactive proof"
           |  implyR('R=="S(x)->[ctrl{|^@|};ode{|^@|};]S(x)");
           |  composeb('R=="[ctrl{|^@|};ode{|^@|};]S(x)");
           |  expand("ctrl");
           |  choiceb('R=="[?S(x);x:=2*x;++?!S(x);?true;][ode{|^@|};]S(x)");
           |  andR('R=="[?S(x);x:=2*x;][ode{|^@|};]S(x)&[?!S(x);?true;][ode{|^@|};]S(x)"); <(
           |    "[?S(x);x:=2*x;][ode{|^@|};]S(x)":
           |      MR("S(x)", 'R=="[?S(x);x:=2*x;][ode{|^@|};]S(x)"); <(
           |        "Use Q->P":
           |          expand("S");
           |          autoClose,
           |        "Show [a]Q":
           |          useLemma("FIDE21/01-Exponential decay", "US({`S(x)~>x>=0::ode{|^@|};~>{x'=-x}::nil`});unfold;id")
           |      ),
           |    "[?!S(x);?true;][ode{|^@|};]S(x)":
           |      composeb('R=="[?!S(x);?true;][ode{|^@|};]S(x)");
           |      useLemma("FIDE21/02-Unsatisfied control guard", "US({`P(x)~>[x:=x;][?true;][{x'=-x}]S(x)::nil`});unfold;id")
           |  )
           |  End.
           |
           |End.
           |
           |Theorem "FIDE21/04-Combine lemmas"
           |
           |  Definitions
           |    Bool A(Real x) <-> x=2;
           |    Bool S(Real x) <-> x>=0;
           |    HP ctrl ::= { if (x>=0) { x:=2*x; } };
           |    HP ode ::= { {x'=-x} };
           |  End.
           |
           |  ProgramVariables
           |    Real x;
           |  End.
           |
           |  Problem
           |    A(x) -> [{ctrl;ode;}*]S(x)
           |  End.
           |
           |  Tactic "Interactive proof"
           |  implyR('R=="A(x)->[{ctrl{|^@|};ode{|^@|};}*]S(x)");
           |  loop("S(x)", 'R=="[{ctrl{|^@|};ode{|^@|};}*]S(x)"); <(
           |    "Init":
           |      expandAllDefs();
           |      QE,
           |    "Post":
           |      id,
           |    "Step":
           |      expandAllDefs();
           |      useLemma("FIDE21/03-Induction step", "prop")
           |  )
           |  End.
           |
           |End.
           |
           |Theorem "FIDE21/05-Parametric loop induction"
           |
           |  Problem
           |    x=2 -> [{x:=1+(x-1)/2;}*]x>=-1
           |  End.
           |
           |  Tactic "Interactive proof"
           |    implyR('R=="x=2->[{x:=1+(x-1)/2;}*]x>=(-1)");
           |    loop("J(x)", 'R=="[{x:=1+(x-1)/2;}*]x>=(-1)"); <(
           |      "Init":
           |        US("(J(.) ~> .>=1)");
           |        QE,
           |      "Post":
           |        US("(J(.) ~> .>=1)");
           |        QE,
           |      "Step":
           |        assignb('R=="[x:=1+(x-1)/2;]J(x)");
           |        US("(J(.) ~> .>=1)");
           |        QE
           |    )
           |  End.
           |
           |End.
           |
           |Theorem "FIDE21/06-Delayed modeling"
           |
           |  Problem    /* Reserved constant symbols A_ are allowed to be specified during the proof */
           |    A__0() -> x>=0 -> [x:=x/y()^2;]x>=0
           |  End.
           |
           |  Tactic "Interactive proof"
           |    implyR('R=="A__0()->x>=0->[x:=x/y()^2;]x>=0");
           |    implyR('R=="x>=0->[x:=x/y()^2;]x>=0");
           |    assignb('R=="[x:=x/y()^2;]x>=0");
           |    US("(A__0() ~> y()!=0)");
           |    QE
           |  End.
           |
           |End.
           |
           |Theorem "FIDE21/07-Temporary hiding"
           |
           |  Problem
           |    (x<0 | x=0) & (y=x | y>0) -> x*y<=y^2
           |  End.
           |
           |  Tactic "Interactive proof"
           |    implyR('R=="(x < 0|x=0)&(y=x|y>0)->x*y<=y^2");
           |    andL('L=="(x < 0|x=0)&(y=x|y>0)");
           |    (orL('L)*; <(
           |      QE,
           |      skip
           |    )) using "y=x|y>0 :: x*y<=y^2 :: nil";
           |    QE
           |  End.
           |
           |End.
           |""".stripMargin
    )
    // TODO: shouldBes
  }

  it should "correctly pass definitions to tactic parser" in withTactics {
    val tacticA =
      """/* tactic parser needs to elaborate to function symbol x() */
        |implyR('R=="x^2 >= 0");
        |cut("x>=x")
        |""".stripMargin
    val contentA = s"""
      |Theorem "A"
      |Definitions
      |  Real x();
      |End.
      |Problem
      |  x^2 >= 0
      |End.
      |Tactic "Proof A"
      |  $tacticA
      |End.
      |End.
      |""".stripMargin
    val contentB = """
      |Theorem "B"
      |ProgramVariables
      |  Real x;
      |End.
      |Problem
      |  x>=0 -> [{x'=x}]x>=0
      |End.
      |Tactic "Proof B"
      |  /* but here x is a variable */
      |  implyR('R=="x>=0 -> [{x'=x}]x>=0");
      |  dC("x>=old(x)", 'R=="[{x'=x}]x>=0")
      |End.
      |End.
      |""".stripMargin
    val a :: Nil = ArchiveParser(contentA)
    val ta = ArchiveParser.tacticParser(tacticA, a.defs) // changes the defs in DLBelleParser, subsequent ArchiveParser calls need to robustly reset it; @todo refactor DLBelleParser to stateless setup
    a.tactics.map(_._3) should contain theSameElementsInOrderAs List(ta)
    //@note if not robustly reset, will use contentA definition x() in tactic parser and as a consequence will get
    // assertion error in the next line because the parser cannot elaborate x in x' to x()
    val b :: Nil = ArchiveParser(contentB)
    b.tactics.map(_._3) should contain theSameElementsInOrderAs
      List("""implyR('R=="x>=0 -> [{x'=x}]x>=0"); dC("x>=old(x)", 'R=="[{x'=x}]x>=0")""".asTactic(b.defs)) // again changes defs here
  }

  it should "elaborate in tactic using ..." in withTactics {
    val input =
      """ArchiveEntry "Test"
        |Definitions Bool p(Real x); End.
        |Problem p(5) End.
        |Tactic "Proof" QE using "p(5) :: nil" End.
        |End.
        |""".stripMargin
      ArchiveParser(input).head.tactics.head._3 shouldBe Using(List(PredOf(edu.cmu.cs.ls.keymaerax.core.Function("p", None, Real, Bool), Number(5))), QE)
  }

  it should "reset tactic definitions at the start of each tactic" in withTactics {
    val input =
      """ArchiveEntry "Test"
        |ProgramVariables Real x,y; End.
        |Problem x^2>=0 & y^2>=0 End.
        |Tactic "Proof A" tactic myQE as (QE); myQE End.
        |Tactic "Proof B" tactic myQE as (prop; doall(QE)); myQE End.
        |End.
        |""".stripMargin
    ArchiveParser(input).head.tactics.map(_._3) should contain theSameElementsAs List(
      DefTactic("myQE", QE) & ApplyDefTactic(DefTactic("myQE", QE)),
      DefTactic("myQE", prop & OnAll(QE)) & ApplyDefTactic(DefTactic("myQE", prop & OnAll(QE)))
    )
  }

}
