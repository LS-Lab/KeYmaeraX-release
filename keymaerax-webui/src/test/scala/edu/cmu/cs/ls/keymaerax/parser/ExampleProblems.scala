/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tools.KeYmaeraXTool
import edu.cmu.cs.ls.keymaerax.{Configuration, FileConfiguration}
import org.scalatest.OptionValues._
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import org.scalatest.{BeforeAndAfterAll, BeforeAndAfterEach}

import scala.collection.mutable.ListBuffer

/** @author Nathan Fulton */
class ExampleProblems extends AnyFlatSpec with Matchers with BeforeAndAfterEach with BeforeAndAfterAll {
  override def beforeAll(): Unit = {
    Configuration.setConfiguration(FileConfiguration)
    KeYmaeraXTool.init(interpreter = KeYmaeraXTool.InterpreterChoice.LazySequential, initDerivationInfoRegistry = false)
  }
  override def afterEach(): Unit = { Parser.parser.setAnnotationListener((_, _) => {}) }

  "parser line messages" should "be properly offset" in {
    val f = {
      """ArchiveEntry "Test"
        |ProgramVariables
        |   Real x, y, z;
        |End.
        |Problem
        |   (x*x*y >= 0 & x >= 0 & z >= x)
        |   ->
        |   [
        |   {x := 2x; y := 2y;}
        |   ](x*y >= 0)
        |End. End.""".stripMargin
    }

    val ex = the[ParseException] thrownBy ArchiveParser.parser(f)
    ex.found should (be("x") or be("\"x; y := 2y\""))
    ex.expect should
      (be("Multiplication in KeYmaera X requires an explicit * symbol. E.g. 2*term") or
        be("""([0-9] | "." | "^" | "*" | "/" | "+" | "-" | ";")"""))
    ex.loc.begin.line shouldBe 9
    ex.loc.begin.column shouldBe 11
  }

  it should "be properly offset in another example" in {
    val f = {
      """ ArchiveEntry "Test"
        | ProgramVariables
        |
        |   Real x, y, z;
        |
        |   End.
        |
        |   Problem
        |
        |   (x*x*y >= 0 & x >= 0 & z >= x)
        |
        |   ->
        |
        |   [
        |
        |   {x := 2x; y := 2y;}
        |
        |  ]
        |
        | (x*y >= 0)
        |
        |End. End.""".stripMargin
    }

    val ex = the[ParseException] thrownBy ArchiveParser.parseAsFormula(f)
    ex.found should (be("x") or be("\"x; y := 2y\""))
    ex.expect should
      (be("Multiplication in KeYmaera X requires an explicit * symbol. E.g. 2*term") or
        be("""([0-9] | "." | "^" | "*" | "/" | "+" | "-" | ";")"""))
    ex.loc.begin.line shouldBe 16
    ex.loc.begin.column shouldBe 11
  }

  it should "work from file input" in {
    val f = {
      """ArchiveEntry "Test"
        |ProgramVariables
        |   Real x, y, z;
        |End.
        |
        |Problem
        |   (x*x*y >= 0 & x >= 0 & z >= x)
        |   ->
        |   [
        |   {x := 2x; y := 2y;}
        |   ](x*y >= 0)
        |End.
        |End.
        |""".stripMargin
    }

    val ex = the[ParseException] thrownBy ArchiveParser.parseAsFormula(f)
    ex.found should (be("x") or be("\"x; y := 2y\""))
    ex.expect should
      (be("Multiplication in KeYmaera X requires an explicit * symbol. E.g. 2*term") or
        be("""([0-9] | "." | "^" | "*" | "/" | "+" | "-" | ";")"""))
    ex.loc.begin.line shouldBe 10
    ex.loc.begin.column shouldBe 11
  }

  "The Parser" should "parse a simple file" in {
    val theProblem = {
      """
        |ArchiveEntry "Test"
        |Definitions
        |  Real f(Real x, Real y);
        |  Real g(Real x);
        |End.
        |ProgramVariables
        |  Real x;
        |  Real y;
        |End.
        |Problem
        |  x > 0 ->
        |  [
        |   x := x + 1;
        |  ] x > 0
        |End.
        |End.
        |""".stripMargin
    }

    val result = ArchiveParser.parser(theProblem)
    result should have size 1
    result.head.model shouldBe "x > 0 -> [x := x + 1;] x > 0".asFormula
  }

  it should "parse x>0 -> \\exists d [{x'=d}]x>0" in {
    val problem = "x>0 -> \\exists d [{x'=d}]x>0"
    val declProblem = {
      s"""
         |ArchiveEntry "Test"
         |ProgramVariables
         |  Real x;
         |End.
         |
         |Problem
         |  $problem
         |End.
         |End.
         |""".stripMargin
    }

    ArchiveParser.parser(declProblem).head.model shouldBe Parser(problem)
  }

  "Interpretation parser" should "parse simple function declarations" in {
    val problem = {
      """
        |ArchiveEntry "Test"
        |Definitions
        |  Real f() = 5;
        |End.
        |
        |Problem
        |  f()>3
        |End.
        |End.
        |""".stripMargin
    }

    val entry = ArchiveParser.parseProblem(problem)
    entry.defs.decls should have size 1
    entry.defs.decls should contain key Name("f", None)
    entry.defs.decls(Name("f", None)) match {
      case Signature(domain, sort, argNames, Right(Some(interpretation)), _) =>
        domain.value shouldBe Unit
        sort shouldBe Real
        argNames shouldBe Some(Nil)
        interpretation shouldBe Number(5)
    }
    entry.model shouldBe Parser("f()>3")
  }

  it should "parse function declarations with one parameter" in {
    val problem = {
      """
        |ArchiveEntry "Test"
        |Definitions
        |  Real f(Real x) = 5 + x*x;
        |End.
        |
        |Problem
        |  f(4)>3
        |End.
        |End.
        |""".stripMargin
    }

    val entry = ArchiveParser.parseProblem(problem)
    entry.defs.decls should have size 1
    entry.defs.decls should contain key Name("f", None)
    entry.defs.decls(Name("f", None)) match {
      case Signature(domain, sort, argNames, Right(interpretation), _) =>
        domain.value shouldBe Real
        sort shouldBe Real
        argNames shouldBe Some((Name("x", None), Real) :: Nil)
        interpretation.value shouldBe Plus(Number(5), Times(Variable("x"), Variable("x")))
    }
    entry.model shouldBe Parser("f(4)>3")
  }

  it should "parse n-ary function declarations" in {
    val problem = {
      """
        |ArchiveEntry "Test"
        |Definitions
        |  Real f(Real x, Real y, Real z) = x + y*z;
        |End.
        |
        |Problem
        |  f(2,3,4)>3
        |End.
        |End.
        |""".stripMargin
    }

    val entry = ArchiveParser.parseProblem(problem)
    entry.defs.decls should have size 1
    entry.defs.decls should contain key Name("f", None)
    entry.defs.decls(Name("f", None)) match {
      case Signature(domain, sort, argNames, Right(interpretation), _) =>
        domain.value shouldBe Tuple(Real, Tuple(Real, Real))
        sort shouldBe Real
        argNames shouldBe Some((Name("x", None), Real) :: (Name("y", None), Real) :: (Name("z", None), Real) :: Nil)
        interpretation.value shouldBe Plus(Variable("x"), Times(Variable("y"), Variable("z")))
    }
    entry.model shouldBe Parser.parser("f(2,3,4)>3")
  }

  it should "detect undeclared arguments" in {
    val problem = {
      """
        |ArchiveEntry "Test"
        |Definitions
        |  Real f(Real x, Real y, Real z) = y + z*u;
        |End.
        |
        |Problem
        |  f(2,3,4)>3
        |End.
        |End.
        |""".stripMargin
    }

    val thrown = the[ParseException] thrownBy ArchiveParser.parseProblem(problem)
    thrown.getMessage should include("Definition f uses undefined symbol(s) u")
  }

  it should "replace names with the appropriate dots" in {
    val problem = {
      """ArchiveEntry "Test"
        |Definitions
        |  Real f(Real x, Real y, Real z) = x + y*z;
        |End.
        |
        |Problem
        |  f(2,3,4)>3
        |End.
        |End.
        |""".stripMargin
    }

    val entry = ArchiveParser.parseProblem(problem)
    entry.defs.decls should have size 1
    entry.defs.decls should contain key Name("f", None)
    entry.defs.decls(Name("f", None)) match {
      case Signature(domain, sort, argNames, Right(interpretation), _) =>
        domain.value shouldBe Tuple(Real, Tuple(Real, Real))
        sort shouldBe Real
        argNames shouldBe Some((Name("x", None), Real) :: (Name("y", None), Real) :: (Name("z", None), Real) :: Nil)
        interpretation.value shouldBe Plus(Variable("x"), Times(Variable("y"), Variable("z")))
    }
    entry.model shouldBe Parser.parser("f(2,3,4)>3")
  }

  it should "not confuse arguments of same name across definitions" in {
    val problem = {
      """ArchiveEntry "Test"
        |Definitions
        |  Real f(Real x, Real y, Real z) = x+y*z;
        |  Real g(Real a, Real x, Real y) = f(x,y,a);
        |End.
        |
        |Problem
        |  f(1,2,3)>0 -> g(3,1,2)>0
        |End.
        |End.
        |""".stripMargin
    }

    val entry = ArchiveParser.parseProblem(problem)
    entry.defs.decls should have size 2
    entry.defs.decls should contain key Name("f", None)
    entry.defs.decls(Name("f", None)) match {
      case Signature(domain, sort, argNames, Right(interpretation), _) =>
        domain.value shouldBe Tuple(Real, Tuple(Real, Real))
        sort shouldBe Real
        argNames shouldBe Some((Name("x", None), Real) :: (Name("y", None), Real) :: (Name("z", None), Real) :: Nil)
        interpretation.value shouldBe Plus(Variable("x"), Times(Variable("y"), Variable("z")))
    }
    entry.defs.decls should contain key Name("g", None)
    entry.defs.decls(Name("g", None)) match {
      case Signature(domain, sort, argNames, Right(interpretation), _) =>
        domain.value shouldBe Tuple(Real, Tuple(Real, Real))
        sort shouldBe Real
        argNames shouldBe Some((Name("a", None), Real) :: (Name("x", None), Real) :: (Name("y", None), Real) :: Nil)
        interpretation.value shouldBe FuncOf(
          Function("f", None, Tuple(Real, Tuple(Real, Real)), Real),
          Pair(Variable("x"), Pair(Variable("y"), Variable("a"))),
        )
    }
    entry.model shouldBe Parser("f(1,2,3)>0 -> g(3,1,2)>0")
  }

  it should "correctly dottify in the presence of unused arguments" in {
    val problem = {
      """ArchiveEntry "Test"
        |Definitions
        |  Real f(Real x, Real y) = y+3;
        |End.
        |
        |Problem
        |  f(1,2)>0
        |End.
        |End.
        |""".stripMargin
    }

    val entry = ArchiveParser.parseProblem(problem)
    entry.defs.decls should have size 1
    entry.defs.decls should contain key Name("f", None)
    entry.defs.decls(Name("f", None)) match {
      case Signature(domain, sort, argNames, Right(interpretation), _) =>
        domain.value shouldBe Tuple(Real, Real)
        sort shouldBe Real
        argNames shouldBe Some((Name("x", None), Real) :: (Name("y", None), Real) :: Nil)
        interpretation.value shouldBe Plus(Variable("y"), Number(3))
    }
    entry.model shouldBe Parser("f(1,2)>0")
  }

  it should "replace argument name of unary function with non-indexed dot (for backwards compatibility)" in {
    val problem = {
      """ArchiveEntry "Test"
        |Definitions
        |  Real f(Real x) = x + 2;
        |End.
        |
        |Problem
        |  f(2)>3
        |End.
        |End.
        |""".stripMargin
    }

    val entry = ArchiveParser.parseProblem(problem)
    entry.defs.decls should have size 1
    entry.defs.decls should contain key Name("f", None)
    entry.defs.decls(Name("f", None)) match {
      case Signature(domain, sort, argNames, Right(interpretation), _) =>
        domain.value shouldBe Real
        sort shouldBe Real
        argNames shouldBe Some((Name("x", None), Real) :: Nil)
        interpretation.value shouldBe Plus(Variable("x"), Number(2))
    }
    entry.model shouldBe Parser("f(2)>3")
  }

  it should "parse program definitions" in {
    val problem = {
      """
        |ArchiveEntry "Test"
        |Definitions
        |  HP a ::= { x:=*; ?x<=5; ++ x:=y; };
        |End.
        |
        |ProgramVariables
        |  Real x;
        |  Real y;
        |End.
        |
        |Problem
        |  y<=5 -> [a;]x<=5
        |End.
        |End.
        |""".stripMargin
    }

    val entry = ArchiveParser.parseProblem(problem)
    entry.defs.decls should contain key Name("a", None)
    entry.defs.decls(Name("a", None)) match {
      case Signature(domain, sort, argNames, Right(interpretation), _) =>
        domain.value shouldBe Unit
        sort shouldBe Trafo
        argNames shouldBe Symbol("empty")
        interpretation.value shouldBe "x:=*; ?x<=5; ++ x:=y;".asProgram
    }
    entry.model shouldBe "y<=5 -> [a{|^@|};]x<=5".asFormula
  }

  it should "parse functions and predicates in program definitions" in {
    val problem = {
      """
        |ArchiveEntry "Test"
        |Definitions
        |  Real f(Real x) = x+2;
        |  Bool p(Real x, Real y) <-> x<=y;
        |  HP a ::= { x:=*; ?p(x,5); ++ x:=f(y); };
        |End.
        |
        |ProgramVariables
        |  Real x;
        |  Real y;
        |End.
        |
        |Problem
        |  y<=5 -> [a;]x<=5
        |End.
        |End.
        |""".stripMargin
    }

    val entry = ArchiveParser.parseProblem(problem)
    entry.defs.decls should contain key Name("a", None)
    entry.defs.decls(Name("a", None)) match {
      case Signature(domain, sort, argNames, Right(interpretation), _) =>
        domain.value shouldBe Unit
        sort shouldBe Trafo
        argNames shouldBe Symbol("empty")
        interpretation.value shouldBe "x:=*; ?p(x,5); ++ x:=f(y);".asProgram
    }
    entry.model shouldBe "y<=5 -> [a{|^@|};]x<=5".asFormula
  }

  it should "parse annotations" in {
    val problem = {
      """
        |ArchiveEntry "Test"
        |Definitions
        |  Bool p(Real x, Real y) <-> x>=y;
        |  HP loopBody ::= { x:=x+2; };
        |  HP a ::= { x:=1; {loopBody;}*@invariant(p(x,1)) };
        |End.
        |
        |ProgramVariables
        |  Real x;
        |End.
        |
        |Problem
        |  [a;]x>=1
        |End.
        |End.
        |""".stripMargin
    }

    val annotations = ListBuffer.empty[(Program, Formula)]
    Parser.parser.setAnnotationListener((prg, fml) => annotations.append(prg -> fml))
    val entry = ArchiveParser.parseProblem(problem)
    entry.defs.decls should contain key Name("a", None)
    entry.defs.decls(Name("a", None)) match {
      case Signature(domain, sort, argNames, Right(interpretation), _) =>
        domain.value shouldBe Unit
        sort shouldBe Trafo
        argNames shouldBe Symbol("empty")
        interpretation.value shouldBe "x:=1; {loopBody{|^@|};}*".asProgram
    }
    entry.defs.decls(Name("loopBody", None)) match {
      case Signature(domain, sort, argNames, Right(interpretation), _) =>
        domain.value shouldBe Unit
        sort shouldBe Trafo
        argNames shouldBe Symbol("empty")
        interpretation.value shouldBe "x:=x+2;".asProgram
    }
    entry.annotations should contain theSameElementsInOrderAs List(("{loopBody{|^@|};}*".asProgram, "p(x,1)".asFormula))
    annotations should contain theSameElementsInOrderAs entry.annotations
    entry.model shouldBe "[a{|^@|};]x>=1".asFormula
  }

  it should "be allowed to ignore later definitions when elaborating annotations" in {
    val problem = {
      """
        |ArchiveEntry "Test"
        |Definitions
        |  HP a ::= { x:=1; {loopBody;}*@invariant(p(x,1)) };
        |  Bool p(Real x, Real y) <-> x>=y;
        |  HP loopBody ::= { x:=x+2; };
        |End.
        |
        |ProgramVariables
        |  Real x;
        |End.
        |
        |Problem
        |  [a;]x>=1
        |End.
        |End.
        |""".stripMargin
    }

    val annotations = ListBuffer.empty[(Program, Formula)]
    Parser.parser.setAnnotationListener((prg, fml) => annotations.append(prg -> fml))
    val entry = ArchiveParser.parseProblem(problem)
    entry.defs.decls should contain key Name("a", None)
    entry.defs.decls(Name("a", None)) match {
      case Signature(domain, sort, argNames, Right(interpretation), _) =>
        domain.value shouldBe Unit
        sort shouldBe Trafo
        argNames shouldBe Symbol("empty")
        interpretation.value shouldBe "x:=1; {loopBody{|^@|};}*".asProgram
    }
    entry.defs.decls(Name("loopBody", None)) match {
      case Signature(domain, sort, argNames, Right(interpretation), _) =>
        domain.value shouldBe Unit
        sort shouldBe Trafo
        argNames shouldBe Symbol("empty")
        interpretation.value shouldBe "x:=x+2;".asProgram
    }
    entry.annotations should contain theSameElementsInOrderAs List(("{loopBody{|^@|};}*".asProgram, "p(x,1)".asFormula))
    annotations should contain theSameElementsInOrderAs entry.annotations
    entry.model shouldBe "[a{|^@|};]x>=1".asFormula
  }
}
