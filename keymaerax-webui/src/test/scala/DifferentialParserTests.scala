/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.{LoadedAxiom, KeYmaeraParser}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import testHelper.ProvabilityTestHelper
import org.scalatest.{PrivateMethodTester, Matchers, FlatSpec}

/**
 * Tests for ContEvolve -> NFContEvolve refactoring.
 * Created by nfulton on 1/2/15.
 * @author Nathan Fulton
 * @author Stefan Mitsch
 */
class DifferentialParserTests extends FlatSpec with Matchers with PrivateMethodTester {
  val helper = new ProvabilityTestHelper((x:String) => ())

  val x = Variable("x", None, Real)
  val y = Variable("y", None, Real)
  val one = Number(1)
  val zero = Number(0)

  "The parser" should "parse diff eqs in normal form into Product(NFContEvolve,Empty)" in {
    helper.parseBareProgram("{x' = 1 & x > 0}") shouldBe
      Some(ODESystem(AtomicODE(DifferentialSymbol(x), Number(1)), Greater(x, zero)))
  }

  it should "not confuse a portion of the diffeq with the evolution domain constraint" in {
    helper.parseBareProgram("{x'=y, y'=x & true}") shouldBe
      Some(ODESystem(DifferentialProduct(
          AtomicODE(DifferentialSymbol(x), y),
          AtomicODE(DifferentialSymbol(y), x)), True))
  }

  it should "parse into normal form when parsing a formula" in {
    val f = helper.parseFormula("[{x'=1 & x>0}]z>=0")
    f match {
      case Box(ODESystem(ev, _), _) => ev match {
        case _: AtomicODE => /* ok */
        case _ => fail()
      }
      case _ => fail("failed to parse to correct thing")
    }
  }

  it should "not confuse a portion of the diffeq system with the evolution domain constraint" in {
    helper.parseBareProgram("{x'=x, y'=y}") shouldBe Some(ODESystem(DifferentialProduct(
          AtomicODE(DifferentialSymbol(x), x),
          AtomicODE(DifferentialSymbol(y), y)), True))
  }

  it should "parse an evolution domain constraint given last into the correct position" in {
    helper.parseBareProgram("{x'=y, y'=x & y>0}") shouldBe Some(ODESystem(DifferentialProduct(
          AtomicODE(DifferentialSymbol(x), y),
          AtomicODE(DifferentialSymbol(y), x)), Greater(y, zero)))
  }

  it should "parse a conjunction of evolution domain constraints given last into the correct position" in {
    helper.parseBareProgram("{x'=y, y'=x & y>0 & x<0}") shouldBe Some(ODESystem(DifferentialProduct(
          AtomicODE(DifferentialSymbol(x), y),
          AtomicODE(DifferentialSymbol(y), x)), And(Greater(y, zero), Less(x, zero))))
  }

  it should "parse a single equation with a constraint as an evolution, not an AND-formula." in {
    helper.parseBareProgram("{x' = y & x >= 0}") shouldBe
      Some(ODESystem(AtomicODE(DifferentialSymbol(x), y), GreaterEqual(x, zero)))
  }

  // TODO not yet supported by parser
  ignore should "collect scattered evolution domain constraints into one evolution domain constraint" in {
    helper.parseBareProgram("{x'=y & x>5, y'=x & y>0 & x<0}") shouldBe
      Some(ODESystem(DifferentialProduct(
          AtomicODE(DifferentialSymbol(x), y),
          AtomicODE(DifferentialSymbol(y), x)), And(Greater(x, Number(5)), And(Greater(y, zero), Less(x, zero)))))
  }

  // TODO not yet supported by parser
  ignore should "parse and associate multiple ODEs correctly" in {
    helper.parseBareProgram("x'=y & x>5, z'=5, y'=x & y>0 & x<0;") shouldBe
      Some(ODESystem(DifferentialProduct(
          AtomicODE(DifferentialSymbol(x), y),
          DifferentialProduct(
            AtomicODE(DifferentialSymbol(Variable("z", None, Real)), Number(5)),
            AtomicODE(DifferentialSymbol(y), x))), And(Greater(x, Number(5)), And(Greater(y, zero), Less(x, zero)))))
  }

  it should "parse DifferentialProgramConstants" in {
    new KeYmaeraParser().ProofFileParser.runParser("Variables. CP a. T x. F p. End. Axiom \"Foo\" . [a;]p End.") match {
      case List(LoadedAxiom(_, Box(prg, _))) => prg shouldBe ODESystem(DifferentialProgramConst("a"), True)
    }
  }

  it should "parse DifferentialProgramConstants in a system with NFContEvolve" in {
    new KeYmaeraParser().ProofFileParser.
      runParser("Variables. CP a. T x. F p. End. Axiom \"Foo\" . [x'=1, a & x>5;]p End.") match {
      case List(LoadedAxiom(_, Box(prg, _))) => prg should be(ODESystem(DifferentialProduct(
        AtomicODE(DifferentialSymbol(x), one),
        DifferentialProgramConst("a")), Greater(x, Number(5))))
    }
  }

  ignore should "not parse ProgramConstants in a system with NFContEvolve" in { //Not sure, but I think this is OK now.
    the [Exception] thrownBy new KeYmaeraParser().ProofFileParser.
      runParser("Variables. P a. T x. F p. End. Axiom \"Foo\" . [x'=1 & x>5, a;]p End.") should have message
      "Failed to parse Lemmas & Axioms at (line: 1, column:60): `'' expected but `;' found"
  }

  it should "parse diff assign" in {
    helper.parseBareProgram("x' := 1;") shouldBe Some(DiffAssign(DifferentialSymbol("x".asVariable), Number(1)))
  }

  it should "parse (x)' as differential and x' as differential symbol" in {
    val x = Variable("x", None, Real)
    "(x)' = x'".asFormula shouldBe Equal(Differential(x), DifferentialSymbol(x))
  }

  it should "parse f()' as differential" in {
    val f = FuncOf(Function("f", None, Unit, Real), Nothing)
    "f()' = 5".asFormula shouldBe Equal(Differential(f), Number(5))
  }

  it should "parse (-f())' as differential" in {
    val f = FuncOf(Function("f", None, Unit, Real), Nothing)
    "(-f())' = 5".asFormula shouldBe Equal(Differential(Neg(f)), Number(5))
  }

  /**
   * This test just makes sure that we parse boxes in the expected way, because that's necessary for the system axioms.
   */
  "The formula parser" should "parse [x:=1;][x:=1;]1=1 as Box(program, Box(program, formula))" in {
    helper.parseFormula("[x:=1;][x:=1;]1=1") shouldBe
      Box(Assign(x, one), Box(Assign(x, one), Equal(one, one)))
  }

}
