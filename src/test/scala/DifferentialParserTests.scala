import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.parser.{ParseSymbols, LoadedAxiom, KeYmaeraParser}
import edu.cmu.cs.ls.keymaera.tests.ProvabilityTestHelper
import org.scalatest.{PrivateMethodTester, Matchers, FlatSpec}
import testHelper.StringConverter

/**
 * Tests for ContEvolve -> NFContEvolve refactoring.
 * Created by nfulton on 1/2/15.
 * @author Nathan Fulton
 * @author Stefan Mitsch
 */
class DifferentialParserTests extends FlatSpec with Matchers with PrivateMethodTester {
  val helper = new ProvabilityTestHelper()

  val x = Variable("x", None, Real)
  val y = Variable("y", None, Real)
  val one = Number(1)
  val zero = Number(0)

  "The parser" should "parse diff eqs in normal form into NFContEvolves" in {
    helper.parseBareProgram("x' = 1 & x > 0;") match {
      case Some(program) => program should be (NFContEvolve(Nil, Derivative(Real, x), Number(1), GreaterThan(Real, x, zero)))
      case None => fail("Parse failed.")
    }
  }

  it should "not confuse a portion of the diffeq with the evolution domain constraint" in {
    helper.parseBareProgram("x'=y, y'=x & true;") match {
      case Some(program) =>
        program should be (ContEvolveProduct(
          NFContEvolve(Nil, Derivative(Real, x), y, True),
          NFContEvolve(Nil, Derivative(Real, y), x, True)))
      case None => fail("Failed to parse.")
    }
  }

  it should "not confuse a portion of the diffeq system with the evolution domain constraint" in {
    helper.parseBareProgram("x'=x, y'=y;") match {
      case Some(program) =>
        program should be (ContEvolveProduct(
          NFContEvolve(Nil, Derivative(Real, x), x, True),
          NFContEvolve(Nil, Derivative(Real, y), y, True)))
      case None => fail("Parse failed.")
    }
  }

  it should "parse an evolution domain constraint given last into the correct position" in {
    helper.parseBareProgram("x'=y, y'=x & y>0;") match {
      case Some(program) =>
        program should be (ContEvolveProduct(
          NFContEvolve(Nil, Derivative(Real, x), y, True),
          NFContEvolve(Nil, Derivative(Real, y), x, GreaterThan(Real, y, zero))))
      case None => fail("Failed to parse.")
    }
  }

  it should "parse a conjunction of evolution domain constraints given last into the correct position" in {
    helper.parseBareProgram("x'=y, y'=x & y>0 & x<0;") match {
      case Some(program) =>
        program should be (ContEvolveProduct(
          NFContEvolve(Nil, Derivative(Real, x), y, True),
          NFContEvolve(Nil, Derivative(Real, y), x, And(GreaterThan(Real, y, zero), LessThan(Real, x, zero)))))
      case None => fail("Failed to parse.")
    }
  }

  it should "parse a single equation with a constraint as an evolution, not an AND-formula." in {
    helper.parseBareProgram("x' = y & x >= 0;") match {
      case Some(p) => p should be (NFContEvolve(Nil, Derivative(Real, x), y, GreaterEqual(Real, x, zero)))
      case _ => fail("failed to parse.")
    }
  }

  it should "parse scattered evolution domain constraints into the correct positions" in {
    helper.parseBareProgram("x'=y & x>5, y'=x & y>0 & x<0;") match {
      case Some(program) =>
        program should be (ContEvolveProduct(
          NFContEvolve(Nil, Derivative(Real, x), y, GreaterThan(Real, x, Number(BigDecimal(5)))),
          NFContEvolve(Nil, Derivative(Real, y), x, And(GreaterThan(Real, y, zero), LessThan(Real, x, zero)))))
      case None => fail("Failed to parse.")
    }
  }

  it should "parse and associate multiple ODEs correctly" in {
    helper.parseBareProgram("x'=y & x>5, z'=5, y'=x & y>0 & x<0;") match {
      case Some(program) =>
        program should be (ContEvolveProduct(
          NFContEvolve(Nil, Derivative(Real, x), y, GreaterThan(Real, x, Number(BigDecimal(5)))),
          ContEvolveProduct(
            NFContEvolve(Nil, Derivative(Real, Variable("z", None, Real)), Number(BigDecimal(5)), True),
            NFContEvolve(Nil, Derivative(Real, y), x, And(GreaterThan(Real, y, zero), LessThan(Real, x, zero))))))
      case None => fail("Failed to parse.")
    }
  }

  it should "parse ContEvolveProgramConstants" in {
    new KeYmaeraParser().ProofFileParser.runParser("Variables. CP a. T x. F p. End. Axiom \"Foo\" . [a;]p End.") match {
      case List(LoadedAxiom(_, BoxModality(prg, _))) => prg should be (ContEvolveProgramConstant("a"))
    }
  }

  it should "parse ContEvolveProgramConstants in a system with NFContEvolve" in {
    new KeYmaeraParser().ProofFileParser.
      runParser("Variables. CP a. T x. F p. End. Axiom \"Foo\" . [x'=1 & x>5, a;]p End.") match {
      case List(LoadedAxiom(_, BoxModality(prg, _))) => prg should be(ContEvolveProduct(
        NFContEvolve(Nil, Derivative(Real, x), one, GreaterThan(Real, x, Number(BigDecimal(5)))),
        ContEvolveProgramConstant("a")))
    }
  }

  it should "not parse ProgramConstants in a system with NFContEvolve" in {
    the [Exception] thrownBy (new KeYmaeraParser().ProofFileParser.
      runParser("Variables. P a. T x. F p. End. Axiom \"Foo\" . [x'=1 & x>5, a;]p End.")) should have message
      "Failed to parse Lemmas & Axioms at (line: 1, column:60): `'' expected but `;' found"
  }

  it should "Parse diff assign" in {
    helper.parseBareProgram("x' := 1;")
  }

  "The IncompleteSystem Parser" should "parse incomplete systems" in {
    val systemCommand = "x'=y & x>0, y' =x, t' = 1 & t < eps" //no semicolon.
    helper.parseBareProgram(systemCommand +";") //Sanity test; it should at least parse.
    helper.parseBareProgram("$$" + systemCommand + "$$;") //should not throw an exception.
  }

  {
    val preamble = "Variables. CP a. T x. T tx. T y. T ty. F H. F Hx. F Hy. F p. End. Axiom \"test123\".\n"
    val end = "\nEnd."
    val parse = (x:String) => new KeYmaeraParser().ProofFileParser.runParser(x)

    it should "sanity-check" in {
      parse(preamble + "1=2" + end) //sanity-check the preamble.
    }


    //@todo these rules need semantically suggestive names.
    //@todo do the equality tests instead of merely making sure the parse does not choke.
    it should "parse the System-Diff-Intro rule" in {
      parse(preamble + "[a;]p <- [$$ a $$;]p" + end)
    }

    it should "parse the System-Diff-Final rule" in {
      parse(preamble + "[$$ x' = tx & Hx $$;]p <- [x' := tx;][?Hx;]p" + end)
    }

    it should "parse the System-Diff-Head-Test rule" in {
      parse(preamble + "[$$ x' = tx & Hx, a $$;][?H;]p <- [x' := tx;][a;][?H&Hx;]p" + end)
    }

    it should "parse the System-Diff-NoHead-Test rule" in {
      parse(preamble + "[$$ x' = tx & Hx, a $$;]p <- [x' := tx;][a;][?Hx;]p" + end)
    }
  }
}
