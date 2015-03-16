import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.parser.{LoadedKnowledge, ParseSymbols, LoadedAxiom, KeYmaeraParser}
import edu.cmu.cs.ls.keymaera.tests.ProvabilityTestHelper
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

  def finalODE(ode: DifferentialProgram) = ODEProduct(ode, EmptyODE())

  "The parser" should "parse diff eqs in normal form into Product(NFContEvolve,Empty)" in {
    helper.parseBareProgram("x' = 1 & x > 0;") match {
      case Some(program) => program should be (ODESystem(finalODE(AtomicODE(Derivative(Real, x), Number(1))), GreaterThan(Real, x, zero)))
      case None => fail("Parse failed.")
    }
  }

  it should "not confuse a portion of the diffeq with the evolution domain constraint" in {
    helper.parseBareProgram("x'=y, y'=x & true;") match {
      case Some(program) =>
        program should be (ODESystem(ODEProduct(
          AtomicODE(Derivative(Real, x), y),
          finalODE(AtomicODE(Derivative(Real, y), x))), True))
      case None => fail("Failed to parse.")
    }
  }

  it should "parse into normal form when parsing a formula" in {
    val f = helper.parseFormula("[x'=1 & x>0;]z>=0")
    f match {
      case BoxModality(ODESystem(_, ev, _), _) => ev match {
        case ODEProduct(l,r) => l match {
          case _: AtomicODE => /* ok */
          case _ => fail()
        }; r match {
          case _: EmptyODE => /* ok */
          case _ => fail()
        }
      }
      case _ => fail("failed to parse to correct thing")
    }
  }

  it should "not confuse a portion of the diffeq system with the evolution domain constraint" in {
    helper.parseBareProgram("x'=x, y'=y;") match {
      case Some(program) =>
        program should be (ODESystem(ODEProduct(
          AtomicODE(Derivative(Real, x), x),
          finalODE(AtomicODE(Derivative(Real, y), y))), True))
      case None => fail("Parse failed.")
    }
  }

  it should "parse an evolution domain constraint given last into the correct position" in {
    helper.parseBareProgram("x'=y, y'=x & y>0;") match {
      case Some(program) =>
        program should be (ODESystem(ODEProduct(
          AtomicODE(Derivative(Real, x), y),
          finalODE(AtomicODE(Derivative(Real, y), x))), GreaterThan(Real, y, zero)))
      case None => fail("Failed to parse.")
    }
  }

  it should "parse a conjunction of evolution domain constraints given last into the correct position" in {
    helper.parseBareProgram("x'=y, y'=x & y>0 & x<0;") match {
      case Some(program) =>
        program should be (ODESystem(ODEProduct(
          AtomicODE(Derivative(Real, x), y),
          finalODE(AtomicODE(Derivative(Real, y), x))), And(GreaterThan(Real, y, zero), LessThan(Real, x, zero))))
      case None => fail("Failed to parse.")
    }
  }

  it should "parse a single equation with a constraint as an evolution, not an AND-formula." in {
    helper.parseBareProgram("x' = y & x >= 0;") match {
      case Some(p) => p should be (ODESystem(finalODE(AtomicODE(Derivative(Real, x), y)), GreaterEqual(Real, x, zero)))
      case _ => fail("failed to parse.")
    }
  }

  // TODO not yet supported by parser
  ignore should "collect scattered evolution domain constraints into one evolution domain constraint" in {
    helper.parseBareProgram("x'=y & x>5, y'=x & y>0 & x<0;") match {
      case Some(program) =>
        program should be (ODESystem(ODEProduct(
          AtomicODE(Derivative(Real, x), y),
          finalODE(AtomicODE(Derivative(Real, y), x))), And(GreaterThan(Real, x, Number(5)), And(GreaterThan(Real, y, zero), LessThan(Real, x, zero)))))
      case None => fail("Failed to parse.")
    }
  }

  // TODO not yet supported by parser
  ignore should "parse and associate multiple ODEs correctly" in {
    helper.parseBareProgram("x'=y & x>5, z'=5, y'=x & y>0 & x<0;") match {
      case Some(program) =>
        program should be (ODESystem(ODEProduct(
          AtomicODE(Derivative(Real, x), y),
          ODEProduct(
            AtomicODE(Derivative(Real, Variable("z", None, Real)), Number(5)),
            finalODE(AtomicODE(Derivative(Real, y), x)))), And(GreaterThan(Real, x, Number(5)), And(GreaterThan(Real, y, zero), LessThan(Real, x, zero)))))
      case None => fail("Failed to parse.")
    }
  }

  it should "parse DifferentialProgramConstants" in {
    new KeYmaeraParser().ProofFileParser.runParser("Variables. CP a. T x. F p. End. Axiom \"Foo\" . [a;]p End.") match {
      case List(LoadedAxiom(_, BoxModality(prg, _))) => prg should be (ODESystem(finalODE(DifferentialProgramConstant("a")), True))
    }
  }

  it should "parse DifferentialProgramConstants in a system with NFContEvolve" in {
    new KeYmaeraParser().ProofFileParser.
      runParser("Variables. CP a. T x. F p. End. Axiom \"Foo\" . [x'=1, a & x>5;]p End.") match {
      case List(LoadedAxiom(_, BoxModality(prg, _))) => prg should be(ODESystem(ODEProduct(
        AtomicODE(Derivative(Real, x), one),
        finalODE(DifferentialProgramConstant("a"))), GreaterThan(Real, x, Number(5))))
    }
  }

  ignore should "not parse ProgramConstants in a system with NFContEvolve" in { //Not sure, but I think this is OK now.
    the [Exception] thrownBy new KeYmaeraParser().ProofFileParser.
      runParser("Variables. P a. T x. F p. End. Axiom \"Foo\" . [x'=1 & x>5, a;]p End.") should have message
      "Failed to parse Lemmas & Axioms at (line: 1, column:60): `'' expected but `;' found"
  }

  it should "Parse diff assign" in {
    helper.parseBareProgram("x' := 1;")
  }

  "The IncompleteSystem Parser" should "parse incomplete systems" in {
    helper.parseBareProgram("x'=y, y' =x, t' = 1 & t < eps;") //Sanity test; it should at least parse.
    helper.parseBareProgram("$$x'=y, y' =x, t' = 1$$ & t < eps;") //should not throw an exception.
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
      parse(preamble + "[$$ x' = tx $$ & Hx ;]p <- [x' := tx;][?Hx;]p" + end)
    }

    it should "parse the System-Diff-Head-Test rule" in {
      parse(preamble + "[$$ x' = tx, a $$ & Hx;][?H;]p <- [x' := tx;][a;][?H&Hx;]p" + end)
    }

    it should "parse the System-Diff-NoHead-Test rule" in {
      parse(preamble + "[$$ x' = tx, a $$ & Hx;]p <- [x' := tx;][a;][?Hx;]p" + end)
    }


    /**
     * A test about how the incomplete system axioms will be parsed.
     */
    it should "parse formula symbols how I expect" in {
      val result:List[LoadedKnowledge] = parse("Variables. T f(x). End. Axiom \"expectations\".\n" + "f(x) = 1" + "End.")
//      result.last.formula.asInstanceOf[Assign].left should be(Function("f", None, Bool, Bool))
    }
  }

  /**
   * This test just makes sure that we parse boxes in the expected way, because that's necessary for the system axioms.
   */
  "The formula parser" should "parse [x:=1;][x:=1;]1=1 as Box(program, Box(program, formula))" in {
    val result = helper.parseFormula("[x:=1;][x:=1;]1=1").asInstanceOf[Modality]
    result match {
      case BoxModality(p,f) => {
        p should be (Assign(x,one))
        f match {
          case BoxModality(p,f) => {
            p should be(Assign(x,one))
            f should be(Equals(Real,one,one))
          }
          case _ => fail("bad structure.")
        }
      }
      case _ => fail("didn't have the structure I expected.")
    }
    //ok everything now. I think the above tests were just added because a typo (2 instead of 1) was causing the test to
    //unexpectedly fail. But anyways, the fine-grained information and the gross test is useful so I'm leaving everything.
    result should be(
      BoxModality(
        Assign(x,one),
        BoxModality(
          Assign(x,one),
          Equals(Real,one,one)
        )
      )
    )
  }

}
