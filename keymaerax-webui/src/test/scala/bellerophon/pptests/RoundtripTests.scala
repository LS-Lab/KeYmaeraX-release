package bellerophon.pptests

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.{BelleParser, BellePrettyPrinter}
import edu.cmu.cs.ls.keymaerax.btactics.{Idioms, TacticTestBase, TactixLibrary}
import edu.cmu.cs.ls.keymaerax.core.{AntePos, AtomicODE, DifferentialSymbol, SeqPos, SuccPos}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.UsualTest


/**
  * Tests BelleExpr roundtrip identity of parser and pretty printer.
  * @author Stefan Mitsch
  */
@UsualTest
class RoundtripTests extends TacticTestBase {
  private def roundTrip(tactic: String): Unit = BellePrettyPrinter(BelleParser(tactic)) shouldBe tactic
  private def roundTrip(tactic: BelleExpr): Unit = BelleParser(BellePrettyPrinter(tactic)) shouldBe tactic
  private def roundTrip(tactic: BelleExpr, ts: String): Unit = {
    BelleParser(ts) shouldBe tactic
    BellePrettyPrinter(tactic) shouldBe ts
    // redundant
    roundTrip(tactic)
    roundTrip(ts)
  }

  //@note this test case points out something that's kind-of a problem with our current setup -- print(parse(x)) != x even if parse(print(x)) = x.
  //In order to get the actually correct behavior we would need DerivedAxiomInfo to be a bidirectional map and then we would need to always prefer that map's
  //names over the actual tactic that was created at the end of the day.
  "Parser and printer roundtrip" should "atomics" in {
    roundTrip(Idioms.nil, "nil")
  }

  it should "position tactics with fixed positions" in {
    roundTrip(TactixLibrary.andR(1), "andR(1)")
  }

  it should "position tactics with locators" in {
    roundTrip(TactixLibrary.andL('L), "andL('L)")
    roundTrip(TactixLibrary.andR('R), "andR('R)")
  }

  it should "combinators" in {
    roundTrip(Idioms.nil & Idioms.nil, "nil & nil")
    roundTrip(Idioms.nil | Idioms.nil, "nil | nil")
    roundTrip(OnAll(Idioms.nil), "doall(nil)")
    roundTrip(Idioms.nil*2, "nil*2")
    roundTrip(PartialTactic(Idioms.nil), "nil partial")
  }

  it should "input tactic transform" in {
    roundTrip(TactixLibrary.transform("x>0".asFormula)(1), "transform({`x>0`}, 1)")
  }

  it should "input tactic generalizeb" in {
    roundTrip(TactixLibrary.generalize("x>0".asFormula)(1), "generalizeb({`x>0`}, 1)")
  }

  it should "input tactic diffCut" in {
    roundTrip(TactixLibrary.diffCut("x>0".asFormula)(1), "diffCut({`x>0`}, 1)")
  }

  it should "input tactic DA4" in {
    //@todo test with BelleExpr data structure, but DifferentialTactics is private
    roundTrip("DA4({`x=0`}, {`x`}, {`1`}, {`2`}, 1)")
  }

  it should "input tactic diffGhost" in {
    //@todo test with BelleExpr data structure, but DifferentialTactics is private
    roundTrip("diffGhost({`x`}, {`1`}, {`2`}, {`0`}, 1)")
  }

  it should "input tactic DGTactic" in {
    roundTrip(TactixLibrary.DG(AtomicODE(DifferentialSymbol("x".asVariable), "5*x+2".asTerm))(1), "DGTactic({`x`}, {`5`}, {`2`}, 1)")
  }

}
