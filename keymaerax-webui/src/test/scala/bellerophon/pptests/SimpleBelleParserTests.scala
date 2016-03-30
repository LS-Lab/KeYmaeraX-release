package bellerophon.pptests

import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.btactics.{HilbertCalculus, DerivedAxioms, TactixLibrary, TacticTestBase}
import edu.cmu.cs.ls.keymaerax.parser.UnknownLocation

/**
  * Very simple unit tests for the Bellerophon parser. Useful for TDD and bug isolation but probably not
  * so useful for anything else.
  *
  * @author Nathan Fulton
  */
class SimpleBelleParserTests extends TacticTestBase {
  //region Atomic tactics

  "Parser" should "parse a built-in tactic" in withMathematica(implicit mathematica => {
    BelleParser("nil") shouldBe TactixLibrary.nil
  })

  it should "parse a built-in tactic with arguments" in withMathematica((implicit mathematica => {
    BelleParser("cut({`1=1`})")
  }))

  it should "parse a built-in argument with an absolute top-level postion" in withMathematica((implicit mathematica => {
    BelleParser("andR(1)") shouldBe TactixLibrary.andR(1)
  }))

  it should "parse a built-in argument with an absolute non-top-level postion" in withMathematica((implicit mathematica => {
    val pos = BelleParser.parseAbsolutePosition("1.1", UnknownLocation)
    BelleParser("boxAnd(1.1)") shouldBe HilbertCalculus.useAt(DerivedAxioms.boxAnd)(pos)
  }))

  ignore should "parse a built-in argument with a position locator" in withMathematica((implicit mathematica => {
    BelleParser("cut({`1=1`})")//@todo write this
  }))

  ignore should "parse a built-in tactic that takes a whole list of arguments" in withMathematica((implicit mathematica => {
    BelleParser("diffInvariant({`1=1`}, 1)") shouldBe ???
  }))

  //endregion

}
