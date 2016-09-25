package bellerophon.pptests

import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BellePrettyPrinter
import edu.cmu.cs.ls.keymaerax.btactics.{TacticTestBase, TactixLibrary}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.UsualTest


/**
  * Tests BelleExpr pretty printing, for expected string representation plus roundtrip identity with parser.
  * @author Nathan Fulton
  * @author Stefan Mitsch
  */
@UsualTest
class BTacticPrettyPrinterTests extends TacticTestBase {
  private val parser = BelleParser

  private def roundTrip(tactic: String) = {
    val parsed = parser(tactic)
    val printed = BellePrettyPrinter(parsed)
    printed shouldBe tactic
    parser(printed) shouldBe parsed
  }

  //@note this test case points out something that's kind-of a problem with our current setup -- print(parse(x)) != x even if parse(print(x)) = x.
  //In order to get the actually correct behavior we would need DerivedAxiomInfo to be a bidirectional map and then we would need to always prefer that map's
  //names over the actual tactic that was created at the end of the day.
  "built-in printer" should "print a built-in expr" in { roundTrip("nil") }

  it should "print e(1)" in { roundTrip("andR(1)") }

  it should "print e('L)" in { roundTrip("andR('L)") }

  it should "print e('R)" in { roundTrip("andR('R)") }

  "seq printer" should "print e & e" in { roundTrip("nil & nil") }

  it should "print e & e & e" in { roundTrip("nil & nil & nil") }

  it should "print (e & e) & e" in { roundTrip("(nil & nil) & nil") }

  it should "print e | e" in { roundTrip("nil | nil") }

  "doall" should "print e & doall(e)" in { roundTrip("andR(1) & doall(andL(1))") }

  "Operator precedence" should "parenthesize saturate *" in { roundTrip("implyR(1) & (andL('L)*)") }

  it should "parenthesize repeat *times" in { roundTrip("implyR(1) & (andL('L)*2)") }

  it should "parenthesize partial" in { roundTrip("implyR(1) & (andL(1) partial)") }

}
