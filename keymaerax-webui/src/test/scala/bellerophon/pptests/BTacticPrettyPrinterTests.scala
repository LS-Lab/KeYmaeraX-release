package bellerophon.pptests

import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BellePrettyPrinter
import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase
import edu.cmu.cs.ls.keymaerax.tags.UsualTest
import org.scalatest.{FlatSpec, Matchers}

/**
  * @author Nathan Fulton
  */
@UsualTest
class BTacticPrettyPrinterTests extends TacticTestBase {
  val parser = BelleParser

  //@note this test case points out something that's kind-of a problem with our current setup -- print(parse(x)) != x even if parse(print(x)) = x.
  //In order to get the actually correct behavior we would need DerivedAxiomInfo to be a bidirectional map and then we would need to always prefer that map's
  //names over the actual tactic that was created at the end of the day.
  "built-in printer" should "print a built-in expr" in {
    val tactic = parser("nil")
    BellePrettyPrinter(tactic) shouldBe "partial(nil)"
  }

  it should "print e(1)" in {
    val tactic = parser("andR(1)")
    BellePrettyPrinter(tactic) shouldBe "andR(1)"
  }

  it should "print e('L)" in {
    val tactic = parser("andR('L)")
    BellePrettyPrinter(tactic) shouldBe "andR('L)"
  }

  it should "print e('R)" in {
    val tactic = parser("andR('R)")
    BellePrettyPrinter(tactic) shouldBe "andR('R)"
  }

  "seq printer" should "print e & e" in {
    val tactic = parser("nil & nil")
    BellePrettyPrinter(tactic) shouldBe "partial(nil) & partial(nil)"
  }

  it should "print e & e & e" in {
    val tactic = parser("nil & (nil & nil)")
    BellePrettyPrinter(tactic) shouldBe "partial(nil) & partial(nil) & partial(nil)"
  }

  it should "print (e & e) & e" in {
    val tactic = parser("(nil & nil) & nil")
    BellePrettyPrinter(tactic) shouldBe "(partial(nil) & partial(nil)) & partial(nil)"
  }

  it should "print e | e" in {
    val tactic = parser("nil | nil")
    BellePrettyPrinter(tactic) shouldBe "partial(nil) | partial(nil)"
  }
}
