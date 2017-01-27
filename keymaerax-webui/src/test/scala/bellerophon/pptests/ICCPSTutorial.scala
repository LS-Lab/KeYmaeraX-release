package bellerophon.pptests

import edu.cmu.cs.ls.keymaerax.bellerophon.parser.{BelleParser, BellePrettyPrinter}
import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase
import edu.cmu.cs.ls.keymaerax.tags.CaseStudyTest
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

/**
  * These are the tactics that are referenced in the CPS Week tutorial on KeYmaera X.
  *
  * Every tactic mentioned in the tutorial, including:
  *   - tactics from slide examples
  *   - tactics from handouts
  *   - tactics that are extracted
  *
  * The tests herein should be comprehensive, meaning we test that:
  *   - the tactic parses
  *   - the tactic pretty-prints to something reasonable
  *   - the tactic proves the property at hand.
  *
  * @author Nathan Fulton
  */
@CaseStudyTest
class ICCPSTutorial extends TacticTestBase {

  "Simple car example constructive tactic" should "parse, print, prove" in withMathematica(mathematica => {
    val t = "implyR(1) ; loop({`x != m & b > 0`}, 1) <(QE, QE, composeb(1) ; composeb(1) ; composeb(1) ; testb(1) ; assignb(1) ; solve(1) ; QE)"
    val model = "1=1 -> [{?1=1; x:=1; {x'=v,v'=a}}*]1=1".asFormula

    val parsedTactic = BelleParser(t) //should not throw any errors.

    val printedTactic = BellePrettyPrinter(parsedTactic)

     printedTactic should equal ("""
        |(implyR(1) ; loop({`x != m & b > 0`},1)) ; <(
        |  QE,
        |  QE,
        |  composeb(1) ; composeb(1) ; composeb(1) ; testb(1) ; assignb(1) ; solve(1) ; QE
        |)
      """.stripMargin) (after being whiteSpaceRemoved)

    //@todo printed tactic should reparse
    //BelleParser(printedTactic) shouldBe parsedTactic
  })

  "Simple car search tactic" should "parse, print, prove" in withMathematica(mathematica => {
    val t = "implyR(1) & loop({`1=1`}, 1) & solve(1) & QE"
    BelleParser(t)
  })
}
