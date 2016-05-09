package bellerophon.pptests

import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase

/**
  * Tests cases derived from known bugs and fixed bugs in the Bellerophon parser.
  *
  * @author Nathan Fulton
  */
class BelleParserRegressionTest extends TacticTestBase {

  "BelleParser" should "pass regression tests" in {
    val t = """implyR(1) &
              |loop({`x<=m`}, 1) <(
              |  MathematicaQE,
              |  MathematicaQE,
              |  partial(composeb(1) & choiceb(1) & andR(1) <(
              |    assignb(1) & diffSolve(1) & nil,
              |    testb(1) & implyR(1) & diffSolve(1) & nil
              |  ))
              |)"""
    BelleParser(t) //should not cause an exception.
  }

}
