package btactics

import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase
import edu.cmu.cs.ls.keymaerax.tags.UsualTest
import edu.cmu.cs.ls.keymaerax.bellerophon.{OnAll, TheType}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.Simplifier
import edu.cmu.cs.ls.keymaerax.btactics.DebuggingTactics.{print, printIndexed}
import edu.cmu.cs.ls.keymaerax.core.{Box, Imply, Sequent}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.SlowTest
import testHelper.ParserFactory._

import scala.collection.immutable._

import scala.language.postfixOps

/**
  * Created by bbohrer on 5/21/16.
  */
@UsualTest
class SimplifierTests extends TacticTestBase {
  "Simplifier" should "simplify mult by 0" in withMathematica { implicit qeTool =>
    val fml = "0 * x = x".asFormula
    val tactic = Simplifier.simp()(1) & debug("After simping", true)
    proveBy(fml, tactic).subgoals should contain only
      Sequent(Nil, IndexedSeq(), IndexedSeq("0 = x".asFormula))
  }

}
