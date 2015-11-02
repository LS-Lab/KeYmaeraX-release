package bellerophon

import edu.cmu.cs.ls.keymaerax.bellerophon.{SequentialInterpreter, BelleProvable, BelleExpr}
import edu.cmu.cs.ls.keymaerax.btactics.ToolTactics
import edu.cmu.cs.ls.keymaerax.core.{Provable, Formula, Sequent}
import edu.cmu.cs.ls.keymaerax.launcher.DefaultConfiguration
import edu.cmu.cs.ls.keymaerax.tools.Mathematica
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import scala.collection.immutable.IndexedSeq
import org.scalatest.{Matchers, FlatSpec}

/**
 * @author Nathan Fulton
 */
class QETests extends FlatSpec with Matchers {
  val theInterpreter = new SequentialInterpreter()

  "Implicit params" should "work for Mathematica" in {
    implicit val qeTool = new Mathematica()
    qeTool.init(DefaultConfiguration.defaultMathematicaConfig)
    qeTool.isInitialized shouldBe true

    shouldClose(ToolTactics.fullQE, "1=1".asFormula)
  }

  private def toSequent(s : String) = new Sequent(Nil, IndexedSeq(), IndexedSeq(s.asFormula))

  private def shouldClose(expr: BelleExpr, f: Formula) = {
    val v = BelleProvable(Provable.startProof(f))
    val result = theInterpreter.apply(expr, v)
    result.isInstanceOf[BelleProvable] shouldBe true
    result.asInstanceOf[BelleProvable].p.isProved shouldBe true
  }

}
