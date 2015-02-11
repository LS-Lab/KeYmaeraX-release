import edu.cmu.cs.ls.keymaera.core.ExpressionTraversal.ExpressionTraversalFunction
import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.Tactics
import edu.cmu.cs.ls.keymaera.tests.ProvabilityTestHelper
import org.scalatest.{BeforeAndAfterEach, Matchers, FlatSpec}

/**
 * Created by nfulton on 2/5/15.
 */
trait TacticTestSuite extends FlatSpec with Matchers with BeforeAndAfterEach {
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Boilerplate
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  val helper = new ProvabilityTestHelper(x=>println(x))

  var tool: Mathematica = null
  val mathematicaConfig = helper.mathematicaConfig

  override def beforeEach() = {
    tool = new Mathematica
    tool.init(mathematicaConfig)
    Tactics.KeYmaeraScheduler.init(Map())
    Tactics.MathematicaScheduler.init(mathematicaConfig)
  }

  override def afterEach() = {
    tool.shutdown()
    tool = null
    Tactics.KeYmaeraScheduler.shutdown()
    Tactics.MathematicaScheduler.shutdown()
  }

  protected def containsOpenGoal(node:ProofNode, f:Formula) =
    !node.openGoals().find(_.sequent.succ.contains(f)).isEmpty

  protected def containsOnlyOpenGoal(node : ProofNode, f : Formula) =
    containsOpenGoal(node, f) && node.openGoals().length == 1

  protected def containsOnlyExactlyOpenGoal(node : ProofNode, f : Formula) =
    !node.openGoals().find(n => n.sequent.succ.contains(f) && n.sequent.succ.length==1 && n.sequent.ante.length==0).isEmpty

  protected def formulaAtExpr(node : ProofNode, position : Position) : Option[Formula] = {
    var formula : Option[Formula] = None
    val fn = new ExpressionTraversalFunction {
      override def preF(posInExpr : PosInExpr, f : Formula) = {
        if(posInExpr.equals(position.inExpr)) {
          formula = Some(f)
          Left(Some(ExpressionTraversal.stop))
        }
        else { Left(None) }
      }
    }
    ExpressionTraversal.traverse(fn, node.sequent(position))
    formula
  }
}
