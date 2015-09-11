package testHelper

/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
import edu.cmu.cs.ls.keymaerax.tactics.ExpressionTraversal
import edu.cmu.cs.ls.keymaerax.tactics.ExpressionTraversal.ExpressionTraversalFunction
import edu.cmu.cs.ls.keymaerax.tactics.Position
import edu.cmu.cs.ls.keymaerax.tactics.PosInExpr
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tactics.{ProofNode, Interpreter, Tactics}
import edu.cmu.cs.ls.keymaerax.tools.{Mathematica, KeYmaera}
import testHelper.ProvabilityTestHelper
import org.scalatest.{BeforeAndAfterEach, Matchers, FlatSpec}

/**
 * Created by nfulton on 2/5/15.
 */
trait TacticTestSuite extends FlatSpec with Matchers with BeforeAndAfterEach {
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Boilerplate
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  val helper = new ProvabilityTestHelper(x=>println(x))

  val mathematicaConfig = helper.mathematicaConfig

  override def beforeEach() = {
    Tactics.KeYmaeraScheduler = new Interpreter(KeYmaera)
    Tactics.MathematicaScheduler = new Interpreter(new Mathematica)

    Tactics.KeYmaeraScheduler.init(Map())
    Tactics.MathematicaScheduler.init(mathematicaConfig)
  }

  override def afterEach() = {
    if (Tactics.KeYmaeraScheduler != null) {
      Tactics.KeYmaeraScheduler.shutdown()
      Tactics.KeYmaeraScheduler = null
    }
    if (Tactics.MathematicaScheduler != null) {
      Tactics.MathematicaScheduler.shutdown()
      Tactics.MathematicaScheduler = null
    }
  }

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