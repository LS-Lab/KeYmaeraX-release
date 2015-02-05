import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.{TermAxiomTactic, Tactics}
import edu.cmu.cs.ls.keymaera.tactics.Tactics.PositionTactic
import org.scalatest.{BeforeAndAfterEach, Matchers, FlatSpec}
import testHelper.StringConverter._
import testHelper.SequentFactory._
import testHelper.ProofFactory._

/**
 * Created by smitsch on 2/5/15.
 * @author Stefan Mitsch
 */
class AxiomTacticTests extends FlatSpec with Matchers with BeforeAndAfterEach {

  override def beforeEach() = {
    Tactics.KeYmaeraScheduler.init(Map())
  }

  override def afterEach() = {
    Tactics.KeYmaeraScheduler.shutdown()
  }

  "Term axiom tactic" should "use axiom instance and substitution constructed by subclasses" in {
    def termAxiomT: PositionTactic = new TermAxiomTactic("+' derive sum", "+' derive sum") {
      override def applies(t: Term) = t match {
        case Derivative(sort, Add(sort2, _, _)) => sort == sort2
        case _ => false
      }

      override def constructInstanceAndSubst(e: Term, ax: Formula, pos: Position): Option[(Formula, Substitution)] = e match {
        case Derivative(sort, Add(sort2, s, t)) if sort == sort2 =>
          // expected axiom instance
          val expected = Add(sort, Derivative(sort, s), Derivative(sort, t))
          val axiomInstance = Equals(sort, e, expected)
          // prepare substitution
          val aS = Variable("s", None, Real)
          val aT = Variable("t", None, Real)
          val subsDefs = List(SubstitutionPair(aS, s), SubstitutionPair(aT, t))
          // bundle result
          Some(axiomInstance, Substitution(subsDefs))
        case _ => None
      }
    }

    val tactic = termAxiomT(SuccPosition(0, PosInExpr(1 :: 0 :: Nil)))
    getProofSequent(tactic, new RootNode(sucSequent("[z:=2;](x+y)'>=0".asFormula))) should be (
      sucSequent("[z:=2;]x'+y'>=0".asFormula)
    )
  }
}
