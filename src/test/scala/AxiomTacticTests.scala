import edu.cmu.cs.ls.keymaera.core.ExpressionTraversal.{StopTraversal, ExpressionTraversalFunction, TraverseToPosition}
import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.{PropositionalInContextTactic, DerivativeAxiomInContextTactic, TermAxiomTactic, Tactics}
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

  "Derivative axiom in context tactic" should "use axiom instance and substitution constructed by subclasses" in {
    def dacT: PositionTactic = new DerivativeAxiomInContextTactic(">' derive >", ">' derive >") {
      override def applies(f: Formula) = f match {
        case FormulaDerivative(GreaterThan(_, _, _)) => true
        case _ => false
      }

      override def constructInstanceAndSubst(f: Formula, top: Formula, ax: Formula, pos: Position): Option[(Formula,
          Substitution, Option[PositionTactic])] = f match {
        case FormulaDerivative(GreaterThan(sort, s, t)) =>
          // expected axiom instance
          val desiredResult = GreaterEqual(sort, Derivative(sort, s), Derivative(sort, t))

          // prepare substitution
          val aS = Variable("s", None, Real)
          val aT = Variable("t", None, Real)
          val subsDefs = List(SubstitutionPair(aS, s), SubstitutionPair(aT, t))

          // alpha rename axiom instance

          // bundle result
          Some(desiredResult, Substitution(subsDefs), None)
        case _ => None
      }
    }

    val tactic = dacT(SuccPosition(0, PosInExpr(1 :: Nil)))
    getProofSequent(tactic, new RootNode(sucSequent("[z':=2;](s>t)'".asFormula))) should be (
      sucSequent("[z':=2;]s'>=t'".asFormula)
    )
  }

  "Propositional context axiom tactic" should "use desired result and substitution constructed by subclasses" in {
    def propT: PositionTactic = new PropositionalInContextTactic("NNF", Equiv(PredicateConstant("f"), Not(Not(PredicateConstant("f"))))) {
      override def applies(f: Formula) = f match {
        case Not(Not(_)) => true
        case _ => false
      }

      override def constructInstanceAndSubst(f: Formula, top: Formula, ax: Formula, pos: Position): Option[(Formula,
          Substitution, Option[PositionTactic])] = f match {
        case Not(Not(phi)) =>
          // expected axiom instance
          val desiredResult = phi

          // prepare substitution
          val aF = PredicateConstant("f")
          val subsDefs = List(SubstitutionPair(aF, f))

          // bundle result
          Some(desiredResult, Substitution(subsDefs), None)
        case _ => None
      }
    }

    val tactic = propT(SuccPosition(0, PosInExpr(1 :: Nil)))
    getProofSequent(tactic, new RootNode(sucSequent("[z:=2;](!(!x>0))".asFormula))) should be (
      sucSequent("[z:=2;]x>0".asFormula)
    )

  }
}
