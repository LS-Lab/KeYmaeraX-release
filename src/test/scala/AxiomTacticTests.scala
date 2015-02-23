import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.PropositionalTacticsImpl._
import edu.cmu.cs.ls.keymaera.tactics._
import edu.cmu.cs.ls.keymaera.tactics.Tactics.PositionTactic
import org.scalatest.{BeforeAndAfterEach, Matchers, FlatSpec}
import testHelper.StringConverter._
import testHelper.SequentFactory._
import testHelper.ProofFactory._

import scala.collection.immutable.List

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
          val aS = Apply(Function("f", None, Real, Real), Anything)
          val aT = Apply(Function("g", None, Real, Real), Anything)
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

  "Derivative axiom in context tactic"  should "use provided renaming tactic" in {
    def dacT: PositionTactic = new DerivativeAxiomInContextTactic(">' derive >", ">' derive >") {
      override def applies(f: Formula) = f match {
        case FormulaDerivative(GreaterThan(_, _, _)) => true
        case _ => false
      }

      import PropositionalTacticsImpl.uniformSubstT
      override def constructInstanceAndSubst(f: Formula) = f match {
        case fd@FormulaDerivative(GreaterThan(sort, s, t)) =>
          // substitution
          val aF = Apply(Function("f", None, sort, sort), Anything)
          val aG = Apply(Function("g", None, sort, sort), Anything)

          val usubst = uniformSubstT(new Substitution(List(SubstitutionPair(aF, s), SubstitutionPair(aG, t))),
            Map(Equiv(fd, GreaterEqual(sort, Derivative(sort, s), Derivative(sort, t))) ->
              Equiv(FormulaDerivative(GreaterThan(sort, aF, aG)),
                GreaterEqual(sort, Derivative(sort, aF), Derivative(sort, aG)))
            ))

          // expected axiom instance
          Some(GreaterEqual(sort, Derivative(sort, s), Derivative(sort, t)), Some(usubst))
        case _ => None
      }
    }

    val tactic = dacT(SuccPosition(0, PosInExpr(1 :: Nil)))
    getProofSequent(tactic, new RootNode(sucSequent("[z':=2;](x>y)'".asFormula))) should be (
      sucSequent("[z':=2;]x'>=y'".asFormula)
    )
  }

  it should "replace arbitrary terms to axiom names" in {
    def dacT: PositionTactic = new DerivativeAxiomInContextTactic(">' derive >", ">' derive >") {
      override def applies(f: Formula) = f match {
        case FormulaDerivative(GreaterThan(_, _, _)) => true
        case _ => false
      }

      override def constructInstanceAndSubst(f: Formula) = f match {
        case fd@FormulaDerivative(GreaterThan(sort, s, t)) =>
          // substitution
          val aF = Apply(Function("f", None, sort, sort), Anything)
          val aG = Apply(Function("g", None, sort, sort), Anything)

          val usubst = uniformSubstT(new Substitution(List(SubstitutionPair(aF, s), SubstitutionPair(aG, t))),
            Map(Equiv(fd, GreaterEqual(sort, Derivative(sort, s), Derivative(sort, t))) ->
              Equiv(FormulaDerivative(GreaterThan(sort, aF, aG)),
                GreaterEqual(sort, Derivative(sort, aF), Derivative(sort, aG)))
            ))

          // expected axiom instance
          Some(GreaterEqual(sort, Derivative(sort, s), Derivative(sort, t)), Some(usubst))
        case _ => None
      }
    }

    val tactic = dacT(SuccPosition(0, PosInExpr(1 :: Nil)))
    getProofSequent(tactic, new RootNode(sucSequent("[z':=2;](x+5>y^2)'".asFormula))) should be (
      sucSequent("[z':=2;](x+5)'>=(y^2)'".asFormula)
    )
  }

  "Propositional context axiom tactic" should "use desired result and renaming tactic constructed by subclasses" in {
    def propT: PositionTactic = new PropositionalInContextTactic("NNF") {
      override def applies(f: Formula) = f match {
        case Not(Not(_)) => true
        case _ => false
      }

      override def constructInstanceAndSubst(f: Formula) = f match {
        case Not(Not(phi)) => Some(phi, None)
        case _ => None
      }
    }

    val tactic = propT(SuccPosition(0, PosInExpr(1 :: Nil)))
    getProofSequent(tactic, new RootNode(sucSequent("[z:=2;](!(!x>0))".asFormula))) should be (
      sucSequent("[z:=2;]x>0".asFormula)
    )

  }
}
