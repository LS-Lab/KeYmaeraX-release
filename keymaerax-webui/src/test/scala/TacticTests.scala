import edu.cmu.cs.ls.keymaerax.tactics.Tactics.Tactic
import testHelper.ProvabilityTestHelper
import org.scalatest._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tactics._
import edu.cmu.cs.ls.keymaerax.tools._
import java.math.BigDecimal
import testHelper.ProofFactory._
import testHelper.SequentFactory._

import scala.collection.immutable._

import edu.cmu.cs.ls.keymaerax.tactics.TacticLibrary._

import org.scalatest.Tag

import test._

object MyTest extends Tag("MyTest")
object USTest extends Tag("USTest")
object BadassignT extends Tag("BadassignT")


class TacticTests extends FlatSpec with Matchers with BeforeAndAfterEach {

  val helper = new ProvabilityTestHelper((x) => println(x))
  val mathematicaConfig: Map[String, String] = helper.mathematicaConfig

  val randomTrials = 10
  val randomFormulaComplexity = 5

  override def beforeEach() = {
    Tactics.KeYmaeraScheduler = new Interpreter(KeYmaera)
    Tactics.MathematicaScheduler = new Interpreter(new Mathematica)

    Tactics.MathematicaScheduler.init(mathematicaConfig)
    Tactics.KeYmaeraScheduler.init(Map())
  }

  override def afterEach() = {
    Tactics.MathematicaScheduler.shutdown()
    Tactics.KeYmaeraScheduler.shutdown()
    Tactics.MathematicaScheduler = null
    Tactics.KeYmaeraScheduler = null
  }

  def num(n : Integer) = Number(new BigDecimal(n.toString))
  def snum(n : String) = Number(new BigDecimal(n))

  sealed abstract class ProvabilityStatus {override def toString = getClass.getName}
  object Provable extends ProvabilityStatus {override def toString = "Provable"}
  object NonProvable extends ProvabilityStatus {override def toString = "NonProvable"}
  object UnknownProvability extends ProvabilityStatus {override def toString = "UnknownProvability"}

  /**
   * Run KeYmaera till completion using given tactic for proving given conjecture f.
   * TODO Improve implementation, e.g., by giving an upper time bound
   */
  def prove(f: Formula, tactic: Tactic = TacticLibrary.default): ProvabilityStatus = {
    getProofGoals(tactic, new RootNode(sucSequent(f))) match {
      case _: ProofNode | _: List[ProofNode] => UnknownProvability
      case _ => Provable
    }
  }

  def prove(f:Formula) : ProvabilityStatus = prove(f, TacticLibrary.default)

  /**
   * Tactic that applies propositional proof rules exhaustively but only closes by axiom lazyly, i.e. if no other rule applies.
   * TODO Implement for real. This strategy uses more than propositional steps.
   */
  def lazyPropositional = ((locate(indecisive(true, false, false, true)) | closeT)*)

  def unsoundUniformSubstitution(assume : Formula, nonconclude : Formula, subst: USubst,
                                 checkAssumption: Boolean = true): ProvabilityStatus = {
    println(s"Premise    ${assume.prettyString()}")
    println(s"Nonclusion ${nonconclude.prettyString()}")
    println(s"Usubst     $subst")
    //@TODO prove(nonconclude) should be (Counterexample) OR: prove(Not(nonconclude)) should be (Satisfiable)
    a [SubstitutionClashException] should be thrownBy UniformSubstitutionRule(subst,
      Sequent(Nil, IndexedSeq(), IndexedSeq(assume))).apply(Sequent(Nil, IndexedSeq(), IndexedSeq(nonconclude)))
    //prove(nonconclude, TacticLibrary.uniformSubstT(subst, Map(assume -> nonconclude))) // would not get us the exceptions
    val nonconcstat = prove(nonconclude, TacticLibrary.default)
    nonconcstat should not be Provable
    if (checkAssumption) prove(assume) should be (Provable)
    nonconcstat
  }

  "Tactics (propositional)" should "prove A->A for any A" in {
    val tactic = lazyPropositional
    for (i <- 1 to randomTrials) {
      val A = new RandomFormula().nextFormula(randomFormulaComplexity)
      val formula = Imply(A, A)
      prove(formula, tactic) should be (Provable)
    }
  }

  it should "prove A->(B->A) for any A,B" in {
    val tactic = lazyPropositional
    for (i <- 1 to randomTrials) {
      val A = new RandomFormula().nextFormula(randomFormulaComplexity)
      val B = new RandomFormula().nextFormula(randomFormulaComplexity)
      val formula = Imply(A, Imply(B, A))
      prove(formula, tactic) should be (Provable)
    }
  }

  it should "prove (A->(B->C)) <-> ((A&B)->C) for any A,B,C" in {
    val tactic = lazyPropositional
    for (i <- 1 to randomTrials) {
      val A = new RandomFormula().nextFormula(randomFormulaComplexity)
      val B = new RandomFormula().nextFormula(randomFormulaComplexity)
      val C = new RandomFormula().nextFormula(randomFormulaComplexity)
      val formula = Equiv(Imply(A, Imply(B, C)), Imply(And(A,B),C))
      prove(formula, tactic) should be (Provable)
    }
  }

  it should "prove (~A->A) -> A for any A" in {
    val tactic = lazyPropositional
    for (i <- 1 to randomTrials) {
      val A = new RandomFormula().nextFormula(randomFormulaComplexity)
      val formula = Imply(Imply(Not(A),A),A)
      prove(formula, tactic) should be (Provable)
    }
  }

  it should "prove (A->B) && (C->D) |= (A&C)->(B&D) for any A,B,C,D" in {
    val tactic = lazyPropositional
    for (i <- 1 to randomTrials) {
      val A = new RandomFormula().nextFormula(randomFormulaComplexity)
      val B = new RandomFormula().nextFormula(randomFormulaComplexity)
      val C = new RandomFormula().nextFormula(randomFormulaComplexity)
      val D = new RandomFormula().nextFormula(randomFormulaComplexity)
      val formula = Imply(And(Imply(A,B),Imply(C,D)) , Imply(And(A,C),And(B,D)))
      prove(formula, tactic) should be (Provable)
    }
  }

  it should "prove ((A->B)->A)->A for any A,B" in {
    val tactic = lazyPropositional
    for (i <- 1 to randomTrials) {
      val A = new RandomFormula().nextFormula(randomFormulaComplexity)
      val B = new RandomFormula().nextFormula(randomFormulaComplexity)
      val formula = Imply(Imply(Imply(A,B),A),A)
      prove(formula, tactic) should be (Provable)
    }
  }

  "Uniform substitution" should "not apply unsoundly to [y:=5 x:=2]p(x)<->p(2) with .>y for p(.)" taggedAs USTest in {
    val x = Variable("x", None, Real)
    val y = Variable("y", None, Real)
    val p1 = Function("p", None, Real, Bool)
    val assume = Equiv(Box(Compose(Assign(y, Number(5)), Assign(x, Number(2))), PredOf(p1, x)),
      PredOf(p1, Number(2)))
    val conclude = Equiv(Box(Compose(Assign(y, Number(5)), Assign(x, Number(2))), Greater(x,y)),
      Greater( Number(2), y))

    unsoundUniformSubstitution(assume, conclude,
      USubst(List(SubstitutionPair(PredOf(p1,DotTerm), Greater(DotTerm,y)))), checkAssumption = false) should not be Provable
  }

  it should "not apply unsoundly to [y:=5 x:=x^2]p(x+y)<->p(x^2+5) with y>=. for p(.)" taggedAs USTest in {
    val x = Variable("x", None, Real)
    val y = Variable("y", None, Real)
    val p1 = Function("p", None, Real, Bool)
    val assume = Equiv(Box(Compose(Assign(y, Number(5)), Assign(x, Power(x, Number(2)))), PredOf(p1, Plus(x,y))),
      PredOf(p1, Plus(Power(x,Number(2)),Number(5))))
    val conclude = Equiv(Box(Compose(Assign(y, Number(5)), Assign(x, Power(x, Number(2)))), GreaterEqual(y, Plus(x,y))),
        GreaterEqual(y, Plus(Power(x,Number(2)),Number(5))))

    // cannot yet prove assumption automatically
    unsoundUniformSubstitution(assume, conclude,
      USubst(List(SubstitutionPair(PredOf(p1,DotTerm),
        GreaterEqual(y,DotTerm)))), checkAssumption = false) should not be Provable
  }

  ignore should "not apply unsoundly to [x:=x+1]p(x)<->p(x+1) with .>0&\\exists x. x<. for p(.)" taggedAs USTest in {
    val x = Variable("x", None, Real)
    val y = Variable("y", None, Real)
    val p1 = Function("p", None, Real, Bool)
    val assume = Equiv(Box(Assign(x, Plus(x,Number(1))), PredOf(p1, x)),
      PredOf(p1, Plus(x, Number(1))))
    val conclude = Equiv(Box(Assign(x, Plus(x,Number(1))), And(Greater(x,Number(0)),Exists(Seq(x),Less(x,x)))),
      And(Greater(Plus(x,Number(1)),Number(0)),Exists(Seq(x),Less(x,Plus(x,Number(1))))))

    unsoundUniformSubstitution(assume, conclude,
      USubst(List(
      SubstitutionPair(PredOf(p1,DotTerm), And(Greater(DotTerm,Number(0)),Exists(Seq(x),Less(x,DotTerm))))))) should not be Provable
  }

  it should "not apply unsoundly to [y:=5 x:=2]q(x)<->q(2) with .>y for q(.)" taggedAs USTest in {
    val x = Variable("x", None, Real)
    val y = Variable("y", None, Real)
    val p1 = Function("q", None, Real, Bool)
    val assume = Equiv(Box(Compose(Assign(y, Number(5)), Assign(x, Number(2))), PredOf(p1, x)),
      PredOf(p1, Number(2)))
    val conclude = Equiv(Box(Compose(Assign(y, Number(5)), Assign(x, Number(2))), Greater(x,y)),
      Greater( Number(2), y))

    unsoundUniformSubstitution(assume, conclude,
      USubst(List(
      SubstitutionPair(PredOf(p1,DotTerm), Greater(DotTerm,y)))), checkAssumption = false) should not be Provable
  }

  it should "not apply unsoundly to [y:=5 x:=x^2]q(x+y)<->q(x^2+5) with y>=. for q(.)" taggedAs USTest in {
    val x = Variable("x", None, Real)
    val y = Variable("y", None, Real)
    val p1 = Function("q", None, Real, Bool)
    val assume = Equiv(Box(Compose(Assign(y, Number(5)), Assign(x, Power(x, Number(2)))), PredOf(p1, Plus(x,y))),
      PredOf(p1, Plus(Power(x,Number(2)),Number(5))))
    val conclude = Equiv(Box(Compose(Assign(y, Number(5)), Assign(x, Power(x, Number(2)))), GreaterEqual(y, Plus(x,y))),
        GreaterEqual(y, Plus(Power(x,Number(2)),Number(5))))

    unsoundUniformSubstitution(assume, conclude,
      USubst(List(SubstitutionPair(PredOf(p1,DotTerm), GreaterEqual(y,DotTerm)))),
      checkAssumption = false) should not be Provable
  }

  ignore should "not apply unsoundly to [x:=x+1]q(x)<->q(x+1) with .>0&\\exists x. x<. for q(.)" taggedAs USTest in {
    val x = Variable("x", None, Real)
    val y = Variable("y", None, Real)
    val p1 = Function("q", None, Real, Bool)
    val assume = Equiv(Box(Assign(x, Plus(x,Number(1))), PredOf(p1, x)),
      PredOf(p1, Plus(x, Number(1))))
    val conclude = Equiv(Box(Assign(x, Plus(x,Number(1))), And(Greater(x,Number(0)),Exists(Seq(x),Less(x,x)))),
      And(Greater(Plus(x,Number(1)),Number(0)),Exists(Seq(x),Less(x,Plus(x,Number(1))))))

    unsoundUniformSubstitution(assume, conclude,
      USubst(List(
      new SubstitutionPair(PredOf(p1,DotTerm), And(Greater(DotTerm,Number(0)),Exists(Seq(x),Less(x,DotTerm))))))) should not be (Provable)
  }

  "Tactics (default)" should "prove the following properties" in {}

  it should "prove a>0 -> [?x>a]x>0" in {
      val x = Variable("x", None, Real)
      val a = Variable("a", None, Real)
      val formula = Imply(Greater( a,Number(0)),
        Box(Test(Greater( x, a)), Greater( a,Number(0))))
      prove(formula) should be (Provable)
  }

  it should "prove a>0 -> [?x>a++?x>=1]x>0" in {
      val x = Variable("x", None, Real)
      val a = Variable("a", None, Real)
      val formula = Imply(Greater( a,Number(0)),
        Box(Choice(Test(Greater( x, a)), Test(GreaterEqual(x,Number(1)))), Greater( a,Number(0))))
      prove(formula) should be (Provable)
  }

  "Tactics (default)" should "prove a>0 -> [x:=77]a>0" taggedAs(MyTest) in {
    val x = Variable("x", None, Real)
    val a = Variable("a", None, Real)
    val formula = Imply(Greater( a,Number(0)),
      Box(Assign(x, Number(77)), Greater( a,Number(0))))
    prove(formula) should be (Provable)
  }

  it should "prove a>0 -> [x:=x+1]a>0" taggedAs(BadassignT) in {
    val x = Variable("x", None, Real)
    val a = Variable("a", None, Real)
    val formula = Imply(Greater( a,Number(0)),
      Box(Assign(x, Plus( x,Number(1))), Greater( a,Number(0))))
    prove(formula) should be (Provable)
  }

  it should "prove z>0 -> [y:=y+1]z>0" in {
    val z = Variable("z", None, Real)
    val y = Variable("y", None, Real)
    val formula = Imply(Greater( z,Number(0)),
      Box(Assign(y, Plus( y,Number(1))), Greater( z,Number(0))))
    prove(formula) should be (Provable)
  }

  it should "prove x>0 -> [x:=x+1]x>1" in {
    val x = Variable("x", None, Real)
    val formula = Imply(Greater( x,Number(0)),
      Box(Assign(x, Plus( x,Number(1))), Greater( x,Number(1))))
    prove(formula) should be (Provable)
  }

  it should "prove z>0 -> [z:=z+1]z>1" in {
    val x = Variable("z", None, Real)
    val formula = Imply(Greater( x,Number(0)),
      Box(Assign(x, Plus( x,Number(1))), Greater( x,Number(1))))
    prove(formula) should be (Provable)
  }

  it should "prove x>0 -> [y:=x x:=y+1 ](x>y & y>0)" in {
    prove("x>0 -> [y:=x; x:=y+1;](x>y & y>0)".asFormula) should be (Provable)
  }

  it should "prove x>0 -> [x:=x+1 y:=x-1 ++ y:=x x:=y+1 ](x>y & y>0)" in {
    val x = Variable("x", None, Real)
    val y = Variable("y", None, Real)
    val formula = Imply(Greater( x,Number(0)),
      Box(Choice(Compose(Assign(x,Plus(x,Number(1))),Assign(y,Minus(x,Number(1)))),
        Compose(Assign(y, x), Assign(x, Plus( y,Number(1))))), And(Greater( x,y), Greater( y, Number(0)))))
    prove(formula) should be (Provable)
  }

  it should "not prove invalid x>0 -> [x:=x+1;y:=x ++ y:=x; x:=y+1; ](x>y & y>0)" in {
    val x = Variable("x", None, Real)
    val y = Variable("y", None, Real)
    val formula = Imply(Greater( x,Number(0)),
      Box(Choice(Compose(Assign(x,Plus(x,Number(1))),Assign(y,x)),
        Compose(Assign(y, x), Assign(x, Plus( y,Number(1))))), And(Greater( x,y), Greater( y, Number(0)))))
    prove(formula) should not be Provable
  }



  "Tactics (predicate)" should "prove p(2)->[x:=2]p(x)" in {
    val x = Variable("x", None, Real)
    val p1 = Function("p", None, Real, Bool)
    val assume = Imply(PredOf(p1, Number(2)),
      Box(Assign(x, Number(2)), PredOf(p1, x)))
    prove(assume) should be (Provable)
  }

  it should "prove q(2)->[x:=2]q(x)" in {
      val x = Variable("x", None, Real)
      val p1 = Function("q", None, Real, Bool)
      val assume = Imply(PredOf(p1, Number(2)),
        Box(Assign(x, Number(2)), PredOf(p1, x)))
      prove(assume) should be (Provable)
  }

  it should "prove q(2)->[x:=2]q(x) by assign axiom" in {
    import Tactics.repeatT
    val x = Variable("x", None, Real)
    val p1 = Function("q", None, Real, Bool)
    val assume = Imply(PredOf(p1, Number(2)),
      Box(Assign(x, Number(2)), PredOf(p1, x)))
    prove(assume, step(SuccPosition(0)) & assignT(SuccPosition(0)) &
      repeatT(closeT | locateAnte(eqLeft(exhaustive = false)) | arithmeticT)) should be (Provable)
  }

  // TODO unnecessary box assignment equational form results in universal quantifier in succedent
  ignore should "prove [x:=2]p(x)<->p(2)" in {
    val x = Variable("x", None, Real)
    val p1 = Function("p", None, Real, Bool)
    val assume = Equiv(Box(Assign(x, Number(2)), PredOf(p1, x)),
      PredOf(p1, Number(2)))
    prove(assume) should be (Provable)
  }

  // TODO unnecessary box assignment equational form results in universal quantifier in succedent
  ignore should "prove [x:=2]q(x)<->q(2)" in {
    val x = Variable("x", None, Real)
    val y = Variable("y", None, Real)
    val p1 = Function("q", None, Real, Bool)
    val assume = Equiv(Box(Assign(x, Number(2)), PredOf(p1, x)),
      PredOf(p1, Number(2)))
    prove(assume) should be (Provable)
  }

  // TODO unnecessary box assignment equational form results in universal quantifier in succedent
  ignore should "prove [y:=5;x:=2]p(x)<->p(2)" in {
    val x = Variable("x", None, Real)
    val y = Variable("y", None, Real)
    val p1 = Function("p", None, Real, Bool)
    val assume = Equiv(Box(Compose(Assign(y, Number(5)), Assign(x, Number(2))), PredOf(p1, x)),
      PredOf(p1, Number(2)))
    prove(assume) should be (Provable)
  }

  // TODO unnecessary box assignment equational form results in universal quantifier in succedent
  ignore should "prove [y:=5;x:=2]c(x)<->c(2)" in {
    val x = Variable("x", None, Real)
    val y = Variable("y", None, Real)
    val p1 = Function("c", None, Real, Bool)
    val assume = Equiv(Box(Compose(Assign(y, Number(5)), Assign(x, Number(2))), PredOf(p1, x)),
      PredOf(p1, Number(2)))
    prove(assume) should be (Provable)
  }


  def tryTactic(tactic: Tactic): ProofNode = {
    val x = Variable("x", None, Real)
    val y = Variable("y", None, Real)
    val xp1 = Plus( x, Number(1))
    val zero = Number(0)
    val r = new RootNode(new Sequent(Nil, Vector(Greater( x, zero), Equal(y, xp1), Imply(And(Greater( x, zero), Equal(y, xp1)), Greater( xp1, zero))), Vector(Greater( xp1, zero))))
    Tactics.KeYmaeraScheduler.dispatch(new TacticWrapper(tactic, r))
//    while(!(Tactics.KeYmaeraScheduler.blocked == Tactics.KeYmaeraScheduler.maxThreads && Tactics.KeYmaeraScheduler.prioList.isEmpty)) {
//      Thread.sleep(10)
//    }
    r
  }

  def checkSingleAlternative(p: ProofNode): Boolean =
    if(p.children.length > 1) {
      println("found two alternatives " + p.children)
      false
    } else if(p.children.length > 0)
      p.children.head.subgoals.isEmpty || p.children.head.subgoals.foldLeft(false)((a: Boolean, b: ProofNode) => a || checkSingleAlternative(b))
    else
      true

  "Tactics (weakSeqT)*" should "produce a proof with no alternatives" in {
    val tactic = ((AxiomCloseT ~ locateSucc(indecisive(true, false, true)) ~ locateAnte(indecisive(true, false, true, true)))*)
    val r = tryTactic(tactic)
    require(checkSingleAlternative(r) == true, "The proof should not have alternatives")
  }

  "Tactics (eitherT)*" should "produce a proof with no alternatives" in {
    val tactic = ((AxiomCloseT | locateSucc(indecisive(true, false, true)) | locateAnte(indecisive(true, false, true, true)))*)
    val r = tryTactic(tactic)
    require(checkSingleAlternative(r) == true, "The proof should not have alternatives")
  }

}
