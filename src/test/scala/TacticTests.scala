import edu.cmu.cs.ls.keymaera.core.ProofNode.ProofStep
import edu.cmu.cs.ls.keymaera.tactics.Tactics.Tactic
import edu.cmu.cs.ls.keymaera.tests.TermTests
import org.scalatest._
import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics._
import edu.cmu.cs.ls.keymaera.tools._
import java.math.BigDecimal
import java.io.File
import scala.collection.immutable._

import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary._

import org.scalatest.Tag

object MyTest extends Tag("MyTest")
object USTest extends Tag("USTest")
object BadassignT extends Tag("BadassignT")


class TacticTests extends FlatSpec with Matchers with BeforeAndAfterEach {
  Config.mathlicenses = 1
  Config.maxCPUs = 1

  val mathematicaConfig : Map[String, String] = Map("linkName" -> "/Applications/Mathematica.app/Contents/MacOS/MathKernel")
  var math : Mathematica = null
  var qet : JLinkMathematicaLink = null

  val randomTrials = 10
  val randomFormulaComplexity = 5

  val x = Variable("x", None, Real)
  val y = Variable("y", None, Real)

  val zero = Number(new BigDecimal("0"))

  val one = Number(new BigDecimal("1"))

  val xgeq0 = GreaterEqual(Real, x, zero)
  val xgt0 = GreaterThan(Real, x, zero)
  val xplus1 = Add(Real, x, one)
  val xplus1gtx = GreaterThan(Real, xplus1, x)

  override def beforeEach() = {
    math = new Mathematica
    math.init(mathematicaConfig)
    qet = new JLinkMathematicaLink()
    qet.init(mathematicaConfig("linkName"))
    Tactics.MathematicaScheduler.init(mathematicaConfig)
    Tactics.KeYmaeraScheduler.init(Map())
  }

  override def afterEach() = {
    math.shutdown()
    math = null
    qet.shutdown()
    qet = null
    Tactics.MathematicaScheduler.shutdown()
    Tactics.KeYmaeraScheduler.shutdown()
  }

  def num(n : Integer) = Number(new BigDecimal(n.toString()))
  def snum(n : String) = Number(new BigDecimal(n))

  sealed abstract class ProvabilityStatus {override def toString = getClass.getName}
  object Provable extends ProvabilityStatus {override def toString = "Provable"}
  object NonProvable extends ProvabilityStatus {override def toString = "NonProvable"}
  object UnknownProvability extends ProvabilityStatus {override def toString = "UnknownProvability"}

  /**
   * Run KeYmaera till completion using given tactic for proving given conjecture f.
   *@todo Improve implementation, e.g., by giving an upper time bound
   */
  def prove(f:Formula, tactic:Tactic = TacticLibrary.default, printOnFail: Boolean = true) : ProvabilityStatus = {
    val r = new RootNode(new Sequent(Nil, Vector(), Vector(f)))
    Tactics.KeYmaeraScheduler.dispatch(new TacticWrapper(tactic, r))
    //For all schedulers, no one is working anymore.
    tactic.synchronized {
      tactic.registerCompletionEventListener(_ => tactic.synchronized(tactic.notifyAll))
      tactic.wait
    }

    if(checkClosed(r))
      Provable
    else {
      if (printOnFail) {
        println("Open goals\n" + openGoals(r))
        println("Open proof\n" + TermTests.print(r))
      }
      UnknownProvability
    }
  }

  def prove(f:Formula, printOnFail: Boolean) : ProvabilityStatus = prove(f, TacticLibrary.default, printOnFail)

  def checkClosed(n: ProofNode): Boolean =
    n.children.map((f: ProofStep) =>  f.subgoals.foldLeft(true)(_ && checkClosed(_))).contains(true)

  def openGoals(n: ProofNode): List[Sequent] = {
    if (checkClosed(n)) Nil
    else if (n.children.isEmpty) {
      if (checkClosed(n)) Nil else List(n.sequent)
    } else
      n.children.map((step:ProofStep)=>step.subgoals).flatten.map(openGoals).flatten.foldLeft(List[Sequent]())((l,r)=>l++List(r))
  }

  /**
   * Tactic that applies propositional proof rules exhaustively but only closes by axiom lazyly, i.e. if no other rule applies.
   * @TODO Implement for real. This strategy uses more than propositional steps.
   */
  def lazyPropositional = ((locate(indecisive(true, false, false, true)) | closeT)*)


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


  def unsoundUniformSubstitution(assume : Formula, nonconclude : Formula, subst: Substitution) : ProvabilityStatus = {
    println("Premise\t" + assume.prettyString)
    println("Nonclusion\t" + nonconclude.prettyString)
    println("Usubst\t" + subst)
    val nonconcstat = prove(nonconclude, TacticLibrary.default, false)
    nonconcstat should not be (Provable)
    val assumestat = prove(assume)
    assumestat should be (Provable)
    //@TODO prove(nonconclude) should be (Counterexample) OR: prove(Not(nonconclude)) should be (Satisfiable)
    val exc = evaluating {
      UniformSubstitution(subst, Sequent(Nil, IndexedSeq(), IndexedSeq(assume))).apply(Sequent(Nil, IndexedSeq(), IndexedSeq(nonconclude)))
      //prove(nonconclude, TacticLibrary.uniformSubstT(subst, Map(assume -> nonconclude))) // would not get us the exceptions
      } should produce [SubstitutionClashException]
    println("Expected exception reported: " + exc)
    nonconcstat
  }

  //@TODO Move the subsequent tests to UniformSubstitutionTest.scala
  "Uniform Substitution" should "not apply unsoundly to [y:=5;x:=2]p(x)<->p(2) with .>y for p(.)" taggedAs(USTest) in {
    val x = Variable("x", None, Real)
    val y = Variable("y", None, Real)
    val p1 = Function("p", None, Real, Bool)
    val assume = Equiv(BoxModality(Sequence(Assign(y, Number(5)), Assign(x, Number(2))), ApplyPredicate(p1, x)),
      ApplyPredicate(p1, Number(2)))
    val conclude = Equiv(BoxModality(Sequence(Assign(y, Number(5)), Assign(x, Number(2))), GreaterThan(Real,x,y)),
      GreaterThan(Real, Number(2), y))
    val l = Variable("l", None, Real)
    unsoundUniformSubstitution(assume, conclude,
      Substitution(List(
      new SubstitutionPair(ApplyPredicate(p1,l), GreaterThan(Real,l,y))))) should not be (Provable)

    unsoundUniformSubstitution(assume, conclude,
      Substitution(List(
      new SubstitutionPair(ApplyPredicate(p1,x), GreaterThan(Real,x,y))))) should not be (Provable)

    unsoundUniformSubstitution(assume, conclude,
      Substitution(List(
      new SubstitutionPair(ApplyPredicate(p1,y), GreaterThan(Real,y,y))))) should not be (Provable)
  }

  it should "not apply unsoundly to [y:=5;x:=x^2]p(x+y)<->p(x^2+5) with y>=. for p(.)" taggedAs(USTest) in {
    val x = Variable("x", None, Real)
    val y = Variable("y", None, Real)
    val p1 = Function("p", None, Real, Bool)
    val assume = Equiv(BoxModality(Sequence(Assign(y, Number(5)), Assign(x, Exp(Real,x, Number(2)))), ApplyPredicate(p1, Add(Real,x,y))),
      ApplyPredicate(p1, Add(Real,Exp(Real,x,Number(2)),Number(5))))
    val conclude = Equiv(BoxModality(Sequence(Assign(y, Number(5)), Assign(x, Exp(Real,x, Number(2)))), GreaterEqual(Real,y, Add(Real,x,y))),
        GreaterEqual(Real,y, Add(Real,Exp(Real,x,Number(2)),Number(5))))
    val l = Variable("l", None, Real)
    unsoundUniformSubstitution(assume, conclude,
      Substitution(List(
      new SubstitutionPair(ApplyPredicate(p1,l), GreaterEqual(Real,y,l))))) should not be (Provable)

    unsoundUniformSubstitution(assume, conclude,
      Substitution(List(
      new SubstitutionPair(ApplyPredicate(p1,x), GreaterEqual(Real,y,x))))) should not be (Provable)

    unsoundUniformSubstitution(assume, conclude,
      Substitution(List(
      new SubstitutionPair(ApplyPredicate(p1,y), GreaterEqual(Real,y,y))))) should not be (Provable)
  }

  ignore should "not apply unsoundly to [x:=x+1]p(x)<->p(x+1) with .>0&\\exists x. x<. for p(.)" taggedAs(USTest) in {
    val x = Variable("x", None, Real)
    val y = Variable("y", None, Real)
    val p1 = Function("p", None, Real, Bool)
    val assume = Equiv(BoxModality(Assign(x, Add(Real,x,Number(1))), ApplyPredicate(p1, x)),
      ApplyPredicate(p1, Add(Real,x, Number(1))))
    val conclude = Equiv(BoxModality(Assign(x, Add(Real,x,Number(1))), And(GreaterThan(Real,x,Number(0)),Exists(Seq(x),LessThan(Real,x,x)))),
      And(GreaterThan(Real,Add(Real,x,Number(1)),Number(0)),Exists(Seq(x),LessThan(Real,x,Add(Real,x,Number(1))))))
    val l = Variable("l", None, Real)
    unsoundUniformSubstitution(assume, conclude,
      Substitution(List(
      new SubstitutionPair(ApplyPredicate(p1,l), And(GreaterThan(Real,l,Number(0)),Exists(Seq(x),LessThan(Real,x,l))))))) should not be (Provable)

    unsoundUniformSubstitution(assume, conclude,
      Substitution(List(
      new SubstitutionPair(ApplyPredicate(p1,x), And(GreaterThan(Real,x,Number(0)),Exists(Seq(x),LessThan(Real,x,x))))))) should not be (Provable)

    unsoundUniformSubstitution(assume, conclude,
      Substitution(List(
      new SubstitutionPair(ApplyPredicate(p1,y), And(GreaterThan(Real,y,Number(0)),Exists(Seq(x),LessThan(Real,x,y))))))) should not be (Provable)
  }

  "Uniform Substitution" should "not apply unsoundly to [y:=5;x:=2]q(x)<->q(2) with .>y for q(.)" taggedAs(USTest) in {
    val x = Variable("x", None, Real)
    val y = Variable("y", None, Real)
    val p1 = Function("q", None, Real, Bool)
    val assume = Equiv(BoxModality(Sequence(Assign(y, Number(5)), Assign(x, Number(2))), ApplyPredicate(p1, x)),
      ApplyPredicate(p1, Number(2)))
    val conclude = Equiv(BoxModality(Sequence(Assign(y, Number(5)), Assign(x, Number(2))), GreaterThan(Real,x,y)),
      GreaterThan(Real, Number(2), y))
    val l = Variable("l", None, Real)
    unsoundUniformSubstitution(assume, conclude,
      Substitution(List(
      new SubstitutionPair(ApplyPredicate(p1,l), GreaterThan(Real,l,y))))) should not be (Provable)

    unsoundUniformSubstitution(assume, conclude,
      Substitution(List(
      new SubstitutionPair(ApplyPredicate(p1,x), GreaterThan(Real,x,y))))) should not be (Provable)

    unsoundUniformSubstitution(assume, conclude,
      Substitution(List(
      new SubstitutionPair(ApplyPredicate(p1,y), GreaterThan(Real,y,y))))) should not be (Provable)
  }

  it should "not apply unsoundly to [y:=5;x:=x^2]q(x+y)<->q(x^2+5) with y>=. for q(.)" taggedAs(USTest) in {
    val x = Variable("x", None, Real)
    val y = Variable("y", None, Real)
    val p1 = Function("q", None, Real, Bool)
    val assume = Equiv(BoxModality(Sequence(Assign(y, Number(5)), Assign(x, Exp(Real,x, Number(2)))), ApplyPredicate(p1, Add(Real,x,y))),
      ApplyPredicate(p1, Add(Real,Exp(Real,x,Number(2)),Number(5))))
    val conclude = Equiv(BoxModality(Sequence(Assign(y, Number(5)), Assign(x, Exp(Real,x, Number(2)))), GreaterEqual(Real,y, Add(Real,x,y))),
        GreaterEqual(Real,y, Add(Real,Exp(Real,x,Number(2)),Number(5))))
    val l = Variable("l", None, Real)
    unsoundUniformSubstitution(assume, conclude,
      Substitution(List(
      new SubstitutionPair(ApplyPredicate(p1,l), GreaterEqual(Real,y,l))))) should not be (Provable)

    unsoundUniformSubstitution(assume, conclude,
      Substitution(List(
      new SubstitutionPair(ApplyPredicate(p1,x), GreaterEqual(Real,y,x))))) should not be (Provable)

    unsoundUniformSubstitution(assume, conclude,
      Substitution(List(
      new SubstitutionPair(ApplyPredicate(p1,y), GreaterEqual(Real,y,y))))) should not be (Provable)
  }

  ignore should "not apply unsoundly to [x:=x+1]q(x)<->q(x+1) with .>0&\\exists x. x<. for q(.)" taggedAs(USTest) in {
    val x = Variable("x", None, Real)
    val y = Variable("y", None, Real)
    val p1 = Function("q", None, Real, Bool)
    val assume = Equiv(BoxModality(Assign(x, Add(Real,x,Number(1))), ApplyPredicate(p1, x)),
      ApplyPredicate(p1, Add(Real,x, Number(1))))
    val conclude = Equiv(BoxModality(Assign(x, Add(Real,x,Number(1))), And(GreaterThan(Real,x,Number(0)),Exists(Seq(x),LessThan(Real,x,x)))),
      And(GreaterThan(Real,Add(Real,x,Number(1)),Number(0)),Exists(Seq(x),LessThan(Real,x,Add(Real,x,Number(1))))))
    val l = Variable("l", None, Real)
    unsoundUniformSubstitution(assume, conclude,
      Substitution(List(
      new SubstitutionPair(ApplyPredicate(p1,l), And(GreaterThan(Real,l,Number(0)),Exists(Seq(x),LessThan(Real,x,l))))))) should not be (Provable)

    unsoundUniformSubstitution(assume, conclude,
      Substitution(List(
      new SubstitutionPair(ApplyPredicate(p1,x), And(GreaterThan(Real,x,Number(0)),Exists(Seq(x),LessThan(Real,x,x))))))) should not be (Provable)

    unsoundUniformSubstitution(assume, conclude,
      Substitution(List(
      new SubstitutionPair(ApplyPredicate(p1,y), And(GreaterThan(Real,y,Number(0)),Exists(Seq(x),LessThan(Real,x,y))))))) should not be (Provable)
  }

  "Tactics (default)" should "prove the following properties" in {}

  it should "prove a>0 -> [?x>a]x>0" in {
      val x = Variable("x", None, Real)
      val a = Variable("a", None, Real)
      val formula = Imply(GreaterThan(Real, a,Number(0)),
        BoxModality(Test(GreaterThan(Real, x, a)), GreaterThan(Real, a,Number(0))))
      prove(formula) should be (Provable)
  }

  it should "prove a>0 -> [?x>a++?x>=1]x>0" in {
      val x = Variable("x", None, Real)
      val a = Variable("a", None, Real)
      val formula = Imply(GreaterThan(Real, a,Number(0)),
        BoxModality(Choice(Test(GreaterThan(Real, x, a)), Test(GreaterEqual(Real,x,Number(1)))), GreaterThan(Real, a,Number(0))))
      prove(formula) should be (Provable)
  }

  "Tactics (default)" should "prove a>0 -> [x:=77]a>0" taggedAs(MyTest) in {
    val x = Variable("x", None, Real)
    val a = Variable("a", None, Real)
    val formula = Imply(GreaterThan(Real, a,Number(0)),
      BoxModality(Assign(x, Number(77)), GreaterThan(Real, a,Number(0))))
    prove(formula) should be (Provable)
  }

  it should "prove a>0 -> [x:=x+1]a>0" taggedAs(BadassignT) in {
    val x = Variable("x", None, Real)
    val a = Variable("a", None, Real)
    val formula = Imply(GreaterThan(Real, a,Number(0)),
      BoxModality(Assign(x, Add(Real, x,Number(1))), GreaterThan(Real, a,Number(0))))
    prove(formula) should be (Provable)
  }

  it should "prove z>0 -> [y:=y+1]z>0" in {
    val z = Variable("z", None, Real)
    val y = Variable("y", None, Real)
    val formula = Imply(GreaterThan(Real, z,Number(0)),
      BoxModality(Assign(y, Add(Real, y,Number(1))), GreaterThan(Real, z,Number(0))))
    prove(formula) should be (Provable)
  }

  it should "prove x>0 -> [x:=x+1]x>1" in {
    val x = Variable("x", None, Real)
    val formula = Imply(GreaterThan(Real, x,Number(0)),
      BoxModality(Assign(x, Add(Real, x,Number(1))), GreaterThan(Real, x,Number(1))))
    prove(formula) should be (Provable)
  }

  it should "prove z>0 -> [z:=z+1]z>1" in {
    val x = Variable("z", None, Real)
    val formula = Imply(GreaterThan(Real, x,Number(0)),
      BoxModality(Assign(x, Add(Real, x,Number(1))), GreaterThan(Real, x,Number(1))))
    prove(formula) should be (Provable)
  }

  it should "prove x>0 -> [y:=x; x:=y+1; ](x>y & y>0)" in {
    val x = Variable("x", None, Real)
    val y = Variable("y", None, Real)
    val formula = Imply(GreaterThan(Real, x,Number(0)),
      BoxModality(Sequence(Assign(y, x), Assign(x, Add(Real, y,Number(1)))), And(GreaterThan(Real, x,y), GreaterThan(Real, y, Number(0)))))
    prove(formula) should be (Provable)
  }

  it should "prove x>0 -> [x:=x+1;y:=x-1 ++ y:=x; x:=y+1; ](x>y & y>0)" in {
    val x = Variable("x", None, Real)
    val y = Variable("y", None, Real)
    val formula = Imply(GreaterThan(Real, x,Number(0)),
      BoxModality(Choice(Sequence(Assign(x,Add(Real,x,Number(1))),Assign(y,Subtract(Real,x,Number(1)))),
        Sequence(Assign(y, x), Assign(x, Add(Real, y,Number(1))))), And(GreaterThan(Real, x,y), GreaterThan(Real, y, Number(0)))))
    prove(formula) should be (Provable)
  }

  it should "not prove invalid x>0 -> [x:=x+1;y:=x ++ y:=x; x:=y+1; ](x>y & y>0)" in {
    val x = Variable("x", None, Real)
    val y = Variable("y", None, Real)
    val formula = Imply(GreaterThan(Real, x,Number(0)),
      BoxModality(Choice(Sequence(Assign(x,Add(Real,x,Number(1))),Assign(y,x)),
        Sequence(Assign(y, x), Assign(x, Add(Real, y,Number(1))))), And(GreaterThan(Real, x,y), GreaterThan(Real, y, Number(0)))))
    prove(formula, false) should not be (Provable)
  }



  "Tactics (predicate)" should "prove p(2)->[x:=2]p(x)" in {
    val x = Variable("x", None, Real)
    val y = Variable("y", None, Real)
    val p1 = Function("p", None, Real, Bool)
    val assume = Imply(ApplyPredicate(p1, Number(2)),
      BoxModality(Assign(x, Number(2)), ApplyPredicate(p1, x)))
    prove(assume) should be (Provable)
  }

  it should "prove q(2)->[x:=2]q(x)" in {
      val x = Variable("x", None, Real)
      val y = Variable("y", None, Real)
      val p1 = Function("q", None, Real, Bool)
      val assume = Imply(ApplyPredicate(p1, Number(2)),
        BoxModality(Assign(x, Number(2)), ApplyPredicate(p1, x)))
      prove(assume) should be (Provable)
  }

  it should "prove q(2)->[x:=2]q(x) by assignment rule" in {
      val x = Variable("x", None, Real)
      val y = Variable("y", None, Real)
      val p1 = Function("q", None, Real, Bool)
      val assume = Imply(ApplyPredicate(p1, Number(2)),
        BoxModality(Assign(x, Number(2)), ApplyPredicate(p1, x)))
    fail("uncomment:")
//      prove(assume, step(SuccPosition(0)) & assignment(SuccPosition(0)) & (closeT | locateAnte(eqLeft(false)) | arithmeticT)*) should be (Provable)
  }

  it should "prove q(2)->[x:=2]q(x) by assign axiom" in {
      val x = Variable("x", None, Real)
      val y = Variable("y", None, Real)
      val p1 = Function("q", None, Real, Bool)
      val assume = Imply(ApplyPredicate(p1, Number(2)),
        BoxModality(Assign(x, Number(2)), ApplyPredicate(p1, x)))
    fail("uncomment:")
//      prove(assume, step(SuccPosition(0)) & assignT(SuccPosition(0)) & (closeT | locateAnte(eqLeft(false)) | arithmeticT)*) should be (Provable)
  }

  it should "prove [x:=2]p(x)<->p(2)" in {
    val x = Variable("x", None, Real)
    val y = Variable("y", None, Real)
    val p1 = Function("p", None, Real, Bool)
    val assume = Equiv(BoxModality(Assign(x, Number(2)), ApplyPredicate(p1, x)),
      ApplyPredicate(p1, Number(2)))
    prove(assume) should be (Provable)
  }

  it should "prove [x:=2]q(x)<->q(2)" in {
    val x = Variable("x", None, Real)
    val y = Variable("y", None, Real)
    val p1 = Function("q", None, Real, Bool)
    val assume = Equiv(BoxModality(Assign(x, Number(2)), ApplyPredicate(p1, x)),
      ApplyPredicate(p1, Number(2)))
    prove(assume) should be (Provable)
  }

  it should "prove [y:=5;x:=2]p(x)<->p(2)" in {
    val x = Variable("x", None, Real)
    val y = Variable("y", None, Real)
    val p1 = Function("p", None, Real, Bool)
    val assume = Equiv(BoxModality(Sequence(Assign(y, Number(5)), Assign(x, Number(2))), ApplyPredicate(p1, x)),
      ApplyPredicate(p1, Number(2)))
    prove(assume) should be (Provable)
  }

  it should "prove [y:=5;x:=2]c(x)<->c(2)" in {
    val x = Variable("x", None, Real)
    val y = Variable("y", None, Real)
    val p1 = Function("c", None, Real, Bool)
    val assume = Equiv(BoxModality(Sequence(Assign(y, Number(5)), Assign(x, Number(2))), ApplyPredicate(p1, x)),
      ApplyPredicate(p1, Number(2)))
    prove(assume) should be (Provable)
  }


  def tryTactic(tactic: Tactic): ProofNode = {
    val x = Variable("x", None, Real)
    val y = Variable("y", None, Real)
    val xp1 = Add(Real, x, Number(1))
    val zero = Number(0)
    val r = new RootNode(new Sequent(Nil, Vector(GreaterThan(Real, x, zero), Equals(Real, y, xp1), Imply(And(GreaterThan(Real, x, zero), Equals(Real, y, xp1)), GreaterThan(Real, xp1, zero))), Vector(GreaterThan(Real, xp1, zero))))
    Tactics.KeYmaeraScheduler.dispatch(new TacticWrapper(tactic, r))
    while(!(Tactics.KeYmaeraScheduler.blocked == Tactics.KeYmaeraScheduler.maxThreads && Tactics.KeYmaeraScheduler.prioList.isEmpty)) {
      Thread.sleep(10)
    }
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




  "Tactics (Lemma)" should "learn a lemma from (x > 0 & y > x) -> x >= 0" in {
    val f = TacticLibrary.universalClosure(Imply(And(xgt0, GreaterThan(Real, y, x)), xgeq0))
    qet.qe(f) should be (True)
    LookupLemma.addRealArithLemma(math, f) match {
      case Some((file, id, res)) =>
        (res match {
          case Equiv(_, True) => true
          case _ => false
        }) should be (true)
        val r = new RootNode(new Sequent(Nil, Vector(), Vector()))
        val t = LookupLemma(file,id)
        val nr = r.apply(t).subgoals.head
        nr.sequent.ante(nr.sequent.ante.length-1) should be (res)
      case None => "Lemma creation" should be ("successful")
    }
  }

  it should "learn a lemma from (x > 0 & y = x+1 & y > x) -> (x >= 0 & y > 0)" in {
    val f = TacticLibrary.universalClosure(Imply(And(And(xgt0, Equals(Real, y, xplus1)), GreaterThan(Real, y, x)), And(xgeq0, GreaterThan(Real, y, zero))))
    qet.qe(f) should be (True)
    LookupLemma.addRealArithLemma(math, f) match {
      case Some((file, id, res)) =>
        (res match {
          case Equiv(_, True) => true
          case _ => false
        }) should be (true)
        val r = new RootNode(new Sequent(Nil, Vector(), Vector()))
        val t = LookupLemma(file,id)
        val nr = r.apply(t).subgoals.head
        nr.sequent.ante(nr.sequent.ante.length-1) should be (res)
      case None => "Lemma creation" should be ("successful")
    }
  }

  it should "learn a lemma from (x > 0 & y = x+1 & y > x) -> (y > 0)" in {
    val f = TacticLibrary.universalClosure(Imply(And(And(xgt0, Equals(Real, y, xplus1)), GreaterThan(Real, y, x)), GreaterThan(Real, y, zero)))
    qet.qe(f) should be (True)
    LookupLemma.addRealArithLemma(math, f) match {
      case Some((file, id, res)) =>
        (res match {
          case Equiv(_, True) => true
          case _ => false
        }) should be (true)
        val r = new RootNode(new Sequent(Nil, Vector(), Vector()))
        val t = LookupLemma(file,id)
        val nr = r.apply(t).subgoals.head
        nr.sequent.ante(nr.sequent.ante.length-1) should be (res)
      case None => "Lemma creation" should be ("successful")
    }
  }

  it should "learn a lemma from (x > 0 & y = x+1 & x+1 > x) -> (x+1 > 0)" in {
    val f = TacticLibrary.universalClosure(Imply(And(And(xgt0, Equals(Real, y, xplus1)), GreaterThan(Real, xplus1, x)), GreaterThan(Real, xplus1, zero)))
    qet.qe(f) should be (True)
    LookupLemma.addRealArithLemma(math, f) match {
      case Some((file, id, res)) =>
        (res match {
          case Equiv(_, True) => true
          case _ => false
        }) should be (true)
        val r = new RootNode(new Sequent(Nil, Vector(), Vector()))
        val t = LookupLemma(file,id)
        val nr = r.apply(t).subgoals.head
        nr.sequent.ante(nr.sequent.ante.length-1) should be (res)
      case None => "Lemma creation" should be ("successful")
    }
  }

}
