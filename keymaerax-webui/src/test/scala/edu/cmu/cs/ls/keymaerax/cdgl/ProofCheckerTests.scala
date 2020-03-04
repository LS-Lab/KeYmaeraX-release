package edu.cmu.cs.ls.keymaerax.cdgl

import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.PosInExpr
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.UsualTest

@UsualTest
// Syntax:  ?P x:=f x:=*  x'=f&Q  a;b  a++b   a*  a^d
class ProofCheckerTests extends TacticTestBase {
  "hyp" should "check" in withMathematica { _ =>
    val G = Context(List(False))
    val M = Hyp(0)
    ProofChecker(G, M) shouldBe False
  }

  "assign" should "substitute" in withMathematica { _ =>
    val vx = Variable("x")
    val vy = Variable("y")
    val G = Context(List(Equal(vx, Number(1))))
    val M = DAssignI(Assign(vx, Plus(vx, Number(2))), Hyp(0), Some(vy))
    a[ProofException] shouldBe thrownBy(ProofChecker(G, M))
  }

  "box solve" should "solve constant 1D ODE" in withMathematica { _ =>
    val ode = ODESystem(AtomicODE(DifferentialSymbol(Variable("x")),Number(2)))
    val post = GreaterEqual(Variable("x"),Number(0))
    val M = BSolve(ode,post,QE(GreaterEqual(Plus(Times(Number(2),Variable("t")),Variable("x",Some(0))),Number(0)), AndI(Hyp(1),Hyp(2))))
    val G = Context(List(GreaterEqual(Variable("x"),Number(0))))
    ProofChecker(G,M) shouldBe Box(ode,post)
  }

  "QE" should "allow valid first-order arithmetic" in withMathematica { _ =>
    val M = QE(GreaterEqual(Times(Variable("x"),Variable("x")), Number(0)), Triv())
    ProofChecker(Context(List()), M) shouldBe GreaterEqual(Times(Variable("x"),Variable("x")), Number(0))
  }

  "QE" should "reject modal formulas" in withMathematica { _ =>
    val M = QE(Box(Test(GreaterEqual(Variable("x"), Number(0))), True), Triv())
    a[ProofException] shouldBe thrownBy(ProofChecker(Context(List()), M))
  }

  "QE" should "catch invalid formulas" in withMathematica { _ =>
    val M = QE(Greater(Variable("x"), Number(0)), Triv())
    a[ProofException] shouldBe thrownBy(ProofChecker(Context(List()), M))
  }
  "QE" should "use context" in withMathematica { _ =>
    val f = Greater(Variable("x"), Number(0))
    val M = QE(f, Hyp(0))
    ProofChecker(Context(List(f)), M) shouldBe f
  }

}