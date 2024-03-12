/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

/**
 * Tests for CdGL natural deduction proof terms and proof checking.
 * @author
 *   Brandon Bohrer
 */
package edu.cmu.cs.ls.keymaerax.cdgl

import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tags.UsualTest

@UsualTest
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

  "[:*]" should "rename" in withMathematica { _ =>
    val x = Variable("x")
    val p = Equal(x, Number(0))
    val M = BRandomI(x, QE(p, Hyp(0)))
    val G = Context(List(p))
    a[ProofException] shouldBe thrownBy(ProofChecker(G, M))
  }

  "[:*]" should "remember other variables" in withMathematica { _ =>
    val (x, y) = (Variable("x"), Variable("y"))
    val (p1, p2, p3) = (Equal(x, Number(0)), Equal(y, Number(1)), GreaterEqual(Power(y, Number(2)), x))
    val M = BRandomI(y, QE(p3, Hyp(1)))
    val G = Context(List(p2, p1))
    ProofChecker(G, M) shouldBe Box(AssignAny(y), p3)
  }

  "<:*>" should "exist" in withMathematica { _ =>
    val (x, y) = (Variable("x"), Variable("y"))
    val a = Assign(x, Plus(y, Number(1)))
    val M = DRandomI(a, QE(Greater(x, y), Hyp(0)))
    ProofChecker(Context.empty, M) shouldBe Diamond(AssignAny(x), Greater(x, y))
  }

  "<:*>" should "ghost" in withMathematica { _ =>
    val (x, y) = (Variable("x"), Variable("y"))
    val (p1, p2) = (Equal(x, y), Greater(x, y))
    val a = Assign(x, Plus(x, Number(1)))
    val M = DRandomI(a, QE(p2, AndI(Hyp(0), Hyp(1))))
    ProofChecker(Context(List(p1)), M) shouldBe Diamond(AssignAny(x), p2)
  }

  "<:*>" should "ban bad ghosts" in withMathematica { _ =>
    val (x, x0, y) = (Variable("x"), Variable("x", Some(0)), Variable("y"))
    val (p1, p2) = (Equal(x, y), GreaterEqual(x0, y))
    val a1 = Assign(x, Plus(x, Number(1)))
    val M = DRandomI(a1, QE(p2, AndI(Hyp(0), Hyp(1))))
    a[ProofException] shouldBe thrownBy(ProofChecker(Context(List(p1)), M))
  }

  "mon" should "simplify choices" in withMathematica { _ =>
    val (x, x0) = (Variable("x"), Variable("x", Some(0)))
    val (a1, a2) = (Assign(x, Plus(x, Number(1))), Assign(x, Minus(x, Number(1))))
    val a = Compose(a1, a2)
    val (p1, p2) = (Equal(x, x0), Equal(x, Plus(x0, Number(1))))
    val G = Context(List(p1))
    val M = BComposeI(Mon(BAssignI(a1, QE(p2, AndI(Hyp(0), Hyp(1)))), BAssignI(a2, QE(p1, AndI(Hyp(0), Hyp(1))))))
    ProofChecker(G, M) shouldBe Box(a, p1)
  }

  "DC+DW" should "solve double integrator" in withMathematica { _ =>
    val (x, v, a) = (Variable("x"), Variable("v"), Variable("a"))
    val j1 = GreaterEqual(v, Number(0))
    val j2 = GreaterEqual(x, Number(0))
    val dp = DifferentialProduct(
      AtomicODE(DifferentialSymbol(Variable("x")), Variable("v")),
      AtomicODE(DifferentialSymbol(Variable("v")), a),
    )
    val dj1 = ProofChecker.deriveFormula(j1, dp)
    val dj2 = ProofChecker.deriveFormula(j2, dp)
    val ode1 = ODESystem(dp, True)
    val ode2 = ODESystem(dp, And(True, j1))
    val ode3 = ODESystem(dp, And(And(True, j1), j2))
    val post = GreaterEqual(Variable("x"), Number(-1))
    val M = DC(
      DI(ode1, QE(j1, Hyp(1)), QE(dj1, Hyp(3))),
      DC(
        DI(ode2, QE(j2, Hyp(0)), QE(dj2, Hyp(0))),
        DW(ode3, QE(post, AndI(AndI(AndI(Hyp(0), Hyp(1)), Hyp(2)), Hyp(3)))),
      ),
    )
    val G = Context(List(
      GreaterEqual(Variable("x"), Number(0)),
      GreaterEqual(Variable("v"), Number(0)),
      GreaterEqual(Variable("a"), Number(0)),
    ))
    ProofChecker(G, M) shouldBe Box(ode1, post)
  }

  "DG" should "ghost its x's" in withMathematica { _ =>
    val (x, y) = (Variable("x"), Variable("y"))
    val (dx, dy) = (DifferentialSymbol(x), DifferentialSymbol(y))
    val rhs = Plus(Times(Divide(Number(1), Number(2)), y), Number(0))
    val dp1 = AtomicODE(dx, Neg(x))
    val dp2 = DifferentialProduct(AtomicODE(dy, rhs), dp1)
    val post = Greater(x, Number(0))
    val j = Equal(Times(x, Power(y, Number(2))), Number(1))
    val (ode1, ode2, ode3) = (ODESystem(dp1), ODESystem(dp2), ODESystem(dp2, And(True, j)))
    val dj = ProofChecker.deriveFormula(j, dp2)
    val G = Context(List(post))
    val M = DG(
      Assign(y, Power(Divide(Number(1), x), Divide(Number(1), Number(2)))),
      rhs,
      DC(DI(ode2, QE(j, AndI(Hyp(0), Hyp(1))), QE(dj, Triv())), DW(ode3, QE(post, Hyp(0)))),
    )
    ProofChecker(G, M) shouldBe Box(ode1, post)
  }

  "box solve" should "solve constant 1D ODE" in withMathematica { _ =>
    val ode = ODESystem(AtomicODE(DifferentialSymbol(Variable("x")), Number(2)))
    val post = GreaterEqual(Variable("x"), Number(0))
    val M = BSolve(
      ode,
      post,
      QE(GreaterEqual(Plus(Times(Number(2), Variable("t")), Variable("x", Some(0))), Number(0)), AndI(Hyp(1), Hyp(2))),
    )
    val G = Context(List(GreaterEqual(Variable("x"), Number(0))))
    ProofChecker(G, M) shouldBe Box(ode, post)
  }

  "box solve" should "solve double integrator" in withMathematica { _ =>
    val ode = ODESystem(DifferentialProduct(
      AtomicODE(DifferentialSymbol(Variable("x")), Variable("v")),
      AtomicODE(DifferentialSymbol(Variable("v")), Variable("a")),
    ))
    val post = GreaterEqual(Variable("x"), Number(0))
    val M = BSolve(
      ode,
      post,
      QE(
        GreaterEqual(
          Plus(
            Plus(
              Times(Variable("a"), Divide(Power(Variable("t"), Number(2)), Number(2))),
              Times(Variable("v", Some(0)), Variable("t")),
            ),
            Variable("x", Some(0)),
          ),
          Number(0),
        ),
        AndI(Hyp(4), AndI(Hyp(3), AndI(Hyp(2), Hyp(1)))),
      ),
    )
    val G = Context(List(
      GreaterEqual(Variable("x"), Number(0)),
      GreaterEqual(Variable("v"), Number(0)),
      GreaterEqual(Variable("a"), Number(0)),
    ))
    ProofChecker(G, M) shouldBe Box(ode, post)
  }

  "box solve" should "solve reversed double integrator" in withMathematica { _ =>
    val ode = ODESystem(DifferentialProduct(
      AtomicODE(DifferentialSymbol(Variable("v")), Variable("a")),
      AtomicODE(DifferentialSymbol(Variable("x")), Variable("v")),
    ))
    val post = GreaterEqual(Variable("x"), Number(0))
    val M = BSolve(
      ode,
      post,
      QE(
        GreaterEqual(
          Plus(
            Plus(
              Times(Variable("a"), Divide(Power(Variable("t"), Number(2)), Number(2))),
              Times(Variable("v", Some(0)), Variable("t")),
            ),
            Variable("x", Some(0)),
          ),
          Number(0),
        ),
        AndI(Hyp(4), AndI(Hyp(3), AndI(Hyp(2), Hyp(1)))),
      ),
    )
    val G = Context(List(
      GreaterEqual(Variable("x"), Number(0)),
      GreaterEqual(Variable("v"), Number(0)),
      GreaterEqual(Variable("a"), Number(0)),
    ))
    ProofChecker(G, M) shouldBe Box(ode, post)
  }

  "box solve" should "support explicit time variable" in withMathematica { _ =>
    val ode = ODESystem(DifferentialProduct(
      DifferentialProduct(
        AtomicODE(DifferentialSymbol(Variable("t")), Number(1)),
        AtomicODE(DifferentialSymbol(Variable("v")), Variable("a")),
      ),
      AtomicODE(DifferentialSymbol(Variable("x")), Variable("v")),
    ))
    val post = GreaterEqual(Plus(Variable("x"), Variable("t")), Number(0))
    val M = BSolve(
      ode,
      post,
      QE(
        GreaterEqual(
          Plus(
            Plus(
              Plus(
                Times(Variable("a"), Divide(Power(Variable("t"), Number(2)), Number(2))),
                Times(Variable("v", Some(0)), Variable("t")),
              ),
              Variable("x", Some(0)),
            ),
            Variable("t"),
          ),
          Number(0),
        ),
        AndI(Hyp(5), AndI(Hyp(4), AndI(Hyp(3), AndI(Hyp(2), Hyp(1))))),
      ),
    )
    val G = Context(List(
      Equal(Variable("t"), Number(0)),
      GreaterEqual(Variable("x"), Number(0)),
      GreaterEqual(Variable("v"), Number(0)),
      GreaterEqual(Variable("a"), Number(0)),
    ))
    ProofChecker(G, M) shouldBe Box(ode, post)
  }

  "box solve" should "reject unsound time variable reference" in withMathematica { _ =>
    val ode = ODESystem(AtomicODE(DifferentialSymbol(Variable("t")), Number(1)))
    val post = GreaterEqual(Variable("t"), Number(0))
    val M = BSolve(ode, post, QE(GreaterEqual(Variable("t"), Number(0)), Hyp(1)))
    val G = Context(List(Equal(Variable("t"), Number(-2))))
    a[ProofException] shouldBe thrownBy(ProofChecker(G, M))
  }

  "box solve" should "reject non-integrable ODE" in withMathematica { _ =>
    val ode = ODESystem(DifferentialProduct(
      AtomicODE(DifferentialSymbol(Variable("x")), Variable("y")),
      AtomicODE(DifferentialSymbol(Variable("y")), Neg(Variable("x"))),
    ))
    val post = Equal(Plus(Times(Variable("x"), Variable("x")), Times(Variable("y"), Variable("y"))), Number(1))
    val M = BSolve(ode, post, QE(post, AndI(Hyp(1), AndI(Hyp(2), Hyp(3)))))
    val G = Context(List(Equal(Variable("x"), Number(0)), Equal(Variable("y"), Number(1))))
    a[ProofException] shouldBe thrownBy(ProofChecker(G, M))
  }

  "DI" should "prove circle ODE" in withMathematica { _ =>
    val ode = ODESystem(DifferentialProduct(
      AtomicODE(DifferentialSymbol(Variable("x")), Variable("y")),
      AtomicODE(DifferentialSymbol(Variable("y")), Neg(Variable("x"))),
    ))
    val (x, y) = (Variable("x"), Variable("y"))
    val post = Equal(Plus(Times(x, x), Times(y, y)), Number(1))
    val diff = Equal(Plus(Plus(Times(y, x), Times(x, y)), Plus(Times(Neg(x), y), Times(y, Neg(x)))), Number(0))
    val pre = QE(post, AndI(Hyp(0), Hyp(1)))
    val child = QE(diff, AndI(Hyp(0), AndI(Hyp(1), Hyp(2))))
    val M = DI(ode, pre, child)
    val G = Context(List(Equal(Variable("x"), Number(0)), Equal(Variable("y"), Number(1))))
    ProofChecker(G, M) shouldBe Box(ode, post)
  }

  "diamond solve" should "solve constant ODE" in withMathematica { _ =>
    val ode = ODESystem(AtomicODE(DifferentialSymbol(Variable("x")), Number(2)))
    val dur = Number(3)
    val t0 = Number(0)
    val tNow = Plus(t0, dur)
    val post = GreaterEqual(Variable("x"), Number(6))
    val M = DSolve(
      ode,
      post,
      QE(GreaterEqual(dur, Number(0)), Triv()),
      QE(True, Triv()),
      QE(GreaterEqual(Plus(Times(Number(2), dur), Variable("x", Some(0))), Number(6)), Hyp(0)),
    )
    val G = Context(List(GreaterEqual(Variable("x"), Number(0))))
    ProofChecker(G, M) shouldBe Diamond(ode, post)
  }

  "DV" should "vary 1D ODE" in withMathematica { _ =>
    val (x, t, s) = (Variable("x"), Variable("t"), Variable("s"))
    val ode = ODESystem(AtomicODE(DifferentialSymbol(x), Number(1)), LessEqual(x, Number(3)))
    val tode = ODESystem(DifferentialProduct(AtomicODE(DifferentialSymbol(t), Number(1)), ode.ode), ode.constraint)
    val post = GreaterEqual(Times(Number(2), x), Number(5))
    val t0 = Number(0)
    val dr = Number(3)
    val tNow = Minus(dr, t0)
    val v = Number(2)
    val G = Context(List(Equal(x, Number(0))))
    val f = Minus(Times(Number(2), x), Number(5))
    val const = QE(And(GreaterEqual(dr, Number(0)), GreaterEqual(f, Neg(Times(dr, v)))), AndI(Hyp(1), Hyp(0)))
    val G1 = G.rename(t, Variable("t", Some(0))).extend(Equal(t, t0))
    ProofChecker(G1, const) shouldBe And(GreaterEqual(dr, Number(0)), GreaterEqual(f, Neg(Times(dr, v))))

    //   G, t=0 |- B: <t'=1, x'=f&Q>t>=d
    val dsPost = GreaterEqual(Minus(t, t0), dr)
    val dur = DSolve(
      tode,
      dsPost,
      QE(GreaterEqual(dr, Number(0)), Triv()),
      QE(LessEqual(Plus(Times(Number(1), s), Variable("x", Some(0))), Number(3)), AndI(Hyp(2), AndI(Hyp(0), Hyp(1)))),
      QE(GreaterEqual(tNow, dr), Hyp(0)),
    )
    ProofChecker(G.extend(Equal(t, Number(0))), dur) shouldBe Diamond(tode, GreaterEqual(Minus(t, Number(0)), dr))

    // G |- C: [x'=f&Q](f' >= v)
    val xsol = Plus(Times(Number(1), t), Variable("x", Some(0)))
    val fdiff = Minus(Plus(Times(Number(0), x), Times(Number(2), Number(1))), Number(0))
    val fdiffSub = Minus(Plus(Times(Number(0), xsol), Times(Number(2), Number(1))), Number(0))
    val bsPost = GreaterEqual(fdiff, v)
    val rate = BSolve(ode, bsPost, QE(GreaterEqual(fdiffSub, v), AndI(Hyp(1), Hyp(2))))
    ProofChecker(G, rate) shouldBe Box(ode, GreaterEqual(fdiff, Number(2)))

    val Mpost = QE(post, Hyp(0))
    val M = DV(const, dur, rate, Mpost)
    val p = Diamond(ode, post)
    ProofChecker(G, M) shouldBe p
  }

  "[*]I" should "induct" in withMathematica { _ =>
    val x = Variable("x")
    val nz = Number(0)
    val G = Context(List(Equal(x, nz)))
    val f = Divide(x, Number(2))
    val j = GreaterEqual(x, nz)
    val post = GreaterEqual(x, Number(-1))
    val a = Assign(x, f)
    val M = BRepeatI(QE(j, Hyp(0)), BAssignI(a, QE(j, AndI(Hyp(0), Hyp(1)))), QE(post, Hyp(0)), a)
    ProofChecker(G, M) shouldBe Box(Loop(a), post)
  }

  "<*>I" should "induct" in withMathematica { _ =>
    val (x, y, mx) = (Variable("x"), Variable("y"), Variable("met"))
    val metric = ConstantMetric(y, mx, QE(Greater(Number(1), Number(0)), Triv()))
    metric.setFact(Greater(Number(1), Number(0)))
    val G = Context(List(Equal(x, Number(10)), Equal(y, Number(20))))
    val fx = Minus(x, Number(1))
    val fy = Minus(y, Number(2))
    val a1 = Assign(x, fx)
    val a2 = Assign(y, fy)
    val a = Compose(a1, a2)
    val j = Equal(y, Times(x, Number(2)))
    val post = LessEqual(x, Number(0))
    val M = DRepeatI(
      metric,
      QE(j, AndI(Hyp(0), Hyp(1))),
      DComposeI(DAssignI(
        a1,
        DAssignI(
          a2,
          AndI(
            QE(j, AndI(AndI(AndI(Hyp(0), Hyp(1)), Hyp(2)), Hyp(3))),
            OrE(
              TermTactics.compareConstant(Variable("y", Some(0)), Number(1), Number(0.5)),
              // progress
              OrIR(metric.isZero, QE(metric.decreased, AndI(Hyp(1), Hyp(3))))
              // finish
              ,
              OrIL(metric.decreased, QE(metric.isZero, AndI(Hyp(0), Hyp(1)))), // AndI(Hyp(2), AndI(Hyp(3),Hyp(4)))))
            ),
          ),
        ),
      )),
      QE(post, AndI(Hyp(0), Hyp(1))),
    )
    ProofChecker(G, M) shouldBe Diamond(Loop(a), post)
  }

  "<*>I" should "reject ill-founded metric" in withMathematica { _ =>
    val (x, mx) = (Variable("x"), Variable("met"))
    val metric = ConstantMetric(x, mx, QE(Greater(Number(1), Number(0)), Triv()))
    metric.setFact(Greater(Number(1), Number(0)))
    val G = Context(List(Equal(x, Number(10))))
    val fx = Divide(x, Number(2))
    val a1 = Assign(x, fx)
    val j = GreaterEqual(x, Number(0))
    val post = Equal(x, Number(0))
    val M = DRepeatI(
      metric,
      QE(j, Hyp(0)),
      DAssignI(a1, QE(And(j, Or(metric.isZero, metric.decreased)), AndI(Hyp(0), AndI(Hyp(1), Hyp(2))))),
      QE(post, AndI(Hyp(0), Hyp(1))),
    )
    a[ProofException] shouldBe thrownBy(ProofChecker(G, M))
  }

  "QE" should "allow valid first-order arithmetic" in withMathematica { _ =>
    val M = QE(GreaterEqual(Times(Variable("x"), Variable("x")), Number(0)), Triv())
    ProofChecker(Context(List()), M) shouldBe GreaterEqual(Times(Variable("x"), Variable("x")), Number(0))
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

  // Propostional tests
  val (p, q) = (UnitPredicational("P", AnyArg), UnitPredicational("Q", AnyArg))

  "^" should "check" in withMathematica { _ =>
    val G = Context(List(p, q))
    ProofChecker(G, AndI(Hyp(0), Hyp(1))) shouldBe And(p, q)
  }

  "->" should "check" in withMathematica { _ =>
    val G = Context(List(q))
    ProofChecker(G, ImplyI(p, Hyp(1))) shouldBe Imply(p, q)
  }

  "|" should "check" in withMathematica { _ =>
    val G = Context(List(p))
    ProofChecker(G, OrIL(q, Hyp(0))) shouldBe Or(p, q)
  }

  "<->" should "check" in withMathematica { _ =>
    ProofChecker(
      Context(List(Imply(p, q), Imply(q, p))),
      EquivI(Equiv(p, q), ImplyE(Hyp(1), Hyp(0)), ImplyE(Hyp(2), Hyp(0))),
    ) shouldBe Equiv(p, q)
  }

  "forall" should "rename" in withMathematica { _ =>
    val x = Variable("x")
    val p = Equal(x, Number(0))
    val M = ForallI(x, QE(p, Hyp(0)))
    val G = Context(List(p))
    a[ProofException] shouldBe thrownBy(ProofChecker(G, M))
  }

  "forall" should "remember other variables" in withMathematica { _ =>
    val (x, y) = (Variable("x"), Variable("y"))
    val (p1, p2, p3) = (Equal(x, Number(0)), Equal(y, Number(1)), GreaterEqual(Power(y, Number(2)), x))
    val M = ForallI(y, QE(p3, Hyp(1)))
    val G = Context(List(p2, p1))
    ProofChecker(G, M) shouldBe Forall(List(y), p3)
  }

  "exists" should "exist" in withMathematica { _ =>
    val (x, y) = (Variable("x"), Variable("y"))
    val a = Assign(x, Plus(y, Number(1)))
    val M = ExistsI(a, QE(Greater(x, y), Hyp(0)))
    ProofChecker(Context.empty, M) shouldBe Exists(List(x), Greater(x, y))
  }

  "exists" should "ghost" in withMathematica { _ =>
    val (x, y) = (Variable("x"), Variable("y"))
    val (p1, p2) = (Equal(x, y), Greater(x, y))
    val a = Assign(x, Plus(x, Number(1)))
    val M = ExistsI(a, QE(p2, AndI(Hyp(0), Hyp(1))))
    ProofChecker(Context(List(p1)), M) shouldBe Exists(List(x), p2)
  }

  "exists" should "ban bad ghosts" in withMathematica { _ =>
    val (x, x0, y) = (Variable("x"), Variable("x", Some(0)), Variable("y"))
    val (p1, p2) = (Equal(x, y), GreaterEqual(x0, y))
    val a1 = Assign(x, Plus(x, Number(1)))
    val M = DRandomI(a1, QE(p2, AndI(Hyp(0), Hyp(1))))
    a[ProofException] shouldBe thrownBy(ProofChecker(Context(List(p1)), M))
  }
}
