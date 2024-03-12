/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */
/**
 * Test CdGL on small example games
 * @author
 *   Brandon Bohrer
 */
package edu.cmu.cs.ls.keymaerax.cdgl

import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.cdgl.TermTactics._
import edu.cmu.cs.ls.keymaerax.tags.UsualTest

@UsualTest
class ExampleGameTests extends TacticTestBase {
  val (va, vd, vx, vy, vk) = (Variable("a"), Variable("d"), Variable("x"), Variable("y"), Variable("k"))
  val cakeTest: Formula = And(LessEqual(Number(0), vx), LessEqual(vx, Number(1)))
  val cake: Program = Compose(
    AssignAny(vx),
    Compose(
      Test(cakeTest),
      Compose(
        Assign(vy, Minus(Number(1), vx)),
        Dual(Choice(Compose(Assign(va, vx), Assign(vd, vy)), Compose(Assign(va, vy), Assign(vd, vx)))),
      ),
    ),
  )

  "cake" should "be safe" in withMathematica { _ =>
    val G = Context(List(Greater(vk, Number(0))))
    val post = Greater(vd, Minus(Number(0.5), vk)) // post
    val Mqe = QE(post, TermTactics.and(6))
    val aLeft = Compose(Assign(va, vx), Assign(vd, vy))
    val aRight = Compose(Assign(va, vy), Assign(vd, vx))
    val M = BComposeI(BRandomI(
      vx,
      BComposeI(BTestI(
        cakeTest,
        BComposeI(BAssignI(
          Assign(vy, Minus(Number(1), vx)),
          BDualI(OrE(
            Compare(vx, Number(0.5), QE(Greater(vk, Number(0)), Hyp(2))),
            DChoiceIR(aLeft, DComposeI(DAssignI(Assign(va, vy), DAssignI(Assign(vd, vx), Mqe)))),
            DChoiceIL(aRight, DComposeI(DAssignI(Assign(va, vx), DAssignI(Assign(vd, vy), Mqe)))),
          )),
        )),
      )),
    ))
    ProofChecker(G, M) shouldBe Box(cake, Greater(vd, Minus(Number(0.5), vk)))
  }

  it should "be live" in withMathematica { _ =>
    val G = Context(List(Greater(vk, Number(0))))
    val post = Greater(va, Minus(Number(0.5), vk)) // post
    val Mqe = QE(post, TermTactics.and(5))
    val McakeTest = QE(cakeTest, and(2))
    val M = DComposeI(DRandomI(
      Assign(vx, Number(0.5)),
      DComposeI(DTestI(
        McakeTest,
        DComposeI(DAssignI(
          Assign(vy, Minus(Number(1), vx)),
          DDualI(BChoiceI(
            BComposeI(BAssignI(Assign(va, vx), BAssignI(Assign(vd, vy), Mqe))),
            BComposeI(BAssignI(Assign(va, vy), BAssignI(Assign(vd, vx), Mqe))),
          )),
        )),
      )),
    ))
    ProofChecker(G, M) shouldBe Diamond(cake, Greater(va, Minus(Number(0.5), vk)))
  }

  val (vv, v0, v1, vt, vA, vD, vg, x0, x2) = (
    Variable("v"),
    Variable("v", Some(0)),
    Variable("v", Some(1)),
    Variable("t"),
    Variable("A"),
    Variable("D"),
    Variable("g"),
    Variable("x", Some(0)),
    Variable("x", Some(2)),
  )
  val pushPullODE: ODESystem = ODESystem(
    DifferentialProduct(AtomicODE(DifferentialSymbol(vx), vv), AtomicODE(DifferentialSymbol(vv), Plus(va, vd)))
  )
  val pushPull: Loop = Loop(Compose(
    Choice(Assign(va, vA), Assign(va, Neg(vA))),
    Compose(Dual(Choice(Assign(vd, vD), Assign(vd, Neg(vD)))), pushPullODE),
  ))

  "push-pull cart" should "be safe" in withMathematica { _ =>
    val j1 = Equal(vA, vD)
    val j2 = Equal(vx, x0)
    val j3 = Equal(vv, Number(0))
    val j = And(And(j1, j2), j3)
    val G = Context(List(j3, j2, j1))
    val subPost = And(
      And(
        Equal(vA, vD),
        Equal(Plus(Plus(Times(Plus(va, vd), Divide(Power(vt, Number(2)), Number(2))), Times(v1, vt)), x2), x0),
      ),
      Equal(Plus(Times(Plus(va, vd), vt), v1), Number(0)),
    )
    val Mqe = QE(subPost, AndI(AndI(AndI(AndI(AndI(Hyp(1), Hyp(2)), Hyp(3)), Hyp(4)), Hyp(5)), Hyp(6)))
    val M = BRepeatI(
      QE(j, and(3)),
      BComposeI(BChoiceI(
        BAssignI(
          Assign(va, vA),
          BComposeI(BDualI(DChoiceIR(Assign(vd, vD), DAssignI(Assign(vd, Neg(vD)), BSolve(pushPullODE, j, Mqe))))),
        ),
        BAssignI(
          Assign(va, Neg(vA)),
          BComposeI(BDualI(DChoiceIL(Assign(vd, Neg(vD)), DAssignI(Assign(vd, vD), BSolve(pushPullODE, j, Mqe))))),
        ),
      )),
      QE(j2, Hyp(0)),
      pushPull.child,
    )
    ProofChecker(G, M) shouldBe Box(pushPull, j2)
  }

  it should "be live" in withMathematica { _ =>
    val post = GreaterEqual(vx, vg)
    val time = Number(1)
    val dist = Minus(vg, vx)
    val ghost = Variable("dist")
    val delta = Times(Minus(vA, vD), Divide(Power(time, Number(2)), Number(2)))
    val j1 = Greater(vA, vD)
    val j2 = GreaterEqual(vv, Number(0))
    val j3 = Greater(vD, Number(0))
    val j = And(And(j1, j2), j3)
    val xSol = Plus(Plus(Times(Plus(va, vd), Divide(Power(time, Number(2)), Number(2))), Times(v0, time)), x0)
    val vSol = Plus(Times(Plus(va, vd), Number(1)), v0)
    val jSub = And(And(j1, GreaterEqual(vSol, Number(0))), j3)
    val jLeft = LessEqual(Minus(vg, vx), Number(0))
    val jLeftSub = LessEqual(Minus(vg, xSol), Number(0))
    val jRight = GreaterEqual(ghost, Plus(Minus(vg, vx), delta))
    val jRightSub = GreaterEqual(ghost, Plus(Minus(vg, xSol), delta))
    val odePost = And(j, Or(jLeft, jRight))
    val G = Context(List(j3, j2, j1))
    val Mmetric = QE(Greater(delta, Number(0)), and(G))
    val metric = ConstantMetric(dist, ghost, Mmetric)
    val Mqe = AndI(QE(jSub, and(4)), OrIR(jLeftSub, QE(jRightSub, and(4))))
    val Mdur: Proof = QE(GreaterEqual(time, Number(0)), Triv())
    val Mdc: Proof = QE(True, Triv())
    val M = DRepeatI(
      metric,
      QE(j, and(G)),
      DComposeI(DChoiceIL(
        Assign(va, Neg(vA)),
        DAssignI(
          Assign(va, vA),
          DComposeI(DDualI(BChoiceI(
            BAssignI(Assign(vd, vD), DSolve(pushPullODE, odePost, Mdur, Mdc, Mqe)),
            BAssignI(Assign(vd, Neg(vD)), DSolve(pushPullODE, odePost, Mdur, Mdc, Mqe)),
          ))),
        ),
      )),
      QE(post, Hyp(0)),
    )
    ProofChecker(G, M) shouldBe Diamond(pushPull, post)
  }

  // @TODO: Implement modular arithmetic and implement Nim example
  "nim" should "be safe" in withMathematica { _ => }

  it should "be live" in withMathematica { _ => }
}
