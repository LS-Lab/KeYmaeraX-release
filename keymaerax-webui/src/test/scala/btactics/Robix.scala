/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.ArithmeticSimplification._
import edu.cmu.cs.ls.keymaerax.btactics.arithmetic.speculative.ArithmeticSpeculativeSimplification._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.SlowTest
import testHelper.ParserFactory._
import edu.cmu.cs.ls.keymaerax.btactics.DebuggingTactics.{print, printIndexed}
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXProblemParser

import scala.language.postfixOps

import org.scalatest.LoneElement._

/**
 * Robix test cases.
 *
 * @author Stefan Mitsch
 * @author Ran Ji
 */
@SlowTest
class Robix extends TacticTestBase {

  "Static Safety" should "be provable" in withMathematica { tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/robix/staticsafetyabs.key"))

    val invariant = """v >= 0
                      | & dx^2+dy^2 = 1
                      | & r != 0
                      | & (abs(x-xo) > v^2 / (2*B())
                      |  | abs(y-yo) > v^2 / (2*B()))""".stripMargin.asFormula

    def di(a: String): DependentPositionTactic = diffInvariant(
      "t>=0".asFormula,
      "dx^2 + dy^2 = 1".asFormula,
      s"v = old(v) + $a*t".asFormula,
      s"-t * (v - $a/2*t) <= x - old(x) & x - old(x) <= t * (v - $a/2*t)".asFormula,
      s"-t * (v - $a/2*t) <= y - old(y) & y - old(y) <= t * (v - $a/2*t)".asFormula)

    val dw: BelleExpr = (andL('L)*) & print("Before diffWeaken") & dW(1) & print("After diffWeaken")

    def accArithTactic: BelleExpr = (alphaRule*) & printIndexed("Before replaceTransform") &
      replaceTransform("ep()".asTerm, "t".asTerm)(-8) & speculativeQE & print("Proved acc arithmetic")

    val tactic = implyR('_) & (andL('_)*) & loop(invariant)('R) <(
      /* base case */ print("Base case...") & speculativeQE & print("Base case done"),
      /* use case */ print("Use case...") & speculativeQE & print("Use case done"),
      /* induction step */ print("Induction step") & unfoldProgramNormalize & printIndexed("After normalize") <(
      print("Braking branch") & di("-B()")(1) & dw & prop & onAll(speculativeQE) & print("Braking branch done"),
      print("Stopped branch") & di("0")(1) & dw & prop & onAll(speculativeQE) & print("Stopped branch done"),
      print("Acceleration branch") & hideL('L, "abs(x-xo_0)>v^2/(2*B())|abs(y-yo_0)>v^2/(2*B())".asFormula) &
        di("a")(1) & dw & prop <(
        hideFactsAbout("y", "yo") & accArithTactic,
        hideFactsAbout("x", "xo") & accArithTactic
        ) & print("Acceleration branch done")
      ) & print("Induction step done")
      ) & print("Proof done")
    proveBy(s, tactic) shouldBe 'proved
  }

  it should "be provable with only braking for a stationary obstacle" in withMathematica { qeTool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/robix/staticsafetyabs_curvestraight_curvature_brakingonly.kyx"))

    val invariant =
      """v >= 0
        | & dx^2+dy^2 = 1
        | & (abs(x-xo) > v^2 / (2*B())
        |   |abs(y-yo) > v^2 / (2*B()) )""".stripMargin.asFormula

    val augmentTime = HilbertCalculus.DGC("t".asVariable, Number(1))(1) & DLBySubst.assignbExists(Number(0))(1) &
      assignb(1)

    def di(a: String): DependentPositionTactic = diffInvariant(
      //@todo allow old(t) in multiple formulas
      "t>=old(t)".asFormula,
      "dx^2 + dy^2 = 1".asFormula,
      s"v = old(v) + $a*(t-t_0)".asFormula,
      s"-(t-t_0) * (v - $a/2*(t-t_0)) <= x - old(x) & x - old(x) <= (t-t_0) * (v - $a/2*(t-t_0))".asFormula,
      s"-(t-t_0) * (v - $a/2*(t-t_0)) <= y - old(y) & y - old(y) <= (t-t_0) * (v - $a/2*(t-t_0))".asFormula)

    val dw: BelleExpr = (andL('L)*) & print("Before diffWeaken") & dW(1) & print("After diffWeaken")

    val tactic = implyR('_) & (andL('_)*) & loop(invariant)('R) <(
      /* base case */ print("Base case...") & speculativeQE & print("Base case done"),
      /* use case */ print("Use case...") & speculativeQE & print("Use case done"),
      /* induction step */ print("Induction step") & unfoldProgramNormalize & printIndexed("After normalize") &
      print("Braking") & augmentTime & di("-B()")(1) & dw & prop & onAll(speculativeQE) &
      print("Induction step done")
    ) & print("Proof done")
    proveBy(s, tactic) shouldBe 'proved
  }

  it should "synthesize a controller monitor" in withMathematica { tool =>
    val in = getClass.getResourceAsStream("/examples/casestudies/robix/staticsafetyabs_curvestraight_curvature_brakingonly.kyx")
    val model = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
    val (modelplexInput, assumptions) = ModelPlex.createMonitorSpecificationConjecture(model,
      Variable("x"), Variable("y"), Variable("v"), Variable("a"), Variable("dx"), Variable("dy"), Variable("w"))

    val foResult = proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1) &
      ModelPlex.optimizationOneWithSearch(Some(tool), assumptions)(1) & SimplifierV2.simpTac(1))

    foResult.subgoals.loneElement shouldBe "==> v>=0&xpost=x&ypost=y&vpost=v&apost=-B()&dxpost=dx&dypost=dy&wpost=w".asSequent
  }

  "Passive Safety" should "be provable" in withMathematica { qeTool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/robix/passivesafetyabs.key"))

    val invariant = """v >= 0
                      | & dx^2+dy^2 = 1
                      | & r != 0
                      | & (v = 0 | abs(x-xo) > v^2 / (2*B()) + V()*(v/B())
                      |          | abs(y-yo) > v^2 / (2*B()) + V()*(v/B()))""".stripMargin.asFormula

    def di(a: String): DependentPositionTactic = diffInvariant(
      "t>=0".asFormula,
      "dx^2 + dy^2 = 1".asFormula,
      s"v = old(v) + $a*t".asFormula,
      s"-t * (v - $a/2*t) <= x - old(x) & x - old(x) <= t * (v - $a/2*t)".asFormula,
      s"-t * (v - $a/2*t) <= y - old(y) & y - old(y) <= t * (v - $a/2*t)".asFormula,
      "-t * V() <= xo - old(xo) & xo - old(xo) <= t * V()".asFormula,
      "-t * V() <= yo - old(yo) & yo - old(yo) <= t * V()".asFormula)

    val dw: BelleExpr = (andL('L)*) & print("Before diffWeaken") & dW(1) & print("After diffWeaken")

    def accArithTactic: BelleExpr = (alphaRule*) & printIndexed("Before replaceTransform") &
      //@todo auto-transform
      replaceTransform("ep()".asTerm, "t".asTerm)(-10) & speculativeQE & print("Proved acc arithmetic")

    val tactic = implyR('_) & (andL('_)*) & loop(invariant)('R) <(
      /* base case */ print("Base case...") & speculativeQE & print("Base case done"),
      /* use case */ print("Use case...") & speculativeQE & print("Use case done"),
      /* induction step */ print("Induction step") & unfoldProgramNormalize & printIndexed("After normalize") <(
        print("Braking branch") & di("-B()")(1) & dw & prop & onAll(speculativeQE) & print("Braking branch done"),
        print("Stopped branch") & di("0")(1) & dw & prop & onAll(speculativeQE) & print("Stopped branch done"),
        print("Acceleration branch") & hideL('L, "v=0|abs(x-xo_0)>v^2/(2*B())+V()*(v/B())|abs(y-yo_0)>v^2/(2*B())+V()*(v/B())".asFormula) &
          di("a")(1) & dw & prop & onAll(hideFactsAbout("dxo", "dyo") partial) <(
            hideFactsAbout("y", "yo") & accArithTactic,
            hideFactsAbout("x", "xo") & accArithTactic
          ) & print("Acceleration branch done")
        ) & print("Induction step done")
      ) & print("Proof done")
    proveBy(s, tactic) shouldBe 'proved
  }

  // todo: robix proof with let inv=bla in ...
  // todo: also try to get distance letified...

  it should "prove just the acceleration x arithmetic" in withMathematica { qeTool =>
    val accArith = "A()>=0 & B()>0 & V()>=0 & ep()>0 & v_0>=0 & -B()<=a & a<=A() & abs(x_0-xo_0)>v_0^2/(2*B())+V()*v_0/B()+(A()/B()+1)*(A()/2*ep()^2+ep()*(v_0+V())) & -t*V()<=xo-xo_0 & xo-xo_0<=t*V() & v=v_0+a*t & -t*(v-a/2*t)<=x-x_0 & x-x_0<=t*(v-a/2*t) & t>=0 & t<=ep() & v>=0 -> v=0|abs(x-xo)>v^2/(2*B())+V()*(v/B())".asFormula

    val tactic = (alphaRule*) & replaceTransform("ep()".asTerm, "t".asTerm)('L, "abs(x_0-xo_0)>v_0^2/(2*B())+V()*v_0/B()+(A()/B()+1)*(A()/2*ep()^2+ep()*(v_0+V()))".asFormula) &
      hideR('R, "v=0".asFormula) & hideL('L, "t<=ep()".asFormula) & hideL('L, "ep()>0".asFormula) & hideL('L, "-B()<=a".asFormula) & speculativeQE & done
//@note manual variant of speculativeQE above
//      abs(1, 0::Nil) & abs(-7, 0::Nil) & orL(-16) & onAll(orL(-15) partial) &
//      onAll((andL('_)*) partial) & onAll((exhaustiveEqL2R(hide=true)('L)*) partial) <(
//        hideL(-11, "x-x_0<=t*(v_0+a*t-a/2*t)".asFormula) & hideL(-8, "-t*V()<=xo-xo_0".asFormula) & QE,
//        hideR(1) & QE,
//        hideR(1) & QE,
//        hideL(-10, "-t*(v_0+a*t-a/2*t)<=x-x_0".asFormula) & hideL(-9, "xo-xo_0<=t*V()".asFormula) & QE
//        )

    proveBy(accArith, tactic) shouldBe 'proved
  }

  it should "prove just the acceleration y arithmetic" in withMathematica { qeTool =>
    val accArith = "A()>=0&B()>0&V()>=0&ep()>0&v_0>=0&-B()<=a&a<=A()&abs(y_0-yo_0)>v_0^2/(2*B())+V()*v_0/B()+(A()/B()+1)*(A()/2*ep()^2+ep()*(v_0+V()))&-t*V()<=yo-yo_0&yo-yo_0<=t*V()&-t*(v-a/2*t)<=y-y_0&y-y_0<=t*(v-a/2*t)&v=v_0+a*t&t>=0&t<=ep()&v>=0->v=0|abs(y-yo)>v^2/(2*B())+V()*(v/B())".asFormula

    val tactic = (alphaRule*) &
      replaceTransform("ep()".asTerm, "t".asTerm)('L, "abs(y_0-yo_0)>v_0^2/(2*B())+V()*v_0/B()+(A()/B()+1)*(A()/2*ep()^2+ep()*(v_0+V()))".asFormula) &
      hideR('R, "v=0".asFormula) & hideL('L, "t<=ep()".asFormula) & hideL('L, "ep()>0".asFormula) & hideL('L, "-B()<=a".asFormula) & speculativeQE & done
//@note manual variant of speculativeQE above
//      abs(1, 0::Nil) & abs(-7, 0::Nil) & orL(-16) & onAll(orL(-15) partial) &
//      onAll((andL('_)*) partial) & onAll((exhaustiveEqL2R(hide=true)('L)*) partial) <(
//        hideL(-11, "y-y_0<=t*(v_0+a*t-a/2*t)".asFormula) & hideL(-8, "-t*V()<=yo-yo_0".asFormula) & QE,
//        hideR(1) & QE,
//        hideR(1) & QE,
//        hideL(-10, "-t*(v_0+a*t-a/2*t)<=y-y_0".asFormula) & hideL(-9, "yo-yo_0<=t*V()".asFormula) & QE
//        )

    proveBy(accArith, tactic) shouldBe 'proved
  }

  "Passive Safety straight and curve" should "be provable" in withMathematica { qeTool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/robix/passivesafetyabs_curvestraight.key"))

    val invariant = """v >= 0
                      | & dx^2+dy^2 = 1
                      | & r != 0
                      | & (v = 0 | abs(x-xo) > v^2 / (2*B()) + V()*(v/B())
                      |          | abs(y-yo) > v^2 / (2*B()) + V()*(v/B()))""".stripMargin.asFormula

    def di(a: String): DependentPositionTactic = diffInvariant(
      "t>=0".asFormula,
      "dx^2 + dy^2 = 1".asFormula,
      s"v = old(v) + $a*t".asFormula,
      s"-t * (v - $a/2*t) <= x - old(x) & x - old(x) <= t * (v - $a/2*t)".asFormula,
      s"-t * (v - $a/2*t) <= y - old(y) & y - old(y) <= t * (v - $a/2*t)".asFormula,
      "-t * V() <= xo - old(xo) & xo - old(xo) <= t * V()".asFormula,
      "-t * V() <= yo - old(yo) & yo - old(yo) <= t * V()".asFormula)

    val dw: BelleExpr = (andL('_)*) & print("Before diffWeaken") & dW(1) & print("After diffWeaken")

    val hideIrrelevantAssumptions: BelleExpr =
      onAll(
        hideL('L, "dx^2+dy^2=1".asFormula) &
        hideL('L, "r!=0".asFormula) &
        hideL('L, "dxo^2+dyo^2<=V()^2".asFormula))

    val brakeStoppedArith: BelleExpr =
      hideIrrelevantAssumptions <(
        hideR('R, "abs(y-yo)>v^2/(2*B())+V()*(v/B())".asFormula) & hideR('R, "abs(x-xo)>v^2/(2*B())+V()*(v/B())".asFormula) & QE,
        hideR('R, "abs(y-yo)>v^2/(2*B())+V()*(v/B())".asFormula) & QE,
        hideR('R, "abs(x-xo)>v^2/(2*B())+V()*(v/B())".asFormula) & QE)

    def accArithTactic(fml: Formula): BelleExpr = implyR(1) & (andL('L)*) & cutL(fml)(AntePos(4)) <(
      hideL('L, "t<=ep()".asFormula) & hideL('L, "ep()>0".asFormula) & hideL('L, "-B()<=a".asFormula) & speculativeQE & done
      ,
      hideR('Rlike, "abs(x-xo)>v^2/(2*B())+V()*(v/B())".asFormula) &
      //@note abbreviate and hide terms over x and xo so that speculativeQE can find lots of formulas to hide
      EqualityTactics.abbrv("abs(x_0-xo_0)".asTerm, Some("absXXo".asVariable)) & hideL('Llast) &
      speculativeQE & done
      ) & print("Proved acc arithmetic: " + fml)

    val accArithX = "A()>=0&B()>0&V()>=0&ep()>0&abs(x_0-xo_0)>v_0^2/(2*B())+V()*v_0/B()+(A()/B()+1)*(A()/2*ep()^2+ep()*(v_0+V()))&v_0>=0&-B()<=a&a<=A()&-t*V()<=xo-xo_0&xo-xo_0<=t*V()&-t*(v-a/2*t)<=x-x_0&x-x_0<=t*(v-a/2*t)&v=v_0+a*t&t>=0&t<=ep()&v>=0->abs(x-xo)>v^2/(2*B())+V()*(v/B())".asFormula
    val accArithXLemma = proveBy(accArithX, accArithTactic("abs(x_0-xo_0)>v_0^2/(2*B())+V()*v_0/B()+(A()/B()+1)*(A()/2*t^2+t*(v_0+V()))".asFormula))
    accArithXLemma shouldBe 'proved

    val accArithY = "A()>=0&B()>0&V()>=0&ep()>0&abs(y_0-yo_0)>v_0^2/(2*B())+V()*v_0/B()+(A()/B()+1)*(A()/2*ep()^2+ep()*(v_0+V()))&v_0>=0&-B()<=a&a<=A()&-t*V()<=yo-yo_0&yo-yo_0<=t*V()&-t*(v-a/2*t)<=y-y_0&y-y_0<=t*(v-a/2*t)&v=v_0+a*t&t>=0&t<=ep()&v>=0->abs(y-yo)>v^2/(2*B())+V()*(v/B())".asFormula
    val accArithYLemma = proveBy(accArithY, accArithTactic("abs(y_0-yo_0)>v_0^2/(2*B())+V()*v_0/B()+(A()/B()+1)*(A()/2*t^2+t*(v_0+V()))".asFormula))
    accArithYLemma shouldBe 'proved

    val tactic = implyR('_) & (andL('_)*) & loop(invariant)('R) <(
      /* base case */ QE & print("Base case done"),
      /* use case */ QE & print("Use case done"),
      /* induction step */ chase(1) & allR(1)*2 & implyR(1) & andR(1) <(
        print("Braking branch") & allR(1) & implyR(1) & andR(1) <(
          implyR(1) & di("-B()")(1) & dw & prop & brakeStoppedArith & print("Braking branch 1 done"),
          implyR(1) & di("-B()")(1) & dw & prop & brakeStoppedArith & print("Braking branch 2 done")
          ),
        print("Free drive branch") & andR(1) <(
          (implyR(1) & allR(1))*2 & implyR(1) & andR(1) <(
            implyR(1) & (andL('L)*) & hideL('L, "v=0|abs(x-xo)>v^2/(2*B())+V()*(v/B())|abs(y-yo)>v^2/(2*B())+V()*(v/B())".asFormula) & di("0")(1) & dw & prop
              & hideIrrelevantAssumptions & hideR('R, "abs(y-yo)>v^2/(2*B())+V()*(v/B())".asFormula) & hideR('R, "abs(x-xo)>v^2/(2*B())+V()*(v/B())".asFormula) & QE & print("Free drive branch 1 done"),
            implyR(1) & (andL('L)*) & hideL('L, "v=0|abs(x-xo)>v^2/(2*B())+V()*(v/B())|abs(y-yo)>v^2/(2*B())+V()*(v/B())".asFormula) & di("-B()")(1) & dw & prop
              & hideIrrelevantAssumptions & hideR('R, "abs(y-yo)>v^2/(2*B())+V()*(v/B())".asFormula) & hideR('R, "abs(x-xo)>v^2/(2*B())+V()*(v/B())".asFormula) & QE & print("Free drive branch 2 done")
            ),
            allR (1) & implyR(1) & andR(1) <(
              allR(1) & implyR(1) & allR(1)*2 & implyR(1) & allR(1) & implyR(1) & andR(1) <(
                implyR(1) & (andL('L)*) & hideL('L, "v=0|abs(x-xo_0)>v^2/(2*B())+V()*(v/B())|abs(y-yo_0)>v^2/(2*B())+V()*(v/B())".asFormula) & di("a")(1) & dw & prop
                  & hideIrrelevantAssumptions <(
                    hideR('R, "abs(y-yo)>v^2/(2*B())+V()*(v/B())".asFormula) & hideR('R, "v=0".asFormula)
                      & hideL('L, "dx^2+dy^2=1".asFormula)
                      & hideL('L, "y-y_0<=t*(v-a/2*t)".asFormula) & hideL('L, "-t*(v-a/2*t)<=y-y_0".asFormula)
                      & hideL('L, "yo-yo_0<=t*V()".asFormula) & hideL('L, "-t*V()<=yo-yo_0".asFormula)
                      & hideL('L, "w=0".asFormula) & hideL('L, "w=0".asFormula) & print("Free drive branch 3 lemma prep")
                      & PropositionalTactics.toSingleFormula & by(accArithXLemma) & print("Free drive branch 3 done"),
                    hideR('R, "abs(x-xo)>v^2/(2*B())+V()*(v/B())".asFormula) & hideR('R, "v=0".asFormula)
                      & hideL('L, "dx^2+dy^2=1".asFormula)
                      & hideL('L, "x-x_0<=t*(v-a/2*t)".asFormula) & hideL('L, "-t*(v-a/2*t)<=x-x_0".asFormula)
                      & hideL('L, "xo-xo_0<=t*V()".asFormula) & hideL('L, "-t*V()<=xo-xo_0".asFormula)
                      & hideL('L, "w=0".asFormula) & hideL('L, "w=0".asFormula) & print("Free drive branch 4 lemma prep")
                      & PropositionalTactics.toSingleFormula & by(accArithYLemma) & print("Free drive branch 4 done")
                  ),
                implyR(1) & (andL('_)*) & cutL("!w=0".asFormula)(AntePos(8)) <(
                    notL('L, "!w=0".asFormula) & closeId  & print("Free drive branch 5 done"),
                    hideR('R, "[{x'=v*dx,y'=v*dy,dx'=-w*dy,dy'=w*dx,v'=a,w'=a/r,xo'=dxo,yo'=dyo,t'=1&t<=ep()&v>=0}](v>=0&dx^2+dy^2=1&r!=0&(v=0|abs(x-xo)>v^2/(2*B())+V()*(v/B())|abs(y-yo)>v^2/(2*B())+V()*(v/B())))".asFormula)
                      & QE & print("Free drive branch 6 done")
                  )
                ),
              (allR(1) & implyR(1))*2 & allR(1)*2 & implyR(1) & allR(1) & implyR(1) & andR(1) <(
                implyR('R) & (andL('L)*) & hideL('L, "v=0|abs(x-xo_0)>v^2/(2*B())+V()*(v/B())|abs(y-yo_0)>v^2/(2*B())+V()*(v/B())".asFormula) & di("a")(1) & dw & prop
                  & hideIrrelevantAssumptions <(
                    hideR('R, "abs(y-yo)>v^2/(2*B())+V()*(v/B())".asFormula) & hideR('R, "v=0".asFormula)
                      & hideL('L, "dx^2+dy^2=1".asFormula)
                      & hideL('L, "y-y_0<=t*(v-a/2*t)".asFormula) & hideL('L, "-t*(v-a/2*t)<=y-y_0".asFormula)
                      & hideL('L, "yo-yo_0<=t*V()".asFormula) & hideL('L, "-t*V()<=yo-yo_0".asFormula)
                      & hideL('L, "r_0!=0".asFormula) & hideL('L, "w=0".asFormula) & hideL('L, "w*r=v_0".asFormula)
                      & print("Free drive branch 7 lemma prep")
                      & PropositionalTactics.toSingleFormula & by(accArithXLemma) & print("Free drive branch 7 done"),
                    hideR('R, "abs(x-xo)>v^2/(2*B())+V()*(v/B())".asFormula) & hideR('R, "v=0".asFormula)
                      & hideL('L, "dx^2+dy^2=1".asFormula)
                      & hideL('L, "x-x_0<=t*(v-a/2*t)".asFormula) & hideL('L, "-t*(v-a/2*t)<=x-x_0".asFormula)
                      & hideL('L, "xo-xo_0<=t*V()".asFormula) & hideL('L, "-t*V()<=xo-xo_0".asFormula)
                      & hideL('L, "r_0!=0".asFormula) & hideL('L, "w=0".asFormula) & hideL('L, "w*r=v_0".asFormula)
                      & print("Free drive branch 8 lemma prep")
                      & PropositionalTactics.toSingleFormula & by(accArithYLemma) & print("Free drive branch 8 done")
                  ),
                implyR('R) & (andL('L)*) & hideL('L, "v=0|abs(x-xo_0)>v^2/(2*B())+V()*(v/B())|abs(y-yo_0)>v^2/(2*B())+V()*(v/B())".asFormula) & di("a")(1) & dw & prop
                  & hideIrrelevantAssumptions <(
                    hideR('R, "abs(y-yo)>v^2/(2*B())+V()*(v/B())".asFormula) & hideR('R, "v=0".asFormula)
                      & hideL('L, "y-y_0<=t*(v-a/2*t)".asFormula) & hideL('L, "-t*(v-a/2*t)<=y-y_0".asFormula)
                      & hideL('L, "yo-yo_0<=t*V()".asFormula) & hideL('L, "-t*V()<=yo-yo_0".asFormula)
                      & hideL('L, "r_0!=0".asFormula)
                      & print("Free drive branch 9 lemma prep")
                      & PropositionalTactics.toSingleFormula & by(accArithXLemma) & print("Free drive branch 9 done"),
                    hideR('R, "abs(x-xo)>v^2/(2*B())+V()*(v/B())".asFormula) & hideR('R, "v=0".asFormula)
                      & hideL('L, "x-x_0<=t*(v-a/2*t)".asFormula) & hideL('L, "-t*(v-a/2*t)<=x-x_0".asFormula)
                      & hideL('L, "xo-xo_0<=t*V()".asFormula) & hideL('L, "-t*V()<=xo-xo_0".asFormula)
                      & hideL('L, "r_0!=0".asFormula)
                      & print("Free drive branch 10 lemma prep")
                      & PropositionalTactics.toSingleFormula & by(accArithYLemma) & print("Free drive branch 10 done")
                  )
                )
              )
          )
        ) & print("Induction step done")
      ) & print("Proof done")

    proveBy(s, tactic) shouldBe 'proved
  }

  "Passive Safety straight and curve using curvature" should "be provable" in withMathematica { qeTool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/robix/passivesafetyabs_curvestraight_curvature.key"))

    val invariant =
      """v >= 0
                      | & dx^2+dy^2 = 1
                      | & (v = 0 | abs(x-xo) > v^2 / (2*B()) + V()*(v/B())
                      |          | abs(y-yo) > v^2 / (2*B()) + V()*(v/B()))""".stripMargin.asFormula

    def di(a: String): DependentPositionTactic = diffInvariant(
      "t>=0".asFormula,
      "dx^2 + dy^2 = 1".asFormula,
      s"v = old(v) + $a*t".asFormula,
      s"-t * (v - $a/2*t) <= x - old(x) & x - old(x) <= t * (v - $a/2*t)".asFormula,
      s"-t * (v - $a/2*t) <= y - old(y) & y - old(y) <= t * (v - $a/2*t)".asFormula,
      "-t * V() <= xo - old(xo) & xo - old(xo) <= t * V()".asFormula,
      "-t * V() <= yo - old(yo) & yo - old(yo) <= t * V()".asFormula)
    
    val dw: BelleExpr = (andL('L)*) & print("Before diffWeaken") & dW(1) & print("After diffWeaken")

    def accArithTactic: BelleExpr = (alphaRule*) &
      //@todo auto-transform
      replaceTransform("ep()".asTerm, "t".asTerm)(-8) & speculativeQE & print("Proved acc arithmetic")

    val tactic = implyR('_) & (andL('_)*) & loop(invariant)('R) <(
      /* base case */ print("Base case...") & speculativeQE & print("Base case done"),
      /* use case */ print("Use case...") & speculativeQE & print("Use case done"),
      /* induction step */ print("Induction step") & unfoldProgramNormalize & printIndexed("After normalize") <(
      print("Braking branch") & di("-B()")(1) & dw & prop & onAll(speculativeQE) & print("Braking branch done"),
      print("Stopped branch") & di("0")(1) & dw & prop & onAll(speculativeQE) & print("Stopped branch done"),
      print("Acceleration branch") & hideL('L, "v=0|abs(x-xo_0)>v^2/(2*B())+V()*(v/B())|abs(y-yo_0)>v^2/(2*B())+V()*(v/B())".asFormula) &
        di("a")(1) & dw & prop & onAll(hideFactsAbout("dx", "dy", "dxo", "dyo", "k", "k_0") partial) <(
        hideFactsAbout("y", "yo") & accArithTactic,
        hideFactsAbout("x", "xo") & accArithTactic
        ) & print("Acceleration branch done")
      ) & print("Induction step done")
      ) & print("Proof done")
    proveBy(s, tactic) shouldBe 'proved
  }

  "Passive Safety straight and curve using curvature with additional braking branch" should "be provable" in withMathematica { qeTool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/robix/passivesafetyabs_curvestraight_curvature_lightbrake.key"))

    val invariant =
      """v >= 0
        | & dx^2+dy^2 = 1
        | & (v = 0 | abs(x-xo) > v^2 / (2*B()) + V()*(v/B())
        |          | abs(y-yo) > v^2 / (2*B()) + V()*(v/B()))""".stripMargin.asFormula

    def di(a: String): DependentPositionTactic = diffInvariant(
      "t>=0".asFormula,
      "dx^2 + dy^2 = 1".asFormula,
      s"v = old(v) + $a*t".asFormula,
      s"-t * (v - $a/2*t) <= x - old(x) & x - old(x) <= t * (v - $a/2*t)".asFormula,
      s"-t * (v - $a/2*t) <= y - old(y) & y - old(y) <= t * (v - $a/2*t)".asFormula,
      "-t * V() <= xo - old(xo) & xo - old(xo) <= t * V()".asFormula,
      "-t * V() <= yo - old(yo) & yo - old(yo) <= t * V()".asFormula)

    val dw: BelleExpr = (andL('L)*) & print("Before diffWeaken") & dW(1) & print("After diffWeaken")

    def accArithTactic: BelleExpr = (alphaRule*) &
      //@todo auto-transform
      replaceTransform("ep()".asTerm, "t".asTerm)(-8) & speculativeQE & print("Proved acc arithmetic")

    val tactic = implyR('_) & (andL('_)*) & loop(invariant)('R) <(
      /* base case */ print("Base case...") & speculativeQE & print("Base case done"),
      /* use case */ print("Use case...") & speculativeQE & print("Use case done"),
      /* induction step */ print("Induction step") & unfoldProgramNormalize & printIndexed("After normalize") <(
      print("Braking branch") & di("-B()")(1) & dw & prop & onAll(speculativeQE) & print("Braking branch done"),
      print("Light braking branch") & hideL('L, "v=0|abs(x-xo)>v^2/(2*B())+V()*(v/B())|abs(y-yo)>v^2/(2*B())+V()*(v/B())".asFormula) &
        di("-B()/2")(1) & dw & prop & onAll(hideFactsAbout("dx", "dy", "dxo", "dyo", "k", "k_0") partial) <(
        hideFactsAbout("y", "yo") & speculativeQE,
        hideFactsAbout("x", "xo") & speculativeQE
        ) & print("Light braking branch done"),
      print("Stopped branch") & di("0")(1) & dw & prop & onAll(speculativeQE) & print("Stopped branch done"),
      print("Acceleration branch") & hideL('L, "v=0|abs(x-xo_0)>v^2/(2*B())+V()*(v/B())|abs(y-yo_0)>v^2/(2*B())+V()*(v/B())".asFormula) &
        di("a")(1) & dw & prop & onAll(hideFactsAbout("dx", "dy", "dxo", "dyo", "k", "k_0") partial) <(
        hideFactsAbout("y", "yo") & accArithTactic,
        hideFactsAbout("x", "xo") & accArithTactic
        ) & print("Acceleration branch done")
      ) & print("Induction step done")
      ) & print("Proof done")
    proveBy(s, tactic) shouldBe 'proved
  }

  "Passive orientation safety" should "be provable" in withMathematica { qeTool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/robix/passiveorientationsafetyabs.key"))
    val invariant =
      """v>=0
        | & dx^2+dy^2=1
        | & r!=0
        | & (v=0 | (abs(beta) + v^2/(2*b()*abs(r)) < gamma()
        |          & (isVisible < 0 | abs(x-ox) > v^2/(2*b()) + V()*(v/b()) | abs(y-oy) > v^2/(2*b()) + V()*(v/b()))))
      """.stripMargin.asFormula

    def di(a: String): DependentPositionTactic = diffInvariant(
      "t>=0".asFormula,
      "dx^2 + dy^2 = 1".asFormula,
      s"v = old(v) + $a*t".asFormula,
      s"-t * (v - $a/2*t) <= x - old(x) & x - old(x) <= t * (v - $a/2*t)".asFormula,
      s"-t * (v - $a/2*t) <= y - old(y) & y - old(y) <= t * (v - $a/2*t)".asFormula,
      "-t * V() <= ox - old(ox) & ox - old(ox) <= t * V()".asFormula,
      "-t * V() <= oy - old(oy) & oy - old(oy) <= t * V()".asFormula,
      "w*r = v".asFormula,
      s"beta = old(beta) + t/r*(v - $a/2*t)".asFormula)

    val dw: BelleExpr = (andL('L)*) & print("Before diffWeaken") & dW(1) & print("After diffWeaken")

    val allImplyTactic = ((allR('R)*) & implyR('R))*

    val tactic = implyR('R) & (andL('L)*) & loop(invariant)('R) <(
      /* base case */ QE & print("Base case done"),
      /* use case */ QE & print("Use case done"),
      /* step */ (andL('L)*) & chase('R) & allR('R)*2 & implyR('R) & andR('R) <(
        print("Braking") & allImplyTactic & di("-b()")('R) & dw & (alphaRule*) & print("After alpha braking") &
          (andR('R) <(closeId, skip))*3 & orR('R) & passiveOrientationBrakingArithTactic & print("Braking branch done"),
        andR('R) <(
          print("Stopped") & allImplyTactic & di("0")('R) & dw & (alphaRule*) & print("After alpha stopped") &
            (andR('R) <(closeId, skip))*3 & orR('R) & passiveOrientationStoppedArithTactic & print("Stopped branch done"),
          print("Accelerating") & allImplyTactic & di("A()")('R) & dw & (alphaRule*) & print("After alpha accelerating") &
            (andR('R) <(closeId, skip))*3 & orR('R) & passiveOrientationAccArithTactic & print("Acc branch done")
          )
        )
      )

    proveBy(s, tactic) shouldBe 'proved
  }

  def passiveOrientationBrakingArithTactic: BelleExpr =
    orL('L, "v_0=0|abs(beta_0)+v_0^2/(2*b()*abs(r)) < gamma()&(isVisible < 0|abs(x_0-ox_0)>v_0^2/(2*b())+V()*(v_0/b())|abs(y_0-oy_0)>v_0^2/(2*b())+V()*(v_0/b()))".asFormula) <(
    hideR(2) & QE,
    andL('L) & andR('R) <(
      QE,
      hideL('L, "abs(beta_0)+v_0^2/(2*b()*abs(r)) < gamma()".asFormula) &
        hideL('L, "beta=beta_0+t/r*(v--b()/2*t)".asFormula) &
        (orR('R)*) &
        orL('Llast, "isVisible < 0|abs(x_0-ox_0)>v_0^2/(2*b())+V()*(v_0/b())|abs(y_0-oy_0)>v_0^2/(2*b())+V()*(v_0/b())".asFormula) <(
          closeId,
          hideR('R, "isVisible < 0".asFormula) & hideR('R, "v=0".asFormula) & hideL('L, "t<=ep()".asFormula) &
            hideL('L, "dx^2+dy^2=1".asFormula) & hideL('L, "w*r=v".asFormula) & hideL('L, "odx^2+ody^2<=V()^2".asFormula) &
            hideL('L, "r!=0".asFormula) & hideL('L, "gamma()>0".asFormula) & hideL('L, "ep()>0".asFormula) &
            orL('Llast, "abs(x_0-ox_0)>v_0^2/(2*b())+V()*(v_0/b())|abs(y_0-oy_0)>v_0^2/(2*b())+V()*(v_0/b())".asFormula) <(
              hideR('R, "abs(y-oy)>v^2/(2*b())+V()*(v/b())".asFormula) & hideL('L, "y-y_0<=t*(v--b()/2*t)".asFormula) & hideL('L, "-t*(v--b()/2*t)<=y-y_0".asFormula) & hideL('L, "oy-oy_0<=t*V()".asFormula) & hideL('L, "-t*V()<=oy-oy_0".asFormula) & QE,
              hideR('R, "abs(x-ox)>v^2/(2*b())+V()*(v/b())".asFormula) & hideL('L, "x-x_0<=t*(v--b()/2*t)".asFormula) & hideL('L, "-t*(v--b()/2*t)<=x-x_0".asFormula) & hideL('L, "ox-ox_0<=t*V()".asFormula) & hideL('L, "-t*V()<=ox-ox_0".asFormula) & QE
              )
          )
      )
    )
  
  it should "prove just braking arithmetic" in withMathematica { tool =>
    val fml = """V()>=0 & A()>=0 & b()>0 & ep()>0 & gamma()>0 & v_0>=0 & r!=0 & (v_0=0|abs(beta_0)+v_0^2/(2*b()*abs(r)) < gamma()&(isVisible < 0|abs(x_0-ox_0)>v_0^2/(2*b())+V()*(v_0/b())|abs(y_0-oy_0)>v_0^2/(2*b())+V()*(v_0/b()))) & odx^2+ody^2<=V()^2 & beta=beta_0+t/r*(v--b()/2*t) & w*r=v & -t*V()<=oy-oy_0 & oy-oy_0<=t*V() & -t*V()<=ox-ox_0 & ox-ox_0<=t*V() & -t*(v--b()/2*t)<=y-y_0 & y-y_0<=t*(v--b()/2*t) & v=v_0+-b()*t & -t*(v--b()/2*t)<=x-x_0 & x-x_0<=t*(v--b()/2*t) & dx^2+dy^2=1 & t>=0 & t<=ep() & v>=0
                |  -> v=0|abs(beta)+v^2/(2*b()*abs(r)) < gamma()&(isVisible < 0|abs(x-ox)>v^2/(2*b())+V()*(v/b())|abs(y-oy)>v^2/(2*b())+V()*(v/b()))""".stripMargin.asFormula

    val tactic = implyR('R) & (andL('L)*) & orR('R) & passiveOrientationBrakingArithTactic

    proveBy(fml, tactic) shouldBe 'proved
  }

  def passiveOrientationStoppedArithTactic: BelleExpr =
    orL('L, "v_0=0|abs(beta_0)+v_0^2/(2*b()*abs(r)) < gamma()&(isVisible < 0|abs(x_0-ox_0)>v_0^2/(2*b())+V()*(v_0/b())|abs(y_0-oy_0)>v_0^2/(2*b())+V()*(v_0/b()))".asFormula) <(
      hideR(2) & QE,
      andL('L) & andR('R) <(
        QE,
        hideL('L, "abs(beta_0)+v_0^2/(2*b()*abs(r)) < gamma()".asFormula) &
          hideL('L, "beta=beta_0+t/r*(v-0/2*t)".asFormula) &
          (orR('R)*) &
          orL('Llast, "isVisible < 0|abs(x_0-ox_0)>v_0^2/(2*b())+V()*(v_0/b())|abs(y_0-oy_0)>v_0^2/(2*b())+V()*(v_0/b())".asFormula) <(
            closeId,
            hideR('R, "abs(y-oy)>v^2/(2*b())+V()*(v/b())".asFormula) & hideR('R, "abs(x-ox)>v^2/(2*b())+V()*(v/b())".asFormula) &
              hideR('R, "isVisible < 0".asFormula) &
              hideL('L, "t<=ep()".asFormula) & hideL('L, "w*r=v".asFormula) & hideL('L, "r!=0".asFormula) &
              hideL('L, "gamma()>0".asFormula) & hideL('L, "ep()>0".asFormula) & hideL('L, "x-x_0<=t*(v-0/2*t)".asFormula) &
              hideL('L, "-t*(v-0/2*t)<=x-x_0".asFormula) & hideL('L, "y-y_0<=t*(v-0/2*t)".asFormula) &
              hideL('L, "-t*(v-0/2*t)<=y-y_0".asFormula) & hideL('L, "ox-ox_0<=t*V()".asFormula) &
              hideL('L, "-t*V()<=ox-ox_0".asFormula) & hideL('L, "oy-oy_0<=t*V()".asFormula) &
              hideL('L, "-t*V()<=oy-oy_0".asFormula) & QE
            )
        )
      )

  it should "prove just stopped arithmetic" in withMathematica { tool =>
    val fml = """V()>=0 & A()>=0 & b()>0 & ep()>0 & gamma()>0 & v_0>=0 & r!=0 & (v_0=0|abs(beta_0)+v_0^2/(2*b()*abs(r)) < gamma()&(isVisible < 0|abs(x_0-ox_0)>v_0^2/(2*b())+V()*(v_0/b())|abs(y_0-oy_0)>v_0^2/(2*b())+V()*(v_0/b()))) & odx^2+ody^2<=V()^2 & v_0=0 & beta=beta_0+t/r*(v-0/2*t) & w*r=v & -t*V()<=oy-oy_0 & oy-oy_0<=t*V() & -t*V()<=ox-ox_0 & ox-ox_0<=t*V() & -t*(v-0/2*t)<=y-y_0 & y-y_0<=t*(v-0/2*t) & v=v_0+0*t & -t*(v-0/2*t)<=x-x_0 & x-x_0<=t*(v-0/2*t) & dx^2+dy^2=1 & t>=0 & t<=ep() & v>=0
                |  -> v=0|abs(beta)+v^2/(2*b()*abs(r)) < gamma()&(isVisible < 0|abs(x-ox)>v^2/(2*b())+V()*(v/b())|abs(y-oy)>v^2/(2*b())+V()*(v/b()))""".stripMargin.asFormula

    val tactic = implyR('R) & (andL('L)*) & orR('R) & passiveOrientationStoppedArithTactic

    proveBy(fml, tactic) shouldBe 'proved
  }

  def passiveOrientationAccArithTactic: BelleExpr =
    hideL('L, "dx^2+dy^2=1".asFormula) & hideL('L, "w*r=v".asFormula) & hideL('L, "odx^2+ody^2<=V()^2".asFormula) &
    hideL('L, "v_0=0|abs(beta_0)+v_0^2/(2*b()*abs(r_0)) < gamma()&(isVisible_0 < 0|abs(x_0-ox_0)>v_0^2/(2*b())+V()*(v_0/b())|abs(y_0-oy_0)>v_0^2/(2*b())+V()*(v_0/b()))".asFormula) &
    hideL('L, "r_0!=0".asFormula) & hideR('R, "v=0".asFormula) & andR('R) <(
      hideL('L, "isVisible < 0|abs(x_0-ox_1)>v_0^2/(2*b())+V()*(v_0/b())+(A()/b()+1)*(A()/2*ep()^2+ep()*(v_0+V()))|abs(y_0-oy_1)>v_0^2/(2*b())+V()*(v_0/b())+(A()/b()+1)*(A()/2*ep()^2+ep()*(v_0+V()))".asFormula) & QE,
      orR('R)*2 & orL('L, "isVisible < 0|abs(x_0-ox_1)>v_0^2/(2*b())+V()*(v_0/b())+(A()/b()+1)*(A()/2*ep()^2+ep()*(v_0+V()))|abs(y_0-oy_1)>v_0^2/(2*b())+V()*(v_0/b())+(A()/b()+1)*(A()/2*ep()^2+ep()*(v_0+V()))".asFormula) <(
        closeId,
        hideR('R, "isVisible < 0".asFormula) & hideL('L, "beta=beta_1+t/r*(v-A()/2*t)".asFormula) & hideL('L, "beta_1=0".asFormula) &
          hideL('L, "v_0^2/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v_0) < gamma()*abs(r)".asFormula) & hideL('L, "r!=0".asFormula) & hideL('L, "gamma()>0".asFormula) &
          orL('L, "abs(x_0-ox_1)>v_0^2/(2*b())+V()*(v_0/b())+(A()/b()+1)*(A()/2*ep()^2+ep()*(v_0+V()))|abs(y_0-oy_1)>v_0^2/(2*b())+V()*(v_0/b())+(A()/b()+1)*(A()/2*ep()^2+ep()*(v_0+V()))".asFormula) <(
            hideR('R, "abs(y-oy)>v^2/(2*b())+V()*(v/b())".asFormula) & hideL('L, "y-y_0<=t*(v-A()/2*t)".asFormula) &
              hideL('L, "-t*(v-A()/2*t)<=y-y_0".asFormula) & hideL('L, "oy-oy_1<=t*V()".asFormula) & hideL('L, "-t*V()<=oy-oy_1".asFormula) &
              abs('R, "abs(x-ox)".asTerm) & abs('L, "abs(x_0-ox_1)".asTerm) &
              orL('L, "x_0-ox_1>=0&abs_1=x_0-ox_1|x_0-ox_1 < 0&abs_1=-(x_0-ox_1)".asFormula) <(
                andL('L) & hideL('L, "x-x_0<=t*(v-A()/2*t)".asFormula) & hideL('L, "-t*V()<=ox-ox_1".asFormula) &
                orL('L, "x-ox>=0&abs_0=x-ox|x-ox < 0&abs_0=-(x-ox)".asFormula) <(
                  print("Foo 1") & QE,
                  hideR(1) & print("Foo 2") & QE
                  ),
                andL('L) & hideL('L, "-t*(v-A()/2*t)<=x-x_0".asFormula) & hideL('L, "ox-ox_1<=t*V()".asFormula) &
                orL('L, "x-ox>=0&abs_0=x-ox|x-ox < 0&abs_0=-(x-ox)".asFormula) <(
                  hideR(1) & print("Foo 3") & QE,
                  cutL("abs_1>v_0^2/(2*b())+V()*(v_0/b())+(A()/b()+1)*(A()/2*t^2+t*(v_0+V()))".asFormula)(AntePos(5)) <(
                    hideL('L, "t<=ep()".asFormula) & hideL('L, "ep()>0".asFormula) & print("Foo 4") & QE,
                    hideR('R, "abs_0>v^2/(2*b())+V()*(v/b())".asFormula) & print("Foo 5") & QE
                    )
                  )

              ),
            hideR('R, "abs(x-ox)>v^2/(2*b())+V()*(v/b())".asFormula) & hideL('L, "x-x_0<=t*(v-A()/2*t)".asFormula) &
              hideL('L, "-t*(v-A()/2*t)<=x-x_0".asFormula) & hideL('L, "ox-ox_1<=t*V()".asFormula) & hideL('L, "-t*V()<=ox-ox_1".asFormula) &
              abs('R, "abs(y-oy)".asTerm) & abs('L, "abs(y_0-oy_1)".asTerm) & cutL("abs_1>v_0^2/(2*b())+V()*(v_0/b())+(A()/b()+1)*(A()/2*t^2+t*(v_0+V()))".asFormula)(AntePos(5)) <(
                hideL('L, "t<=ep()".asFormula) & hideL('L, "ep()>0".asFormula) &
                orL('L, "y_0-oy_1>=0&abs_1=y_0-oy_1|y_0-oy_1 < 0&abs_1=-(y_0-oy_1)".asFormula) <(
                  andL('L) & hideL('L, "y-y_0<=t*(v-A()/2*t)".asFormula) & hideL('L, "-t*V()<=oy-oy_1".asFormula) &
                  orL('L, "y-oy>=0&abs_0=y-oy|y-oy < 0&abs_0=-(y-oy)".asFormula) <(
                    print("Bar 1") & QE,
                    hideR(1) & print("Bar 2") & QE
                    ),
                  andL('L) & hideL('L, "-t*(v-A()/2*t)<=y-y_0".asFormula) & hideL('L, "oy-oy_1<=t*V()".asFormula) &
                  orL('L, "y-oy>=0&abs_0=y-oy|y-oy < 0&abs_0=-(y-oy)".asFormula) <(
                    hideR(1) & print("Bar 3") & QE,
                    print("Bar 4") & QE
                    )
                  ),
                hideR(1, "abs_0>v^2/(2*b())+V()*(v/b())".asFormula) & print("Bar 5") & QE
              )
            )
        )
      )

  it should "prove just acceleration arithmetic" in withMathematica { tool =>
    val fml = """V()>=0 & A()>=0 & b()>0 & ep()>0 & gamma()>0 & v_0>=0 & r_0!=0 & (v_0=0|abs(beta_0)+v_0^2/(2*b()*abs(r_0)) < gamma()&(isVisible_0 < 0|abs(x_0-ox_0)>v_0^2/(2*b())+V()*(v_0/b())|abs(y_0-oy_0)>v_0^2/(2*b())+V()*(v_0/b()))) & odx^2+ody^2<=V()^2 & r!=0 & (isVisible < 0|abs(x_0-ox_1)>v_0^2/(2*b())+V()*(v_0/b())+(A()/b()+1)*(A()/2*ep()^2+ep()*(v_0+V()))|abs(y_0-oy_1)>v_0^2/(2*b())+V()*(v_0/b())+(A()/b()+1)*(A()/2*ep()^2+ep()*(v_0+V()))) & v_0^2/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v_0) < gamma()*abs(r) & beta_1=0 & beta=beta_1+t/r*(v-A()/2*t) & w*r=v & -t*V()<=oy-oy_1 & oy-oy_1<=t*V() & -t*V()<=ox-ox_1 & ox-ox_1<=t*V() & -t*(v-A()/2*t)<=y-y_0 & y-y_0<=t*(v-A()/2*t) & v=v_0+A()*t & -t*(v-A()/2*t)<=x-x_0 & x-x_0<=t*(v-A()/2*t) & dx^2+dy^2=1 & t>=0 & t<=ep() & v>=0
                |  ->  v=0|abs(beta)+v^2/(2*b()*abs(r)) < gamma()&(isVisible < 0|abs(x-ox)>v^2/(2*b())+V()*(v/b())|abs(y-oy)>v^2/(2*b())+V()*(v/b()))""".stripMargin.asFormula

    val tactic = implyR('R) & (andL('L)*) & orR('R) & passiveOrientationAccArithTactic

    proveBy(fml, tactic) shouldBe 'proved
  }

  "Passive safety with curvature and uncertainty" should "prove" in withZ3 { tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/robix/passivesafetyabs_curvestraight_curvature_uncertainty.key"))

    val invariant =
      """v >= 0
        | & dx^2+dy^2 = 1
        | & (v = 0 | abs(x-xo) > v^2 / (2*Da()*B()) + V()*(v/(Da()*B()))
        |          | abs(y-yo) > v^2 / (2*Da()*B()) + V()*(v/(Da()*B())))""".stripMargin.asFormula

    def di(a: String): DependentPositionTactic = diffInvariant(
      "t>=0".asFormula,
      "dx^2 + dy^2 = 1".asFormula,
      s"old(v) + $a*pa*t = v".asFormula,
      s"-t * (v - $a*pa/2*t) <= x - old(x) & x - old(x) <= t * (v - $a*pa/2*t)".asFormula, // Mathematica won't prove -> need better hiding in DI
      s"-t * (v - $a*pa/2*t) <= y - old(y) & y - old(y) <= t * (v - $a*pa/2*t)".asFormula,
      "-t * V() <= xo - old(xo) & xo - old(xo) <= t * V()".asFormula,
      "-t * V() <= yo - old(yo) & yo - old(yo) <= t * V()".asFormula)

    val dw: BelleExpr = (andL('L)*) & print("Before diffWeaken") & dW(1) & print("After diffWeaken")

    def accArithTactic: BelleExpr = (alphaRule*) & printIndexed("Before replaceTransform") &
      //@todo auto-transform
      replaceTransform("ep()".asTerm, "t".asTerm)('Llike, "abs(mx-mxo)>(mv+Dv())^2/(2*B()*Da())+V()*(mv+Dv())/(B()*Da())+Dpr()+Dpo()+(A()/(B()*Da())+1)*(A()/2*ep()^2+ep()*(mv+Dv()+V()))".asFormula) & speculativeQE & print("Proved acc arithmetic")

    val tactic = implyR('R) & (andL('L)*) & loop(invariant)('R) <(
      /* base case */ print("Base case...") & speculativeQE & print("Base case done"),
      /* use case */ print("Use case...") & speculativeQE & print("Use case done"),
      /* induction step */ print("Induction step") & unfoldProgramNormalize & printIndexed("After normalize") <(
      print("Braking branch") & di("-B()")(1) & dw & prop & onAll(speculativeQE) & print("Braking branch done"),
      print("Stopped branch") & di("0")(1) & dw & prop & onAll(speculativeQE) & print("Stopped branch done"),
      print("Acceleration branch") & hideL('L, "v=0|abs(x-xo_0)>v^2/(2*Da()*B())+V()*(v/(Da()*B()))|abs(y-yo_0)>v^2/(2*Da()*B())+V()*(v/(Da()*B()))".asFormula) &
        di("a")(1) & dw & prop & onAll(hideFactsAbout("dxo", "dyo")) <(
        hideFactsAbout("y", "yo") & accArithTactic,
        hideFactsAbout("x", "xo") & accArithTactic
        ) & print("Acceleration branch done")
      ) & print("Induction step done")
      ) & print("Proof done")
    proveBy(s, tactic) shouldBe 'proved
  }

  "Reach goal before deadline expires" should "be provable" in withZ3 { tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/robix/reachgoal_boxliveness_deadline.kyx"))

    val invariant = """0 <= vr & vr <= Vmax() & xr + vr^2/(2*b()) < xg + Delta()
                      |				& (xg - Delta() < xr -> (vr = 0 | T >= vr/b()))
                      |				& (xr <= xg - Delta() -> (vr >= A()*ep() & T > (xg - Delta() - xr)/(A()*ep()) + ep() + Vmax()/b()) /* travel + realize to stop + stopping */
                      |				                     | (vr <= A()*ep() & T > ep()-vr/A() + (xg - Delta() - xr)/(A()*ep()) + ep() + Vmax()/b())) /* acc. + travel + realize to stop + stopping */""".stripMargin.asFormula

    val tactic = implyR('R) & (andL('L)*) & loop(invariant)(1) & Idioms.<(
      print("Base case") & QE & done,
      print("Use case") & QE & done,
      print("Induction step") & unfoldProgramNormalize & onAll(ODE('R) & allR('R) & implyR('R)*2 & allL("t_".asVariable)('Llast) & QE & done)
    )

    proveBy(s, tactic) shouldBe 'proved
  }
}
