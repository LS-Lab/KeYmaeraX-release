/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core.{Formula, AntePos}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.SlowTest
import testHelper.ParserFactory._

import scala.language.postfixOps

/**
 * Robix test cases.
 * @author Stefan Mitsch
 */
@SlowTest
class Robix extends TacticTestBase {

  "Passive Safety" should "be provable" in withMathematica { implicit qeTool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/robix/passivesafetyabs.key"))

    val invariant = """v >= 0
                      | & dx^2+dy^2 = 1
                      | & r != 0
                      | & (v = 0 | abs(x-xo) > v^2 / (2*B) + V()*(v/B)
                      |          | abs(y-yo) > v^2 / (2*B) + V()*(v/B))""".stripMargin.asFormula

    def di(a: String): DependentPositionTactic = diffInvariant(
      "t>=0".asFormula,
      "dx^2 + dy^2 = 1".asFormula,
      s"v = old(v) + $a*t".asFormula,
      s"-t * (v - $a/2*t) <= x - old(x) & x - old(x) <= t * (v - $a/2*t)".asFormula,
      s"-t * (v - $a/2*t) <= y - old(y) & y - old(y) <= t * (v - $a/2*t)".asFormula,
      "-t * V() <= xo - old(xo) & xo - old(xo) <= t * V()".asFormula,
      "-t * V() <= yo - old(yo) & yo - old(yo) <= t * V()".asFormula)

    val dw: BelleExpr = exhaustiveEqR2L(hide=true)('Llast)*5 /* 5 old(...) in DI */ & andL('_)*@TheType() &
      debug("Before diffWeaken") & diffWeaken(1) & debug("After diffWeaken")

    val hideIrrelevantAssumptions: BelleExpr =
      OnAll(
        hideL(Find.FindL(0, Some("dx^2+dy^2=1".asFormula))) &
        hideL(Find.FindL(0, Some("r!=0".asFormula))) &
        hideL(Find.FindL(0, Some("dxo^2+dyo^2<=V()^2".asFormula))) partial)

    val brakeStoppedArith: BelleExpr =
      hideIrrelevantAssumptions <(
        hideR(3, "abs(y-yo)>v^2/(2*B)+V()*(v/B)".asFormula) & hideR(2, "abs(x-xo)>v^2/(2*B)+V()*(v/B)".asFormula) & QE,
        hideR(3, "abs(y-yo)>v^2/(2*B)+V()*(v/B)".asFormula) & QE,
        hideR(2, "abs(x-xo)>v^2/(2*B)+V()*(v/B)".asFormula) & QE)

    def accArithTactic(fml: Formula): BelleExpr = implyR(1) & andL('_)*@TheType() & cutL(fml)(AntePos(4)) <(
      hideL(-15) & hideL(-4) & abs(1, 0::Nil) & abs(-4, 0::Nil) & orL(-16) & OnAll(orL(-15) partial) &
        OnAll(andL('_)*@TheType() partial) & OnAll(exhaustiveEqL2R(hide=true)('L)*@TheType() partial) <(
        hideL(-11) & hideL(-8) & QE,
        hideR(1) & QE,
        hideR(1) & QE,
        hideL(-10) & hideL(-9) & QE
        ),
      hideR(1) & (-12 to -6).map(hideL(_)).reduce[BelleExpr](_&_) & implyR(1) & abs(1, 0::Nil) & hideL(-10) & QE
      ) & debug("Proved acc arithmetic: " + fml)
    val accArithX = "A>=0 & B>0 & V()>=0 & ep>0 & abs(x_0-xo_0)>v_0^2/(2*B)+V()*v_0/B+(A/B+1)*(A/2*ep^2+ep*(v_0+V())) & v_0>=0 & -B<=a & a<=A & -t*V()<=xo-xo_0 & xo-xo_0<=t*V() & v=v_0+a*t & -t*(v-a/2*t)<=x-x_0 & x-x_0<=t*(v-a/2*t) & t>=0 & t<=ep & v>=0 -> abs(x-xo)>v^2/(2*B)+V()*(v/B)".asFormula
    val accArithXLemma = proveBy(accArithX, accArithTactic("abs(x_0-xo_0)>v_0^2/(2*B)+V()*v_0/B+(A/B+1)*(A/2*t^2+t*(v_0+V()))".asFormula))
    accArithXLemma shouldBe 'proved

    val accArithY = "A>=0 & B>0 & V()>=0 & ep>0 & abs(y_0-yo_0)>v_0^2/(2*B)+V()*v_0/B+(A/B+1)*(A/2*ep^2+ep*(v_0+V())) & v_0>=0 & -B<=a & a<=A & -t*V()<=yo-yo_0 & yo-yo_0<=t*V() & -t*(v-a/2*t)<=y-y_0 & y-y_0<=t*(v-a/2*t) & v=v_0+a*t & t>=0 & t<=ep & v>=0 -> abs(y-yo)>v^2/(2*B)+V()*(v/B)".asFormula
    val accArithYLemma = proveBy(accArithY, accArithTactic("abs(y_0-yo_0)>v_0^2/(2*B)+V()*v_0/B+(A/B+1)*(A/2*t^2+t*(v_0+V()))".asFormula))
    accArithYLemma shouldBe 'proved

    val tactic = implyR('_) & andL('_)*@TheType() & loop(invariant)('R) <(
      /* use case */ QE & debug("Use case done"),
      /* base case */ QE & debug("Base case done"),
      /* induction step */ chase(1) & allR(1)*2 & implyR(1) & andR(1) <(
        debug("Braking branch") & allR(1) & implyR(1) & di("-B")(1) & dw & prop & brakeStoppedArith & debug("Braking branch done"),
        andR(1) <(
          debug("Stopped branch") & implyR(1) & allR(1) & implyR(1) & allR(1) & implyR(1) & di("0")(1) & dw & prop & brakeStoppedArith & debug("Stopped branch done"),
          debug("Acceleration branch") & (allR(1) & implyR(1))*3 & allR(1)*2 & implyR(1) & allR(1) & implyR(1) &
            andL('_)*@TheType() & hideL(Find.FindL(0, Some("v=0|abs(x-xo_0)>v^2/(2*B)+V()*(v/B)|abs(y-yo_0)>v^2/(2*B)+V()*(v/B)".asFormula))) &
            di("a")(1) & dw & prop & hideIrrelevantAssumptions <(
              hideR(3, "abs(y-yo)>v^2/(2*B)+V()*(v/B)".asFormula) & hideR(1, "v=0".asFormula) &
                hideL(-15, "y-y_0<=t*(v-a/2*t)".asFormula) & hideL(-14, "-t*(v-a/2*t)<=y-y_0".asFormula) &
                hideL(-11, "yo-yo_0<=t*V()".asFormula) & hideL(-10, "-t*V()<=yo-yo_0".asFormula) &
                hideL(-9, "r_0!=0".asFormula) & PropositionalTactics.toSingleFormula & by(accArithXLemma),
              hideR(2, "abs(x-xo)>v^2/(2*B)+V()*(v/B)".asFormula) & hideR(1, "v=0".asFormula) &
                hideL(-18, "x-x_0<=t*(v-a/2*t)".asFormula) & hideL(-17, "-t*(v-a/2*t)<=x-x_0".asFormula) &
                hideL(-13, "xo-xo_0<=t*V()".asFormula) & hideL(-12, "-t*V()<=xo-xo_0".asFormula) &
                hideL(-9, "r_0!=0".asFormula) & PropositionalTactics.toSingleFormula & by(accArithYLemma)) & debug("Acceleration branch done")
          )
        ) & debug("Induction step done")
      ) & debug("Proof done")
    proveBy(s, tactic) shouldBe 'proved
  }

  it should "prove just the acceleration x arithmetic" in withMathematica { implicit qeTool =>
    val accArith = "A>=0 & B>0 & V()>=0 & ep>0 & abs(x_0-xo_0)>v_0^2/(2*B)+V()*v_0/B+(A/B+1)*(A/2*ep^2+ep*(v_0+V())) & v_0>=0 & -B<=a & a<=A & -t*V()<=xo-xo_0 & xo-xo_0<=t*V() & v=v_0+a*t & -t*(v-a/2*t)<=x-x_0 & x-x_0<=t*(v-a/2*t) & t>=0 & t<=ep & v>=0 -> abs(x-xo)>v^2/(2*B)+V()*(v/B)".asFormula

    val tactic = implyR(1) & andL('_)*@TheType() & cutL("abs(x_0-xo_0)>v_0^2/(2*B)+V()*v_0/B+(A/B+1)*(A/2*t^2+t*(v_0+V()))".asFormula)(AntePos(4)) <(
      hideL(-15) & hideL(-4) & abs(1, 0::Nil) & abs(-4, 0::Nil) & orL(-16) & OnAll(orL(-15) partial) &
        OnAll(andL('_)*@TheType() partial) & OnAll(exhaustiveEqL2R(hide=true)('L)*@TheType() partial) <(
        hideL(-11) & hideL(-8) & QE,
        hideR(1) & QE,
        hideR(1) & QE,
        hideL(-10) & hideL(-9) & QE
        ),
      hideR(1) & (-12 to -6).map(hideL(_)).reduce[BelleExpr](_&_) & implyR(1) & abs(1, 0::Nil) & hideL(-10) & QE
      )

    proveBy(accArith, tactic) shouldBe 'proved
  }

  it should "prove just the acceleration y arithmetic" in withMathematica { implicit qeTool =>
    val accArith = "A>=0 & B>0 & V()>=0 & ep>0 & abs(y_0-yo_0)>v_0^2/(2*B)+V()*v_0/B+(A/B+1)*(A/2*ep^2+ep*(v_0+V())) & v_0>=0 & -B<=a & a<=A & -t*V()<=yo-yo_0 & yo-yo_0<=t*V() & -t*(v-a/2*t)<=y-y_0 & y-y_0<=t*(v-a/2*t) & v=v_0+a*t & t>=0 & t<=ep & v>=0 -> abs(y-yo)>v^2/(2*B)+V()*(v/B)".asFormula

    val tactic = implyR(1) & andL('_)*@TheType() & cutL("abs(y_0-yo_0)>v_0^2/(2*B)+V()*v_0/B+(A/B+1)*(A/2*t^2+t*(v_0+V()))".asFormula)(AntePos(4)) <(
      hideL(-15) & hideL(-4) & abs(1, 0::Nil) & abs(-4, 0::Nil) & orL(-16) & OnAll(orL(-15) partial) &
        OnAll(andL('_)*@TheType() partial) & OnAll(exhaustiveEqL2R(hide=true)('L)*@TheType() partial) <(
        hideL(-11) & hideL(-8) & QE,
        hideR(1) & QE,
        hideR(1) & QE,
        hideL(-10) & hideL(-9) & QE
        ),
      hideR(1) & (-12 to -6).map(hideL(_)).reduce[BelleExpr](_&_) & implyR(1) & abs(1, 0::Nil) & hideL(-10) & QE
      )

    proveBy(accArith, tactic) shouldBe 'proved
  }
}
