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

import scala.language.postfixOps

/**
 * Robix test cases.
 *
 * @author Stefan Mitsch
 * @author Ran Ji
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
      print("Before diffWeaken") & diffWeaken(1) & print("After diffWeaken")

    def accArithTactic: BelleExpr = alphaRule*@TheType() &
      //@todo auto-transform
      replaceTransform("ep".asTerm, "t".asTerm)(-8) & speculativeQE & print("Proved acc arithmetic")

    val tactic = implyR('_) & andL('_)*@TheType() & loop(invariant)('R) <(
      /* base case */ print("Base case...") & speculativeQE & print("Base case done"),
      /* use case */ print("Use case...") & speculativeQE & print("Use case done"),
      /* induction step */ print("Induction step") & chase(1) & normalize(andR('R), skip, skip) & printIndexed("After normalize") <(
        print("Braking branch") & di("-B")(1) & dw & prop & OnAll(speculativeQE) & print("Braking branch done"),
        print("Stopped branch") & di("0")(1) & dw & prop & OnAll(speculativeQE) & print("Stopped branch done"),
        print("Acceleration branch") & hideL(Find.FindL(0, Some("v=0|abs(x-xo_0)>v^2/(2*B)+V()*(v/B)|abs(y-yo_0)>v^2/(2*B)+V()*(v/B)".asFormula))) &
          di("a")(1) & dw & prop & OnAll(hideFactsAbout("dx", "dy", "dxo", "dyo", "r", "r_0") partial) <(
            hideFactsAbout("y", "yo") & accArithTactic,
            hideFactsAbout("x", "xo") & accArithTactic
          ) & print("Acceleration branch done")
        ) & print("Induction step done")
      ) & print("Proof done")
    proveBy(s, tactic) shouldBe 'proved
  }

  // todo: robix proof with let inv=bla in ...
  // todo: also try to get distance letified...

  it should "prove just the acceleration x arithmetic" in withMathematica { implicit qeTool =>
    val accArith = "A>=0 & B>0 & V()>=0 & ep>0 & v_0>=0 & -B<=a & a<=A & abs(x_0-xo_0)>v_0^2/(2*B)+V()*v_0/B+(A/B+1)*(A/2*ep^2+ep*(v_0+V())) & -t*V()<=xo-xo_0 & xo-xo_0<=t*V() & v=v_0+a*t & -t*(v-a/2*t)<=x-x_0 & x-x_0<=t*(v-a/2*t) & t>=0 & t<=ep & v>=0 -> v=0|abs(x-xo)>v^2/(2*B)+V()*(v/B)".asFormula

    val tactic = alphaRule*@TheType() & replaceTransform("ep".asTerm, "t".asTerm)(-8, "abs(x_0-xo_0)>v_0^2/(2*B)+V()*v_0/B+(A/B+1)*(A/2*ep^2+ep*(v_0+V()))".asFormula) &
      hideR(1, "v=0".asFormula) & hideL(-15, "t<=ep".asFormula) & hideL(-4, "ep>0".asFormula) &
      abs(1, 0::Nil) & abs(-7, 0::Nil) & orL(-16) & OnAll(orL(-15) partial) &
      OnAll(andL('_)*@TheType() partial) & OnAll(exhaustiveEqL2R(hide=true)('L)*@TheType() partial) <(
        hideL(-11, "x-x_0<=t*(v_0+a*t-a/2*t)".asFormula) & hideL(-8, "-t*V()<=xo-xo_0".asFormula) & QE,
        hideR(1) & QE,
        hideR(1) & QE,
        hideL(-10, "-t*(v_0+a*t-a/2*t)<=x-x_0".asFormula) & hideL(-9, "xo-xo_0<=t*V()".asFormula) & QE
        )

    proveBy(accArith, tactic) shouldBe 'proved
  }

  it should "prove just the acceleration y arithmetic" in withMathematica { implicit qeTool =>
    val accArith = "A>=0&B>0&V()>=0&ep>0&v_0>=0&-B<=a&a<=A&abs(y_0-yo_0)>v_0^2/(2*B)+V()*v_0/B+(A/B+1)*(A/2*ep^2+ep*(v_0+V()))&-t*V()<=yo-yo_0&yo-yo_0<=t*V()&-t*(v-a/2*t)<=y-y_0&y-y_0<=t*(v-a/2*t)&v=v_0+a*t&t>=0&t<=ep&v>=0->v=0|abs(y-yo)>v^2/(2*B)+V()*(v/B)".asFormula

    val tactic = alphaRule*@TheType() &
      replaceTransform("ep".asTerm, "t".asTerm)(-8, "abs(y_0-yo_0)>v_0^2/(2*B)+V()*v_0/B+(A/B+1)*(A/2*ep^2+ep*(v_0+V()))".asFormula) &
      hideR(1, "v=0".asFormula) & hideL(-15, "t<=ep".asFormula) & hideL(-4, "ep>0".asFormula) &
      abs(1, 0::Nil) & abs(-7, 0::Nil) & orL(-16) & OnAll(orL(-15) partial) &
      OnAll(andL('_)*@TheType() partial) & OnAll(exhaustiveEqL2R(hide=true)('L)*@TheType() partial) <(
        hideL(-11, "y-y_0<=t*(v_0+a*t-a/2*t)".asFormula) & hideL(-8, "-t*V()<=yo-yo_0".asFormula) & QE,
        hideR(1) & QE,
        hideR(1) & QE,
        hideL(-10, "-t*(v_0+a*t-a/2*t)<=y-y_0".asFormula) & hideL(-9, "yo-yo_0<=t*V()".asFormula) & QE
        )

    proveBy(accArith, tactic) shouldBe 'proved
  }

  "Passive Safety straight and curve" should "be provable" in withMathematica { implicit qeTool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/robix/passivesafetyabs_curvestraight.key"))

    val invariant = """v >= 0
                      | & dx^2+dy^2 = 1
                      | & r != 0
                      | & (v = 0 | abs(x-xo) > v^2 / (2*B) + V*(v/B)
                      |          | abs(y-yo) > v^2 / (2*B) + V*(v/B))""".stripMargin.asFormula

    def di(a: String): DependentPositionTactic = diffInvariant(
      "t>=0".asFormula,
      "dx^2 + dy^2 = 1".asFormula,
      s"v = old(v) + $a*t".asFormula,
      s"-t * (v - $a/2*t) <= x - old(x) & x - old(x) <= t * (v - $a/2*t)".asFormula,
      s"-t * (v - $a/2*t) <= y - old(y) & y - old(y) <= t * (v - $a/2*t)".asFormula,
      "-t * V <= xo - old(xo) & xo - old(xo) <= t * V".asFormula,
      "-t * V <= yo - old(yo) & yo - old(yo) <= t * V".asFormula)

    val dw: BelleExpr = exhaustiveEqR2L(hide=true)('Llast)*5 /* 5 old(...) in DI */ & andL('_)*@TheType() &
      debug("Before diffWeaken") & diffWeaken(1) & debug("After diffWeaken")

    val hideIrrelevantAssumptions: BelleExpr =
      OnAll(
        hideL(Find.FindL(0, Some("dx^2+dy^2=1".asFormula))) &
          hideL(Find.FindL(0, Some("r!=0".asFormula))) &
          hideL(Find.FindL(0, Some("dxo^2+dyo^2<=V^2".asFormula))) partial)

    val brakeStoppedArith: BelleExpr =
      hideIrrelevantAssumptions <(
        hideR(3, "abs(y-yo)>v^2/(2*B)+V*(v/B)".asFormula) & hideR(2, "abs(x-xo)>v^2/(2*B)+V*(v/B)".asFormula) & QE,
        hideR(3, "abs(y-yo)>v^2/(2*B)+V*(v/B)".asFormula) & QE,
        hideR(2, "abs(x-xo)>v^2/(2*B)+V*(v/B)".asFormula) & QE)

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

    val accArithX = "A>=0 & B>0 & V>=0 & ep>0 & abs(x_0-xo_0)>v_0^2/(2*B)+V*v_0/B+(A/B+1)*(A/2*ep^2+ep*(v_0+V)) & v_0>=0 & -B<=a & a<=A & -t*V<=xo-xo_0 & xo-xo_0<=t*V & v=v_0+a*t & -t*(v-a/2*t)<=x-x_0 & x-x_0<=t*(v-a/2*t) & t>=0 & t<=ep & v>=0 -> abs(x-xo)>v^2/(2*B)+V*(v/B)".asFormula
    val accArithXLemma = proveBy(accArithX, accArithTactic("abs(x_0-xo_0)>v_0^2/(2*B)+V*v_0/B+(A/B+1)*(A/2*t^2+t*(v_0+V))".asFormula))
    accArithXLemma shouldBe 'proved

    val accArithY = "A>=0 & B>0 & V>=0 & ep>0 & abs(y_0-yo_0)>v_0^2/(2*B)+V*v_0/B+(A/B+1)*(A/2*ep^2+ep*(v_0+V)) & v_0>=0 & -B<=a & a<=A & -t*V<=yo-yo_0 & yo-yo_0<=t*V & -t*(v-a/2*t)<=y-y_0 & y-y_0<=t*(v-a/2*t) & v=v_0+a*t & t>=0 & t<=ep & v>=0 -> abs(y-yo)>v^2/(2*B)+V*(v/B)".asFormula
    val accArithYLemma = proveBy(accArithY, accArithTactic("abs(y_0-yo_0)>v_0^2/(2*B)+V*v_0/B+(A/B+1)*(A/2*t^2+t*(v_0+V))".asFormula))
    accArithYLemma shouldBe 'proved

    val tactic = implyR('_) & andL('_)*@TheType() & loop(invariant)('R) <(
      /* base case */ QE & debug("Base case done"),
      /* use case */ QE & debug("Use case done"),
      /* induction step */ chase(1) & allR(1)*2 & implyR(1) & andR(1) <(
        debug("Braking branch") & allR(1) & implyR(1) & andR(1) <(
          implyR(1) & di("-B")(1) & dw & prop & brakeStoppedArith & debug("Braking branch 1 done"),
          implyR(1) & di("-B")(1) & dw & prop & brakeStoppedArith & debug("Braking branch 2 done")
          ),
        debug("Free drive branch") & andR(1) <(
          (implyR(1) & allR(1))*2 & implyR(1) & andR(1) <(
            implyR(1) & andL('_)*@TheType() & hideL(Find.FindL(0, Some("v=0|abs(x-xo)>v^2/(2*B)+V*(v/B)|abs(y-yo)>v^2/(2*B)+V*(v/B)".asFormula))) & di("0")(1) & dw & prop
              & hideIrrelevantAssumptions & hideR(3, "abs(y-yo)>v^2/(2*B)+V*(v/B)".asFormula) & hideR(2, "abs(x-xo)>v^2/(2*B)+V*(v/B)".asFormula) & QE & debug("Free drive branch 1 done"),
            implyR(1) & andL('_)*@TheType() & hideL(Find.FindL(0, Some("v=0|abs(x-xo)>v^2/(2*B)+V*(v/B)|abs(y-yo)>v^2/(2*B)+V*(v/B)".asFormula))) & di("-B")(1) & dw & prop
              & hideIrrelevantAssumptions & hideR(3, "abs(y-yo)>v^2/(2*B)+V*(v/B)".asFormula) & hideR(2, "abs(x-xo)>v^2/(2*B)+V*(v/B)".asFormula) & QE & debug("Free drive branch 2 done")
            ),
            allR (1) & implyR(1) & andR(1) <(
              allR(1) & implyR(1) & allR(1)*2 & implyR(1) & allR(1) & implyR(1) & andR(1) <(
                implyR(1) & andL('_)*@TheType() & hideL(Find.FindL(0, Some("v=0|abs(x-xo_0)>v^2/(2*B)+V*(v/B)|abs(y-yo_0)>v^2/(2*B)+V*(v/B)".asFormula))) & di("a")(1) & dw & prop
                  & hideIrrelevantAssumptions <(
                    hideR(3, "abs(y-yo)>v^2/(2*B)+V*(v/B)".asFormula) & hideR(1, "v=0".asFormula)
                      & hideL(-20, "dx^2+dy^2=1".asFormula)
                      & hideL(-16, "y-y_0<=t*(v-a/2*t)".asFormula) & hideL(-15, "-t*(v-a/2*t)<=y-y_0".asFormula)
                      & hideL(-12, "yo-yo_0<=t*V".asFormula) & hideL(-11, "-t*V<=yo-yo_0".asFormula)
                      & hideL(-7, "w=0".asFormula) & hideL(-5, "w=0".asFormula)
                      & PropositionalTactics.toSingleFormula & by(accArithXLemma) & debug("Free drive branch 3 done"),
                    hideR(2, "abs(x-xo)>v^2/(2*B)+V*(v/B)".asFormula) & hideR(1, "v=0".asFormula)
                      & hideL(-20, "dx^2+dy^2=1".asFormula)
                      & hideL(-19, "x-x_0<=t*(v-a/2*t)".asFormula) & hideL(-18, "-t*(v-a/2*t)<=x-x_0".asFormula)
                      & hideL(-14, "xo-xo_0<=t*V".asFormula) & hideL(-13, "-t*V<=xo-xo_0".asFormula)
                      & hideL(-7, "w=0".asFormula) & hideL(-5, "w=0".asFormula)
                      & PropositionalTactics.toSingleFormula & by(accArithYLemma) & debug("Free drive branch 4 done")
                  ),
                implyR(1) & andL('_)*@TheType() & cutL("!w=0".asFormula)(AntePos(8)) <(
                    notL(-9, "!w=0".asFormula) & closeId  & debug("Free drive branch 5 done"),
                    hideR(1, "[{x'=v*dx,y'=v*dy,dx'=-w*dy,dy'=w*dx,v'=a,w'=a/r,xo'=dxo,yo'=dyo,t'=1&t<=ep&v>=0}](v>=0&dx^2+dy^2=1&r!=0&(v=0|abs(x-xo)>v^2/(2*B)+V*(v/B)|abs(y-yo)>v^2/(2*B)+V*(v/B)))".asFormula)
                      & implyR(1) & QE & debug("Free drive branch 6 done")
                  )
                ),
              (allR(1) & implyR(1))*2 & allR(1)*2 & implyR(1) & allR(1) & implyR(1) & andR(1) <(
                implyR(1) & andL('_)*@TheType() & hideL(Find.FindL(0, Some("v=0|abs(x-xo_0)>v^2/(2*B)+V*(v/B)|abs(y-yo_0)>v^2/(2*B)+V*(v/B)".asFormula))) & di("a")(1) & dw & prop
                  & hideIrrelevantAssumptions <(
                    hideR(3, "abs(y-yo)>v^2/(2*B)+V*(v/B)".asFormula) & hideR(1, "v=0".asFormula)
                      & hideL(-21, "dx^2+dy^2=1".asFormula)
                      & hideL(-17, "y-y_0<=t*(v-a/2*t)".asFormula) & hideL(-16, "-t*(v-a/2*t)<=y-y_0".asFormula)
                      & hideL(-13, "yo-yo_0<=t*V".asFormula) & hideL(-12, "-t*V<=yo-yo_0".asFormula)
                      & hideL(-11, "r_0!=0".asFormula) & hideL(-7, "w=0".asFormula) & hideL(-5, "w*r=v_0".asFormula)
                      & PropositionalTactics.toSingleFormula & by(accArithXLemma) & debug("Free drive branch 7 done"),
                    hideR(2, "abs(x-xo)>v^2/(2*B)+V*(v/B)".asFormula) & hideR(1, "v=0".asFormula)
                      & hideL(-21, "dx^2+dy^2=1".asFormula)
                      & hideL(-20, "x-x_0<=t*(v-a/2*t)".asFormula) & hideL(-19, "-t*(v-a/2*t)<=x-x_0".asFormula)
                      & hideL(-15, "xo-xo_0<=t*V".asFormula) & hideL(-14, "-t*V<=xo-xo_0".asFormula)
                      & hideL(-11, "r_0!=0".asFormula) & hideL(-7, "w=0".asFormula) & hideL(-5, "w*r=v_0".asFormula)
                      & PropositionalTactics.toSingleFormula & by(accArithYLemma) & debug("Free drive branch 8 done")
                  ),
                implyR(1) & andL('_)*@TheType() & hideL(Find.FindL(0, Some("v=0|abs(x-xo_0)>v^2/(2*B)+V*(v/B)|abs(y-yo_0)>v^2/(2*B)+V*(v/B)".asFormula))) & di("a")(1) & dw & prop
                  & hideIrrelevantAssumptions <(
                    hideR(3, "abs(y-yo)>v^2/(2*B)+V*(v/B)".asFormula) & hideR(1, "v=0".asFormula)
                      & hideL(-15, "y-y_0<=t*(v-a/2*t)".asFormula) & hideL(-14, "-t*(v-a/2*t)<=y-y_0".asFormula)
                      & hideL(-11, "yo-yo_0<=t*V".asFormula) & hideL(-10, "-t*V<=yo-yo_0".asFormula)
                      & hideL(-9, "r_0!=0".asFormula)
                      & PropositionalTactics.toSingleFormula & by(accArithXLemma) & debug("Free drive branch 9 done"),
                    hideR(2, "abs(x-xo)>v^2/(2*B)+V*(v/B)".asFormula) & hideR(1, "v=0".asFormula)
                      & hideL(-18, "x-x_0<=t*(v-a/2*t)".asFormula) & hideL(-17, "-t*(v-a/2*t)<=x-x_0".asFormula)
                      & hideL(-13, "xo-xo_0<=t*V".asFormula) & hideL(-12, "-t*V<=xo-xo_0".asFormula)
                      & hideL(-9, "r_0!=0".asFormula)
                      & PropositionalTactics.toSingleFormula & by(accArithYLemma) & debug("Free drive branch 10 done")
                  )
                )
              )
          )
        ) & debug("Induction step done")
      ) & debug("Proof done")

    proveBy(s, tactic) shouldBe 'proved
  }

  "Passive Safety straight and curve using curvature" should "be provable" in withMathematica { implicit qeTool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/robix/passivesafetyabs_curvestraight_curvature.key"))

    val invariant =
      """v >= 0
                      | & dx^2+dy^2 = 1
                      | & (v = 0 | abs(x-xo) > v^2 / (2*B) + V*(v/B)
                      |          | abs(y-yo) > v^2 / (2*B) + V*(v/B))""".stripMargin.asFormula

    def di(a: String): DependentPositionTactic = diffInvariant(
      "t>=0".asFormula,
      "dx^2 + dy^2 = 1".asFormula,
      s"v = old(v) + $a*t".asFormula,
      s"-t * (v - $a/2*t) <= x - old(x) & x - old(x) <= t * (v - $a/2*t)".asFormula,
      s"-t * (v - $a/2*t) <= y - old(y) & y - old(y) <= t * (v - $a/2*t)".asFormula,
      "-t * V <= xo - old(xo) & xo - old(xo) <= t * V".asFormula,
      "-t * V <= yo - old(yo) & yo - old(yo) <= t * V".asFormula)
    
    val dw: BelleExpr = exhaustiveEqR2L(hide=true)('Llast)*5 /* 5 old(...) in DI */ & andL('_)*@TheType() &
      debug("Before diffWeaken") & diffWeaken(1) & debug("After diffWeaken")

    def accArithTactic: BelleExpr = alphaRule*@TheType() &
      //@todo auto-transform
      replaceTransform("ep".asTerm, "t".asTerm)(-8) & speculativeQE & print("Proved acc arithmetic")

    val tactic = implyR('_) & andL('_)*@TheType() & loop(invariant)('R) <(
      /* base case */ print("Base case...") & speculativeQE & print("Base case done"),
      /* use case */ print("Use case...") & speculativeQE & print("Use case done"),
      /* induction step */ print("Induction step") & chase(1) & normalize(andR('R), skip, skip) & printIndexed("After normalize") <(
      print("Braking branch") & di("-B")(1) & dw & prop & OnAll(speculativeQE) & print("Braking branch done"),
      print("Stopped branch") & di("0")(1) & dw & prop & OnAll(speculativeQE) & print("Stopped branch done"),
      print("Acceleration branch") & hideL(Find.FindL(0, Some("v=0|abs(x-xo_0)>v^2/(2*B)+V*(v/B)|abs(y-yo_0)>v^2/(2*B)+V*(v/B)".asFormula))) &
        di("a")(1) & dw & prop & OnAll(hideFactsAbout("dx", "dy", "dxo", "dyo", "k", "k_0") partial) <(
        hideFactsAbout("y", "yo") & accArithTactic,
        hideFactsAbout("x", "xo") & accArithTactic
        ) & print("Acceleration branch done")
      ) & print("Induction step done")
      ) & print("Proof done")
    proveBy(s, tactic) shouldBe 'proved
  }

  "Passive Safety straight and curve using curvature with additional braking branch" should "be provable" in withMathematica { implicit qeTool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/robix/passivesafetyabs_curvestraight_curvature_lightbrake.key"))

    val invariant =
      """v >= 0
        | & dx^2+dy^2 = 1
        | & (v = 0 | abs(x-xo) > v^2 / (2*B) + V*(v/B)
        |          | abs(y-yo) > v^2 / (2*B) + V*(v/B))""".stripMargin.asFormula

    def di(a: String): DependentPositionTactic = diffInvariant(
      "t>=0".asFormula,
      "dx^2 + dy^2 = 1".asFormula,
      s"v = old(v) + $a*t".asFormula,
      s"-t * (v - $a/2*t) <= x - old(x) & x - old(x) <= t * (v - $a/2*t)".asFormula,
      s"-t * (v - $a/2*t) <= y - old(y) & y - old(y) <= t * (v - $a/2*t)".asFormula,
      "-t * V <= xo - old(xo) & xo - old(xo) <= t * V".asFormula,
      "-t * V <= yo - old(yo) & yo - old(yo) <= t * V".asFormula)

    val dw: BelleExpr = exhaustiveEqR2L(hide=true)('Llast)*5 /* 5 old(...) in DI */ & andL('_)*@TheType() &
      debug("Before diffWeaken") & diffWeaken(1) & debug("After diffWeaken")

    def accArithTactic: BelleExpr = alphaRule*@TheType() &
      //@todo auto-transform
      replaceTransform("ep".asTerm, "t".asTerm)(-8) & speculativeQE & print("Proved acc arithmetic")

    val tactic = implyR('_) & andL('_)*@TheType() & loop(invariant)('R) <(
      /* base case */ print("Base case...") & speculativeQE & print("Base case done"),
      /* use case */ print("Use case...") & speculativeQE & print("Use case done"),
      /* induction step */ print("Induction step") & chase(1) & normalize(andR('R), skip, skip) & printIndexed("After normalize") <(
      print("Braking branch") & di("-B")(1) & dw & prop & OnAll(speculativeQE) & print("Braking branch done"),
      print("Light braking branch") & hideL(Find.FindL(0, Some("v=0|abs(x-xo)>v^2/(2*B)+V*(v/B)|abs(y-yo)>v^2/(2*B)+V*(v/B)".asFormula))) &
        di("-B/2")(1) & dw & prop & OnAll(hideFactsAbout("dx", "dy", "dxo", "dyo", "k", "k_0") partial) <(
        hideFactsAbout("y", "yo") & speculativeQE,
        hideFactsAbout("x", "xo") & speculativeQE
        ) & print("Light braking branch done"),
      print("Stopped branch") & di("0")(1) & dw & prop & OnAll(speculativeQE) & print("Stopped branch done"),
      print("Acceleration branch") & hideL(Find.FindL(0, Some("v=0|abs(x-xo_0)>v^2/(2*B)+V*(v/B)|abs(y-yo_0)>v^2/(2*B)+V*(v/B)".asFormula))) &
        di("a")(1) & dw & prop & OnAll(hideFactsAbout("dx", "dy", "dxo", "dyo", "k", "k_0") partial) <(
        hideFactsAbout("y", "yo") & accArithTactic,
        hideFactsAbout("x", "xo") & accArithTactic
        ) & print("Acceleration branch done")
      ) & print("Induction step done")
      ) & print("Proof done")
    proveBy(s, tactic) shouldBe 'proved
  }

  "Passive orientation safety" should "be provable" in withMathematica { implicit qeTool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/robix/passiveorientationsafetyabs.key"))
    val invariant =
      """v>=0
        | & dx^2+dy^2=1
        | & r!=0
        | & (v=0 | (abs(beta) + v^2/(2*b*abs(r)) < gamma
        |          & (isVisible < 0 | abs(x-ox) > v^2/(2*b) + V*(v/b) | abs(y-oy) > v^2/(2*b) + V*(v/b))))
      """.stripMargin.asFormula

    def di(a: String): DependentPositionTactic = diffInvariant(
      "t>=0".asFormula,
      "dx^2 + dy^2 = 1".asFormula,
      s"v = old(v) + $a*t".asFormula,
      s"-t * (v - $a/2*t) <= x - old(x) & x - old(x) <= t * (v - $a/2*t)".asFormula,
      s"-t * (v - $a/2*t) <= y - old(y) & y - old(y) <= t * (v - $a/2*t)".asFormula,
      "-t * V <= ox - old(ox) & ox - old(ox) <= t * V".asFormula,
      "-t * V <= oy - old(oy) & oy - old(oy) <= t * V".asFormula,
      "w*r = v".asFormula,
      s"beta = old(beta) + t/r*(v - $a/2*t)".asFormula)

    val dw: BelleExpr = exhaustiveEqR2L(hide=true)('Llast)*6 /* 6 old(...) in DI */ & andL('L)*@TheType() &
      print("Before diffWeaken") & diffWeaken(1) & print("After diffWeaken")

    val allImplyTactic = ((allR('R)*@TheType() & implyR('R))*@TheType())*@TheType()

    val tactic = implyR('R) & andL('L)*@TheType() & loop(invariant)('R) <(
      /* base case */ QE & print("Base case done"),
      /* use case */ QE & print("Use case done"),
      /* step */ andL('L)*@TheType() & chase('R) & allR('R)*2 & implyR('R) & andR('R) <(
        print("Braking") & allImplyTactic & di("-b")('R) & dw & alphaRule*@TheType() & print("After alpha braking") &
          (andR('R) <(closeId, skip))*3 & orR('R) & passiveOrientationBrakingArithTactic & print("Braking branch done"),
        andR('R) <(
          print("Stopped") & allImplyTactic & di("0")('R) & dw & alphaRule*@TheType() & print("After alpha stopped") &
            (andR('R) <(closeId, skip))*3 & orR('R) & passiveOrientationStoppedArithTactic & print("Stopped branch done"),
          print("Accelerating") & allImplyTactic & di("A")('R) & dw & alphaRule*@TheType() & print("After alpha accelerating") &
            (andR('R) <(closeId, skip))*3 & orR('R) & passiveOrientationAccArithTactic & print("Acc branch done")
          )
        )
      )

    proveBy(s, tactic) shouldBe 'proved
  }

  def passiveOrientationBrakingArithTactic: BelleExpr =
    orL(-8, "v_0=0|abs(beta_0)+v_0^2/(2*b*abs(r)) < gamma&(isVisible < 0|abs(x_0-ox_0)>v_0^2/(2*b)+V*(v_0/b)|abs(y_0-oy_0)>v_0^2/(2*b)+V*(v_0/b))".asFormula) <(
    hideR(2) & QE,
    andL('L) & andR('R) <(
      QE,
      hideL(-24, "abs(beta_0)+v_0^2/(2*b*abs(r)) < gamma".asFormula) &
        hideL(-9, "beta=beta_0+t/r*(v--b/2*t)".asFormula) &
        orR('R)*@TheType() &
        orL('Llast, "isVisible < 0|abs(x_0-ox_0)>v_0^2/(2*b)+V*(v_0/b)|abs(y_0-oy_0)>v_0^2/(2*b)+V*(v_0/b)".asFormula) <(
          closeId,
          hideR(2, "isVisible < 0".asFormula) & hideR(1, "v=0".asFormula) & hideL(-21, "t<=ep".asFormula) &
            hideL(-19, "dx^2+dy^2=1".asFormula) & hideL(-9, "w*r=v".asFormula) & hideL(-8, "odx^2+ody^2<=V^2".asFormula) &
            hideL(-7, "r!=0".asFormula) & hideL(-5, "gamma>0".asFormula) & hideL(-4, "ep>0".asFormula) &
            orL('Llast, "abs(x_0-ox_0)>v_0^2/(2*b)+V*(v_0/b)|abs(y_0-oy_0)>v_0^2/(2*b)+V*(v_0/b)".asFormula) <(
              hideR(2, "abs(y-oy)>v^2/(2*b)+V*(v/b)".asFormula) & hideL(-10, "y-y_0<=t*(v--b/2*t)".asFormula) & hideL(-9, "-t*(v--b/2*t)<=y-y_0".asFormula) & hideL(-6, "oy-oy_0<=t*V".asFormula) & hideL(-5, "-t*V<=oy-oy_0".asFormula) & QE,
              hideR(1, "abs(x-ox)>v^2/(2*b)+V*(v/b)".asFormula) & hideL(-13, "x-x_0<=t*(v--b/2*t)".asFormula) & hideL(-12, "-t*(v--b/2*t)<=x-x_0".asFormula) & hideL(-8, "ox-ox_0<=t*V".asFormula) & hideL(-7, "-t*V<=ox-ox_0".asFormula) & QE
              )
          )
      )
    )
  
  it should "prove just braking arithmetic" in withMathematica { tool =>
    val fml = """V>=0 & A>=0 & b>0 & ep>0 & gamma>0 & v_0>=0 & r!=0 & (v_0=0|abs(beta_0)+v_0^2/(2*b*abs(r)) < gamma&(isVisible < 0|abs(x_0-ox_0)>v_0^2/(2*b)+V*(v_0/b)|abs(y_0-oy_0)>v_0^2/(2*b)+V*(v_0/b))) & odx^2+ody^2<=V^2 & beta=beta_0+t/r*(v--b/2*t) & w*r=v & -t*V<=oy-oy_0 & oy-oy_0<=t*V & -t*V<=ox-ox_0 & ox-ox_0<=t*V & -t*(v--b/2*t)<=y-y_0 & y-y_0<=t*(v--b/2*t) & v=v_0+-b*t & -t*(v--b/2*t)<=x-x_0 & x-x_0<=t*(v--b/2*t) & dx^2+dy^2=1 & t>=0 & t<=ep & v>=0
                |  -> v=0|abs(beta)+v^2/(2*b*abs(r)) < gamma&(isVisible < 0|abs(x-ox)>v^2/(2*b)+V*(v/b)|abs(y-oy)>v^2/(2*b)+V*(v/b))""".stripMargin.asFormula

    val tactic = implyR('R) & andL('L)*@TheType() & orR('R) & passiveOrientationBrakingArithTactic

    proveBy(fml, tactic) shouldBe 'proved
  }

  def passiveOrientationStoppedArithTactic: BelleExpr =
    orL(-8, "v_0=0|abs(beta_0)+v_0^2/(2*b*abs(r)) < gamma&(isVisible < 0|abs(x_0-ox_0)>v_0^2/(2*b)+V*(v_0/b)|abs(y_0-oy_0)>v_0^2/(2*b)+V*(v_0/b))".asFormula) <(
      hideR(2) & QE,
      andL('L) & andR('R) <(
        QE,
        hideL(-25, "abs(beta_0)+v_0^2/(2*b*abs(r)) < gamma".asFormula) &
          hideL(-10, "beta=beta_0+t/r*(v-0/2*t)".asFormula) &
          orR('R)*@TheType() &
          orL('Llast, "isVisible < 0|abs(x_0-ox_0)>v_0^2/(2*b)+V*(v_0/b)|abs(y_0-oy_0)>v_0^2/(2*b)+V*(v_0/b)".asFormula) <(
            closeId,
            hideR(4, "abs(y-oy)>v^2/(2*b)+V*(v/b)".asFormula) & hideR(3, "abs(x-ox)>v^2/(2*b)+V*(v/b)".asFormula) &
              hideR(2, "isVisible < 0".asFormula) &
              hideL(-22, "t<=ep".asFormula) & hideL(-10, "w*r=v".asFormula) & hideL(-7, "r!=0".asFormula) &
              hideL(-5, "gamma>0".asFormula) & hideL(-4, "ep>0".asFormula) & hideL(-15, "x-x_0<=t*(v-0/2*t)".asFormula) &
              hideL(-14, "-t*(v-0/2*t)<=x-x_0".asFormula) & hideL(-12, "y-y_0<=t*(v-0/2*t)".asFormula) &
              hideL(-11, "-t*(v-0/2*t)<=y-y_0".asFormula) & hideL(-10, "ox-ox_0<=t*V".asFormula) &
              hideL(-9, "-t*V<=ox-ox_0".asFormula) & hideL(-8, "oy-oy_0<=t*V".asFormula) &
              hideL(-7, "-t*V<=oy-oy_0".asFormula) & QE
            )
        )
      )

  it should "prove just stopped arithmetic" in withMathematica { tool =>
    val fml = """V>=0 & A>=0 & b>0 & ep>0 & gamma>0 & v_0>=0 & r!=0 & (v_0=0|abs(beta_0)+v_0^2/(2*b*abs(r)) < gamma&(isVisible < 0|abs(x_0-ox_0)>v_0^2/(2*b)+V*(v_0/b)|abs(y_0-oy_0)>v_0^2/(2*b)+V*(v_0/b))) & odx^2+ody^2<=V^2 & v_0=0 & beta=beta_0+t/r*(v-0/2*t) & w*r=v & -t*V<=oy-oy_0 & oy-oy_0<=t*V & -t*V<=ox-ox_0 & ox-ox_0<=t*V & -t*(v-0/2*t)<=y-y_0 & y-y_0<=t*(v-0/2*t) & v=v_0+0*t & -t*(v-0/2*t)<=x-x_0 & x-x_0<=t*(v-0/2*t) & dx^2+dy^2=1 & t>=0 & t<=ep & v>=0
                |  -> v=0|abs(beta)+v^2/(2*b*abs(r)) < gamma&(isVisible < 0|abs(x-ox)>v^2/(2*b)+V*(v/b)|abs(y-oy)>v^2/(2*b)+V*(v/b))""".stripMargin.asFormula

    val tactic = implyR('R) & andL('L)*@TheType() & orR('R) & passiveOrientationStoppedArithTactic

    proveBy(fml, tactic) shouldBe 'proved
  }

  def passiveOrientationAccArithTactic: BelleExpr =
    hideL(-25, "dx^2+dy^2=1".asFormula) & hideL(-15, "w*r=v".asFormula) & hideL(-9, "odx^2+ody^2<=V^2".asFormula) &
    hideL(-8, "v_0=0|abs(beta_0)+v_0^2/(2*b*abs(r_0)) < gamma&(isVisible_0 < 0|abs(x_0-ox_0)>v_0^2/(2*b)+V*(v_0/b)|abs(y_0-oy_0)>v_0^2/(2*b)+V*(v_0/b))".asFormula) &
    hideL(-7, "r_0!=0".asFormula) & hideR(1, "v=0".asFormula) & andR('R) <(
      hideL(-8, "isVisible < 0|abs(x_0-ox_1)>v_0^2/(2*b)+V*(v_0/b)+(A/b+1)*(A/2*ep^2+ep*(v_0+V))|abs(y_0-oy_1)>v_0^2/(2*b)+V*(v_0/b)+(A/b+1)*(A/2*ep^2+ep*(v_0+V))".asFormula) & QE,
      orR('R)*2 & orL(-8, "isVisible < 0|abs(x_0-ox_1)>v_0^2/(2*b)+V*(v_0/b)+(A/b+1)*(A/2*ep^2+ep*(v_0+V))|abs(y_0-oy_1)>v_0^2/(2*b)+V*(v_0/b)+(A/b+1)*(A/2*ep^2+ep*(v_0+V))".asFormula) <(
        closeId,
        hideR(1, "isVisible < 0".asFormula) & hideL(-11, "beta=beta_1+t/r*(v-A/2*t)".asFormula) & hideL(-10, "beta_1=0".asFormula) &
          hideL(-9, "v_0^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v_0) < gamma*abs(r)".asFormula) & hideL(-7, "r!=0".asFormula) & hideL(-5, "gamma>0".asFormula) &
          orL(-6, "abs(x_0-ox_1)>v_0^2/(2*b)+V*(v_0/b)+(A/b+1)*(A/2*ep^2+ep*(v_0+V))|abs(y_0-oy_1)>v_0^2/(2*b)+V*(v_0/b)+(A/b+1)*(A/2*ep^2+ep*(v_0+V))".asFormula) <(
            hideR(2, "abs(y-oy)>v^2/(2*b)+V*(v/b)".asFormula) & hideL(-12, "y-y_0<=t*(v-A/2*t)".asFormula) &
              hideL(-11, "-t*(v-A/2*t)<=y-y_0".asFormula) & hideL(-8, "oy-oy_1<=t*V".asFormula) & hideL(-7, "-t*V<=oy-oy_1".asFormula) &
              abs(1, 0::Nil) & abs(-6, 0::Nil) &
              orL(-16, "x_0-ox_1>=0&abs_1=x_0-ox_1|x_0-ox_1 < 0&abs_1=-(x_0-ox_1)".asFormula) <(
                andL('L) & hideL(-11, "x-x_0<=t*(v-A/2*t)".asFormula) & hideL(-7, "-t*V<=ox-ox_1".asFormula) &
                orL(-13, "x-ox>=0&abs_0=x-ox|x-ox < 0&abs_0=-(x-ox)".asFormula) <(
                  print("Foo 1") & QE,
                  hideR(1) & print("Foo 2") & QE
                  ),
                andL('L) & hideL(-10, "-t*(v-A/2*t)<=x-x_0".asFormula) & hideL(-8, "ox-ox_1<=t*V".asFormula) &
                orL(-13, "x-ox>=0&abs_0=x-ox|x-ox < 0&abs_0=-(x-ox)".asFormula) <(
                  hideR(1) & print("Foo 3") & QE,
                  cutL("abs_1>v_0^2/(2*b)+V*(v_0/b)+(A/b+1)*(A/2*t^2+t*(v_0+V))".asFormula)(AntePos(5)) <(
                    hideL(-11, "t<=ep".asFormula) & hideL(-4, "ep>0".asFormula) & print("Foo 4") & QE,
                    hideR(1, "abs_0>v^2/(2*b)+V*(v/b)".asFormula) & print("Foo 5") & QE
                    )
                  )

              ),
            hideR(1, "abs(x-ox)>v^2/(2*b)+V*(v/b)".asFormula) & hideL(-15, "x-x_0<=t*(v-A/2*t)".asFormula) &
              hideL(-14, "-t*(v-A/2*t)<=x-x_0".asFormula) & hideL(-10, "ox-ox_1<=t*V".asFormula) & hideL(-9, "-t*V<=ox-ox_1".asFormula) &
              abs(1, 0::Nil) & abs(-6, 0::Nil) & cutL("abs_1>v_0^2/(2*b)+V*(v_0/b)+(A/b+1)*(A/2*t^2+t*(v_0+V))".asFormula)(AntePos(5)) <(
                hideL(-13, "t<=ep".asFormula) & hideL(-4, "ep>0".asFormula) &
                orL(-14, "y_0-oy_1>=0&abs_1=y_0-oy_1|y_0-oy_1 < 0&abs_1=-(y_0-oy_1)".asFormula) <(
                  andL('L) & hideL(-9, "y-y_0<=t*(v-A/2*t)".asFormula) & hideL(-6, "-t*V<=oy-oy_1".asFormula) &
                  orL(-11, "y-oy>=0&abs_0=y-oy|y-oy < 0&abs_0=-(y-oy)".asFormula) <(
                    print("Bar 1") & QE,
                    hideR(1) & print("Bar 2") & QE
                    ),
                  andL('L) & hideL(-8, "-t*(v-A/2*t)<=y-y_0".asFormula) & hideL(-7, "oy-oy_1<=t*V".asFormula) &
                  orL(-11, "y-oy>=0&abs_0=y-oy|y-oy < 0&abs_0=-(y-oy)".asFormula) <(
                    hideR(1) & print("Bar 3") & QE,
                    print("Bar 4") & QE
                    )
                  ),
                hideR(1, "abs_0>v^2/(2*b)+V*(v/b)".asFormula) & print("Bar 5") & QE
              )
            )
        )
      )

  it should "prove just acceleration arithmetic" in withMathematica { tool =>
    val fml = """V>=0 & A>=0 & b>0 & ep>0 & gamma>0 & v_0>=0 & r_0!=0 & (v_0=0|abs(beta_0)+v_0^2/(2*b*abs(r_0)) < gamma&(isVisible_0 < 0|abs(x_0-ox_0)>v_0^2/(2*b)+V*(v_0/b)|abs(y_0-oy_0)>v_0^2/(2*b)+V*(v_0/b))) & odx^2+ody^2<=V^2 & r!=0 & (isVisible < 0|abs(x_0-ox_1)>v_0^2/(2*b)+V*(v_0/b)+(A/b+1)*(A/2*ep^2+ep*(v_0+V))|abs(y_0-oy_1)>v_0^2/(2*b)+V*(v_0/b)+(A/b+1)*(A/2*ep^2+ep*(v_0+V))) & v_0^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v_0) < gamma*abs(r) & beta_1=0 & beta=beta_1+t/r*(v-A/2*t) & w*r=v & -t*V<=oy-oy_1 & oy-oy_1<=t*V & -t*V<=ox-ox_1 & ox-ox_1<=t*V & -t*(v-A/2*t)<=y-y_0 & y-y_0<=t*(v-A/2*t) & v=v_0+A*t & -t*(v-A/2*t)<=x-x_0 & x-x_0<=t*(v-A/2*t) & dx^2+dy^2=1 & t>=0 & t<=ep & v>=0
                |  ->  v=0|abs(beta)+v^2/(2*b*abs(r)) < gamma&(isVisible < 0|abs(x-ox)>v^2/(2*b)+V*(v/b)|abs(y-oy)>v^2/(2*b)+V*(v/b))""".stripMargin.asFormula

    val tactic = implyR('R) & andL('L)*@TheType() & orR('R) & passiveOrientationAccArithTactic

    proveBy(fml, tactic) shouldBe 'proved
  }
}
