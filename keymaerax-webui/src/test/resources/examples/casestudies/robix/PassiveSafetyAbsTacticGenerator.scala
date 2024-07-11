import org.keymaerax.bellerophon._
import org.keymaerax.btactics.{PropositionalTactics, ToolTactics}
import org.keymaerax.btactics.TactixLibrary._
import org.keymaerax.btactics.DebuggingTactics.print
import org.keymaerax.parser.StringConverter._
import org.keymaerax.core.{Formula, QETool}
import org.keymaerax.infrastruct.AntePosition

import scala.language.postfixOps

class PassiveSafetyAbsTacticGenerator extends (() => BelleExpr) {

  def apply(): BelleExpr = {
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

    val dw: BelleExpr = exhaustiveEqR2L(hide=true)('Llast)*5 /* 5 old(...) in DI */ & andL('_).*() &
      print("Before diffWeaken") & dW(1) & print("After diffWeaken")

    val hideIrrelevantAssumptions: BelleExpr =
      OnAll(
        hideL(Find.FindL(0, Some("dx^2+dy^2=1".asFormula))) &
          hideL(Find.FindL(0, Some("r!=0".asFormula))) &
          hideL(Find.FindL(0, Some("dxo^2+dyo^2<=V()^2".asFormula))))

    val brakeStoppedArith: BelleExpr =
      hideIrrelevantAssumptions <(
        hideR(3, "abs(y-yo)>v^2/(2*B)+V()*(v/B)".asFormula) & hideR(2, "abs(x-xo)>v^2/(2*B)+V()*(v/B)".asFormula) & QE,
        hideR(3, "abs(y-yo)>v^2/(2*B)+V()*(v/B)".asFormula) & QE,
        hideR(2, "abs(x-xo)>v^2/(2*B)+V()*(v/B)".asFormula) & QE)

    def accArithTactic(fml: Formula): BelleExpr = implyR(1) & andL('_).*() & cutL(fml)(AntePosition.base0(4).top) <(
      hideL(-15) & hideL(-4) & abs(1, 0::Nil) & abs(-4, 0::Nil) & orL(-16) & OnAll(orL(-15)) &
        OnAll(andL('_).*()) & OnAll(exhaustiveEqL2R(hide=true)('L).*()) <(
        hideL(-11) & hideL(-8) & QE,
        hideR(1) & QE,
        hideR(1) & QE,
        hideL(-10) & hideL(-9) & QE
        ),
      hideR(1) & (-12 to -6).map(hideL(_)).reduce[BelleExpr](_&_) & implyR(1) & abs(1, 0::Nil) & hideL(-10) & QE
      ) & print("Proved acc arithmetic: " + fml)

    val accArithX = "A>=0 & B>0 & V()>=0 & ep>0 & abs(x_0-xo_0)>v_0^2/(2*B)+V()*v_0/B+(A/B+1)*(A/2*ep^2+ep*(v_0+V())) & v_0>=0 & -B<=a & a<=A & -t*V()<=xo-xo_0 & xo-xo_0<=t*V() & v=v_0+a*t & -t*(v-a/2*t)<=x-x_0 & x-x_0<=t*(v-a/2*t) & t>=0 & t<=ep & v>=0 -> abs(x-xo)>v^2/(2*B)+V()*(v/B)".asFormula
    val accArithXLemma = proveBy(accArithX, accArithTactic("abs(x_0-xo_0)>v_0^2/(2*B)+V()*v_0/B+(A/B+1)*(A/2*t^2+t*(v_0+V()))".asFormula))

    val accArithY = "A>=0 & B>0 & V()>=0 & ep>0 & abs(y_0-yo_0)>v_0^2/(2*B)+V()*v_0/B+(A/B+1)*(A/2*ep^2+ep*(v_0+V())) & v_0>=0 & -B<=a & a<=A & -t*V()<=yo-yo_0 & yo-yo_0<=t*V() & -t*(v-a/2*t)<=y-y_0 & y-y_0<=t*(v-a/2*t) & v=v_0+a*t & t>=0 & t<=ep & v>=0 -> abs(y-yo)>v^2/(2*B)+V()*(v/B)".asFormula
    val accArithYLemma = proveBy(accArithY, accArithTactic("abs(y_0-yo_0)>v_0^2/(2*B)+V()*v_0/B+(A/B+1)*(A/2*t^2+t*(v_0+V()))".asFormula))

    implyR('_) & andL('_).*() & loop(invariant)('R) <(
      /* base case */ QE & print("Base case done"),
      /* use case */ QE & print("Use case done"),
      /* induction step */ chase(1) & allR(1)*2 & implyR(1) & andR(1) <(
      print("Braking branch") & allR(1) & implyR(1) & di("-B")(1) & dw & prop & brakeStoppedArith & print("Braking branch done"),
      andR(1) <(
        print("Stopped branch") & implyR(1) & allR(1) & implyR(1) & allR(1) & implyR(1) & di("0")(1) & dw & prop & brakeStoppedArith & print("Stopped branch done"),
        print("Acceleration branch") & (allR(1) & implyR(1))*3 & allR(1)*2 & implyR(1) & allR(1) & implyR(1) &
          andL('_).*() & hideL(Find.FindL(0, Some("v=0|abs(x-xo_0)>v^2/(2*B)+V()*(v/B)|abs(y-yo_0)>v^2/(2*B)+V()*(v/B)".asFormula))) &
          di("a")(1) & dw & prop & hideIrrelevantAssumptions <(
          hideR(3, "abs(y-yo)>v^2/(2*B)+V()*(v/B)".asFormula) & hideR(1, "v=0".asFormula) &
            hideL(-15, "y-y_0<=t*(v-a/2*t)".asFormula) & hideL(-14, "-t*(v-a/2*t)<=y-y_0".asFormula) &
            hideL(-11, "yo-yo_0<=t*V()".asFormula) & hideL(-10, "-t*V()<=yo-yo_0".asFormula) &
            hideL(-9, "r_0!=0".asFormula) & PropositionalTactics.toSingleFormula & by(accArithXLemma),
          hideR(2, "abs(x-xo)>v^2/(2*B)+V()*(v/B)".asFormula) & hideR(1, "v=0".asFormula) &
            hideL(-18, "x-x_0<=t*(v-a/2*t)".asFormula) & hideL(-17, "-t*(v-a/2*t)<=x-x_0".asFormula) &
            hideL(-13, "xo-xo_0<=t*V()".asFormula) & hideL(-12, "-t*V()<=xo-xo_0".asFormula) &
            hideL(-9, "r_0!=0".asFormula) & PropositionalTactics.toSingleFormula & by(accArithYLemma)) & print("Acceleration branch done")
        )
      ) & print("Induction step done")
      ) & print("Proof done")
  }
}
