/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core.AntePos
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.SlowTest
import testHelper.ParserFactory._

/**
  * Fixedwing test cases
  * Created by ran on 3/28/16.
  *
  * @author Ran Ji
  */
@SlowTest
class Fixedwing extends TacticTestBase {

  "Fixed wing simple nobound" should "be provable" in withZ3 { implicit qeTool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/fixedwing/fixedwing_simple_nobound.key"))

    val invariant = """       dx^2+dy^2 = 1
                      |      & dz^2+dxy^2 = 1
                      |      & v>=Vmin
                      |      & theta <= Theta
                      |      & theta >= -Theta
                      |      & (((abs(x-xo)>(v^2-Vmin^2)/(2*B)+2*r & abs(x-xo)>(v^2-Vmin^2)/(2*B)+Vmin*((Theta-abs(theta))/W-(v-Vmin)/B)+2*r) | (abs(y-yo)>(v^2-Vmin^2)/(2*B)+2*r & abs(y-yo)>(v^2-Vmin^2)/(2*B)+Vmin*((Theta-abs(theta))/W-(v-Vmin)/B)+2*r))
                      |          | (v=Vmin & theta>=0 & theta<Theta & (abs(x-xo)>Vmin*(Theta-theta)/W+2*r | abs(y-yo)>Vmin*(Theta-theta)/W+2*r))
                      |          | (v=Vmin & theta<0 & theta>-Theta & (abs(x-xo)>Vmin*(Theta+theta)/W+2*r | abs(y-yo)>Vmin*(Theta+theta)/W+2*r))
                      |          | (v=Vmin & theta=Theta & dxy=dXY & dz=dZ & (abs(x-xo-r*dy)>r | abs(y-yo+r*dx)>r))
                      |          | (v=Vmin & theta=-Theta & dxy=-dXY & dz=dZ & (abs(x-xo+r*dy)>r | abs(y-yo-r*dx)>r)))""".stripMargin.asFormula

    def di(a: String, w: String): DependentPositionTactic = diffInvariant(
      "t>=0".asFormula,
      "dx^2 + dy^2 = 1".asFormula,
      "dz^2 + dxy^2 = 1".asFormula,
      s"v = old(v) + $a*t".asFormula,
      s"theta = old(theta) + $w*t".asFormula)

    val diMaxRoll: DependentPositionTactic = diffInvariant("dxy=old(dxy) & dz=old(dz)".asFormula)

    val diLoiterPosTheta: DependentPositionTactic = diffInvariant("x-r*dy=old(x)-r*old(dy) & y+r*dx=old(y)+r*old(dx)".asFormula)

    val diLoiterNegTheta: DependentPositionTactic = diffInvariant("x+r*dy=old(x)+r*old(dy) & y-r*dx=old(y)-r*old(dx)".asFormula)

    def diFreeFly(a: String): DependentPositionTactic = diffInvariant(
      s"-t * (v - $a/2*t) <= x - old(x) & x - old(x) <= t * (v - $a/2*t)".asFormula,
      s"-t * (v - $a/2*t) <= y - old(y) & y - old(y) <= t * (v - $a/2*t)".asFormula)

    /* Tactic for useCase when using Mathamatica */
    val useCaseTactic: BelleExpr = andL('_)*@TheType() & orL(-17, "(abs(x-xo)>(v^2-Vmin^2)/(2*B)+2*r&abs(x-xo)>(v^2-Vmin^2)/(2*B)+Vmin*((Theta-abs(theta))/W-(v-Vmin)/B)+2*r|abs(y-yo)>(v^2-Vmin^2)/(2*B)+2*r&abs(y-yo)>(v^2-Vmin^2)/(2*B)+Vmin*((Theta-abs(theta))/W-(v-Vmin)/B)+2*r)|v=Vmin&theta>=0&theta < Theta&(abs(x-xo)>Vmin*(Theta-theta)/W+2*r|abs(y-yo)>Vmin*(Theta-theta)/W+2*r)|v=Vmin&theta < 0&theta>-Theta&(abs(x-xo)>Vmin*(Theta+theta)/W+2*r|abs(y-yo)>Vmin*(Theta+theta)/W+2*r)|v=Vmin&theta=Theta&dxy=dXY&dz=dZ&(abs(x-xo-r*dy)>r|abs(y-yo+r*dx)>r)|v=Vmin&theta=-Theta&dxy=-dXY&dz=dZ&(abs(x-xo+r*dy)>r|abs(y-yo-r*dx)>r)".asFormula) <(
      QE & debug("done"),
      orL(-17, "v=Vmin&theta>=0&theta < Theta&(abs(x-xo)>Vmin*(Theta-theta)/W+2*r|abs(y-yo)>Vmin*(Theta-theta)/W+2*r)|v=Vmin&theta < 0&theta>-Theta&(abs(x-xo)>Vmin*(Theta+theta)/W+2*r|abs(y-yo)>Vmin*(Theta+theta)/W+2*r)|v=Vmin&theta=Theta&dxy=dXY&dz=dZ&(abs(x-xo-r*dy)>r|abs(y-yo+r*dx)>r)|v=Vmin&theta=-Theta&dxy=-dXY&dz=dZ&(abs(x-xo+r*dy)>r|abs(y-yo-r*dx)>r)".asFormula) <(
        QE,
        orL(-17, "v=Vmin&theta < 0&theta>-Theta&(abs(x-xo)>Vmin*(Theta+theta)/W+2*r|abs(y-yo)>Vmin*(Theta+theta)/W+2*r)|v=Vmin&theta=Theta&dxy=dXY&dz=dZ&(abs(x-xo-r*dy)>r|abs(y-yo+r*dx)>r)|v=Vmin&theta=-Theta&dxy=-dXY&dz=dZ&(abs(x-xo+r*dy)>r|abs(y-yo-r*dx)>r)".asFormula) <(
          QE,
          orL(-17, "v=Vmin&theta=Theta&dxy=dXY&dz=dZ&(abs(x-xo-r*dy)>r|abs(y-yo+r*dx)>r)|v=Vmin&theta=-Theta&dxy=-dXY&dz=dZ&(abs(x-xo+r*dy)>r|abs(y-yo-r*dx)>r)".asFormula) <(
            QE,
            QE
            )
          )
        )
      )

    /* Tactic to split into 5 branches (because the loop invariant is a disjunction of 5 formulas) */
    def splitTactic(a: String, w: String): BelleExpr = andL('_)*@TheType() & di(a, w)(1) & orL(Find.FindL(0, Some("(abs(x-xo)>(v^2-Vmin^2)/(2*B)+2*r&abs(x-xo)>(v^2-Vmin^2)/(2*B)+Vmin*((Theta-abs(theta))/W-(v-Vmin)/B)+2*r|abs(y-yo)>(v^2-Vmin^2)/(2*B)+2*r&abs(y-yo)>(v^2-Vmin^2)/(2*B)+Vmin*((Theta-abs(theta))/W-(v-Vmin)/B)+2*r)|v=Vmin&theta>=0&theta < Theta&(abs(x-xo)>Vmin*(Theta-theta)/W+2*r|abs(y-yo)>Vmin*(Theta-theta)/W+2*r)|v=Vmin&theta < 0&theta>-Theta&(abs(x-xo)>Vmin*(Theta+theta)/W+2*r|abs(y-yo)>Vmin*(Theta+theta)/W+2*r)|v=Vmin&theta=Theta&dxy=dXY&dz=dZ&(abs(x-xo-r*dy)>r|abs(y-yo+r*dx)>r)|v=Vmin&theta=-Theta&dxy=-dXY&dz=dZ&(abs(x-xo+r*dy)>r|abs(y-yo-r*dx)>r)".asFormula))) <(
      /* far away */ exhaustiveEqR2L(hide=true)('Llast)*2 partial,
      orL(Find.FindL(0, Some("v=Vmin&theta>=0&theta < Theta&(abs(x-xo)>Vmin*(Theta-theta)/W+2*r|abs(y-yo)>Vmin*(Theta-theta)/W+2*r)|v=Vmin&theta < 0&theta>-Theta&(abs(x-xo)>Vmin*(Theta+theta)/W+2*r|abs(y-yo)>Vmin*(Theta+theta)/W+2*r)|v=Vmin&theta=Theta&dxy=dXY&dz=dZ&(abs(x-xo-r*dy)>r|abs(y-yo+r*dx)>r)|v=Vmin&theta=-Theta&dxy=-dXY&dz=dZ&(abs(x-xo+r*dy)>r|abs(y-yo-r*dx)>r)".asFormula))) <(
        /* positive theta */ exhaustiveEqR2L(hide=true)('Llast)*2 & andL('_)*@TheType() partial,
        orL(Find.FindL(0, Some("v=Vmin&theta < 0&theta>-Theta&(abs(x-xo)>Vmin*(Theta+theta)/W+2*r|abs(y-yo)>Vmin*(Theta+theta)/W+2*r)|v=Vmin&theta=Theta&dxy=dXY&dz=dZ&(abs(x-xo-r*dy)>r|abs(y-yo+r*dx)>r)|v=Vmin&theta=-Theta&dxy=-dXY&dz=dZ&(abs(x-xo+r*dy)>r|abs(y-yo-r*dx)>r)".asFormula))) <(
          /* negative theta */ exhaustiveEqR2L(hide=true)('Llast)*2 & andL('_)*@TheType() partial,
          orL(Find.FindL(0, Some("v=Vmin&theta=Theta&dxy=dXY&dz=dZ&(abs(x-xo-r*dy)>r|abs(y-yo+r*dx)>r)|v=Vmin&theta=-Theta&dxy=-dXY&dz=dZ&(abs(x-xo+r*dy)>r|abs(y-yo-r*dx)>r)".asFormula))) <(
            /* loiter Theta */ exhaustiveEqR2L(hide=true)('Llast)*2 & andL('_)*@TheType() partial,
            /* loiter -Theta */ exhaustiveEqR2L(hide=true)('Llast)*2 & andL('_)*@TheType() partial
            ) partial
          ) partial
        ) partial
      ) partial

    /* Tactics for Goal1: v=Vmin & theta=Theta */
    def goal1Tactic(a: String, w: String): BelleExpr = splitTactic(a, w) <(
      /* case 1: abs(x-xo)... | abs(y-yo)... */
      diMaxRoll(1) & exhaustiveEqR2L(hide=true)('Llast)*2
        & diLoiterPosTheta(1) & exhaustiveEqR2L(hide=true)('Llast)*4
        & diffWeaken(1) & implyR(1) & andL('_)*@TheType() & QE
        & debug("Goal1 case1 done"),
      /* case 2: v=Vmin & 0<=theta<Theta */
      cutL("!theta_0=Theta".asFormula)(AntePos(23)) <(
        notL(-24, "!theta_0=Theta".asFormula) & closeId,
        hideR(1) & implyR(1) & QE
        ) & debug("Goal1 case2 done"),
      /* case 3: v=Vmin & -Theta<theta<0 */
      cutL("!theta_0=Theta".asFormula)(AntePos(22)) <(
        notL(-23, "!theta_0=Theta".asFormula) & closeId,
        hideR(1) & implyR(1) & QE
        ) & debug("Goal1 case3 done"),
      /* case 4: v=Vmin & theta_0=Theta */
      diMaxRoll(1) & exhaustiveEqR2L(hide=true)('Llast)*2
        & diLoiterPosTheta(1) & exhaustiveEqR2L(hide=true)('Llast)*4
        & diffWeaken(1) & implyR(1) & andL('_)*@TheType() & QE
        & debug("Goal1 case4 done"),
      /* case 5: v=Vmin & theta_0=-Theta */
      cutL("!theta_0=Theta".asFormula)(AntePos(22)) <(
        notL(-23, "!theta_0=Theta".asFormula) & closeId,
        hideR(1) & implyR(1) & QE
        ) & debug("Goal1 case5 done")
      )

    /* Tactics for Goal2: v=Vmin & theta=-Theta */
    def goal2Tactic(a: String, w: String): BelleExpr = splitTactic(a, w) <(
      /* case 1: abs(x-xo)... | abs(y-yo)... */
      diMaxRoll(1) & exhaustiveEqR2L(hide=true)('Llast)*2
        & diLoiterNegTheta(1) & exhaustiveEqR2L(hide=true)('Llast)*4
        & diffWeaken(1) & implyR(1) & andL('_)*@TheType() & QE
        & debug("Goal2 case1 done"),
      /* case 2: v=Vmin & 0<=theta<Theta */
      cutL("!theta_0=-Theta".asFormula)(AntePos(22)) <(
        notL(-23, "!theta_0=-Theta".asFormula) & closeId,
        hideR(1) & implyR(1) & QE
        ) & debug("Goal2 case2 done"),
      /* case 3: v=Vmin & -Theta<theta<0 */
      cutL("!theta_0=-Theta".asFormula)(AntePos(23)) <(
        notL(-24, "!theta_0=-Theta".asFormula) & closeId,
        hideR(1) & implyR(1) & QE
        ) & debug("Goal2 case3 done"),
      /* case 4: v=Vmin & theta_0=Theta */
      cutL("!theta_0=-Theta".asFormula)(AntePos(22)) <(
        notL(-23, "!theta_0=-Theta".asFormula) & closeId,
        hideR(1) & implyR(1) & QE
        ) & debug("Goal2 case4 done"),
      /* case 5: v=Vmin & theta_0=-Theta */
      diMaxRoll(1) & exhaustiveEqR2L(hide=true)('Llast)*2
        & diLoiterNegTheta(1) & exhaustiveEqR2L(hide=true)('Llast)*4
        & diffWeaken(1) & implyR(1) & andL('_)*@TheType() & QE
        & debug("Goal2 case5 done")
      )

    /* Tactics for Goal3: v=Vmin & 0<=theta<Theta */
    def goal3Tactic(a: String, w: String): BelleExpr = splitTactic(a, w) <(
      /* case 1: abs(x-xo)... | abs(y-yo)... */
      diFreeFly(a)(1) & exhaustiveEqR2L(hide=true)('Llast)*2
        & diffWeaken(1) & implyR(1) & andL('_)*@TheType() & QE
        & debug("Goal3 case1 done"),
      /* case 2: v=Vmin & 0<=theta<Theta */
      diFreeFly(a)(1) & exhaustiveEqR2L(hide=true)('Llast)*2
        & diffWeaken(1) & implyR(1) & andL('_)*@TheType() & QE
        & debug("Goal3 case2 done"),
      /* case 3: v=Vmin & -Theta<theta<0 */
      cutL("!0<=theta_0".asFormula)(AntePos(23)) <(
        notL(-24, "!0<=theta_0".asFormula) & closeId,
        hideR(1) & implyR(1) & QE
        ) & debug("Goal3 case3 done"),
      /* case 4: v=Vmin & theta_0=Theta */
      cutL("!theta_0 < Theta".asFormula)(AntePos(23)) <(
        notL(-24, "!theta_0 < Theta".asFormula) & closeId,
        hideR(1) & implyR(1) & QE
        ) & debug("Goal3 case4 done"),
      /* case 5: v=Vmin & theta_0=-Theta */
      cutL("!0<=theta_0".asFormula)(AntePos(23)) <(
        notL(-24, "!0<=theta_0".asFormula) & closeId,
        hideR(1) & implyR(1) & QE
        ) & debug("Goal3 case5 done")
      )

    /* Tactic for Goal4: v=Vmin & -Theta<theta<0 */
    def goal4Tactic(a: String, w: String): BelleExpr = splitTactic(a, w) <(
      /* case 1: abs(x-xo)... | abs(y-yo)... */
      diFreeFly(a)(1) & exhaustiveEqR2L(hide=true)('Llast)*2
        & diffWeaken(1) & implyR(1) & andL('_)*@TheType() & QE
        & debug("Goal4 case1 done"),
      /* case 2: v=Vmin & 0<=theta<Theta */
      cutL("!theta_0 < 0".asFormula)(AntePos(23)) <(
        notL(-24, "!theta_0 < 0".asFormula) & closeId,
        hideR(1) & implyR(1) & QE
        ) & debug("Goal4 case2 done"),
      /* case 3: v=Vmin & -Theta<theta<0 */
      diFreeFly(a)(1) & exhaustiveEqR2L(hide=true)('Llast)*2
        & diffWeaken(1) & implyR(1) & andL('_)*@TheType() & QE
        & debug("Goal4 case3 done"),
      /* case 4: v=Vmin & theta_0=Theta */
      cutL("!theta_0 < 0".asFormula)(AntePos(23)) <(
        notL(-24, "!theta_0 < 0".asFormula) & closeId,
        hideR(1) & implyR(1) & QE
        ) & debug("Goal4 case4 done"),
      /* case 5: v=Vmin & theta_0=-Theta */
      cutL("!-Theta < theta_0".asFormula)(AntePos(23)) <(
        notL(-24, "!-Theta < theta_0".asFormula) & closeId,
        hideR(1) & implyR(1) & QE
        ) & debug("Goal4 case5 done")
      )

    /* Tactics for Goal5: v>Vmin & theta=Theta */
    def goal5Tactic(a: String, w: String): BelleExpr = splitTactic(a, w) <(
      /* case 1: abs(x-xo)... | abs(y-yo)... */
      diMaxRoll(1) & exhaustiveEqR2L(hide=true)('Llast)*2
        & diFreeFly(a)(1) & exhaustiveEqR2L(hide=true)('Llast)*2
        & diffWeaken(1) & implyR(1) & andL('_)*@TheType() & QE
        & debug("Goal5 case1 done"),
      /* case 2: v=Vmin & 0<=theta<Theta */
      cutL("!v_0>Vmin".asFormula)(AntePos(21)) <(
        notL(-22, "!v_0>Vmin".asFormula) & closeId,
        hideR(1) & implyR(1) & QE
        ) & debug("Goal5 case2 done"),
      /* case 3: v=Vmin & -Theta<theta<0 */
      cutL("!v_0>Vmin".asFormula)(AntePos(21)) <(
        notL(-22, "!v_0>Vmin".asFormula) & closeId,
        hideR(1) & implyR(1) & QE
        ) & debug("Goal5 case3 done"),
      /* case 4: v=Vmin & theta_0=Theta */
      cutL("!v_0>Vmin".asFormula)(AntePos(21)) <(
        notL(-22, "!v_0>Vmin".asFormula) & closeId,
        hideR(1) & implyR(1) & QE
        ) & debug("Goal5 case4 done"),
      /* case 5: v=Vmin & theta_0=-Theta */
      cutL("!v_0>Vmin".asFormula)(AntePos(21)) <(
        notL(-22, "!v_0>Vmin".asFormula) & closeId,
        hideR(1) & implyR(1) & QE
        ) & debug("Goal5 case5 done")
      )

    /* Tactics for Goal6: v>Vmin & theta=-Theta */
    def goal6Tactic(a: String, w: String): BelleExpr = splitTactic(a, w) <(
      /* case 1: abs(x-xo)... | abs(y-yo)... */
      diMaxRoll(1) & exhaustiveEqR2L(hide=true)('Llast)*2
        & diFreeFly(a)(1) & exhaustiveEqR2L(hide=true)('Llast)*2
        & diffWeaken(1) & implyR(1) & andL('_)*@TheType() & QE
        & debug("Goal6 case1 done"),
      /* case 2: v=Vmin & 0<=theta<Theta */
      cutL("!v_0>Vmin".asFormula)(AntePos(21)) <(
        notL(-22, "!v_0>Vmin".asFormula) & closeId,
        hideR(1) & implyR(1) & QE
        ) & debug("Goal6 case2 done"),
      /* case 3: v=Vmin & -Theta<theta<0 */
      cutL("!v_0>Vmin".asFormula)(AntePos(21)) <(
        notL(-22, "!v_0>Vmin".asFormula) & closeId,
        hideR(1) & implyR(1) & QE
        ) & debug("Goal6 case3 done"),
      /* case 4: v=Vmin & theta_0=Theta */
      cutL("!v_0>Vmin".asFormula)(AntePos(21)) <(
        notL(-22, "!v_0>Vmin".asFormula) & closeId,
        hideR(1) & implyR(1) & QE
        ) & debug("Goal6 case4 done"),
      /* case 5: v=Vmin & theta_0=-Theta */
      cutL("!v_0>Vmin".asFormula)(AntePos(21)) <(
        notL(-22, "!v_0>Vmin".asFormula) & closeId,
        hideR(1) & implyR(1) & QE
        ) & debug("Goal6 case5 done")
      )

    /* Tactics for Goal7: v>Vmin & 0<=theta<Theta */
    def goal7Tactic(a: String, w: String): BelleExpr = splitTactic(a, w) <(
      /* case 1: abs(x-xo)... | abs(y-yo)... */
      diFreeFly(a)(1) & exhaustiveEqR2L(hide=true)('Llast)*2
        & diffWeaken(1) & implyR(1) & andL('_)*@TheType() & QE
        & debug("Goal7 case1 done"),
      /* case 2: v=Vmin & 0<=theta<Theta */
      cutL("!v_0>Vmin".asFormula)(AntePos(22)) <(
        notL(-23, "!v_0>Vmin".asFormula) & closeId,
        hideR(1) & implyR(1) & QE
        ) & debug("Goal7 case2 done"),
      /* case 3: v=Vmin & -Theta<theta<0 */
      cutL("!v_0>Vmin".asFormula)(AntePos(22)) <(
        notL(-23, "!v_0>Vmin".asFormula) & closeId,
        hideR(1) & implyR(1) & QE
        ) & debug("Goal7 case3 done"),
      /* case 4: v=Vmin & theta_0=Theta */
      cutL("!v_0>Vmin".asFormula)(AntePos(22)) <(
        notL(-23, "!v_0>Vmin".asFormula) & closeId,
        hideR(1) & implyR(1) & QE
        ) & debug("Goal7 case4 done"),
      /* case 5: v=Vmin & theta_0=-Theta */
      cutL("!v_0>Vmin".asFormula)(AntePos(22)) <(
        notL(-23, "!v_0>Vmin".asFormula) & closeId,
        hideR(1) & implyR(1) & QE
        ) & debug("Goal7 case5 done")
      )

    /* Tactic for Goal8: v>Vmin & -Theta<theta<0 */
    def goal8Tactic(a: String, w: String): BelleExpr = splitTactic(a, w) <(
      /* case 1: abs(x-xo)... | abs(y-yo)... */
      diFreeFly(a)(1) & exhaustiveEqR2L(hide=true)('Llast)*2
        & diffWeaken(1) & implyR(1) & andL('_)*@TheType() & QE
        & debug("Goal8 case1 done"),
      /* case 2: v=Vmin & 0<=theta<Theta */
      cutL("!v_0>Vmin".asFormula)(AntePos(22)) <(
        notL(-23, "!v_0>Vmin".asFormula) & closeId,
        hideR(1) & implyR(1) & QE
        ) & debug("Goal8 case2 done"),
      /* case 3: v=Vmin & -Theta<theta<0 */
      cutL("!v_0>Vmin".asFormula)(AntePos(22)) <(
        notL(-23, "!v_0>Vmin".asFormula) & closeId,
        hideR(1) & implyR(1) & QE
        ) & debug("Goal8 case3 done"),
      /* case 4: v=Vmin & theta_0=Theta */
      cutL("!v_0>Vmin".asFormula)(AntePos(22)) <(
        notL(-23, "!v_0>Vmin".asFormula) & closeId,
        hideR(1) & implyR(1) & QE
        ) & debug("Goal8 case4 done"),
      /* case 5: v=Vmin & theta_0=-Theta */
      cutL("!v_0>Vmin".asFormula)(AntePos(22)) <(
        notL(-23, "!v_0>Vmin".asFormula) & closeId,
        hideR(1) & implyR(1) & QE
        ) & debug("Goal8 case5 done")
      )

    def goal9DiffInv(a: String, w: String): BelleExpr =
      andL('_)*@TheType() & di(a, w)(1) & exhaustiveEqR2L(hide=true)('Llast)*2 & diFreeFly(a)(1) & exhaustiveEqR2L(hide=true)('Llast)*2 & diffWeaken(1) & implyR(1) & andL('_)*@TheType() partial

    def goal9Tactic(a: String, w: String): BelleExpr = goal9DiffInv(a, w) & andR(1) <(
      QE,
      andR(1) <(
        QE,
        andR(1) <(
          QE,
          andR(1) <(
            QE,
            andR(1) <(
              QE,
              orR(1) & hideR(2, "v=Vmin&theta>=0&theta < Theta&(abs(x-xo)>Vmin*(Theta-theta)/W+2*r|abs(y-yo)>Vmin*(Theta-theta)/W+2*r)|v=Vmin&theta < 0&theta>-Theta&(abs(x-xo)>Vmin*(Theta+theta)/W+2*r|abs(y-yo)>Vmin*(Theta+theta)/W+2*r)|v=Vmin&theta=Theta&dxy=dXY&dz=dZ&(abs(x-xo-r*dy)>r|abs(y-yo+r*dx)>r)|v=Vmin&theta=-Theta&dxy=-dXY&dz=dZ&(abs(x-xo+r*dy)>r|abs(y-yo-r*dx)>r)".asFormula)
                & hideL(-30, "dx^2+dy^2=1".asFormula) & hideL(-29, "dz^2+dxy^2=1".asFormula) & hideL(-22, "theta_0>=-Theta".asFormula) & hideL(-21, "theta_0<=Theta".asFormula) & hideL(-20, "v_0>=Vmin".asFormula)
                & hideL(-11, "r=Vmin^2/(g*(dXY/dZ))".asFormula) & hideL(-10, "dZ^2+dXY^2=1".asFormula) & hideL(-9, "dXY>0".asFormula) & hideL(-8, "dZ>0".asFormula) & hideL(-1, "g>0".asFormula)
                & orL(Find.FindL(0, Some("abs(x_0-xo)>(v_1^2-Vmin^2)/(2*B)+2*r+(A/B+1)*(A/2*ep^2+ep*v_1)&abs(x_0-xo)>(v_1^2-Vmin^2)/(2*B)+Vmin*((Theta-abs(theta_1))/W-(v_1-Vmin)/B)+2*r+(A/B+1)*(A/2*ep^2+ep*v_1)+Vmin*ep|abs(y_0-yo)>(v_1^2-Vmin^2)/(2*B)+2*r+(A/B+1)*(A/2*ep^2+ep*v_1)&abs(y_0-yo)>(v_1^2-Vmin^2)/(2*B)+Vmin*((Theta-abs(theta_1))/W-(v_1-Vmin)/B)+2*r+(A/B+1)*(A/2*ep^2+ep*v_1)+Vmin*ep".asFormula))) <(
                /* abs(x)... */
                orR(1) & hideR(2, "abs(y-yo)>(v^2-Vmin^2)/(2*B)+2*r&abs(y-yo)>(v^2-Vmin^2)/(2*B)+Vmin*((Theta-abs(theta))/W-(v-Vmin)/B)+2*r".asFormula)
                  & andL('_)*@TheType() & hideL(-15, "y-y_0<=t*(v-a/2*t)".asFormula) & hideL(-14, "-t*(v-a/2*t)<=y-y_0".asFormula) & andR(1) <(
                  hideL(-24, "abs(x_0-xo)>(v_1^2-Vmin^2)/(2*B)+Vmin*((Theta-abs(theta_1))/W-(v_1-Vmin)/B)+2*r+(A/B+1)*(A/2*ep^2+ep*v_1)+Vmin*ep".asFormula) & QE,
                  hideL(-23, "abs(x_0-xo)>(v_1^2-Vmin^2)/(2*B)+2*r+(A/B+1)*(A/2*ep^2+ep*v_1)".asFormula) & QE
                  ),
                /* abs(y)... */
                orR(1) & hideR(1, "abs(x-xo)>(v^2-Vmin^2)/(2*B)+2*r&abs(x-xo)>(v^2-Vmin^2)/(2*B)+Vmin*((Theta-abs(theta))/W-(v-Vmin)/B)+2*r".asFormula)
                  & andL('_)*@TheType() & hideL(-18, "x-x_0<=t*(v-a/2*t)".asFormula) & hideL(-17, "-t*(v-a/2*t)<=x-x_0".asFormula) & andR(1) <(
                  hideL(-24, "abs(y_0-yo)>(v_1^2-Vmin^2)/(2*B)+Vmin*((Theta-abs(theta_1))/W-(v_1-Vmin)/B)+2*r+(A/B+1)*(A/2*ep^2+ep*v_1)+Vmin*ep".asFormula) & QE,
                  hideL(-23, "abs(y_0-yo)>(v_1^2-Vmin^2)/(2*B)+2*r+(A/B+1)*(A/2*ep^2+ep*v_1)".asFormula) & QE
                  )
                )
              )
            )
          )
        )
      )


    val tactic = implyR('_) & andL('_)*@TheType() & loop(invariant)('R) <(
      /* base case */ QE &  debug("Base case done"),
      /* use case */  QE & debug("Use case done"),
      /* induction step */ chase(1) & andR(1) <(
      /* maneuver */
      andR(1) <(
        /* v=Vmin */
        implyR(1) & andR(1) <(
          /* Goal1: v=Vmin & theta=Theta */ implyR(1)*2 & allR(1) & implyR(1) & goal1Tactic("0", "0") & debug("Goal1 done"),
          andR(1) <(
            /* Goal2: v=Vmin & theta=-Theta */ implyR(1)*2 & allR(1) & implyR(1) & goal2Tactic("0", "0") & debug("Goal2 done"),
            andR(1) <(
              /* Goal3: v=Vmin & 0<=theta<Theta */ implyR(1)*2 & allR(1) & implyR(1) & goal3Tactic("0", "W") & debug("Goal3 done"),
              /* Goal4: v=Vmin & -Theta<theta<0 */ implyR(1)*2 & allR(1) & implyR(1) & goal4Tactic("0", "-W") & debug("Goal4 done")
              )
            )
          ),
        /* v>Vmin */
        implyR(1) & andR(1) <(
          /* Goal5: v>Vmin & theta=Theta */ implyR(1)*2 & allR(1) & implyR(1) & goal5Tactic("-B", "0") & debug("Goal5 done"),
          andR(1) <(
            /* Goal6: v>Vmin & theta=-Theta */ implyR(1)*2 & allR(1) & implyR(1) & goal6Tactic("-B", "0") & debug("Goal6 done"),
            andR(1) <(
              /* Goal7: v>Vmin & 0<=theta<Theta */ implyR(1)*2 & allR(1) & implyR(1) & goal7Tactic("-B", "W") & debug("Goal7 done"),
              /* Goal8: v>Vmin & -Theta<theta<0 */ implyR(1)*2 & allR(1) & implyR(1) & goal8Tactic("-B", "-W") & debug("Goal8 done")
              )
            )
          )
        ) & debug("Maneuver done"),
      /* Free fly */
      /* Goal9: New curve */ (allR(1) & implyR(1))*4 & allR(1) & (allR(1) & implyR(1))*2 & goal9Tactic("a", "w") & debug("Goal9 done")
      ) & debug("Induction step done")
    ) & debug("Proof done")

    proveBy(s, tactic) shouldBe 'proved
  }
}
