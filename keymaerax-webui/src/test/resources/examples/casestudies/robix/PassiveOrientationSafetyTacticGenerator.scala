import edu.cmu.cs.ls.keymaerax.core.{Real, Nothing, Function, FuncOf, Unit, Variable}
import edu.cmu.cs.ls.keymaerax.tactics.BranchLabels._
import edu.cmu.cs.ls.keymaerax.tactics.EqualityRewritingImpl.eqLeft
import edu.cmu.cs.ls.keymaerax.tactics.FOQuantifierTacticsImpl.skolemizeT
import edu.cmu.cs.ls.keymaerax.tactics.HybridProgramTacticsImpl.{boxAssignT, boxChoiceT, boxNDetAssign, boxSeqT,
boxTestT, discreteGhostT}
import edu.cmu.cs.ls.keymaerax.tactics.ODETactics.{diffIntroduceConstantT, diffCutT, diffInvariantT, diffWeakenT}
import edu.cmu.cs.ls.keymaerax.tactics.PropositionalTacticsImpl._
import edu.cmu.cs.ls.keymaerax.tactics.SearchTacticsImpl._
import edu.cmu.cs.ls.keymaerax.tactics.TacticLibrary.{cutT, debugT, hideT, inductionT}
import edu.cmu.cs.ls.keymaerax.tactics.Tactics.{Tactic, LabelBranch, PositionTactic}
import edu.cmu.cs.ls.keymaerax.tactics._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

import scala.language.postfixOps


class PassiveOrientationSafetyTacticGenerator extends (() => Tactic) {

  def apply() = {
    def ls(tactic: PositionTactic, fml: String*) =
      if (fml.isEmpty) locateSucc(tactic)
      else fml.map(f => locateSucc(tactic, _ == f.asFormula) | debugT("Unable to find formula " + f + " in succedent")).reduce(_ & _)
    def la(tactic: PositionTactic, fml: String*) =
      if (fml.isEmpty) locateAnte(tactic)
      else fml.map(f => locateAnte(tactic, _ == f.asFormula) | debugT("Unable to find formula " + f + " in antecedent")).reduce(_ & _)

    val QE = /*Tactics.NilT*/ TacticLibrary.arithmeticT

    val invariant =
      """
        |   v >= 0
        | & dx^2+dy^2 = 1
        |	& r != 0
        |	& (v = 0 |
        |      (((talpha >= 0 & r >= 0 -> talpha + v^2/(2*b()*r) < alpha()) &
        |        (talpha >= 0 & r < 0 -> talpha + v^2/(-2*b()*r) < alpha()) &
        |        (talpha < 0 & r >= 0 -> -talpha + v^2/(2*b()*r) < alpha()) &
        |        (talpha < 0 & r < 0 -> -talpha + v^2/(-2*b()*r) < alpha()))
        |       &
        |        (isVisible < 0 |
        |           ( ( (x-ox >= 0 -> x-ox > v^2 / (2*b()) + V()*(v/b()))
        |             & (x-ox <= 0 -> ox-x > v^2 / (2*b()) + V()*(v/b())))
        |           | ( (y-oy >= 0 -> y-oy > v^2 / (2*b()) + V()*(v/b()))
        |             & (y-oy <= 0 -> oy-y > v^2 / (2*b()) + V()*(v/b())))))
        |      )
        |		)
      """.stripMargin.asFormula

    val odePos = SuccPosition(0)

    def plantT(a: FuncOf, r: FuncOf, dx: Variable, dy: Variable, ox: Variable, oy: Variable) = debugT("Plant") & ls(boxSeqT) & ls(boxAssignT) & ls(boxSeqT) & ls(boxNDetAssign) & ls(skolemizeT) &
      ls(boxTestT) & ls(ImplyRightT) & ls(diffIntroduceConstantT) &
      ls(diffCutT("t_2>=0".asFormula)) & onBranch(
      (cutShowLbl, debugT("Show t_2>=0") &
        la(hideT, s"v_0=0|(talpha_0>=0&r_0()>=0->talpha_0+v_0^2/(2*b()*r_0()) < alpha())&(talpha_0>=0&r_0() < 0->talpha_0+v_0^2/(-2*b()*r_0()) < alpha())&(talpha_0 < 0&r_0()>=0->-talpha_0+v_0^2/(2*b()*r_0()) < alpha())&(talpha_0 < 0&r_0() < 0->-talpha_0+v_0^2/(-2*b()*r_0()) < alpha())&(isVisible < 0|((x_0-ox_0>=0->x_0-ox_0>v_0^2/(2*b())+V()*(v_0/b()))&(x_0-ox_0<=0->ox_0-x_0>v_0^2/(2*b())+V()*(v_0/b()))|(y_0-oy_0>=0->y_0-oy_0>v_0^2/(2*b())+V()*(v_0/b()))&(y_0-oy_0<=0->oy_0-y_0>v_0^2/(2*b())+V()*(v_0/b()))))", s"r_0()!=0", "v_0>=0", "dx^2+dy^2=1", "odx()^2+ody()^2<=V()^2", s"w*r_0()=v_0") &
        (ls(diffInvariantT) | debugT("Diff. inv. t>=0 failed"))),
      (cutUseLbl, debugT("Use t_2>=0") &
        ls(diffCutT(s"${dx.prettyString}^2+${dy.prettyString}^2=1".asFormula)) & onBranch(
        (cutShowLbl, debugT("Show dx^2+dy^2=1") &
          la(hideT, s"v_0=0|(talpha_0>=0&r_0()>=0->talpha_0+v_0^2/(2*b()*r_0()) < alpha())&(talpha_0>=0&r_0() < 0->talpha_0+v_0^2/(-2*b()*r_0()) < alpha())&(talpha_0 < 0&r_0()>=0->-talpha_0+v_0^2/(2*b()*r_0()) < alpha())&(talpha_0 < 0&r_0() < 0->-talpha_0+v_0^2/(-2*b()*r_0()) < alpha())&(isVisible < 0|((x_0-ox_0>=0->x_0-ox_0>v_0^2/(2*b())+V()*(v_0/b()))&(x_0-ox_0<=0->ox_0-x_0>v_0^2/(2*b())+V()*(v_0/b()))|(y_0-oy_0>=0->y_0-oy_0>v_0^2/(2*b())+V()*(v_0/b()))&(y_0-oy_0<=0->oy_0-y_0>v_0^2/(2*b())+V()*(v_0/b()))))", s"r_0()!=0", "v_0>=0", "odx()^2+ody()^2<=V()^2", "t_2=0", s"w*r_0()=v_0") &
          ls(diffInvariantT) | debugT("Diff. inv. dx^2+dy^2=1 failed")),
        (cutUseLbl, debugT("Use dx^2+dy^2=1") &
          discreteGhostT(Some(Variable("v0")), Variable("v", Some(0)))(odePos) &
          boxAssignT(FOQuantifierTacticsImpl.skolemizeToFnT(_))(odePos) & debugT("Cutting in v=v0+a*t") &
          ls(diffCutT(("v_0=v0_1()+" + a.prettyString + "*t_2").asFormula)) & onBranch(
          (cutShowLbl, debugT("Show v=v0+a*t") &
            la(hideT, s"v_0=0|(talpha_0>=0&r_0()>=0->talpha_0+v_0^2/(2*b()*r_0()) < alpha())&(talpha_0>=0&r_0() < 0->talpha_0+v_0^2/(-2*b()*r_0()) < alpha())&(talpha_0 < 0&r_0()>=0->-talpha_0+v_0^2/(2*b()*r_0()) < alpha())&(talpha_0 < 0&r_0() < 0->-talpha_0+v_0^2/(-2*b()*r_0()) < alpha())&(isVisible < 0|((x_0-ox_0>=0->x_0-ox_0>v_0^2/(2*b())+V()*(v_0/b()))&(x_0-ox_0<=0->ox_0-x_0>v_0^2/(2*b())+V()*(v_0/b()))|(y_0-oy_0>=0->y_0-oy_0>v_0^2/(2*b())+V()*(v_0/b()))&(y_0-oy_0<=0->oy_0-y_0>v_0^2/(2*b())+V()*(v_0/b()))))", s"r_0()!=0", "dx^2+dy^2=1", "odx()^2+ody()^2<=V()^2") &
            (ls(diffInvariantT) | debugT("Diff. inv. v=v0+a*t failed"))),
          (cutUseLbl, debugT("Use v=v0+a*t") &
            discreteGhostT(Some(Variable("x0")), Variable("x", Some(0)))(odePos) &
            boxAssignT(FOQuantifierTacticsImpl.skolemizeToFnT(_))(odePos) &
            ls(diffCutT(("-t_2*(v_0 - " + a.prettyString + "/2*t_2) <= x_0 - x0_1() & x_0 - x0_1() <= t_2*(v_0 - " + a.prettyString + "/2*t_2)").asFormula)) & onBranch(
            (cutShowLbl, debugT("Show ... <= x - x0 <= ...") & la(hideT, s"v_0=0|(talpha_0>=0&r_0()>=0->talpha_0+v_0^2/(2*b()*r_0()) < alpha())&(talpha_0>=0&r_0() < 0->talpha_0+v_0^2/(-2*b()*r_0()) < alpha())&(talpha_0 < 0&r_0()>=0->-talpha_0+v_0^2/(2*b()*r_0()) < alpha())&(talpha_0 < 0&r_0() < 0->-talpha_0+v_0^2/(-2*b()*r_0()) < alpha())&(isVisible < 0|((x_0-ox_0>=0->x_0-ox_0>v_0^2/(2*b())+V()*(v_0/b()))&(x_0-ox_0<=0->ox_0-x_0>v_0^2/(2*b())+V()*(v_0/b()))|(y_0-oy_0>=0->y_0-oy_0>v_0^2/(2*b())+V()*(v_0/b()))&(y_0-oy_0<=0->oy_0-y_0>v_0^2/(2*b())+V()*(v_0/b()))))", s"r_0()!=0", "dx^2+dy^2=1", "odx()^2+ody()^2<=V()^2") & ls(diffInvariantT)),
            (cutUseLbl, debugT("Use ... <= x -x0 <= ...") & discreteGhostT(Some(Variable("y0")), Variable("y", Some(0)))(odePos) &
              boxAssignT(FOQuantifierTacticsImpl.skolemizeToFnT(_))(odePos) &
              ls(diffCutT(("-t_2*(v_0 - " + a.prettyString + "/2*t_2) <= y_0 - y0_1() & y_0 - y0_1() <= t_2*(v_0 - " + a.prettyString + "/2*t_2)").asFormula)) & onBranch(
              (cutShowLbl, debugT("Show ... <= y - y0 <= ...") & la(hideT, s"v_0=0|(talpha_0>=0&r_0()>=0->talpha_0+v_0^2/(2*b()*r_0()) < alpha())&(talpha_0>=0&r_0() < 0->talpha_0+v_0^2/(-2*b()*r_0()) < alpha())&(talpha_0 < 0&r_0()>=0->-talpha_0+v_0^2/(2*b()*r_0()) < alpha())&(talpha_0 < 0&r_0() < 0->-talpha_0+v_0^2/(-2*b()*r_0()) < alpha())&(isVisible < 0|((x_0-ox_0>=0->x_0-ox_0>v_0^2/(2*b())+V()*(v_0/b()))&(x_0-ox_0<=0->ox_0-x_0>v_0^2/(2*b())+V()*(v_0/b()))|(y_0-oy_0>=0->y_0-oy_0>v_0^2/(2*b())+V()*(v_0/b()))&(y_0-oy_0<=0->oy_0-y_0>v_0^2/(2*b())+V()*(v_0/b()))))", s"r_0()!=0", "dx^2+dy^2=1", "odx()^2+ody()^2<=V()^2") & ls(diffInvariantT)),
              (cutUseLbl, debugT("Use ... <= y - y) <= ...") &
                discreteGhostT(Some(Variable("ox0")), ox)(odePos) &
                boxAssignT(FOQuantifierTacticsImpl.skolemizeToFnT(_))(odePos) &
                ls(diffCutT(("-t_2 * V() <= " + ox.prettyString + " - ox0_1() & " + ox.prettyString + " - ox0_1() <= t_2 * V()").asFormula)) & onBranch(
                (cutShowLbl, debugT("Show ... <= ox - ox0 <= ...") & la(hideT, s"v_0=0|(talpha_0>=0&r_0()>=0->talpha_0+v_0^2/(2*b()*r_0()) < alpha())&(talpha_0>=0&r_0() < 0->talpha_0+v_0^2/(-2*b()*r_0()) < alpha())&(talpha_0 < 0&r_0()>=0->-talpha_0+v_0^2/(2*b()*r_0()) < alpha())&(talpha_0 < 0&r_0() < 0->-talpha_0+v_0^2/(-2*b()*r_0()) < alpha())&(isVisible < 0|((x_0-ox_0>=0->x_0-ox_0>v_0^2/(2*b())+V()*(v_0/b()))&(x_0-ox_0<=0->ox_0-x_0>v_0^2/(2*b())+V()*(v_0/b()))|(y_0-oy_0>=0->y_0-oy_0>v_0^2/(2*b())+V()*(v_0/b()))&(y_0-oy_0<=0->oy_0-y_0>v_0^2/(2*b())+V()*(v_0/b()))))", s"r_0()!=0", "v_0>=0", "dx^2+dy^2=1", s"w*r_0()=v_0", "v0_1()=v_0", "x0_1()=x_0", "y0_1()=y_0") & ls(diffInvariantT)),
                (cutUseLbl, debugT("Use ... <= ox - ox0 <= ...") & discreteGhostT(Some(Variable("oy0")), oy)(odePos) &
                  boxAssignT(FOQuantifierTacticsImpl.skolemizeToFnT(_))(odePos) &
                  ls(diffCutT(("-t_2 * V() <= " + oy.prettyString + " - oy0_1() & " + oy.prettyString + " - oy0_1() <= t_2 * V()").asFormula)) & onBranch(
                  (cutShowLbl, debugT("Show ... <= oy - oy0 <= ...") & la(hideT, s"v_0=0|(talpha_0>=0&r_0()>=0->talpha_0+v_0^2/(2*b()*r_0()) < alpha())&(talpha_0>=0&r_0() < 0->talpha_0+v_0^2/(-2*b()*r_0()) < alpha())&(talpha_0 < 0&r_0()>=0->-talpha_0+v_0^2/(2*b()*r_0()) < alpha())&(talpha_0 < 0&r_0() < 0->-talpha_0+v_0^2/(-2*b()*r_0()) < alpha())&(isVisible < 0|((x_0-ox_0>=0->x_0-ox_0>v_0^2/(2*b())+V()*(v_0/b()))&(x_0-ox_0<=0->ox_0-x_0>v_0^2/(2*b())+V()*(v_0/b()))|(y_0-oy_0>=0->y_0-oy_0>v_0^2/(2*b())+V()*(v_0/b()))&(y_0-oy_0<=0->oy_0-y_0>v_0^2/(2*b())+V()*(v_0/b()))))", s"r_0()!=0", "v_0>=0", "dx^2+dy^2=1", s"w*r_0()=v_0", "v0_1()=v_0", "x0_1()=x_0", "y0_1()=y_0") & ls(diffInvariantT)),
                  (cutUseLbl, debugT("Use ... <= oy - oy0 <= ...") &
                    // here starts the new stuff (additional to passive safety diff. cuts)
                    ls(diffCutT(("w=(" + a.prettyString + "*t_2+v0_1())/" + r.prettyString).asFormula)) & onBranch(
                    (cutShowLbl, debugT("Show w = (a*t+v0)/r") & la(hideT, s"v_0=0|(talpha_0>=0&r_0()>=0->talpha_0+v_0^2/(2*b()*r_0()) < alpha())&(talpha_0>=0&r_0() < 0->talpha_0+v_0^2/(-2*b()*r_0()) < alpha())&(talpha_0 < 0&r_0()>=0->-talpha_0+v_0^2/(2*b()*r_0()) < alpha())&(talpha_0 < 0&r_0() < 0->-talpha_0+v_0^2/(-2*b()*r_0()) < alpha())&(isVisible < 0|((x_0-ox_0>=0->x_0-ox_0>v_0^2/(2*b())+V()*(v_0/b()))&(x_0-ox_0<=0->ox_0-x_0>v_0^2/(2*b())+V()*(v_0/b()))|(y_0-oy_0>=0->y_0-oy_0>v_0^2/(2*b())+V()*(v_0/b()))&(y_0-oy_0<=0->oy_0-y_0>v_0^2/(2*b())+V()*(v_0/b()))))", "dx^2+dy^2=1", "odx()^2+ody()^2<=V()^2", "x0_1()=x_0", "y0_1()=y_0", s"ox0_1()=${ox.prettyString}", s"oy0_1()=${oy.prettyString}") & ls(diffInvariantT)),
                    (cutUseLbl, debugT("Use w = (a*t+v0)/r") & discreteGhostT(Some(Variable("talpha0")), Variable("talpha", Some(0)))(odePos) &
                      boxAssignT(FOQuantifierTacticsImpl.skolemizeToFnT(_))(odePos) &
                      ls(diffCutT(("talpha_0-talpha0_1() = " + a.prettyString + "*t_2^2/(2*" + r.prettyString + ") + v0_1()*t_2/" + r.prettyString).asFormula)) & onBranch(
                      (cutShowLbl, debugT("Show talpha-talpha0 = a*t^2/(2*r) + v0*t/r") & la(hideT, s"v_0=0|(talpha_0>=0&r_0()>=0->talpha_0+v_0^2/(2*b()*r_0()) < alpha())&(talpha_0>=0&r_0() < 0->talpha_0+v_0^2/(-2*b()*r_0()) < alpha())&(talpha_0 < 0&r_0()>=0->-talpha_0+v_0^2/(2*b()*r_0()) < alpha())&(talpha_0 < 0&r_0() < 0->-talpha_0+v_0^2/(-2*b()*r_0()) < alpha())&(isVisible < 0|((x_0-ox_0>=0->x_0-ox_0>v_0^2/(2*b())+V()*(v_0/b()))&(x_0-ox_0<=0->ox_0-x_0>v_0^2/(2*b())+V()*(v_0/b()))|(y_0-oy_0>=0->y_0-oy_0>v_0^2/(2*b())+V()*(v_0/b()))&(y_0-oy_0<=0->oy_0-y_0>v_0^2/(2*b())+V()*(v_0/b()))))", "dx^2+dy^2=1", "odx()^2+ody()^2<=V()^2", "x0_1()=x_0", "y0_1()=y_0", s"ox0_1()=${ox.prettyString}", s"oy0_1()=${oy.prettyString}") & ls(diffInvariantT)),
                      (cutUseLbl, debugT("Use talpha-talpha0 = a*t^2/(2*r) + v0*t/r") &
                        ls(diffWeakenT) & ls(ImplyRightT) & (la(AndLeftT)*) & debugT("Plant finished")
                        ) /* use talpha=talpha0 = a*t^2/(2*r) + v0*t/r */
                    )) /* use w = (a*t+v0)/r */
                  )) /* use ... <= oy-oy0 <= */
                )) /* use ... <= ox-ox0 <= */
              )) /* use ... <= y-y0 <= ... */
            )) /* use ... <= x-x0 <= ... */
          )) /* use v=v0+a*t */
        )) /* use dx^2+dy^2=1 */
      ))
    )

    def plantAccelerateT(a: FuncOf, r: FuncOf, dx: Variable, dy: Variable, ox: Variable, oy: Variable) = debugT("Plant Accelerate") & ls(boxSeqT) & ls(boxAssignT) & ls(boxSeqT) & ls(boxNDetAssign) & ls(skolemizeT) &
      ls(boxTestT) & ls(ImplyRightT) & ls(diffIntroduceConstantT) &
      ls(diffCutT("t_2>=0".asFormula)) & onBranch(
      (cutShowLbl, debugT("Show t_2>=0") &
        la(hideT, s"v_0=0|(talpha_0>=0&r_0>=0->talpha_0+v_0^2/(2*b()*r_0) < alpha())&(talpha_0>=0&r_0 < 0->talpha_0+v_0^2/(-2*b()*r_0) < alpha())&(talpha_0 < 0&r_0>=0->-talpha_0+v_0^2/(2*b()*r_0) < alpha())&(talpha_0 < 0&r_0 < 0->-talpha_0+v_0^2/(-2*b()*r_0) < alpha())&(isVisible < 0|((x_0-ox_0>=0->x_0-ox_0>v_0^2/(2*b())+V()*(v_0/b()))&(x_0-ox_0<=0->ox_0-x_0>v_0^2/(2*b())+V()*(v_0/b()))|(y_0-oy_0>=0->y_0-oy_0>v_0^2/(2*b())+V()*(v_0/b()))&(y_0-oy_0<=0->oy_0-y_0>v_0^2/(2*b())+V()*(v_0/b()))))", s"r_0!=0", "v_0>=0", "dx^2+dy^2=1", "odx()^2+ody()^2<=V()^2", s"w*r_1()=v_0") &
        (ls(diffInvariantT) | debugT("Diff. inv. t>=0 failed"))),
      (cutUseLbl, debugT("Use t_2>=0") &
        ls(diffCutT(s"${dx.prettyString}^2+${dy.prettyString}^2=1".asFormula)) & onBranch(
        (cutShowLbl, debugT("Show dx^2+dy^2=1") &
          la(hideT, s"v_0=0|(talpha_0>=0&r_0>=0->talpha_0+v_0^2/(2*b()*r_0) < alpha())&(talpha_0>=0&r_0 < 0->talpha_0+v_0^2/(-2*b()*r_0) < alpha())&(talpha_0 < 0&r_0>=0->-talpha_0+v_0^2/(2*b()*r_0) < alpha())&(talpha_0 < 0&r_0 < 0->-talpha_0+v_0^2/(-2*b()*r_0) < alpha())&(isVisible < 0|((x_0-ox_0>=0->x_0-ox_0>v_0^2/(2*b())+V()*(v_0/b()))&(x_0-ox_0<=0->ox_0-x_0>v_0^2/(2*b())+V()*(v_0/b()))|(y_0-oy_0>=0->y_0-oy_0>v_0^2/(2*b())+V()*(v_0/b()))&(y_0-oy_0<=0->oy_0-y_0>v_0^2/(2*b())+V()*(v_0/b()))))", s"r_0!=0", "v_0>=0", "odx()^2+ody()^2<=V()^2", "t_2=0", s"w*r_1()=v_0") &
          ls(diffInvariantT) | debugT("Diff. inv. dx^2+dy^2=1 failed")),
        (cutUseLbl, debugT("Use dx^2+dy^2=1") &
          discreteGhostT(Some(Variable("v0")), Variable("v", Some(0)))(odePos) &
          boxAssignT(FOQuantifierTacticsImpl.skolemizeToFnT(_))(odePos) & debugT("Cutting in v=v0+a*t") &
          ls(diffCutT(("v_0=v0_1()+" + a.prettyString + "*t_2").asFormula)) & onBranch(
          (cutShowLbl, debugT("Show v=v0+a*t") &
            la(hideT, s"v_0=0|(talpha_0>=0&r_0>=0->talpha_0+v_0^2/(2*b()*r_0) < alpha())&(talpha_0>=0&r_0 < 0->talpha_0+v_0^2/(-2*b()*r_0) < alpha())&(talpha_0 < 0&r_0>=0->-talpha_0+v_0^2/(2*b()*r_0) < alpha())&(talpha_0 < 0&r_0 < 0->-talpha_0+v_0^2/(-2*b()*r_0) < alpha())&(isVisible < 0|((x_0-ox_0>=0->x_0-ox_0>v_0^2/(2*b())+V()*(v_0/b()))&(x_0-ox_0<=0->ox_0-x_0>v_0^2/(2*b())+V()*(v_0/b()))|(y_0-oy_0>=0->y_0-oy_0>v_0^2/(2*b())+V()*(v_0/b()))&(y_0-oy_0<=0->oy_0-y_0>v_0^2/(2*b())+V()*(v_0/b()))))", s"r_0!=0", "dx^2+dy^2=1", "odx()^2+ody()^2<=V()^2") &
            (ls(diffInvariantT) | debugT("Diff. inv. v=v0+a*t failed"))),
          (cutUseLbl, debugT("Use v=v0+a*t") &
            discreteGhostT(Some(Variable("x0")), Variable("x", Some(0)))(odePos) &
            boxAssignT(FOQuantifierTacticsImpl.skolemizeToFnT(_))(odePos) &
            ls(diffCutT(("-t_2*(v_0 - " + a.prettyString + "/2*t_2) <= x_0 - x0_1() & x_0 - x0_1() <= t_2*(v_0 - " + a.prettyString + "/2*t_2)").asFormula)) & onBranch(
            (cutShowLbl, debugT("Show ... <= x - x0 <= ...") & la(hideT, s"v_0=0|(talpha_0>=0&r_0>=0->talpha_0+v_0^2/(2*b()*r_0) < alpha())&(talpha_0>=0&r_0 < 0->talpha_0+v_0^2/(-2*b()*r_0) < alpha())&(talpha_0 < 0&r_0>=0->-talpha_0+v_0^2/(2*b()*r_0) < alpha())&(talpha_0 < 0&r_0 < 0->-talpha_0+v_0^2/(-2*b()*r_0) < alpha())&(isVisible < 0|((x_0-ox_0>=0->x_0-ox_0>v_0^2/(2*b())+V()*(v_0/b()))&(x_0-ox_0<=0->ox_0-x_0>v_0^2/(2*b())+V()*(v_0/b()))|(y_0-oy_0>=0->y_0-oy_0>v_0^2/(2*b())+V()*(v_0/b()))&(y_0-oy_0<=0->oy_0-y_0>v_0^2/(2*b())+V()*(v_0/b()))))", s"r_0!=0", "dx^2+dy^2=1", "odx()^2+ody()^2<=V()^2") & ls(diffInvariantT)),
            (cutUseLbl, debugT("Use ... <= x -x0 <= ...") & discreteGhostT(Some(Variable("y0")), Variable("y", Some(0)))(odePos) &
              boxAssignT(FOQuantifierTacticsImpl.skolemizeToFnT(_))(odePos) &
              ls(diffCutT(("-t_2*(v_0 - " + a.prettyString + "/2*t_2) <= y_0 - y0_1() & y_0 - y0_1() <= t_2*(v_0 - " + a.prettyString + "/2*t_2)").asFormula)) & onBranch(
              (cutShowLbl, debugT("Show ... <= y - y0 <= ...") & la(hideT, s"v_0=0|(talpha_0>=0&r_0>=0->talpha_0+v_0^2/(2*b()*r_0) < alpha())&(talpha_0>=0&r_0 < 0->talpha_0+v_0^2/(-2*b()*r_0) < alpha())&(talpha_0 < 0&r_0>=0->-talpha_0+v_0^2/(2*b()*r_0) < alpha())&(talpha_0 < 0&r_0 < 0->-talpha_0+v_0^2/(-2*b()*r_0) < alpha())&(isVisible < 0|((x_0-ox_0>=0->x_0-ox_0>v_0^2/(2*b())+V()*(v_0/b()))&(x_0-ox_0<=0->ox_0-x_0>v_0^2/(2*b())+V()*(v_0/b()))|(y_0-oy_0>=0->y_0-oy_0>v_0^2/(2*b())+V()*(v_0/b()))&(y_0-oy_0<=0->oy_0-y_0>v_0^2/(2*b())+V()*(v_0/b()))))", s"r_0!=0", "dx^2+dy^2=1", "odx()^2+ody()^2<=V()^2") & ls(diffInvariantT)),
              (cutUseLbl, debugT("Use ... <= y - y) <= ...") &
                discreteGhostT(Some(Variable("ox0")), ox)(odePos) &
                boxAssignT(FOQuantifierTacticsImpl.skolemizeToFnT(_))(odePos) &
                ls(diffCutT(("-t_2 * V() <= " + ox.prettyString + " - ox0_1() & " + ox.prettyString + " - ox0_1() <= t_2 * V()").asFormula)) & onBranch(
                (cutShowLbl, debugT("Show ... <= ox - ox0 <= ...") & la(hideT, s"v_0=0|(talpha_0>=0&r_0>=0->talpha_0+v_0^2/(2*b()*r_0) < alpha())&(talpha_0>=0&r_0 < 0->talpha_0+v_0^2/(-2*b()*r_0) < alpha())&(talpha_0 < 0&r_0>=0->-talpha_0+v_0^2/(2*b()*r_0) < alpha())&(talpha_0 < 0&r_0 < 0->-talpha_0+v_0^2/(-2*b()*r_0) < alpha())&(isVisible < 0|((x_0-ox_0>=0->x_0-ox_0>v_0^2/(2*b())+V()*(v_0/b()))&(x_0-ox_0<=0->ox_0-x_0>v_0^2/(2*b())+V()*(v_0/b()))|(y_0-oy_0>=0->y_0-oy_0>v_0^2/(2*b())+V()*(v_0/b()))&(y_0-oy_0<=0->oy_0-y_0>v_0^2/(2*b())+V()*(v_0/b()))))", s"r_0!=0", "v_0>=0", "dx^2+dy^2=1", s"w*r_1()=v_0", "v0_1()=v_0", "x0_1()=x_0", "y0_1()=y_0") & ls(diffInvariantT)),
                (cutUseLbl, debugT("Use ... <= ox - ox0 <= ...") & discreteGhostT(Some(Variable("oy0")), oy)(odePos) &
                  boxAssignT(FOQuantifierTacticsImpl.skolemizeToFnT(_))(odePos) &
                  ls(diffCutT(("-t_2 * V() <= " + oy.prettyString + " - oy0_1() & " + oy.prettyString + " - oy0_1() <= t_2 * V()").asFormula)) & onBranch(
                  (cutShowLbl, debugT("Show ... <= oy - oy0 <= ...") & la(hideT, s"v_0=0|(talpha_0>=0&r_0>=0->talpha_0+v_0^2/(2*b()*r_0) < alpha())&(talpha_0>=0&r_0 < 0->talpha_0+v_0^2/(-2*b()*r_0) < alpha())&(talpha_0 < 0&r_0>=0->-talpha_0+v_0^2/(2*b()*r_0) < alpha())&(talpha_0 < 0&r_0 < 0->-talpha_0+v_0^2/(-2*b()*r_0) < alpha())&(isVisible < 0|((x_0-ox_0>=0->x_0-ox_0>v_0^2/(2*b())+V()*(v_0/b()))&(x_0-ox_0<=0->ox_0-x_0>v_0^2/(2*b())+V()*(v_0/b()))|(y_0-oy_0>=0->y_0-oy_0>v_0^2/(2*b())+V()*(v_0/b()))&(y_0-oy_0<=0->oy_0-y_0>v_0^2/(2*b())+V()*(v_0/b()))))", s"r_0!=0", "v_0>=0", "dx^2+dy^2=1", s"w*r_1()=v_0", "v0_1()=v_0", "x0_1()=x_0", "y0_1()=y_0") & ls(diffInvariantT)),
                  (cutUseLbl, debugT("Use ... <= oy - oy0 <= ...") &
                    // here starts the new stuff (additional to passive safety diff. cuts)
                    ls(diffCutT(("w=(" + a.prettyString + "*t_2+v0_1())/" + r.prettyString).asFormula)) & onBranch(
                    (cutShowLbl, debugT("Show w = (a*t+v0)/r") & la(hideT, s"v_0=0|(talpha_0>=0&r_0>=0->talpha_0+v_0^2/(2*b()*r_0) < alpha())&(talpha_0>=0&r_0 < 0->talpha_0+v_0^2/(-2*b()*r_0) < alpha())&(talpha_0 < 0&r_0>=0->-talpha_0+v_0^2/(2*b()*r_0) < alpha())&(talpha_0 < 0&r_0 < 0->-talpha_0+v_0^2/(-2*b()*r_0) < alpha())&(isVisible < 0|((x_0-ox_0>=0->x_0-ox_0>v_0^2/(2*b())+V()*(v_0/b()))&(x_0-ox_0<=0->ox_0-x_0>v_0^2/(2*b())+V()*(v_0/b()))|(y_0-oy_0>=0->y_0-oy_0>v_0^2/(2*b())+V()*(v_0/b()))&(y_0-oy_0<=0->oy_0-y_0>v_0^2/(2*b())+V()*(v_0/b()))))", "dx^2+dy^2=1", "odx()^2+ody()^2<=V()^2", "x0_1()=x_0", "y0_1()=y_0", s"ox0_1()=${ox.prettyString}", s"oy0_1()=${oy.prettyString}") & ls(diffInvariantT)),
                    (cutUseLbl, debugT("Use w = (a*t+v0)/r") & discreteGhostT(Some(Variable("talpha0")), Variable("talpha", Some(3)))(odePos) &
                      boxAssignT(FOQuantifierTacticsImpl.skolemizeToFnT(_))(odePos) &
                      ls(diffCutT(("talpha_3-talpha0_1() = " + a.prettyString + "*t_2^2/(2*" + r.prettyString + ") + v0_1()*t_2/" + r.prettyString).asFormula)) & onBranch(
                      (cutShowLbl, debugT("Show talpha-talpha0 = a*t^2/(2*r) + v0*t/r") & la(hideT, s"v_0=0|(talpha_0>=0&r_0>=0->talpha_0+v_0^2/(2*b()*r_0) < alpha())&(talpha_0>=0&r_0 < 0->talpha_0+v_0^2/(-2*b()*r_0) < alpha())&(talpha_0 < 0&r_0>=0->-talpha_0+v_0^2/(2*b()*r_0) < alpha())&(talpha_0 < 0&r_0 < 0->-talpha_0+v_0^2/(-2*b()*r_0) < alpha())&(isVisible < 0|((x_0-ox_0>=0->x_0-ox_0>v_0^2/(2*b())+V()*(v_0/b()))&(x_0-ox_0<=0->ox_0-x_0>v_0^2/(2*b())+V()*(v_0/b()))|(y_0-oy_0>=0->y_0-oy_0>v_0^2/(2*b())+V()*(v_0/b()))&(y_0-oy_0<=0->oy_0-y_0>v_0^2/(2*b())+V()*(v_0/b()))))", "dx^2+dy^2=1", "odx()^2+ody()^2<=V()^2", "x0_1()=x_0", "y0_1()=y_0", s"ox0_1()=${ox.prettyString}", s"oy0_1()=${oy.prettyString}") & ls(diffInvariantT)),
                      (cutUseLbl, debugT("Use talpha-talpha0 = a*t^2/(2*r) + v0*t/r") &
                        ls(diffWeakenT) & ls(ImplyRightT) & (la(AndLeftT)*) & debugT("Plant finished")
                        ) /* use talpha=talpha0 = a*t^2/(2*r) + v0*t/r */
                    )) /* use w = (a*t+v0)/r */
                  )) /* use ... <= oy-oy0 <= */
                )) /* use ... <= ox-ox0 <= */
              )) /* use ... <= y-y0 <= ... */
            )) /* use ... <= x-x0 <= ... */
          )) /* use v=v0+a*t */
        )) /* use dx^2+dy^2=1 */
      ))
    )

    def hideAndEqT(ox: Variable, oy: Variable) = ls(AndRightT) && (
      (AxiomCloseT | ls(AndRightT))*,
      ls(OrRightT) & la(eqLeft(exhaustive=true), "v0_1()=v_0", "x0_1()=x_0", "y0_1()=y_0", s"ox0_1()=${ox.prettyString}", s"oy0_1()=${oy.prettyString}", "talpha0_1()=talpha_0") &
        debugT("Done equality rewriting") & la(hideT, "r_0()!=0", "dx^2+dy^2=1", /*"dx_0^2+dy_0^2=1",*/ "odx()^2+ody()^2<=V()^2", "t_2=0", "v0_1()=v_0", "x0_1()=x_0", "y0_1()=y_0", s"ox0_1()=${ox.prettyString}", s"oy0_1()=${oy.prettyString}", "talpha0_1()=talpha_0") & debugT("Done hiding") & ls(AndRightT) && (
        la(OrLeftT, s"v_0=0|(talpha_0>=0&r_0()>=0->talpha_0+v_0^2/(2*b()*r_0()) < alpha())&(talpha_0>=0&r_0() < 0->talpha_0+v_0^2/(-2*b()*r_0()) < alpha())&(talpha_0 < 0&r_0()>=0->-talpha_0+v_0^2/(2*b()*r_0()) < alpha())&(talpha_0 < 0&r_0() < 0->-talpha_0+v_0^2/(-2*b()*r_0()) < alpha())&(isVisible < 0|((x_0-${ox.prettyString}>=0->x_0-${ox.prettyString}>v_0^2/(2*b())+V()*(v_0/b()))&(x_0-${ox.prettyString}<=0->${ox.prettyString}-x_0>v_0^2/(2*b())+V()*(v_0/b()))|(y_0-${oy.prettyString}>=0->y_0-${oy.prettyString}>v_0^2/(2*b())+V()*(v_0/b()))&(y_0-${oy.prettyString}<=0->${oy.prettyString}-y_0>v_0^2/(2*b())+V()*(v_0/b()))))") && (
          LabelBranch("Show drive visual, know v=0"),
          (la(AndLeftT)*) & la(hideT, s"isVisible < 0|((x_0-${ox.prettyString}>=0->x_0-${ox.prettyString}>v_0^2/(2*b())+V()*(v_0/b()))&(x_0-${ox.prettyString}<=0->${ox.prettyString}-x_0>v_0^2/(2*b())+V()*(v_0/b()))|(y_0-${oy.prettyString}>=0->y_0-${oy.prettyString}>v_0^2/(2*b())+V()*(v_0/b()))&(y_0-${oy.prettyString}<=0->${oy.prettyString}-y_0>v_0^2/(2*b())+V()*(v_0/b())))") & LabelBranch("Show drive visual, know < alpha")
          ),
        ls(OrRightT)*2 & la(OrLeftT, s"v_0=0|(talpha_0>=0&r_0()>=0->talpha_0+v_0^2/(2*b()*r_0()) < alpha())&(talpha_0>=0&r_0() < 0->talpha_0+v_0^2/(-2*b()*r_0()) < alpha())&(talpha_0 < 0&r_0()>=0->-talpha_0+v_0^2/(2*b()*r_0()) < alpha())&(talpha_0 < 0&r_0() < 0->-talpha_0+v_0^2/(-2*b()*r_0()) < alpha())&(isVisible < 0|((x_0-${ox.prettyString}>=0->x_0-${ox.prettyString}>v_0^2/(2*b())+V()*(v_0/b()))&(x_0-${ox.prettyString}<=0->${ox.prettyString}-x_0>v_0^2/(2*b())+V()*(v_0/b()))|(y_0-${oy.prettyString}>=0->y_0-${oy.prettyString}>v_0^2/(2*b())+V()*(v_0/b()))&(y_0-${oy.prettyString}<=0->${oy.prettyString}-y_0>v_0^2/(2*b())+V()*(v_0/b()))))") && (
          LabelBranch("Show safe dist, know v=0"),
          la(AndLeftT) & la(hideT, "(talpha_0>=0&r_0()>=0->talpha_0+v_0^2/(2*b()*r_0()) < alpha())&(talpha_0>=0&r_0() < 0->talpha_0+v_0^2/(-2*b()*r_0()) < alpha())&(talpha_0 < 0&r_0()>=0->-talpha_0+v_0^2/(2*b()*r_0()) < alpha())&(talpha_0 < 0&r_0() < 0->-talpha_0+v_0^2/(-2*b()*r_0()) < alpha())", "talpha_1-talpha_0=a_1()*t_3^2/(2*r_0())+v_0*t_3/r_0()") & la(OrLeftT, s"isVisible < 0|((x_0-${ox.prettyString}>=0->x_0-${ox.prettyString}>v_0^2/(2*b())+V()*(v_0/b()))&(x_0-${ox.prettyString}<=0->${ox.prettyString}-x_0>v_0^2/(2*b())+V()*(v_0/b()))|(y_0-${oy.prettyString}>=0->y_0-${oy.prettyString}>v_0^2/(2*b())+V()*(v_0/b()))&(y_0-${oy.prettyString}<=0->${oy.prettyString}-y_0>v_0^2/(2*b())+V()*(v_0/b())))") && (
            LabelBranch("Show safe dist, know invisible"),
            la(OrLeftT, s"((x_0-${ox.prettyString}>=0->x_0-${ox.prettyString}>v_0^2/(2*b())+V()*(v_0/b()))&(x_0-${ox.prettyString}<=0->${ox.prettyString}-x_0>v_0^2/(2*b())+V()*(v_0/b()))|(y_0-${oy.prettyString}>=0->y_0-${oy.prettyString}>v_0^2/(2*b())+V()*(v_0/b()))&(y_0-${oy.prettyString}<=0->${oy.prettyString}-y_0>v_0^2/(2*b())+V()*(v_0/b())))") && (
              LabelBranch("Show safe dist, know x"),
              LabelBranch("Show safe dist, know y")
              )
            )
          )
        )
      )

    def hideAndEqAccelerate1T(ox: Variable, oy: Variable) = ls(AndRightT) && (
      (AxiomCloseT | ls(AndRightT))*,
      ls(OrRightT) & la(eqLeft(exhaustive=true), "v0_1()=v_0", "x0_1()=x_0", "y0_1()=y_0", s"ox0_1()=${ox.prettyString}", s"oy0_1()=${oy.prettyString}", "talpha0_1()=talpha_3") &
        debugT("Done equality rewriting") & la(hideT, "r_0!=0", "dx^2+dy^2=1", "odx()^2+ody()^2<=V()^2", "t_2=0", "v0_1()=v_0", "x0_1()=x_0", "y0_1()=y_0", s"ox0_1()=${ox.prettyString}", s"oy0_1()=${oy.prettyString}", "talpha0_1()=talpha_3") & debugT("Done hiding") & ls(AndRightT) && (
        la(OrLeftT, "v_0=0|(talpha_0>=0&r_0>=0->talpha_0+v_0^2/(2*b()*r_0) < alpha())&(talpha_0>=0&r_0 < 0->talpha_0+v_0^2/(-2*b()*r_0) < alpha())&(talpha_0 < 0&r_0>=0->-talpha_0+v_0^2/(2*b()*r_0) < alpha())&(talpha_0 < 0&r_0 < 0->-talpha_0+v_0^2/(-2*b()*r_0) < alpha())&(isVisible < 0|((x_0-ox_0>=0->x_0-ox_0>v_0^2/(2*b())+V()*(v_0/b()))&(x_0-ox_0<=0->ox_0-x_0>v_0^2/(2*b())+V()*(v_0/b()))|(y_0-oy_0>=0->y_0-oy_0>v_0^2/(2*b())+V()*(v_0/b()))&(y_0-oy_0<=0->oy_0-y_0>v_0^2/(2*b())+V()*(v_0/b()))))") && (
          LabelBranch("Show drive visual, know v=0"),
          (la(AndLeftT)*) & la(hideT, "isVisible_0 < 0|((x_0-ox_1>=0->x_0-ox_1>v_0^2/(-2*a())+V()*(v_0/-a()))&(x_0-ox_1<=0->ox_1-x_0>v_0^2/(-2*a())+V()*(v_0/-a()))|(y_0-oy_1>=0->y_0-oy_1>v_0^2/(-2*a())+V()*(v_0/-a()))&(y_0-oy_1<=0->oy_1-y_0>v_0^2/(-2*a())+V()*(v_0/-a())))") & LabelBranch("Show drive visual, know < alpha")
          ),
        ls(OrRightT)*2 & la(OrLeftT, "v_0=0|(talpha_0>=0&r_0>=0->talpha_0+v_0^2/(2*b()*r_0) < alpha())&(talpha_0>=0&r_0 < 0->talpha_0+v_0^2/(-2*b()*r_0) < alpha())&(talpha_0 < 0&r_0>=0->-talpha_0+v_0^2/(2*b()*r_0) < alpha())&(talpha_0 < 0&r_0 < 0->-talpha_0+v_0^2/(-2*b()*r_0) < alpha())&(isVisible < 0|((x_0-ox_0>=0->x_0-ox_0>v_0^2/(2*b())+V()*(v_0/b()))&(x_0-ox_0<=0->ox_0-x_0>v_0^2/(2*b())+V()*(v_0/b()))|(y_0-oy_0>=0->y_0-oy_0>v_0^2/(2*b())+V()*(v_0/b()))&(y_0-oy_0<=0->oy_0-y_0>v_0^2/(2*b())+V()*(v_0/b()))))") && (
          LabelBranch("Show safe dist, know v=0"),
          la(AndLeftT) & la(hideT, "(talpha_0>=0&r_0>=0->talpha_0+v_0^2/(2*b()*r_0) < alpha())&(talpha_0>=0&r_0 < 0->talpha_0+v_0^2/(-2*b()*r_0) < alpha())&(talpha_0 < 0&r_0>=0->-talpha_0+v_0^2/(2*b()*r_0) < alpha())&(talpha_0 < 0&r_0 < 0->-talpha_0+v_0^2/(-2*b()*r_0) < alpha())", "talpha_4-talpha_3=a()*t_3^2/(2*r_1())+v_0*t_3/r_1()") &
            la(OrLeftT, "isVisible_0 < 0|((x_0-ox_1>=0->x_0-ox_1>v_0^2/(-2*a())+V()*(v_0/-a()))&(x_0-ox_1<=0->ox_1-x_0>v_0^2/(-2*a())+V()*(v_0/-a()))|(y_0-oy_1>=0->y_0-oy_1>v_0^2/(-2*a())+V()*(v_0/-a()))&(y_0-oy_1<=0->oy_1-y_0>v_0^2/(-2*a())+V()*(v_0/-a())))") && (
            LabelBranch("Show safe dist, know invisible"),
            la(OrLeftT, "((x_0-ox_1>=0->x_0-ox_1>v_0^2/(-2*a())+V()*(v_0/-a()))&(x_0-ox_1<=0->ox_1-x_0>v_0^2/(-2*a())+V()*(v_0/-a()))|(y_0-oy_1>=0->y_0-oy_1>v_0^2/(-2*a())+V()*(v_0/-a()))&(y_0-oy_1<=0->oy_1-y_0>v_0^2/(-2*a())+V()*(v_0/-a())))") && (
              LabelBranch("Show safe dist, know x"),
              LabelBranch("Show safe dist, know y")
              )
            )
          )
        )
      )

    def hideAndEqAccelerate2T(ox: Variable, oy: Variable) = ls(AndRightT) && (
      (AxiomCloseT | ls(AndRightT))*,
      ls(OrRightT) & la(eqLeft(exhaustive=true), "v0_1()=v_0", "x0_1()=x_0", "y0_1()=y_0", s"ox0_1()=${ox.prettyString}", s"oy0_1()=${oy.prettyString}", "talpha0_1()=talpha_3") &
        debugT("Done equality rewriting") & la(hideT, "r_0!=0", "dx^2+dy^2=1", "odx()^2+ody()^2<=V()^2", "t_2=0", "v0_1()=v_0", "x0_1()=x_0", "y0_1()=y_0", s"ox0_1()=${ox.prettyString}", s"oy0_1()=${oy.prettyString}", "talpha0_1()=talpha_3") & debugT("Done hiding") & ls(AndRightT) && (
        la(OrLeftT, "v_0=0|(talpha_0>=0&r_0>=0->talpha_0+v_0^2/(2*b()*r_0) < alpha())&(talpha_0>=0&r_0 < 0->talpha_0+v_0^2/(-2*b()*r_0) < alpha())&(talpha_0 < 0&r_0>=0->-talpha_0+v_0^2/(2*b()*r_0) < alpha())&(talpha_0 < 0&r_0 < 0->-talpha_0+v_0^2/(-2*b()*r_0) < alpha())&(isVisible < 0|((x_0-ox_0>=0->x_0-ox_0>v_0^2/(2*b())+V()*(v_0/b()))&(x_0-ox_0<=0->ox_0-x_0>v_0^2/(2*b())+V()*(v_0/b()))|(y_0-oy_0>=0->y_0-oy_0>v_0^2/(2*b())+V()*(v_0/b()))&(y_0-oy_0<=0->oy_0-y_0>v_0^2/(2*b())+V()*(v_0/b()))))") && (
          LabelBranch("Show drive visual, know v=0"),
          (la(AndLeftT)*) & la(hideT, "isVisible_0 < 0|((x_0-ox_1>=0->x_0-ox_1>v_0^2/(2*b())+V()*(v_0/b())+(a()/b()+1)*(a()/2*ep()^2+ep()*(v_0+V())))&(x_0-ox_1<=0->ox_1-x_0>v_0^2/(2*b())+V()*(v_0/b())+(a()/b()+1)*(a()/2*ep()^2+ep()*(v_0+V())))|(y_0-oy_1>=0->y_0-oy_1>v_0^2/(2*b())+V()*(v_0/b())+(a()/b()+1)*(a()/2*ep()^2+ep()*(v_0+V())))&(y_0-oy_1<=0->oy_1-y_0>v_0^2/(2*b())+V()*(v_0/b())+(a()/b()+1)*(a()/2*ep()^2+ep()*(v_0+V()))))") & LabelBranch("Show drive visual, know < alpha")
          ),
        ls(OrRightT)*2 & la(OrLeftT, "v_0=0|(talpha_0>=0&r_0>=0->talpha_0+v_0^2/(2*b()*r_0) < alpha())&(talpha_0>=0&r_0 < 0->talpha_0+v_0^2/(-2*b()*r_0) < alpha())&(talpha_0 < 0&r_0>=0->-talpha_0+v_0^2/(2*b()*r_0) < alpha())&(talpha_0 < 0&r_0 < 0->-talpha_0+v_0^2/(-2*b()*r_0) < alpha())&(isVisible < 0|((x_0-ox_0>=0->x_0-ox_0>v_0^2/(2*b())+V()*(v_0/b()))&(x_0-ox_0<=0->ox_0-x_0>v_0^2/(2*b())+V()*(v_0/b()))|(y_0-oy_0>=0->y_0-oy_0>v_0^2/(2*b())+V()*(v_0/b()))&(y_0-oy_0<=0->oy_0-y_0>v_0^2/(2*b())+V()*(v_0/b()))))") && (
          LabelBranch("Show safe dist, know v=0"),
          la(AndLeftT) & la(hideT, "(talpha_0>=0&r_0>=0->talpha_0+v_0^2/(2*b()*r_0) < alpha())&(talpha_0>=0&r_0 < 0->talpha_0+v_0^2/(-2*b()*r_0) < alpha())&(talpha_0 < 0&r_0>=0->-talpha_0+v_0^2/(2*b()*r_0) < alpha())&(talpha_0 < 0&r_0 < 0->-talpha_0+v_0^2/(-2*b()*r_0) < alpha())", "talpha_4-talpha_3=a()*t_3^2/(2*r_1())+v_0*t_3/r_1()") &
            la(OrLeftT, "isVisible_0 < 0|((x_0-ox_1>=0->x_0-ox_1>v_0^2/(2*b())+V()*(v_0/b())+(a()/b()+1)*(a()/2*ep()^2+ep()*(v_0+V())))&(x_0-ox_1<=0->ox_1-x_0>v_0^2/(2*b())+V()*(v_0/b())+(a()/b()+1)*(a()/2*ep()^2+ep()*(v_0+V())))|(y_0-oy_1>=0->y_0-oy_1>v_0^2/(2*b())+V()*(v_0/b())+(a()/b()+1)*(a()/2*ep()^2+ep()*(v_0+V())))&(y_0-oy_1<=0->oy_1-y_0>v_0^2/(2*b())+V()*(v_0/b())+(a()/b()+1)*(a()/2*ep()^2+ep()*(v_0+V()))))") && (
            LabelBranch("Show safe dist, know invisible"),
            la(OrLeftT, "(x_0-ox_1>=0->x_0-ox_1>v_0^2/(2*b())+V()*(v_0/b())+(a()/b()+1)*(a()/2*ep()^2+ep()*(v_0+V())))&(x_0-ox_1<=0->ox_1-x_0>v_0^2/(2*b())+V()*(v_0/b())+(a()/b()+1)*(a()/2*ep()^2+ep()*(v_0+V())))|(y_0-oy_1>=0->y_0-oy_1>v_0^2/(2*b())+V()*(v_0/b())+(a()/b()+1)*(a()/2*ep()^2+ep()*(v_0+V())))&(y_0-oy_1<=0->oy_1-y_0>v_0^2/(2*b())+V()*(v_0/b())+(a()/b()+1)*(a()/2*ep()^2+ep()*(v_0+V())))") && (
              LabelBranch("Show safe dist, know x"),
              LabelBranch("Show safe dist, know y")
              )
            )
          )
        )
      )

    def finishBrakeStoppedT = onBranch(
      ("Show drive visual, know v=0", ls(hideT, "(talpha_1>=0&r_0()>=0->talpha_1+v_1^2/(2*b()*r_0()) < alpha())&(talpha_1>=0&r_0() < 0->talpha_1+v_1^2/(-2*b()*r_0()) < alpha())&(talpha_1 < 0&r_0()>=0->-talpha_1+v_1^2/(2*b()*r_0()) < alpha())&(talpha_1 < 0&r_0() < 0->-talpha_1+v_1^2/(-2*b()*r_0()) < alpha())") & QE),
      ("Show drive visual, know < alpha",
        la(hideT, "-t_3*(v_1-a_1()/2*t_3)<=x_1-x_0", "x_1-x_0<=t_3*(v_1-a_1()/2*t_3)", "-t_3*(v_1-a_1()/2*t_3)<=y_1-y_0", "y_1-y_0<=t_3*(v_1-a_1()/2*t_3)", "-t_3*V()<=ox_1-ox_0", "ox_1-ox_0<=t_3*V()", "-t_3*V()<=oy_1-oy_0", "oy_1-oy_0<=t_3*V()") &
          ls(AndRightT) && (
          ls(AndRightT) && (
            ls(AndRightT) && (
              debugT("Show talpha >= 0 & r >= 0") & (AxiomCloseT | QE | debugT("QE failed unexpectedly") & Tactics.stopT),
              debugT("Show talpha >= 0 & r < 0")) & la(hideT, "talpha_0 < 0&r_0() < 0->-talpha_0+v_0^2/(-2*b()*r_0()) < alpha()", "talpha_0 < 0&r_0()>=0->-talpha_0+v_0^2/(2*b()*r_0()) < alpha()", "talpha_0>=0&r_0()>=0->talpha_0+v_0^2/(2*b()*r_0()) < alpha()") &
              (ls(ImplyRightT)*) & (la(ImplyLeftT)*) & (AxiomCloseT | QE | debugT("QE failed unexpectedly") & Tactics.stopT),
            debugT("Show talpha < 0 & r >= 0") & la(hideT, "talpha_0 < 0&r_0() < 0->-talpha_0+v_0^2/(-2*b()*r_0()) < alpha()", "talpha_0>=0&r_0()>=0->talpha_0+v_0^2/(2*b()*r_0()) < alpha()", "talpha_0>=0&r_0() < 0->talpha_0+v_0^2/(-2*b()*r_0()) < alpha()") &
              (ls(ImplyRightT)*) & (la(ImplyLeftT)*) & (AxiomCloseT | QE | debugT("QE failed unexpectedly") & Tactics.stopT)),
          debugT("Show talpha < 0 & r < 0") & (AxiomCloseT | QE | debugT("QE failed unexpectedly") & Tactics.stopT)
          )),
      ("Show safe dist, know v=0", ls(hideT, "isVisible < 0", "(x_1-ox_1>=0->x_1-ox_1>v_1^2/(2*b())+V()*(v_1/b()))&(x_1-ox_1<=0->ox_1-x_1>v_1^2/(2*b())+V()*(v_1/b()))", "(y_1-oy_1>=0->y_1-oy_1>v_1^2/(2*b())+V()*(v_1/b()))&(y_1-oy_1<=0->oy_1-y_1>v_1^2/(2*b())+V()*(v_1/b()))") & QE),
      ("Show safe dist, know invisible", AxiomCloseT),
      ("Show safe dist, know x",
        la(hideT, "-t_3*(v_1-a_1()/2*t_3)<=y_1-y_0", "y_1-y_0<=t_3*(v_1-a_1()/2*t_3)", "-t_3*V()<=oy_1-oy_0", "oy_1-oy_0<=t_3*V()") &
          ls(hideT, "(y_1-oy_1>=0->y_1-oy_1>v_1^2/(2*b())+V()*(v_1/b()))&(y_1-oy_1<=0->oy_1-y_1>v_1^2/(2*b())+V()*(v_1/b()))") &
          la(AndLeftT) & (ls(ImplyRightT)*) & (la(ImplyLeftT)*) & (QE | debugT("QE failed unexpectedly") & Tactics.stopT)),
      ("Show safe dist, know y",
        la(hideT, "-t_3*(v_1-a_1()/2*t_3)<=x_1-x_0", "x_1-x_0<=t_3*(v_1-a_1()/2*t_3)", "-t_3*V()<=ox_1-ox_0", "ox_1-ox_0<=t_3*V()") &
          ls(hideT, "(x_1-ox_1>=0->x_1-ox_1>v_1^2/(2*b())+V()*(v_1/b()))&(x_1-ox_1<=0->ox_1-x_1>v_1^2/(2*b())+V()*(v_1/b()))") &
          la(AndLeftT) & (ls(ImplyRightT)*) & (la(ImplyLeftT)*) & (QE | debugT("QE failed unexpectedly") & Tactics.stopT))
    )

    def finishAccelerate1T = onBranch(
      ("Show drive visual, know v=0", ls(hideT, "(talpha_4>=0&r_1()>=0->talpha_4+v_1^2/(2*b()*r_1()) < alpha())&(talpha_4>=0&r_1() < 0->talpha_4+v_1^2/(-2*b()*r_1()) < alpha())&(talpha_4 < 0&r_1()>=0->-talpha_4+v_1^2/(2*b()*r_1()) < alpha())&(talpha_4 < 0&r_1() < 0->-talpha_4+v_1^2/(-2*b()*r_1()) < alpha())") & QE),
      ("Show drive visual, know < alpha",
        la(hideT,
          "-t_3*(v_1-a()/2*t_3)<=x_1-x_0", "x_1-x_0<=t_3*(v_1-a()/2*t_3)", "-t_3*(v_1-a()/2*t_3)<=y_1-y_0",
          "y_1-y_0<=t_3*(v_1-a()/2*t_3)", "-t_3*V()<=ox_2-ox_1", "ox_2-ox_1<=t_3*V()", "-t_3*V()<=oy_2-oy_1",
          "oy_2-oy_1<=t_3*V()", "dx_0^2+dy_0^2=1",
          "isVisible < 0|((x_0-ox_0>=0->x_0-ox_0>v_0^2/(2*b())+V()*(v_0/b()))&(x_0-ox_0<=0->ox_0-x_0>v_0^2/(2*b())+V()*(v_0/b()))|(y_0-oy_0>=0->y_0-oy_0>v_0^2/(2*b())+V()*(v_0/b()))&(y_0-oy_0<=0->oy_0-y_0>v_0^2/(2*b())+V()*(v_0/b())))") &
          ls(AndRightT) && (
          ls(AndRightT) && (
            ls(AndRightT) && (
              debugT("Show talpha >= 0 & r >= 0") & (AxiomCloseT | QE | debugT("QE failed unexpectedly") & Tactics.stopT),
              debugT("Show talpha >= 0 & r < 0")) & ls(hideT, "v_1=0") & la(hideT, "A>=0", "a()<=A", "V()>=0", "w_0=(a()*t_3+v_0)/r_1()", "w*r_1()=v_0", "talpha_0 < 0&r_0 < 0->-talpha_0+v_0^2/(-2*b()*r_0) < alpha()", "talpha_0 < 0&r_0>=0->-talpha_0+v_0^2/(2*b()*r_0) < alpha()", "talpha_0>=0&r_0>=0->talpha_0+v_0^2/(2*b()*r_0) < alpha()") &
              (ls(ImplyRightT)*) & la(ImplyLeftT, "r_1()>=0->v_0^2/(-2*a()) < alpha()*r_1()") && (
              la(ImplyLeftT, "r_1() < 0->v_0^2/(-2*a()) < -alpha()*r_1()") && (
                /* |- r>=0 | r<0 */ QE,
                la(hideT, "talpha_0>=0&r_0 < 0->talpha_0+v_0^2/(-2*b()*r_0) < alpha()") & ls(hideT, "r_1()>=0") & QE
                ),
              la(ImplyLeftT, "r_1() < 0->v_0^2/(-2*a()) < -alpha()*r_1()") && (
                /* r<0 |- r<0 */ la(AndLeftT, "talpha_4>=0&r_1() < 0") & AxiomCloseT,
                /* unsat ante x < alpha*r & x < -alpha*r */ la(hideT, "talpha_0>=0&r_0 < 0->talpha_0+v_0^2/(-2*b()*r_0) < alpha()") & QE
                )
              ),
            debugT("Show talpha < 0 & r >= 0") & ls(hideT, "v_1=0") & la(hideT, "A>=0", "a()<=A", "V()>=0", "w_0=(a()*t_3+v_0)/r_1()", "w*r_1()=v_0", "talpha_0 < 0&r_0 < 0->-talpha_0+v_0^2/(-2*b()*r_0) < alpha()", "talpha_0>=0&r_0>=0->talpha_0+v_0^2/(2*b()*r_0) < alpha()", "talpha_0>=0&r_0 < 0->talpha_0+v_0^2/(-2*b()*r_0) < alpha()") &
              (ls(ImplyRightT)*) & debugT("IMPLY LEFT")) & la(ImplyLeftT, "r_1()>=0->v_0^2/(-2*a()) < alpha()*r_1()") && (
            la(ImplyLeftT, "r_1() < 0->v_0^2/(-2*a()) < -alpha()*r_1()") && (
              /* |- r>=0 | r<0 */ QE,
              /* r>=0 |- r>=0*/ la(AndLeftT, "talpha_4 < 0&r_1()>=0") & AxiomCloseT
              ),
            la(ImplyLeftT, "r_1() < 0->v_0^2/(-2*a()) < -alpha()*r_1()") && (
              la(hideT, "talpha_0 < 0&r_0>=0->-talpha_0+v_0^2/(2*b()*r_0) < alpha()") & QE,
              /* unsat ante x < alpha*r & x < -alpha*r */ la(hideT, "talpha_0 < 0&r_0>=0->-talpha_0+v_0^2/(2*b()*r_0) < alpha()") & QE
              )
            ),
          debugT("Show talpha < 0 & r < 0") & (AxiomCloseT | QE | debugT("QE failed unexpectedly") & Tactics.stopT)
          )
        ),
      ("Show safe dist, know v=0",
        la(hideT,
          "isVisible_0 < 0|((x_0-ox_1>=0->x_0-ox_1>v_0^2/(-2*a())+V()*(v_0/-a()))&(x_0-ox_1<=0->ox_1-x_0>v_0^2/(-2*a())+V()*(v_0/-a()))|(y_0-oy_1>=0->y_0-oy_1>v_0^2/(-2*a())+V()*(v_0/-a()))&(y_0-oy_1<=0->oy_1-y_0>v_0^2/(-2*a())+V()*(v_0/-a())))",
          "a()<=A", "r_1()>=0->v_0^2/(-2*a()) < alpha()*r_1()", "r_1() < 0->v_0^2/(-2*a()) < -alpha()*r_1()",
          "dx_0^2+dy_0^2=1", "-t_3*(v_1-a()/2*t_3)<=x_1-x_0", "x_1-x_0<=t_3*(v_1-a()/2*t_3)",
          "-t_3*(v_1-a()/2*t_3)<=y_1-y_0", "y_1-y_0<=t_3*(v_1-a()/2*t_3)", "-t_3*V()<=ox_2-ox_1", "ox_2-ox_1<=t_3*V()",
          "-t_3*V()<=oy_2-oy_1", "oy_2-oy_1<=t_3*V()", "talpha_4-talpha_3=a()*t_3^2/(2*r_1())+v_0*t_3/r_1()") &
          ls(hideT,
            "isVisible_0 < 0",
            "(x_1-ox_2>=0->x_1-ox_2>v_1^2/(2*b())+V()*(v_1/b()))&(x_1-ox_2<=0->ox_2-x_1>v_1^2/(2*b())+V()*(v_1/b()))",
            "(y_1-oy_2>=0->y_1-oy_2>v_1^2/(2*b())+V()*(v_1/b()))&(y_1-oy_2<=0->oy_2-y_1>v_1^2/(2*b())+V()*(v_1/b()))") & QE),
      ("Show safe dist, know invisible", AxiomCloseT),
      ("Show safe dist, know x",
        la(hideT,
          "-t_3*(v_1-a()/2*t_3)<=y_1-y_0", "y_1-y_0<=t_3*(v_1-a()/2*t_3)", "-t_3*V()<=oy_2-oy_1", "oy_2-oy_1<=t_3*V()",
          "r_1()>=0->v_0^2/(-2*a()) < alpha()*r_1()", "r_1() < 0->v_0^2/(-2*a()) < -alpha()*r_1()",
          "dx_0^2+dy_0^2=1", "w_0=(a()*t_3+v_0)/r_1()", "w*r_1()=v_0", "a()<=A",
          "isVisible < 0|((x_0-ox_0>=0->x_0-ox_0>v_0^2/(2*b())+V()*(v_0/b()))&(x_0-ox_0<=0->ox_0-x_0>v_0^2/(2*b())+V()*(v_0/b()))|(y_0-oy_0>=0->y_0-oy_0>v_0^2/(2*b())+V()*(v_0/b()))&(y_0-oy_0<=0->oy_0-y_0>v_0^2/(2*b())+V()*(v_0/b())))") &
          ls(hideT, "(y_1-oy_2>=0->y_1-oy_2>v_1^2/(2*b())+V()*(v_1/b()))&(y_1-oy_2<=0->oy_2-y_1>v_1^2/(2*b())+V()*(v_1/b()))") &
          la(AndLeftT) & la(ImplyLeftT, "(x_0-ox_1>=0->x_0-ox_1>v_0^2/(-2*a())+V()*(v_0/-a()))") && (
          la(ImplyLeftT, "(x_0-ox_1<=0->ox_1-x_0>v_0^2/(-2*a())+V()*(v_0/-a()))") && (
            /* |- x>=0 | x<=0 */ QE,
            QE
            ),
          la(ImplyLeftT, "(x_0-ox_1<=0->ox_1-x_0>v_0^2/(-2*a())+V()*(v_0/-a()))") && (
            QE,
            /* unsat x>a & -x>a |- */ QE
            )
          )
        ),
      ("Show safe dist, know y",
        la(hideT,
          "-t_3*(v_1-a()/2*t_3)<=x_1-x_0", "x_1-x_0<=t_3*(v_1-a()/2*t_3)", "-t_3*V()<=ox_2-ox_1", "ox_2-ox_1<=t_3*V()",
          "r_1()>=0->v_0^2/(-2*a()) < alpha()*r_1()", "r_1() < 0->v_0^2/(-2*a()) < -alpha()*r_1()",
          "dx_0^2+dy_0^2=1", "w_0=(a()*t_3+v_0)/r_1()", "w*r_1()=v_0", "a()<=A",
          "isVisible < 0|((x_0-ox_0>=0->x_0-ox_0>v_0^2/(2*b())+V()*(v_0/b()))&(x_0-ox_0<=0->ox_0-x_0>v_0^2/(2*b())+V()*(v_0/b()))|(y_0-oy_0>=0->y_0-oy_0>v_0^2/(2*b())+V()*(v_0/b()))&(y_0-oy_0<=0->oy_0-y_0>v_0^2/(2*b())+V()*(v_0/b())))") &
          ls(hideT, "(x_1-ox_2>=0->x_1-ox_2>v_1^2/(2*b())+V()*(v_1/b()))&(x_1-ox_2<=0->ox_2-x_1>v_1^2/(2*b())+V()*(v_1/b()))") &
          la(AndLeftT) & la(ImplyLeftT, "y_0-oy_1>=0->y_0-oy_1>v_0^2/(-2*a())+V()*(v_0/-a())") && (
          la(ImplyLeftT, "y_0-oy_1<=0->oy_1-y_0>v_0^2/(-2*a())+V()*(v_0/-a())") && (
            /* |- y>=0 | y<=0 */ QE,
            QE
            ),
          la(ImplyLeftT, "y_0-oy_1<=0->oy_1-y_0>v_0^2/(-2*a())+V()*(v_0/-a())") && (
            QE,
            /* unsat x>a & -x<a |- */ QE
            )
          )
        )
    )

    def finishAccelerate2AlphaT = la(hideT,
      "-t_3*(v_1-a()/2*t_3)<=x_1-x_0", "x_1-x_0<=t_3*(v_1-a()/2*t_3)", "-t_3*(v_1-a()/2*t_3)<=y_1-y_0",
      "y_1-y_0<=t_3*(v_1-a()/2*t_3)", "-t_3*V()<=ox_2-ox_1", "ox_2-ox_1<=t_3*V()", "-t_3*V()<=oy_2-oy_1",
      "oy_2-oy_1<=t_3*V()", "dx_0^2+dy_0^2=1",
      "isVisible_0 < 0|((x_0-ox_1>=0->x_0-ox_1>v_0^2/(2*b())+V()*(v_0/b())+(a()/b()+1)*(a()/2*ep()^2+ep()*(v_0+V())))&(x_0-ox_1<=0->ox_1-x_0>v_0^2/(2*b())+V()*(v_0/b())+(a()/b()+1)*(a()/2*ep()^2+ep()*(v_0+V())))|(y_0-oy_1>=0->y_0-oy_1>v_0^2/(2*b())+V()*(v_0/b())+(a()/b()+1)*(a()/2*ep()^2+ep()*(v_0+V())))&(y_0-oy_1<=0->oy_1-y_0>v_0^2/(2*b())+V()*(v_0/b())+(a()/b()+1)*(a()/2*ep()^2+ep()*(v_0+V()))))") &
      ls(AndRightT) && (
      ls(AndRightT) && (
        ls(AndRightT) && (
          debugT("Show talpha >= 0 & r >= 0") & (AxiomCloseT | QE | debugT("QE failed unexpectedly") & Tactics.stopT),
          debugT("Show talpha >= 0 & r < 0") & ls(hideT, "v_1=0") & la(hideT, "A>=0", "a()<=A", "V()>=0", "w_0=(a()*t_3+v_0)/r_1()", "w*r_1()=v_0") &
            (ls(ImplyRightT)*) & la(ImplyLeftT, "r_1()>=0->v_0^2/(2*b())+(a()/b()+1)*(a()/2*ep()^2+ep()*v_0) < alpha()*r_1()") && (
            la(ImplyLeftT, "r_1() < 0->v_0^2/(2*b())+(a()/b()+1)*(a()/2*ep()^2+ep()*v_0) < -alpha()*r_1()") && (
              /* |- r>=0 | r<0 */ QE,
              ls(hideT, "r_1()>=0") & QE
              ),
            la(ImplyLeftT, "r_1() < 0->v_0^2/(2*b())+(a()/b()+1)*(a()/2*ep()^2+ep()*v_0) < -alpha()*r_1()") && (
              /* r<0 |- r<0 */ la(AndLeftT, "talpha_4>=0&r_1() < 0") & AxiomCloseT,
              /* unsat ante x < alpha*r & x < -alpha*r */ QE
              )
            )
          ),
        debugT("Show talpha < 0 & r >= 0") & ls(hideT, "v_1=0") & la(hideT, "A>=0", "a()<=A", "V()>=0", "w_0=(a()*t_3+v_0)/r_1()", "w*r_1()=v_0") &
          (ls(ImplyRightT)*) & la(ImplyLeftT, "r_1()>=0->v_0^2/(2*b())+(a()/b()+1)*(a()/2*ep()^2+ep()*v_0) < alpha()*r_1()") && (
          la(ImplyLeftT, "r_1() < 0->v_0^2/(2*b())+(a()/b()+1)*(a()/2*ep()^2+ep()*v_0) < -alpha()*r_1()") && (
            /* |- r>=0 | r<0 */ QE,
            /* r>=0 |- r>=0*/ la(AndLeftT, "talpha_4 < 0&r_1()>=0") & AxiomCloseT
            ),
          la(ImplyLeftT, "r_1() < 0->v_0^2/(2*b())+(a()/b()+1)*(a()/2*ep()^2+ep()*v_0) < -alpha()*r_1()") && (
            QE,
            /* unsat ante x < alpha*r & x < -alpha*r */ QE
            )
          )
        ),
      debugT("Show talpha < 0 & r < 0") & (AxiomCloseT | QE | debugT("QE failed unexpectedly") & Tactics.stopT)
      )

    def finishAccelerate2T = onBranch(
      ("Show drive visual, know v=0", finishAccelerate2AlphaT),
      ("Show drive visual, know < alpha", finishAccelerate2AlphaT),
      ("Show safe dist, know v=0",
        la(hideT,
          "r_1()>=0->v_0^2/(2*b())+(a()/b()+1)*(a()/2*ep()^2+ep()*v_0) < alpha()*r_1()",
          "r_1() < 0->v_0^2/(2*b())+(a()/b()+1)*(a()/2*ep()^2+ep()*v_0) < -alpha()*r_1()",
          "dx_0^2+dy_0^2=1", "talpha_4-talpha_3=a()*t_3^2/(2*r_1())+v_0*t_3/r_1()", "w_0=(a()*t_3+v_0)/r_1()", "v_0>=0",
          "r_1()!=0", "alpha()>0", "talpha_3=0", "w*r_1()=v_0") &
          la(OrLeftT, "isVisible_0 < 0|((x_0-ox_1>=0->x_0-ox_1>v_0^2/(2*b())+V()*(v_0/b())+(a()/b()+1)*(a()/2*ep()^2+ep()*(v_0+V())))&(x_0-ox_1<=0->ox_1-x_0>v_0^2/(2*b())+V()*(v_0/b())+(a()/b()+1)*(a()/2*ep()^2+ep()*(v_0+V())))|(y_0-oy_1>=0->y_0-oy_1>v_0^2/(2*b())+V()*(v_0/b())+(a()/b()+1)*(a()/2*ep()^2+ep()*(v_0+V())))&(y_0-oy_1<=0->oy_1-y_0>v_0^2/(2*b())+V()*(v_0/b())+(a()/b()+1)*(a()/2*ep()^2+ep()*(v_0+V()))))") && (
          /* know invisible */ AxiomCloseT,
          la(OrLeftT, "(x_0-ox_1>=0->x_0-ox_1>v_0^2/(2*b())+V()*(v_0/b())+(a()/b()+1)*(a()/2*ep()^2+ep()*(v_0+V())))&(x_0-ox_1<=0->ox_1-x_0>v_0^2/(2*b())+V()*(v_0/b())+(a()/b()+1)*(a()/2*ep()^2+ep()*(v_0+V())))|(y_0-oy_1>=0->y_0-oy_1>v_0^2/(2*b())+V()*(v_0/b())+(a()/b()+1)*(a()/2*ep()^2+ep()*(v_0+V())))&(y_0-oy_1<=0->oy_1-y_0>v_0^2/(2*b())+V()*(v_0/b())+(a()/b()+1)*(a()/2*ep()^2+ep()*(v_0+V())))") && (
            /* know x */
            ls(hideT, "v_1=0", "isVisible_0 < 0", "(y_1-oy_2>=0->y_1-oy_2>v_1^2/(2*b())+V()*(v_1/b()))&(y_1-oy_2<=0->oy_2-y_1>v_1^2/(2*b())+V()*(v_1/b()))") &
              la(hideT, "-t_3*(v_1-a()/2*t_3)<=y_1-y_0", "y_1-y_0<=t_3*(v_1-a()/2*t_3)", "-t_3*V()<=oy_2-oy_1", "oy_2-oy_1<=t_3*V()") &
              la(AndLeftT) &
              la(ImplyLeftT, "x_0-ox_1>=0->x_0-ox_1>v_0^2/(2*b())+V()*(v_0/b())+(a()/b()+1)*(a()/2*ep()^2+ep()*(v_0+V()))") && (
              la(ImplyLeftT, "x_0-ox_1<=0->ox_1-x_0>v_0^2/(2*b())+V()*(v_0/b())+(a()/b()+1)*(a()/2*ep()^2+ep()*(v_0+V()))") && (
                /* |- x>=0 | x<=0 */ ls(hideT, "(x_1-ox_2>=0->x_1-ox_2>v_1^2/(2*b())+V()*(v_1/b()))&(x_1-ox_2<=0->ox_2-x_1>v_1^2/(2*b())+V()*(v_1/b()))") & QE,
                ls(AndRightT) && (
                  /* unsat. ante */ ls(ImplyRightT) & ls(hideT, "x_1-ox_2>v_1^2/(2*b())+V()*(v_1/b())") & QE,
                  ls(ImplyRightT) & QE
                  )
                ),
              la(ImplyLeftT, "x_0-ox_1<=0->ox_1-x_0>v_0^2/(2*b())+V()*(v_0/b())+(a()/b()+1)*(a()/2*ep()^2+ep()*(v_0+V()))") && (
                ls(AndRightT) && (
                  ls(ImplyRightT) & QE,
                  ls(ImplyRightT) & QE
                  ),
                ls(AndRightT) && (ls(ImplyRightT) & QE, ls(ImplyRightT) & QE)
                )
              ),
            /* know y */
            ls(hideT, "v_1=0", "isVisible_0 < 0", "(x_1-ox_2>=0->x_1-ox_2>v_1^2/(2*b())+V()*(v_1/b()))&(x_1-ox_2<=0->ox_2-x_1>v_1^2/(2*b())+V()*(v_1/b()))") &
              la(hideT, "-t_3*(v_1-a()/2*t_3)<=x_1-x_0", "x_1-x_0<=t_3*(v_1-a()/2*t_3)", "-t_3*V()<=ox_2-ox_1", "ox_2-ox_1<=t_3*V()") &
              la(AndLeftT) &
              la(ImplyLeftT, "y_0-oy_1>=0->y_0-oy_1>v_0^2/(2*b())+V()*(v_0/b())+(a()/b()+1)*(a()/2*ep()^2+ep()*(v_0+V()))") && (
              la(ImplyLeftT, "y_0-oy_1<=0->oy_1-y_0>v_0^2/(2*b())+V()*(v_0/b())+(a()/b()+1)*(a()/2*ep()^2+ep()*(v_0+V()))") && (
                /* |- x>=0 | x<=0 */ ls(hideT, "(y_1-oy_2>=0->y_1-oy_2>v_1^2/(2*b())+V()*(v_1/b()))&(y_1-oy_2<=0->oy_2-y_1>v_1^2/(2*b())+V()*(v_1/b()))") & QE,
                ls(AndRightT) && (
                  /* unsat. ante */ ls(ImplyRightT) & ls(hideT, "y_1-oy_2>v_1^2/(2*b())+V()*(v_1/b())") & QE,
                  ls(ImplyRightT) & QE
                  )
                ),
              la(ImplyLeftT, "y_0-oy_1<=0->oy_1-y_0>v_0^2/(2*b())+V()*(v_0/b())+(a()/b()+1)*(a()/2*ep()^2+ep()*(v_0+V()))") && (
                ls(AndRightT) && (
                  ls(ImplyRightT) & QE,
                  ls(ImplyRightT) & QE
                  ),
                ls(AndRightT) && (ls(ImplyRightT) & QE, ls(ImplyRightT) & QE)
                )
              )
            )
          )),
      ("Show safe dist, know invisible", AxiomCloseT),
      ("Show safe dist, know x", debugT("Foo 5") &
        la(hideT,
          "y_1-y_0<=t_3*(v_1-a()/2*t_3)", "-t_3*(v_1-a()/2*t_3)<=y_1-y_0",
          "-t_3*V()<=oy_2-oy_1", "oy_2-oy_1<=t_3*V()",
          "r_1()>=0->v_0^2/(2*b())+(a()/b()+1)*(a()/2*ep()^2+ep()*v_0) < alpha()*r_1()",
          "r_1() < 0->v_0^2/(2*b())+(a()/b()+1)*(a()/2*ep()^2+ep()*v_0) < -alpha()*r_1()",
          "dx_0^2+dy_0^2=1", "w_0=(a()*t_3+v_0)/r_1()", "w*r_1()=v_0", "talpha_3=0", "alpha()>0", "r_1()!=0",
          "isVisible < 0|((x_0-ox_0>=0->x_0-ox_0>v_0^2/(2*b())+V()*(v_0/b()))&(x_0-ox_0<=0->ox_0-x_0>v_0^2/(2*b())+V()*(v_0/b()))|(y_0-oy_0>=0->y_0-oy_0>v_0^2/(2*b())+V()*(v_0/b()))&(y_0-oy_0<=0->oy_0-y_0>v_0^2/(2*b())+V()*(v_0/b())))") &
        ls(hideT, "v_1=0", "isVisible_0 < 0", "(y_1-oy_2>=0->y_1-oy_2>v_1^2/(2*b())+V()*(v_1/b()))&(y_1-oy_2<=0->oy_2-y_1>v_1^2/(2*b())+V()*(v_1/b()))") &
        la(AndLeftT) & la(ImplyLeftT, "x_0-ox_1>=0->x_0-ox_1>v_0^2/(2*b())+V()*(v_0/b())+(a()/b()+1)*(a()/2*ep()^2+ep()*(v_0+V()))") && (
        la(ImplyLeftT, "x_0-ox_1<=0->ox_1-x_0>v_0^2/(2*b())+V()*(v_0/b())+(a()/b()+1)*(a()/2*ep()^2+ep()*(v_0+V()))") && (
          /* |- x>=0 | x<=0 */ QE,
          ls(AndRightT) && (
            ls(ImplyRightT) & ls(hideT, "x_1-ox_2>v_1^2/(2*b())+V()*(v_1/b())") & QE,
            ls(ImplyRightT) & la(hideT, "ox_2-ox_1<=t_3*V()", "-t_3*(v_1-a()/2*t_3)<=x_1-x_0") &
              cutT(Some("ox_1-x_0>v_0^2/(2*b())+V()*(v_0/b())+(a()/b()+1)*(a()/2*t_3^2+t_3*(v_0+V()))".asFormula)) & onBranch(
              (cutShowLbl, ls(hideT, "x_0-ox_1>=0", "ox_2-x_1>v_1^2/(2*b())+V()*(v_1/b())") & QE),
              (cutUseLbl, cutT(Some("v_0+a()*t_3>=0".asFormula)) & onBranch(
                (cutShowLbl, ls(hideT, "x_0-ox_1>=0", "ox_2-x_1>v_1^2/(2*b())+V()*(v_1/b())") & la(hideT, "ox_1-x_0>v_0^2/(2*b())+V()*(v_0/b())+(a()/b()+1)*(a()/2*ep()^2+ep()*(v_0+V()))") & QE),
                (cutUseLbl, la(hideT,
                  "v_0+a()*ep()>=0",
                  "ox_1-x_0>v_0^2/(2*b())+V()*(v_0/b())+(a()/b()+1)*(a()/2*ep()^2+ep()*(v_0+V()))",
                  "ep()>0", "t_3<=ep()") & debugT("Bar 5b2") & QE)
              ))
            ))
          ),
        la(ImplyLeftT, "x_0-ox_1<=0->ox_1-x_0>v_0^2/(2*b())+V()*(v_0/b())+(a()/b()+1)*(a()/2*ep()^2+ep()*(v_0+V()))") && (
          ls(AndRightT) && (
            ls(ImplyRightT) & la(hideT, "-t_3*V()<=ox_2-ox_1", "x_1-x_0<=t_3*(v_1-a()/2*t_3)") &
              cutT(Some("x_0-ox_1>v_0^2/(2*b())+V()*(v_0/b())+(a()/b()+1)*(a()/2*t_3^2+t_3*(v_0+V()))".asFormula)) & onBranch(
              (cutShowLbl, ls(hideT, "x_0-ox_1<=0", "x_1-ox_2>v_1^2/(2*b())+V()*(v_1/b())") & QE),
              (cutUseLbl, cutT(Some("v_0+a()*t_3>=0".asFormula)) & onBranch(
                (cutShowLbl, ls(hideT, "x_0-ox_1<=0", "x_1-ox_2>v_1^2/(2*b())+V()*(v_1/b())") & la(hideT, "x_0-ox_1>v_0^2/(2*b())+V()*(v_0/b())+(a()/b()+1)*(a()/2*ep()^2+ep()*(v_0+V()))") & QE),
                (cutUseLbl, la(hideT,
                  "v_0+a()*ep()>=0",
                  "x_0-ox_1>v_0^2/(2*b())+V()*(v_0/b())+(a()/b()+1)*(a()/2*ep()^2+ep()*(v_0+V()))",
                  "ep()>0", "t_3<=ep()") & QE)
              ))
            ),
            ls(ImplyRightT) & la(hideT, "-t_3*V()<=ox_2-ox_1", "x_1-x_0<=t_3*(v_1-a()/2*t_3)") &
              cutT(Some("x_0-ox_1>v_0^2/(2*b())+V()*(v_0/b())+(a()/b()+1)*(a()/2*t_3^2+t_3*(v_0+V()))".asFormula)) & onBranch(
              (cutShowLbl, ls(hideT, "x_0-ox_1<=0", "ox_2-x_1>v_1^2/(2*b())+V()*(v_1/b())") & QE),
              (cutUseLbl, cutT(Some("v_0+a()*t_3>=0".asFormula)) & onBranch(
                (cutShowLbl, ls(hideT, "x_0-ox_1<=0", "ox_2-x_1>v_1^2/(2*b())+V()*(v_1/b())") & la(hideT, "x_0-ox_1>v_0^2/(2*b())+V()*(v_0/b())+(a()/b()+1)*(a()/2*ep()^2+ep()*(v_0+V()))") & QE),
                (cutUseLbl, la(hideT,
                  "v_0+a()*ep()>=0",
                  "x_0-ox_1>v_0^2/(2*b())+V()*(v_0/b())+(a()/b()+1)*(a()/2*ep()^2+ep()*(v_0+V()))",
                  "ep()>0", "t_3<=ep()") & QE)
              ))
            )),
          /* unsat x>a & -x>a |- */ la(hideT, "-t_3*(v_1-a()/2*t_3)<=x_1-x_0", "x_1-x_0<=t_3*(v_1-a()/2*t_3)", "-t_3*V()<=ox_2-ox_1", "ox_2-ox_1<=t_3*V()") & QE
          )
        )
        ),
      ("Show safe dist, know y", debugT("Foo 6") &
        la(hideT,
          "x_1-x_0<=t_3*(v_1-a()/2*t_3)", "-t_3*(v_1-a()/2*t_3)<=x_1-x_0",
          "-t_3*V()<=ox_2-ox_1", "ox_2-ox_1<=t_3*V()",
          "r_1()>=0->v_0^2/(2*b())+(a()/b()+1)*(a()/2*ep()^2+ep()*v_0) < alpha()*r_1()",
          "r_1() < 0->v_0^2/(2*b())+(a()/b()+1)*(a()/2*ep()^2+ep()*v_0) < -alpha()*r_1()",
          "dx_0^2+dy_0^2=1", "w_0=(a()*t_3+v_0)/r_1()", "w*r_1()=v_0", "talpha_3=0", "alpha()>0", "r_1()!=0",
          "isVisible < 0|((x_0-ox_0>=0->x_0-ox_0>v_0^2/(2*b())+V()*(v_0/b()))&(x_0-ox_0<=0->ox_0-x_0>v_0^2/(2*b())+V()*(v_0/b()))|(y_0-oy_0>=0->y_0-oy_0>v_0^2/(2*b())+V()*(v_0/b()))&(y_0-oy_0<=0->oy_0-y_0>v_0^2/(2*b())+V()*(v_0/b())))") &
        ls(hideT, "v_1=0", "isVisible_0 < 0", "(x_1-ox_2>=0->x_1-ox_2>v_1^2/(2*b())+V()*(v_1/b()))&(x_1-ox_2<=0->ox_2-x_1>v_1^2/(2*b())+V()*(v_1/b()))") &
        la(AndLeftT) & la(ImplyLeftT, "y_0-oy_1>=0->y_0-oy_1>v_0^2/(2*b())+V()*(v_0/b())+(a()/b()+1)*(a()/2*ep()^2+ep()*(v_0+V()))") && (
        la(ImplyLeftT, "y_0-oy_1<=0->oy_1-y_0>v_0^2/(2*b())+V()*(v_0/b())+(a()/b()+1)*(a()/2*ep()^2+ep()*(v_0+V()))") && (
          /* |- x>=0 | x<=0 */ QE,
          ls(AndRightT) && (
            ls(ImplyRightT) & ls(hideT, "y_1-oy_2>v_1^2/(2*b())+V()*(v_1/b())") & QE,
            ls(ImplyRightT) & la(hideT, "oy_2-oy_1<=t_3*V()", "-t_3*(v_1-a()/2*t_3)<=y_1-y_0") &
              cutT(Some("oy_1-y_0>v_0^2/(2*b())+V()*(v_0/b())+(a()/b()+1)*(a()/2*t_3^2+t_3*(v_0+V()))".asFormula)) & onBranch(
              (cutShowLbl, ls(hideT, "y_0-oy_1>=0", "oy_2-y_1>v_1^2/(2*b())+V()*(v_1/b())") & QE),
              (cutUseLbl, cutT(Some("v_0+a()*t_3>=0".asFormula)) & onBranch(
                (cutShowLbl, ls(hideT, "y_0-oy_1>=0", "oy_2-y_1>v_1^2/(2*b())+V()*(v_1/b())") & la(hideT, "oy_1-y_0>v_0^2/(2*b())+V()*(v_0/b())+(a()/b()+1)*(a()/2*ep()^2+ep()*(v_0+V()))") & QE),
                (cutUseLbl, la(hideT,
                  "v_0+a()*ep()>=0",
                  "oy_1-y_0>v_0^2/(2*b())+V()*(v_0/b())+(a()/b()+1)*(a()/2*ep()^2+ep()*(v_0+V()))",
                  "ep()>0", "t_3<=ep()") & debugT("Bar 5b2") & QE)
              ))
            ))
          ),
        la(ImplyLeftT, "y_0-oy_1<=0->oy_1-y_0>v_0^2/(2*b())+V()*(v_0/b())+(a()/b()+1)*(a()/2*ep()^2+ep()*(v_0+V()))") && (
          ls(AndRightT) && (
            ls(ImplyRightT) & la(hideT, "-t_3*V()<=oy_2-oy_1", "y_1-y_0<=t_3*(v_1-a()/2*t_3)") &
              cutT(Some("y_0-oy_1>v_0^2/(2*b())+V()*(v_0/b())+(a()/b()+1)*(a()/2*t_3^2+t_3*(v_0+V()))".asFormula)) & onBranch(
              (cutShowLbl, ls(hideT, "y_0-oy_1<=0", "y_1-oy_2>v_1^2/(2*b())+V()*(v_1/b())") & QE),
              (cutUseLbl, cutT(Some("v_0+a()*t_3>=0".asFormula)) & onBranch(
                (cutShowLbl, ls(hideT, "y_0-oy_1<=0", "y_1-oy_2>v_1^2/(2*b())+V()*(v_1/b())") & la(hideT, "y_0-oy_1>v_0^2/(2*b())+V()*(v_0/b())+(a()/b()+1)*(a()/2*ep()^2+ep()*(v_0+V()))") & QE),
                (cutUseLbl, la(hideT,
                  "v_0+a()*ep()>=0",
                  "y_0-oy_1>v_0^2/(2*b())+V()*(v_0/b())+(a()/b()+1)*(a()/2*ep()^2+ep()*(v_0+V()))",
                  "ep()>0", "t_3<=ep()") & QE)
              ))
            ),
            ls(ImplyRightT) & la(hideT, "-t_3*V()<=oy_2-oy_1", "y_1-y_0<=t_3*(v_1-a()/2*t_3)") &
              cutT(Some("y_0-oy_1>v_0^2/(2*b())+V()*(v_0/b())+(a()/b()+1)*(a()/2*t_3^2+t_3*(v_0+V()))".asFormula)) & onBranch(
              (cutShowLbl, ls(hideT, "y_0-oy_1<=0", "oy_2-y_1>v_1^2/(2*b())+V()*(v_1/b())") & QE),
              (cutUseLbl, cutT(Some("v_0+a()*t_3>=0".asFormula)) & onBranch(
                (cutShowLbl, ls(hideT, "y_0-oy_1<=0", "oy_2-y_1>v_1^2/(2*b())+V()*(v_1/b())") & la(hideT, "y_0-oy_1>v_0^2/(2*b())+V()*(v_0/b())+(a()/b()+1)*(a()/2*ep()^2+ep()*(v_0+V()))") & QE),
                (cutUseLbl, la(hideT,
                  "v_0+a()*ep()>=0",
                  "y_0-oy_1>v_0^2/(2*b())+V()*(v_0/b())+(a()/b()+1)*(a()/2*ep()^2+ep()*(v_0+V()))",
                  "ep()>0", "t_3<=ep()") & QE)
              ))
            )),
          /* unsat x>a & -x>a |- */ la(hideT, "-t_3*(v_1-a()/2*t_3)<=y_1-y_0", "y_1-y_0<=t_3*(v_1-a()/2*t_3)", "-t_3*V()<=oy_2-oy_1", "oy_2-oy_1<=t_3*V()") & QE
          )
        )
        )
    )

    val tactic = ls(ImplyRightT) & (la(AndLeftT)*) & ls(inductionT(Some(invariant))) & onBranch(
      (indInitLbl, debugT("Base case") & ((AxiomCloseT | la(Propositional) | ls(Propositional))*) & (AxiomCloseT | QE)),
      (indUseCaseLbl, debugT("Use case") & la(hideT, "talpha=0", "r>=0->v^2/(2*b()*r) < alpha()", "r < 0->v^2/(2*b()*-r) < alpha()",
        "(x-ox>=0->x-ox>v^2/(2*b())+V()*(v/b()))&(x-ox<=0->ox-x>v^2/(2*b())+V()*(v/b()))|(y-oy>=0->y-oy>v^2/(2*b())+V()*(v/b()))&(y-oy<=0->oy-y>v^2/(2*b())+V()*(v/b()))",
        "v>=0") & ls(ImplyRightT) & QE),
      (indStepLbl, debugT("Induction step") & la(hideT, "r!=0", "talpha=0", "r>=0->v^2/(2*b()*r) < alpha()",
        "r < 0->v^2/(2*b()*-r) < alpha()", "(x-ox>=0->x-ox>v^2/(2*b())+V()*(v/b()))&(x-ox<=0->ox-x>v^2/(2*b())+V()*(v/b()))|(y-oy>=0->y-oy>v^2/(2*b())+V()*(v/b()))&(y-oy<=0->oy-y>v^2/(2*b())+V()*(v/b()))",
        "v>=0") &
        ls(ImplyRightT) & (la(AndLeftT)*) & ls(boxSeqT) &
        /* control obstacle */
        (ls(boxSeqT) & ls(boxNDetAssign) & ls(skolemizeT))*2 &
        ls(boxSeqT) & ls(boxTestT) & ls(ImplyRightT) &
        /* control robot */
        ls(boxSeqT) & ls(boxChoiceT) & ls(AndRightT) && (
        debugT("Brake") & ls(boxAssignT) &
          plantT(FuncOf(Function("a", Some(1), Unit, Real), Nothing), FuncOf(Function("r", Some(0), Unit, Real), Nothing), Variable("dx"), Variable("dy"), Variable("ox", Some(0)), Variable("oy", Some(0))) &
          hideAndEqT(Variable("ox", Some(0)), Variable("oy", Some(0))) & finishBrakeStoppedT,
        ls(boxChoiceT) & ls(AndRightT) && (
          debugT("Stopped") & ls(boxSeqT) & ls(boxTestT) & ls(ImplyRightT) & ls(boxSeqT) & ls(boxAssignT) &
            ls(boxSeqT) & ls(boxAssignT)*2 &
            plantT(FuncOf(Function("a", Some(1), Unit, Real), Nothing), FuncOf(Function("r", Some(0), Unit, Real), Nothing), Variable("dx", Some(2)), Variable("dy", Some(2)), Variable("ox", Some(0)), Variable("oy", Some(0))) &
            hideAndEqT(Variable("ox", Some(0)), Variable("oy", Some(0))) & finishBrakeStoppedT,
          debugT("Accelerate") & (ls(boxSeqT) & ls(boxNDetAssign) & ls(skolemizeT) & ls(boxSeqT) & ls(boxTestT) & ls(ImplyRightT))*2 &
            (ls(boxSeqT) & ls(boxNDetAssign) & ls(skolemizeT))*3 &
            ls(boxSeqT) &
            ls(boxChoiceT) & ls(AndRightT) && (
            debugT("if v+a*ep<0") & ls(boxSeqT) & ls(boxTestT) & ls(ImplyRightT) & ls(boxSeqT) & ls(boxTestT) & ls(ImplyRightT) & ls(boxTestT) & ls(ImplyRightT) & ls(boxAssignT) &
              plantAccelerateT(FuncOf(Function("a", None, Unit, Real), Nothing), FuncOf(Function("r", Some(1), Unit, Real), Nothing), Variable("dx"), Variable("dy"), Variable("ox", Some(1)), Variable("oy", Some(1))) &
              hideAndEqAccelerate1T(Variable("ox", Some(1)), Variable("oy", Some(1))) & finishAccelerate1T,
            debugT("else") & ls(boxSeqT) & ls(boxTestT) & ls(ImplyRightT) & ls(boxSeqT) & ls(boxTestT) & ls(ImplyRightT) & ls(boxTestT) & ls(ImplyRightT) & ls(boxAssignT) &
              plantAccelerateT(FuncOf(Function("a", None, Unit, Real), Nothing), FuncOf(Function("r", Some(1), Unit, Real), Nothing), Variable("dx"), Variable("dy"), Variable("ox", Some(1)), Variable("oy", Some(1))) &
              hideAndEqAccelerate2T(Variable("ox", Some(1)), Variable("oy", Some(1))) & finishAccelerate2T
            )
          )
        )
        )
    )

    tactic
  }
}

new PassiveOrientationSafetyTacticGenerator()