import edu.cmu.cs.ls.keymaerax.core.{Real, Nothing, Function, FuncOf, Unit, Variable}
import edu.cmu.cs.ls.keymaerax.tactics.ArithmeticTacticsImpl._
import edu.cmu.cs.ls.keymaerax.tactics.BranchLabels._
import edu.cmu.cs.ls.keymaerax.tactics.EqualityRewritingImpl.eqLeft
import edu.cmu.cs.ls.keymaerax.tactics.FOQuantifierTacticsImpl.skolemizeT
import edu.cmu.cs.ls.keymaerax.tactics.HybridProgramTacticsImpl.{boxAssignT, boxChoiceT, boxNDetAssign, boxSeqT,
boxTestT, discreteGhostT}
import edu.cmu.cs.ls.keymaerax.tactics.ODETactics.{diffIntroduceConstantT, diffCutT, diffInvariantT, diffWeakenT}
import edu.cmu.cs.ls.keymaerax.tactics.PropositionalTacticsImpl._
import edu.cmu.cs.ls.keymaerax.tactics.SearchTacticsImpl._
import edu.cmu.cs.ls.keymaerax.tactics.TacticLibrary.{debugT, hideT, inductionT}
import edu.cmu.cs.ls.keymaerax.tactics.Tactics.{Tactic, LabelBranch, PositionTactic}
import edu.cmu.cs.ls.keymaerax.tactics._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

import scala.language.postfixOps


class PassiveSafetyAbsTacticGenerator extends (() => Tactic) {

  def apply() = {
    def ls(tactic: PositionTactic, fml: String*) =
      if (fml.isEmpty) locateSucc(tactic)
      else fml.map(f => locateSucc(tactic, _ == f.asFormula) | debugT("Unable to find formula " + f + " in succedent")).reduce(_ & _)
    def la(tactic: PositionTactic, fml: String*) =
      if (fml.isEmpty) locateAnte(tactic)
      else fml.map(f => locateAnte(tactic, _ == f.asFormula) | debugT("Unable to find formula " + f + " in antecedent")).reduce(_ & _)

    val QE = TacticLibrary.arithmeticT

    val invariant = """   v >= 0
                      | & dx^2+dy^2 = 1
                      | & r != 0
                      | & (v = 0 | abs(x-xo) > v^2 / (2*B) + V()*(v/B)
                      |          | abs(y-yo) > v^2 / (2*B) + V()*(v/B) )""".stripMargin.asFormula

    val odePos = SuccPosition(0)

    def plantT(a: FuncOf, xo: Variable, yo: Variable) = ls(boxAssignT) & ls(diffIntroduceConstantT) &
      // differential cuts
      ls(diffCutT("t_2>=0".asFormula)) & onBranch(
      (cutShowLbl, debugT("Show t_2>=0") &
        la(hideT, "v_0=0|abs(x_0-xo_0)>v_0^2/(2*B)+V()*(v_0/B)|abs(y_0-yo_0)>v_0^2/(2*B)+V()*(v_0/B)", "dxo()^2+dyo()^2<=V()^2", "dx^2+dy^2=1", "abs(x_0-xo_1)>v_0^2/(2*B)+V()*v_0/B+(A/B+1)*(A/2*ep()^2+ep()*(v_0+V()))|abs(y_0-yo_1)>v_0^2/(2*B)+V()*v_0/B+(A/B+1)*(A/2*ep()^2+ep()*(v_0+V()))") &
        (ls(diffInvariantT) | debugT("Diff. inv. t>=0 failed"))),
      (cutUseLbl, debugT("Use t_2>=0") &
        ls(diffCutT("dx^2+dy^2=1".asFormula)) & onBranch(
        (cutShowLbl, debugT("Show dx^2+dy^2=1") &
          la(hideT, "v_0=0|abs(x_0-xo_0)>v_0^2/(2*B)+V()*(v_0/B)|abs(y_0-yo_0)>v_0^2/(2*B)+V()*(v_0/B)", "dxo()^2+dyo()^2<=V()^2", "abs(x_0-xo_1)>v_0^2/(2*B)+V()*v_0/B+(A/B+1)*(A/2*ep()^2+ep()*(v_0+V()))|abs(y_0-yo_1)>v_0^2/(2*B)+V()*v_0/B+(A/B+1)*(A/2*ep()^2+ep()*(v_0+V()))") &
          ls(diffInvariantT) | debugT("Diff. inv. dx^2+dy^2=1 failed")),
        (cutUseLbl, debugT("Use dx^2+dy^2=1") & discreteGhostT(Some(Variable("v0")), Variable("v", Some(0)))(odePos) &
          boxAssignT(FOQuantifierTacticsImpl.skolemizeToFnT(_))(odePos) & debugT("Cutting in v=v0+a*t") &
          ls(diffCutT(("v_0=v0_1()+" + a.prettyString + "*t_2").asFormula)) & onBranch(
          (cutShowLbl, debugT("Show v=v0+a*t") &
            la(hideT, "v_0=0|abs(x_0-xo_0)>v_0^2/(2*B)+V()*(v_0/B)|abs(y_0-yo_0)>v_0^2/(2*B)+V()*(v_0/B)", "dxo()^2+dyo()^2<=V()^2", "dx^2+dy^2=1", "abs(x_0-xo_1)>v_0^2/(2*B)+V()*v_0/B+(A/B+1)*(A/2*ep()^2+ep()*(v_0+V()))|abs(y_0-yo_1)>v_0^2/(2*B)+V()*v_0/B+(A/B+1)*(A/2*ep()^2+ep()*(v_0+V()))") &
            (ls(diffInvariantT) | debugT("Diff. inv. v=v0+a*t failed"))),
          (cutUseLbl, debugT("Use v=v0+a*t") & discreteGhostT(Some(Variable("x0")), Variable("x", Some(0)))(odePos) &
            boxAssignT(FOQuantifierTacticsImpl.skolemizeToFnT(_))(odePos) &
            ls(diffCutT(("-t_2*(v_0 - " + a.prettyString + "/2*t_2) <= x_0 - x0_1() & x_0 - x0_1() <= t_2*(v_0 - " + a.prettyString + "/2*t_2)").asFormula)) & onBranch(
            (cutShowLbl, debugT("Show ... <= x - x0 <= ...") & la(hideT, /*"r_0()!=0", "dx^2+dy^2=1",*/ "v_0=0|abs(x_0-xo_0)>v_0^2/(2*B)+V()*(v_0/B)|abs(y_0-yo_0)>v_0^2/(2*B)+V()*(v_0/B)", "abs(x_0-xo_1)>v_0^2/(2*B)+V()*v_0/B+(A/B+1)*(A/2*ep()^2+ep()*(v_0+V()))|abs(y_0-yo_1)>v_0^2/(2*B)+V()*v_0/B+(A/B+1)*(A/2*ep()^2+ep()*(v_0+V()))") & ls(diffInvariantT)),
            (cutUseLbl, debugT("Use ... <= x -x0 <= ...") & discreteGhostT(Some(Variable("y0")), Variable("y", Some(0)))(odePos) &
              boxAssignT(FOQuantifierTacticsImpl.skolemizeToFnT(_))(odePos) &
              ls(diffCutT(("-t_2*(v_0 - " + a.prettyString + "/2*t_2) <= y_0 - y0_1() & y_0 - y0_1() <= t_2*(v_0 - " + a.prettyString + "/2*t_2)").asFormula)) & onBranch(
              (cutShowLbl, debugT("Show ... <= y - y0 <= ...") & la(hideT, /*"r_0()!=0", "dx^2+dy^2=1",*/ "v_0=0|abs(x_0-xo_0)>v_0^2/(2*B)+V()*(v_0/B)|abs(y_0-yo_0)>v_0^2/(2*B)+V()*(v_0/B)", "abs(x_0-xo_1)>v_0^2/(2*B)+V()*v_0/B+(A/B+1)*(A/2*ep()^2+ep()*(v_0+V()))|abs(y_0-yo_1)>v_0^2/(2*B)+V()*v_0/B+(A/B+1)*(A/2*ep()^2+ep()*(v_0+V()))") & ls(diffInvariantT)),
              (cutUseLbl, debugT("Use ... <= y - y) <= ...") & discreteGhostT(Some(Variable("xo0")), xo)(odePos) &
                boxAssignT(FOQuantifierTacticsImpl.skolemizeToFnT(_))(odePos) &
                ls(diffCutT(("-t_2 * V() <= " + xo.prettyString + " - xo0_1() & " + xo.prettyString + " - xo0_1() <= t_2 * V()").asFormula)) & onBranch(
                (cutShowLbl, debugT("Show ... <= xo - xo0 <= ...") & la(hideT, /*"r_0()!=0", "dx^2+dy^2=1",*/ "v_0=0|abs(x_0-xo_0)>v_0^2/(2*B)+V()*(v_0/B)|abs(y_0-yo_0)>v_0^2/(2*B)+V()*(v_0/B)", "abs(x_0-xo_1)>v_0^2/(2*B)+V()*v_0/B+(A/B+1)*(A/2*ep()^2+ep()*(v_0+V()))|abs(y_0-yo_1)>v_0^2/(2*B)+V()*v_0/B+(A/B+1)*(A/2*ep()^2+ep()*(v_0+V()))") & ls(diffInvariantT)),
                (cutUseLbl, debugT("Use ... <= xo - xo0 <= ...") & discreteGhostT(Some(Variable("yo0")), yo)(odePos) &
                  boxAssignT(FOQuantifierTacticsImpl.skolemizeToFnT(_))(odePos) &
                  ls(diffCutT(("-t_2 * V() <= " + yo.prettyString + " - yo0_1() & " + yo.prettyString + " - yo0_1() <= t_2 * V()").asFormula)) & onBranch(
                  (cutShowLbl, debugT("Show ... <= yo - yo0 <= ...") & la(hideT, /*"r_0()!=0", "dx^2+dy^2=1",*/ "v_0=0|abs(x_0-xo_0)>v_0^2/(2*B)+V()*(v_0/B)|abs(y_0-yo_0)>v_0^2/(2*B)+V()*(v_0/B)", "abs(x_0-xo_1)>v_0^2/(2*B)+V()*v_0/B+(A/B+1)*(A/2*ep()^2+ep()*(v_0+V()))|abs(y_0-yo_1)>v_0^2/(2*B)+V()*v_0/B+(A/B+1)*(A/2*ep()^2+ep()*(v_0+V()))") & ls(diffInvariantT)),
                  (cutUseLbl, debugT("Use ... <= yo - yo0 <= ...") & ls(diffWeakenT) & ls(ImplyRightT) & (la(AndLeftT)*))
                ))
              ))
            ))
          ))
        ))
      ))
    )

    def hideAndEqT(xo: Variable, yo: Variable) = ls(AndRightT) && ((ls(AndRightT)*) & (AxiomCloseT | debugT("AxiomClose failed")), debugT("Hide") &
      la(eqLeft(exhaustive = true), "v0_1()=v_0", "x0_1()=x_0", "y0_1()=y_0", "xo0_1()=" + xo.prettyString, "yo0_1()=" + yo.prettyString) &
      debugT("Done equality rewriting") &
      la(hideT, "r!=0", "v>=0", "dx^2+dy^2=1", "dxo()^2+dyo()^2<=V()^2", "t_2=0", "v0_1()=v_0",
        "x0_1()=x_0", "y0_1()=y_0", "xo0_1()=" + xo.prettyString, "yo0_1()=" + yo.prettyString, "dx_0^2+dy_0^2=1") & debugT("Done hiding") &
      (ls(OrRightT)*) &
      OrLeftT(AntePosition(4)) && (OrLeftT(AntePosition(4)) && (
      LabelBranch("Know v=0"),
      LabelBranch("Know x")),
      LabelBranch("Know y"))
      )

    val brakeFinishT = onBranch(
      ("Know v=0",
        la(hideT, "ep()>0", "V()>=0", "A>=0", "v_0>=0", "t_3<=ep()", "x_1-x_0<=t_3*(v_1--B/2*t_3)",
          "-t_3*(v_1--B/2*t_3)<=x_1-x_0", "-t_3*(v_1--B/2*t_3)<=y_1-y_0", "y_1-y_0<=t_3*(v_1--B/2*t_3)",
          "-t_3*V()<=xo_1-xo_0", "xo_1-xo_0<=t_3*V()", "-t_3*V()<=yo_1-yo_0", "yo_1-yo_0<=t_3*V()") &
          ls(hideT, "abs(y_1-yo_1)>v_1^2/(2*B)+V()*(v_1/B)", "abs(x_1-xo_1)>v_1^2/(2*B)+V()*(v_1/B)") &
          QE),
      ("Know x", debugT("Brake Bar") & la(hideT, "y_1-y_0<=t_3*(v_1--B/2*t_3)", "-t_3*(v_1--B/2*t_3)<=y_1-y_0",
        "-t_3*V()<=yo_1-yo_0", "yo_1-yo_0<=t_3*V()") &
        ls(hideT, "abs(y_1-yo_1)>v_1^2/(2*B)+V()*(v_1/B)") &
        AbsT(AntePosition(4).first) &
        AbsT(SuccPosition(1).first) &
        debugT("Handing off to QE") &
        (QE | debugT("QE failed unexpectedly") & Tactics.stopT)),
      ("Know y", debugT("Brake Zee") & la(hideT, "-t_3*(v_1--B/2*t_3)<=x_1-x_0", "x_1-x_0<=t_3*(v_1--B/2*t_3)",
        "-t_3*V()<=xo_1-xo_0", "xo_1-xo_0<=t_3*V()") &
        ls(hideT, "abs(x_1-xo_1)>v_1^2/(2*B)+V()*(v_1/B)") &
        AbsT(AntePosition(4).first) &
        AbsT(SuccPosition(0).first) &
        debugT("Handing off to QE") &
        (QE | debugT("QE failed unexpectedly") & Tactics.stopT))
    )

    val stoppedFinishT = onBranch(
      ("Know v=0",
        la(hideT, "ep()>0", "V()>=0", "B>0", "A>=0", "v_0>=0", "w_2=0", "t_3<=ep()", "v_1>=0",
          "-t_3*(v_1-a_1()/2*t_3)<=x_1-x_0", "x_1-x_0<=t_3*(v_1-a_1()/2*t_3)", "-t_3*(v_1-a_1()/2*t_3)<=y_1-y_0",
          "y_1-y_0<=t_3*(v_1-a_1()/2*t_3)", "-t_3*V()<=xo_1-xo_0", "xo_1-xo_0<=t_3*V()", "-t_3*V()<=yo_1-yo_0", "yo_1-yo_0<=t_3*V()") &
          ls(hideT, "abs(y_1-yo_1)>v_1^2/(2*B)+V()*(v_1/B)", "abs(x_1-xo_1)>v_1^2/(2*B)+V()*(v_1/B)") &
          (QE | debugT("QE failed unexpectedly") & Tactics.stopT)),
      ("Know x",
        la(hideT, "ep()>0", "V()>=0", "B>0", "A>=0", "abs(x_0-xo_0)>v_0^2/(2*B)+V()*(v_0/B)",
          "v_0>=0", "w_2=0", "t_3<=ep()", "v_1>=0", "-t_3*(v_1-a_1()/2*t_3)<=x_1-x_0", "x_1-x_0<=t_3*(v_1-a_1()/2*t_3)",
          "-t_3*(v_1-a_1()/2*t_3)<=y_1-y_0", "y_1-y_0<=t_3*(v_1-a_1()/2*t_3)", "-t_3*V()<=xo_1-xo_0", "xo_1-xo_0<=t_3*V()",
          "-t_3*V()<=yo_1-yo_0", "yo_1-yo_0<=t_3*V()") &
          debugT("Stopped Foo") &
          ls(hideT, "abs(y_1-yo_1)>v_1^2/(2*B)+V()*(v_1/B)", "abs(x_1-xo_1)>v_1^2/(2*B)+V()*(v_1/B)") &
          (QE | debugT("QE failed unexpectedly") & Tactics.stopT)),
      ("Know y",
        la(hideT, "ep()>0", "V()>=0", "B>0", "A>=0", "abs(y_0-yo_0)>v_0^2/(2*B)+V()*(v_0/B)",
          "v_0>=0", "w_2=0", "t_3<=ep()", "v_1>=0", "-t_3*(v_1-a_1()/2*t_3)<=x_1-x_0", "x_1-x_0<=t_3*(v_1-a_1()/2*t_3)",
          "-t_3*(v_1-a_1()/2*t_3)<=y_1-y_0", "y_1-y_0<=t_3*(v_1-a_1()/2*t_3)", "-t_3*V()<=xo_1-xo_0", "xo_1-xo_0<=t_3*V()",
          "-t_3*V()<=yo_1-yo_0", "yo_1-yo_0<=t_3*V()") &
          debugT("Stopped Bar") &
          ls(hideT, "abs(y_1-yo_1)>v_1^2/(2*B)+V()*(v_1/B)", "abs(x_1-xo_1)>v_1^2/(2*B)+V()*(v_1/B)") &
          (QE | debugT("QE failed unexpectedly") & Tactics.stopT))
    )

    val accelerateFinishBaseT = la(OrLeftT) && (
      la(hideT, "-t_3*(v_1-a()/2*t_3)<=y_1-y_0", "y_1-y_0<=t_3*(v_1-a()/2*t_3)", "-t_3*V()<=yo_2-yo_1", "yo_2-yo_1<=t_3*V()") &
        ls(hideT, "abs(y_1-yo_2)>v_1^2/(2*B)+V()*(v_1/B)") & debugT("Foo 1") &
        cutT(Some("abs(x_0-xo_1)>v_0^2/(2*B)+V()*v_0/B+(A/B+1)*(A/2*t_3^2+t_3*(v_0+V()))".asFormula)) & onBranch(
        (cutShowLbl, debugT("Showing cut that replaces ep ~> t_3") &
          la(hideT, "v_1>=0", "v_1=v_0+a()*t_3", "-t_3*(v_1-a()/2*t_3)<=x_1-x_0", "x_1-x_0<=t_3*(v_1-a()/2*t_3)", "-t_3*V()<=xo_2-xo_1", "xo_2-xo_1<=t_3*V()") &
          ls(hideT, "v_1=0", "abs(x_1-xo_2)>v_1^2/(2*B)+V()*(v_1/B)") &
          AbsT(AntePosition(7).first) &
          lastAnte(hideT) & QE
          ),
        (cutUseLbl, debugT("Use cut") &
          la(hideT, "abs(x_0-xo_1)>v_0^2/(2*B)+V()*v_0/B+(A/B+1)*(A/2*ep()^2+ep()*(v_0+V()))", "ep()>0", "t_3<=ep()") &
          AbsT(AntePosition(13).first) & AbsT(SuccPosition(1).first) & debugT("Foo 1-1") &
          la(OrLeftT, "x_0-xo_1>=0&abs_0=x_0-xo_1|x_0-xo_1<=0&abs_0=-(x_0-xo_1)") && (
          la(hideT, "x_1-x_0<=t_3*(v_1-a()/2*t_3)", "-t_3*V()<=xo_2-xo_1") &
            la(OrLeftT, "x_1-xo_2>=0&abs_1=x_1-xo_2|x_1-xo_2<=0&abs_1=-(x_1-xo_2)") && (
            debugT("Foo 1-1-1") & QE,
            debugT("Foo 1-1-2") & QE
            ),
          la(hideT, "-t_3*(v_1-a()/2*t_3)<=x_1-x_0", "xo_2-xo_1<=t_3*V()") &
            la(OrLeftT, "x_1-xo_2>=0&abs_1=x_1-xo_2|x_1-xo_2<=0&abs_1=-(x_1-xo_2)") && (
            debugT("Foo 1-1-3") & QE,
            debugT("Foo 1-1-4") & QE
            )
          )
          )
      ),
      la(hideT, "-t_3*(v_1-a()/2*t_3)<=x_1-x_0", "x_1-x_0<=t_3*(v_1-a()/2*t_3)", "-t_3*V()<=xo_2-xo_1", "xo_2-xo_1<=t_3*V()") &
        ls(hideT, "abs(x_1-xo_2)>v_1^2/(2*B)+V()*(v_1/B)") & debugT("Foo 2") &
        cutT(Some("abs(y_0-yo_1)>v_0^2/(2*B)+V()*v_0/B+(A/B+1)*(A/2*t_3^2+t_3*(v_0+V()))".asFormula)) & onBranch(
        (cutShowLbl, debugT("Showing cut that replaces ep ~> t_3") &
          la(hideT, "v_1>=0", "v_1=v_0+a()*t_3", "-t_3*(v_1-a()/2*t_3)<=y_1-y_0", "y_1-y_0<=t_3*(v_1-a()/2*t_3)", "-t_3*V()<=yo_2-yo_1", "yo_2-yo_1<=t_3*V()") &
          ls(hideT, "v_1=0", "abs(y_1-yo_2)>v_1^2/(2*B)+V()*(v_1/B)") &
          AbsT(AntePosition(7).first) &
          lastAnte(hideT) & QE
          ),
        (cutUseLbl, debugT("Use cut") &
          la(hideT, "abs(y_0-yo_1)>v_0^2/(2*B)+V()*v_0/B+(A/B+1)*(A/2*ep()^2+ep()*(v_0+V()))", "ep()>0", "t_3<=ep()") &
          debugT("Now what?") &
          AbsT(AntePosition(13).first) & AbsT(SuccPosition(0).first) & debugT("Foo 1-1") &
          la(OrLeftT, "y_0-yo_1>=0&abs_0=y_0-yo_1|y_0-yo_1<=0&abs_0=-(y_0-yo_1)") && (
            la(hideT, "y_1-y_0<=t_3*(v_1-a()/2*t_3)", "-t_3*V()<=yo_2-yo_1") &
            la(OrLeftT, "y_1-yo_2>=0&abs_1=y_1-yo_2|y_1-yo_2<=0&abs_1=-(y_1-yo_2)") && (
            debugT("Foo 1-1-1") & QE,
            debugT("Foo 1-1-2") & QE
            ),
          la(hideT, "-t_3*(v_1-a()/2*t_3)<=y_1-y_0", "yo_2-yo_1<=t_3*V()") &
            la(OrLeftT, "y_1-yo_2>=0&abs_1=y_1-yo_2|y_1-yo_2<=0&abs_1=-(y_1-yo_2)") && (
            debugT("Foo 1-1-3") & QE,
            debugT("Foo 1-1-4") & QE
            )
          )
          )
      )
      )

    val accelerateFinishT = la(hideT, "r_1()!=0", "w*r_1()=v_0") & onBranch(
      ("Know v=0", la(hideT, "v_0>=0") & accelerateFinishBaseT),
      ("Know x", debugT("Bar") & la(hideT, "abs(x_0-xo_0)>v_0^2/(2*B)+V()*(v_0/B)") & accelerateFinishBaseT),
      ("Know y", debugT("Baz") & la(hideT, "abs(y_0-yo_0)>v_0^2/(2*B)+V()*(v_0/B)") & accelerateFinishBaseT)
    )

    ls(ImplyRightT) & (la(AndLeftT)*) & ls(inductionT(Some(invariant))) & onBranch(
      (indInitLbl, debugT("Base case") & (ls(AndRightT)*) & (ls(OrRightT)*) & la(OrLeftT) & (AxiomCloseT | debugT("Robix axiom close failed unexpectedly") & Tactics.stopT)),
      (indUseCaseLbl, debugT("Use case") & la(hideT, "abs(x-xo)>v^2/(2*B)+V()*(v/B)|abs(y-yo)>v^2/(2*B)+V()*(v/B)") & ls(ImplyRightT) & (la(AndLeftT)*) & ls(ImplyRightT) & debugT("Before ImplyL") & la(OrLeftT) && (la(OrLeftT) && (QE, AbsT(AntePosition(6).first) & QE), AbsT(AntePosition(6).first) & QE)),
      (indStepLbl, debugT("Induction step") & la(hideT, "abs(x-xo)>v^2/(2*B)+V()*(v/B)|abs(y-yo)>v^2/(2*B)+V()*(v/B)") & ls(ImplyRightT) & (la(AndLeftT)*) &
        ls(boxSeqT) &
        // obstacle control
        debugT("Obstacle control") & ls(boxSeqT) & ((ls(boxNDetAssign) & ls(skolemizeT) & ls(boxSeqT))*) & ls(boxTestT) & ls(ImplyRightT) &
        // robot control
        debugT("Robot control") & ls(boxSeqT) & ls(boxChoiceT) & ls(AndRightT) && (
        // brake
        debugT("B1") & ls(boxAssignT) & plantT(FuncOf(Function("a", Some(1), Unit, Real), Nothing), Variable("xo", Some(0)), Variable("yo", Some(0))) & la(eqLeft(exhaustive = true), "a_1()=-B") & la(hideT, "a_1()=-B") &
          hideAndEqT(Variable("xo", Some(0)), Variable("yo", Some(0))) & brakeFinishT,
        ls(boxChoiceT) & ls(AndRightT) && (
          // stay stopped
          debugT("B2") & ls(boxSeqT) & ls(boxTestT) & ls(ImplyRightT) & ls(boxSeqT) & (ls(boxAssignT)*2) & plantT(FuncOf(Function("a", Some(1), Unit, Real), Nothing), Variable("xo", Some(0)), Variable("yo", Some(0))) &
            hideAndEqT(Variable("xo", Some(0)), Variable("yo", Some(0))) & stoppedFinishT,
          // accelerate/new curve
          debugT("B3") &
            // acceleration/radius/angular velocity nondeterministic assignments with tests
            ((ls(boxSeqT) & ls(boxNDetAssign) & ls(skolemizeT) & ls(boxSeqT) & ls(boxTestT) & ls(ImplyRightT) & (la(AndLeftT)*))*3) &
            // measure obstacle and test for safety
            ((ls(boxSeqT) & ls(boxNDetAssign) & ls(skolemizeT))*2) & ls(boxTestT) & ls(ImplyRightT) & plantT(FuncOf(Function("a", None, Unit, Real), Nothing), Variable("xo", Some(1)), Variable("yo", Some(1))) &
            la(hideT, "r_0!=0") & hideAndEqT(Variable("xo", Some(1)), Variable("yo", Some(1))) & accelerateFinishT
          )
        )
        )
    )
  }
}

new PassiveSafetyAbsTacticGenerator()