import edu.cmu.cs.ls.keymaerax.core.{Real, Nothing, Function, FuncOf, Unit, Variable}
import edu.cmu.cs.ls.keymaerax.tactics.BranchLabels._
import edu.cmu.cs.ls.keymaerax.tactics.EqualityRewritingImpl.eqLeft
import edu.cmu.cs.ls.keymaerax.tactics.FOQuantifierTacticsImpl.skolemizeT
import edu.cmu.cs.ls.keymaerax.tactics.HybridProgramTacticsImpl.{boxAssignT, boxChoiceT, boxNDetAssign, boxSeqT,
boxTestT, discreteGhostT}
import edu.cmu.cs.ls.keymaerax.tactics.ODETactics.{diffIntroduceConstantT, diffCutT, diffInvariantT, diffWeakenT}
import edu.cmu.cs.ls.keymaerax.tactics.PropositionalTacticsImpl.{AndLeftT, AndRightT, AxiomCloseT, ImplyLeftT,
ImplyRightT, OrLeftT, OrRightT}
import edu.cmu.cs.ls.keymaerax.tactics.SearchTacticsImpl._
import edu.cmu.cs.ls.keymaerax.tactics.SearchTacticsImpl.onBranch
import edu.cmu.cs.ls.keymaerax.tactics.TacticLibrary.{debugT, hideT, inductionT}
import edu.cmu.cs.ls.keymaerax.tactics.Tactics.{Tactic, LabelBranch, PositionTactic}
import edu.cmu.cs.ls.keymaerax.tactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.tactics._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

import scala.language.postfixOps


class PassiveSafetyTacticGenerator extends (() => Tactic) {

  def apply() = {
    def ls(tactic: PositionTactic, fml: String*) =
      if (fml.isEmpty) locateSucc(tactic)
      else fml.map(f => locateSucc(tactic, _ == f.asFormula)).reduce(_ & _)
    def la(tactic: PositionTactic, fml: String*) =
      if (fml.isEmpty) locateAnte(tactic)
      else fml.map(f => locateAnte(tactic, _ == f.asFormula)).reduce(_ & _)

    val QE = TacticLibrary.arithmeticT

    val invariant = """   v >= 0
                      | & dx^2+dy^2 = 1
                      | & r != 0
                      | & (v = 0 | (  (x-xo >= 0 -> x-xo > v^2 / (2*B) + V()*(v/B))
                      |             & (x-xo <= 0 -> xo-x > v^2 / (2*B) + V()*(v/B)))
                      |          | (  (y-yo >= 0 -> y-yo > v^2 / (2*B) + V()*(v/B))
                      |             & (y-yo <= 0 -> yo-y > v^2 / (2*B) + V()*(v/B))))""".stripMargin.asFormula

    def plantT(av: Variable, xov: Variable, yov: Variable) = {
      val a = av.prettyString
      val xo = xov.prettyString
      val yo = yov.prettyString
      ls(assignb) & ls(diffInvariant(
        "t_2>=0".asFormula ::
          "dx^2+dy^2=1".asFormula ::
          s"v_0=old(v_0)+$a*t_2".asFormula ::
          s"-t_2*(v_0 - $a/2*t_2) <= x_0 - old(x_0) & x_0 - old(x_0) <= t_2*(v_0 - $a/2*t_2)".asFormula ::
          s"-t_2*(v_0 - $a/2*t_2) <= y_0 - old(y_0) & y_0 - old(y_0) <= t_2*(v_0 - $a/2*t_2)".asFormula ::
          s"-t_2 * V() <= $xo - old($xo) & $xo - old($xo) <= t_2 * V()".asFormula ::
          s"-t_2 * V() <= $yo - old($yo) & $yo - old($yo) <= t_2 * V()".asFormula ::
          Nil)) ~
        (debugT("Diff. Inv. result") & ls(diffWeakenT) & ls(ImplyRightT) & (la(AndLeftT)*) & debugT("Plant result"))
    }

    def hideAndEqT(xo: Variable, yo: Variable) = ls(AndRightT) && ((ls(AndRightT)*) & (AxiomCloseT | debugT("AxiomClose failed")), debugT("Hide") &
      la(eqLeft(exhaustive = true), "v0_1()=v_0", "x0_1()=x_0", "y0_1()=y_0", "xo0_1()=" + xo.prettyString, "yo0_1()=" + yo.prettyString) &
      debugT("Done equality rewriting") &
      la(hideT, "r!=0", "v>=0", "dx^2+dy^2=1", "dxo^2+dyo^2<=V()^2", "t_2=0", "v0_1()=v_0",
        "x0_1()=x_0", "y0_1()=y_0", "xo0_1()=" + xo.prettyString, "yo0_1()=" + yo.prettyString, "dx_0^2+dy_0^2=1") & debugT("Done hiding") &
      (ls(OrRightT)*) &
      OrLeftT(AntePosition(4)) && (OrLeftT(AntePosition(4)) && (
      LabelBranch("Know v=0"),
      LabelBranch("Know x")),
      LabelBranch("Know y"))
      )

    val brakeFinishT = onBranch(
      ("Know v=0",
        la(hideT, "ep>0", "V()>=0", "A>=0", "v_0>=0", "t_3<=ep", "x_1-x_0<=t_3*(v_1--B/2*t_3)",
          "-t_3*(v_1--B/2*t_3)<=x_1-x_0", "-t_3*(v_1--B/2*t_3)<=y_1-y_0", "y_1-y_0<=t_3*(v_1--B/2*t_3)",
          "-t_3*V()<=xo_1-xo_0", "xo_1-xo_0<=t_3*V()", "-t_3*V()<=yo_1-yo_0", "yo_1-yo_0<=t_3*V()") &
          ls(hideT, "(y_1-yo_1>=0->y_1-yo_1>v_1^2/(2*B)+V()*(v_1/B))&(y_1-yo_1<=0->yo_1-y_1>v_1^2/(2*B)+V()*(v_1/B))",
            "(x_1-xo_1>=0->x_1-xo_1>v_1^2/(2*B)+V()*(v_1/B))&(x_1-xo_1<=0->xo_1-x_1>v_1^2/(2*B)+V()*(v_1/B))") &
          QE),
      ("Know x", la(AndLeftT) & la(hideT, "y_1-y_0<=t_3*(v_1--B/2*t_3)", "-t_3*(v_1--B/2*t_3)<=y_1-y_0",
        "-t_3*V()<=yo_1-yo_0", "yo_1-yo_0<=t_3*V()") &
        ls(hideT, "(y_1-yo_1>=0->y_1-yo_1>v_1^2/(2*B)+V()*(v_1/B))&(y_1-yo_1<=0->yo_1-y_1>v_1^2/(2*B)+V()*(v_1/B))") &
        ls(AndRightT) & (ls(ImplyRightT)*) & (la(ImplyLeftT)*) & (QE | debugT("QE failed unexpectedly") & Tactics.stopT)),
      ("Know y", la(AndLeftT) & la(hideT, "-t_3*(v_1--B/2*t_3)<=x_1-x_0", "x_1-x_0<=t_3*(v_1--B/2*t_3)",
        "-t_3*V()<=xo_1-xo_0", "xo_1-xo_0<=t_3*V()") &
        ls(hideT, "(x_1-xo_1>=0->x_1-xo_1>v_1^2/(2*B)+V()*(v_1/B))&(x_1-xo_1<=0->xo_1-x_1>v_1^2/(2*B)+V()*(v_1/B))") &
        ls(AndRightT) & (ls(ImplyRightT)*) & (la(ImplyLeftT)*) & (QE | debugT("QE failed unexpectedly") & Tactics.stopT))
    )

    val stoppedFinishT = onBranch(
      ("Know v=0",
        la(hideT, "ep>0", "V()>=0", "B>0", "A>=0", "v_0>=0", "w_2=0", "t_3<=ep", "v_1>=0",
          "-t_3*(v_1-a_1/2*t_3)<=x_1-x_0", "x_1-x_0<=t_3*(v_1-a_1/2*t_3)", "-t_3*(v_1-a_1/2*t_3)<=y_1-y_0",
          "y_1-y_0<=t_3*(v_1-a_1/2*t_3)", "-t_3*V()<=xo_1-xo_0", "xo_1-xo_0<=t_3*V()", "-t_3*V()<=yo_1-yo_0", "yo_1-yo_0<=t_3*V()") &
          ls(hideT, "(y_1-yo_1>=0->y_1-yo_1>v_1^2/(2*B)+V()*(v_1/B))&(y_1-yo_1<=0->yo_1-y_1>v_1^2/(2*B)+V()*(v_1/B))",
            "(x_1-xo_1>=0->x_1-xo_1>v_1^2/(2*B)+V()*(v_1/B))&(x_1-xo_1<=0->xo_1-x_1>v_1^2/(2*B)+V()*(v_1/B))") &
          (QE | debugT("QE failed unexpectedly") & Tactics.stopT)),
      ("Know x",
        la(hideT, "ep>0", "V()>=0", "B>0", "A>=0", "(x_0-xo_0>=0->x_0-xo_0>v_0^2/(2*B)+V()*(v_0/B))&(x_0-xo_0<=0->xo_0-x_0>v_0^2/(2*B)+V()*(v_0/B))",
          "v_0>=0", "w_2=0", "t_3<=ep", "v_1>=0", "-t_3*(v_1-a_1/2*t_3)<=x_1-x_0", "x_1-x_0<=t_3*(v_1-a_1/2*t_3)",
          "-t_3*(v_1-a_1/2*t_3)<=y_1-y_0", "y_1-y_0<=t_3*(v_1-a_1/2*t_3)", "-t_3*V()<=xo_1-xo_0", "xo_1-xo_0<=t_3*V()",
          "-t_3*V()<=yo_1-yo_0", "yo_1-yo_0<=t_3*V()") &
          ls(hideT, "(y_1-yo_1>=0->y_1-yo_1>v_1^2/(2*B)+V()*(v_1/B))&(y_1-yo_1<=0->yo_1-y_1>v_1^2/(2*B)+V()*(v_1/B))",
            "(x_1-xo_1>=0->x_1-xo_1>v_1^2/(2*B)+V()*(v_1/B))&(x_1-xo_1<=0->xo_1-x_1>v_1^2/(2*B)+V()*(v_1/B))") &
          (QE | debugT("QE failed unexpectedly") & Tactics.stopT)),
      ("Know y",
        la(hideT, "ep>0", "V()>=0", "B>0", "A>=0", "(y_0-yo_0>=0->y_0-yo_0>v_0^2/(2*B)+V()*(v_0/B))&(y_0-yo_0<=0->yo_0-y_0>v_0^2/(2*B)+V()*(v_0/B))",
          "v_0>=0", "w_2=0", "t_3<=ep", "v_1>=0", "-t_3*(v_1-a_1/2*t_3)<=x_1-x_0", "x_1-x_0<=t_3*(v_1-a_1/2*t_3)",
          "-t_3*(v_1-a_1/2*t_3)<=y_1-y_0", "y_1-y_0<=t_3*(v_1-a_1/2*t_3)", "-t_3*V()<=xo_1-xo_0", "xo_1-xo_0<=t_3*V()",
          "-t_3*V()<=yo_1-yo_0", "yo_1-yo_0<=t_3*V()") &
          ls(hideT, "(y_1-yo_1>=0->y_1-yo_1>v_1^2/(2*B)+V()*(v_1/B))&(y_1-yo_1<=0->yo_1-y_1>v_1^2/(2*B)+V()*(v_1/B))",
            "(x_1-xo_1>=0->x_1-xo_1>v_1^2/(2*B)+V()*(v_1/B))&(x_1-xo_1<=0->xo_1-x_1>v_1^2/(2*B)+V()*(v_1/B))") &
          (QE | debugT("QE failed unexpectedly") & Tactics.stopT))
    )

    val accelerateFinishBaseT = la(OrLeftT) && (
      la(hideT, "-t_3*(v_1-a/2*t_3)<=y_1-y_0", "y_1-y_0<=t_3*(v_1-a/2*t_3)", "-t_3*V()<=yo_2-yo_1", "yo_2-yo_1<=t_3*V()") &
        ls(hideT, "(y_1-yo_2>=0->y_1-yo_2>v_1^2/(2*B)+V()*(v_1/B))&(y_1-yo_2<=0->yo_2-y_1>v_1^2/(2*B)+V()*(v_1/B))") & la(AndLeftT) &
        ls(AndRightT) && (
        ls(ImplyRightT) & debugT("Foo 1-1") & ImplyLeftT(AntePosition(15)) /*x_0-xo_1>=0->x_0-xo_1>v_0^2/(2*B)+V()*v_0/B+(A/B+1)*(A/2*ep()^2+ep()*(v_0+V()))*/ && (
          /*"x_0-xo_1<=0->xo_1-x_0>v_0^2/(2*B)+V()*v_0/B+(A/B+1)*(A/2*ep()^2+ep()*(v_0+V()))*/
          ImplyLeftT(AntePosition(15)) && (
            /* tautology x-xo >= 0 | x-xo <= 0 in succedent */ QE,
            /* contradiction in antecedent */ debugT("Foo 1-1a") & la(hideT, "-t_3*(v_1-a/2*t_3)<=x_1-x_0", "xo_2-xo_1<=t_3*V()", "-B<=a") & ls(hideT, "x_1-xo_2>v_1^2/(2*B)+V()*(v_1/B)", "x_0-xo_1>=0") & QE
            ),
          ImplyLeftT(AntePosition(15)) && (
            debugT("Foo 1-1b") & la(hideT, "x_1-x_0<=t_3*(v_1-a/2*t_3)", "-t_3*V()<=xo_2-xo_1", "-B<=a") & ls(hideT, "x_0-xo_1<=0") & QE,
            /* contradiction in antecedent */ QE
            )
          ),
        ls(ImplyRightT) & debugT("Foo 1-2") & ImplyLeftT(AntePosition(15)) /* x_0-xo_1>=0->x_0-xo_1>v_0^2/(2*B)+V()*v_0/B+(A/B+1)*(A/2*ep()^2+ep()*(v_0+V())) */ && (
          /*"x_0-xo_1<=0->xo_1-x_0>v_0^2/(2*B)+V()*v_0/B+(A/B+1)*(A/2*ep()^2+ep()*(v_0+V()))*/
          ImplyLeftT(AntePosition(15)) && (
            /* tautology x-xo >= 0 | x-xo <= 0 in succedent */ QE,
            debugT("Foo 1-2a") & la(hideT, "-t_3*(v_1-a/2*t_3)<=x_1-x_0", "xo_2-xo_1<=t_3*V()", "-B<=a") & ls(hideT, "x_0-xo_1>=0") & QE
            ),
          ImplyLeftT(AntePosition(15)) && (
            /* contradiction in antecedent */ debugT("Foo 1-2b") & la(hideT, "x_1-x_0<=t_3*(v_1-a/2*t_3)", "-t_3*V()<=xo_2-xo_1", "-B<=a") & ls(hideT, "xo_2-x_1>v_1^2/(2*B)+V()*(v_1/B)") & QE,
            /* contradiction in antecedent */ QE
            )
          )
        ),
      debugT("Foo 2") &
        la(hideT, "-t_3*(v_1-a/2*t_3)<=x_1-x_0", "x_1-x_0<=t_3*(v_1-a/2*t_3)", "-t_3*V()<=xo_2-xo_1", "xo_2-xo_1<=t_3*V()") &
        ls(hideT, "(x_1-xo_2>=0->x_1-xo_2>v_1^2/(2*B)+V()*(v_1/B))&(x_1-xo_2<=0->xo_2-x_1>v_1^2/(2*B)+V()*(v_1/B))") & la(AndLeftT) &
        ls(AndRightT) && (
        ls(ImplyRightT) & debugT("Foo 2-1") & ImplyLeftT(AntePosition(15)) /* y_0-yo_1>=0->y_0-yo_1>v_0^2/(2*B)+V()*v_0/B+(A/B+1)*(A/2*ep()^2+ep()*(v_0+V())) */ && (
          // y_0-yo_1<=0->yo_1-y_0>v_0^2/(2*B)+V()*v_0/B+(A/B+1)*(A/2*ep()^2+ep()*(v_0+V()))
          ImplyLeftT(AntePosition(15)) && (
            /* tautology in succedent */ QE,
            /* contradiction in antecedent */ debugT("Foo 2-1a") & la(hideT, "-t_3*(v_1-a/2*t_3)<=y_1-y_0", "yo_2-yo_1<=t_3*V()", "-B<=a") & ls(hideT, "y_1-yo_2>v_1^2/(2*B)+V()*(v_1/B)", "y_0-yo_1>=0") & QE
            ),
          ImplyLeftT(AntePosition(15)) && (
            debugT("Foo 2-1b") & la(hideT, "y_1-y_0<=t_3*(v_1-a/2*t_3)", "-t_3*V()<=yo_2-yo_1", "-B<=a") & ls(hideT, "y_0-yo_1<=0") & QE,
            /* contradiction in antecedent */ QE
            )
          ),
        ls(ImplyRightT) & debugT("Foo 2-2") & ImplyLeftT(AntePosition(15)) /* y_0-yo_1>=0->y_0-yo_1>v_0^2/(2*B)+V()*v_0/B+(A/B+1)*(A/2*ep()^2+ep()*(v_0+V())) */ && (
          // y_0-yo_1<=0->yo_1-y_0>v_0^2/(2*B)+V()*v_0/B+(A/B+1)*(A/2*ep()^2+ep()*(v_0+V()))
          ImplyLeftT(AntePosition(15)) && (
            /* tautology in succedent */ QE,
            debugT("Foo 2-2a") & la(hideT, "-t_3*(v_1-a/2*t_3)<=y_1-y_0", "yo_2-yo_1<=t_3*V()", "-B<=a") & ls(hideT, "y_0-yo_1>=0") & QE
            ),
          ImplyLeftT(AntePosition(15)) && (
            /* contradiction in antecedent */ debugT("Foo 2-2b") & la(hideT, "y_1-y_0<=t_3*(v_1-a/2*t_3)", "-t_3*V()<=yo_2-yo_1", "-B<=a") & ls(hideT, "yo_2-y_1>v_1^2/(2*B)+V()*(v_1/B)") & QE,
            /* contradiction in antecedent */ QE
            )
          )
        )
      )

    val accelerateFinishT = la(hideT, "r_1!=0", "w*r_1=v_0") & onBranch(
      ("Know v=0", la(hideT, "v_0>=0") & accelerateFinishBaseT),
      ("Know x", debugT("Bar") & la(hideT, "(x_0-xo_0>=0->x_0-xo_0>v_0^2/(2*B)+V()*(v_0/B))&(x_0-xo_0<=0->xo_0-x_0>v_0^2/(2*B)+V()*(v_0/B))") & accelerateFinishBaseT),
      ("Know y", debugT("Baz") & la(hideT, "(y_0-yo_0>=0->y_0-yo_0>v_0^2/(2*B)+V()*(v_0/B))&(y_0-yo_0<=0->yo_0-y_0>v_0^2/(2*B)+V()*(v_0/B))") & accelerateFinishBaseT)
    )

    ls(ImplyRightT) & (la(AndLeftT)*) & ls(inductionT(Some(invariant))) & onBranch(
      (indInitLbl, debugT("Base case") & (ls(AndRightT)*) & (ls(OrRightT)*) & la(OrLeftT) & (AxiomCloseT | debugT("Robix axiom close failed unexpectedly") & Tactics.stopT)),
      (indUseCaseLbl, debugT("Use case") & la(hideT, "(x-xo>=0->x-xo>v^2/(2*B)+V()*(v/B))&(x-xo<=0->xo-x>v^2/(2*B)+V()*(v/B))|(y-yo>=0->y-yo>v^2/(2*B)+V()*(v/B))&(y-yo<=0->yo-y>v^2/(2*B)+V()*(v/B))") & ls(ImplyRightT) & (la(AndLeftT)*) & ls(ImplyRightT) & (AxiomCloseT | QE | debugT("Failed unexpectedly"))),
      (indStepLbl, debugT("Induction step") & la(hideT, "(x-xo>=0->x-xo>v^2/(2*B)+V()*(v/B))&(x-xo<=0->xo-x>v^2/(2*B)+V()*(v/B))|(y-yo>=0->y-yo>v^2/(2*B)+V()*(v/B))&(y-yo<=0->yo-y>v^2/(2*B)+V()*(v/B))") & ls(ImplyRightT) & (la(AndLeftT)*) &
        ls(boxSeqT) &
        // obstacle control
        debugT("Obstacle control") & ls(boxSeqT) & ((ls(boxNDetAssign) & ls(skolemizeT) & ls(boxSeqT))*) & ls(boxTestT) & ls(ImplyRightT) &
        // robot control
        debugT("Robot control") & ls(boxSeqT) & ls(boxChoiceT) & ls(AndRightT) && (
        // brake
        debugT("B1") & ls(boxAssignT) & plantT(Variable("a", Some(1)), Variable("xo", Some(0)), Variable("yo", Some(0))) & la(eqLeft(exhaustive = true), "a_1=-B") & la(hideT, "a_1=-B") &
          hideAndEqT(Variable("xo", Some(0)), Variable("yo", Some(0))) & brakeFinishT,
        ls(boxChoiceT) & ls(AndRightT) && (
          // stay stopped
          debugT("B2") & ls(boxSeqT) & ls(boxTestT) & ls(ImplyRightT) & ls(boxSeqT) & (ls(boxAssignT)*2) & plantT(Variable("a", Some(1)), Variable("xo", Some(0)), Variable("yo", Some(0))) &
            hideAndEqT(Variable("xo", Some(0)), Variable("yo", Some(0))) & stoppedFinishT,
          // accelerate/new curve
          debugT("B3") &
            // acceleration/radius/angular velocity nondeterministic assignments with tests
            ((ls(boxSeqT) & ls(boxNDetAssign) & ls(skolemizeT) & ls(boxSeqT) & ls(boxTestT) & ls(ImplyRightT) & (la(AndLeftT)*))*3) &
            // measure obstacle and test for safety
            ((ls(boxSeqT) & ls(boxNDetAssign) & ls(skolemizeT))*2) & ls(boxTestT) & ls(ImplyRightT) & plantT(Variable("a"), Variable("xo", Some(1)), Variable("yo", Some(1))) &
            la(hideT, "r_0!=0") & hideAndEqT(Variable("xo", Some(1)), Variable("yo", Some(1))) & accelerateFinishT
          )
        )
        )
    )
  }
}

new PassiveSafetyTacticGenerator()