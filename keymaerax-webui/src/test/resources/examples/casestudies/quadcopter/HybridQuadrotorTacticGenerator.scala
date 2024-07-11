import org.keymaerax.core._
import org.keymaerax.parser.StringConverter._
import org.keymaerax.tactics.BranchLabels._
import org.keymaerax.tactics.HybridProgramTacticsImpl._
import org.keymaerax.tactics.SearchTacticsImpl._
import org.keymaerax.tactics.SearchTacticsImpl.locateAnte
import org.keymaerax.tactics.SearchTacticsImpl.locateSucc
import org.keymaerax.tactics.TacticLibrary._
import org.keymaerax.tactics.TactixLibrary.onBranch
import org.keymaerax.tactics.{FOQuantifierTacticsImpl, HybridProgramTacticsImpl, ODETactics, SuccPosition}
import org.keymaerax.tactics.Tactics.{PositionTactic, Tactic}
import org.keymaerax.tactics.TactixLibrary._

class HybridQuadrotorTacticGenerator extends (() => Tactic) {
  def apply() = {

    def ls(tactic: PositionTactic, fml: String*) =
      if (fml.isEmpty) locateSucc(tactic)
      else fml.map(f => locateSucc(tactic, _ == f.asFormula) | debugT("Unable to find formula " + f + " in succedent")).reduce(_ & _)
    def la(tactic: PositionTactic, fml: String*) =
      if (fml.isEmpty) locateAnte(tactic)
      else fml.map(f => locateAnte(tactic, _ == f.asFormula) | debugT("Unable to find formula " + f + " in antecedent")).reduce(_ & _)

    val odePos = SuccPosition(0)

    val inv = "h>=href".asFormula
    val cut1 = "(h^2*kp^2 - 2*h*href*kp^2 + href^2*kp^2 + h*kd()*kp*v - href*kd()*kp*v + kp*v^2) * (h0_1()^2*kp^2 - 2*h0_1()*href*kp^2 + href^2*kp^2 + h0_1()*kd()*kp*v0_1() - href*kd()*kp*v0_1() + kp*v0_1()^2) > 0".asFormula
    val cut2 = "(h^2*kp^2 - 2*h*href*kp^2 + href^2*kp^2 + h*kd()*kp*v - href*kd()*kp*v + kp*v^2) * (h0_1()^2*kp^2 - 2*h0_1()*href*kp^2 + href^2*kp^2 + h0_1()*kd()*kp*v0_1() - href*kd()*kp*v0_1() + kp*v0_1()^2) * z = (h0_1()^2*kp^2 - 2*h0_1()*href*kp^2 + h0_1()*kd()*kp*v0_1() - href*kd()*kp*v0_1() + kp*v0_1()^2)^2 * z0_1() & z > 0".asFormula

    val tactic = ls(implyR) &
      ls(I(inv)) &
      onBranch(
        (indInitLbl, debug("Base case") & QE),
        (indUseCaseLbl, debug("Use case") & ls(implyR) & closeId),
        (indStepLbl,
          debug("Induction step") &
            ls(implyR) &
            lastAnte(hide) &
            ls(composeb) &
            ls(composeb) & ls(randomb) & ls(allR) & ls(testb) & ls(implyR) &
            debug("Introducing ghost h0") &
            HybridProgramTacticsImpl.discreteGhostT(Some(Variable("h0")), Variable("h"))(odePos) &
            HybridProgramTacticsImpl.boxAssignT(FOQuantifierTacticsImpl.skolemizeToFnT(_))(odePos) &
            debug("Introducing ghost v0") &
            HybridProgramTacticsImpl.discreteGhostT(Some(Variable("v0")), Variable("v"))(odePos) &
            HybridProgramTacticsImpl.boxAssignT(FOQuantifierTacticsImpl.skolemizeToFnT(_))(odePos) &
            debug("Diff. cut (1)") &
            DC(cut1)(odePos) &
            onBranch(
              (cutShowLbl,
                debug("Introducing diff. auxiliary z'=z*kd()") &
                  DA(Variable("z"), FuncOf(Function("kd", None, Unit, Real), Nothing), "0".asTerm, And(cut1, "z>0".asFormula))(odePos) & onBranch(
                  ("Diff. Aux. P Initially Valid", debug("Initially valid") & QE),
                  ("Diff. Aux. Show Equivalence (1)", debug("Auxiliary equivalent (1)") & QE),
                  ("Diff. Aux. Show Equivalence (2)", debug("Auxiliary equivalent (2)") & QE),
                  ("Diff. Aux. Result", debug("DA result") &
                    debug("Introducing ghost z0") &
                    HybridProgramTacticsImpl.discreteGhostT(Some(Variable("z0")), Variable("z"))(odePos) &
                    HybridProgramTacticsImpl.boxAssignT(FOQuantifierTacticsImpl.skolemizeToFnT(_))(odePos) &
                    debug("Diff. cut (2)") &
                    DC(cut2)(odePos) &
                    onBranch(
                      (cutShowLbl,
                        debug("[]split box conjunction") &
                          lastSucc(boxSplitConjunctionT) &
                          ls(andR) &&(
                          debug("Show first conjunct with DI") & ls(Dconstify) & ls(DI),
                          debug("Hiding irrelevant facts in second conjunct") &
                            la(andL, "(h^2*kp^2-2*h*href*kp^2+href^2*kp^2+h*kd()*kp*v-href*kd()*kp*v+kp*v^2)*(h0_1()^2*kp^2-2*h0_1()*href*kp^2+href^2*kp^2+h0_1()*kd()*kp*v0_1()-href*kd()*kp*v0_1()+kp*v0_1()^2)>0&z>0") &
                            la(hide, "(h^2*kp^2-2*h*href*kp^2+href^2*kp^2+h*kd()*kp*v-href*kd()*kp*v+kp*v^2)*(h0_1()^2*kp^2-2*h0_1()*href*kp^2+href^2*kp^2+h0_1()*kd()*kp*v0_1()-href*kd()*kp*v0_1()+kp*v0_1()^2)>0") &
                            debug("Introducing diff. auxiliary u'=u*-1/2*kd()") &
                            DA(Variable("u"), "-1/2*kd()".asTerm, "0".asTerm, "z>0 & z*u^2=1".asFormula)(odePos) & onBranch(
                            ("Diff. Aux. P Initially Valid", debug("Initially valid") & closeId),
                            ("Diff. Aux. Show Equivalence (1)", debug("Auxiliary equivalent (1)") & QE),
                            ("Diff. Aux. Show Equivalence (2)", debug("Auxiliary equivalent (2)") & QE),
                            ("Diff. Aux. Result", debug("DA result") &
                              debug("Diff. cut (3)") &
                              DC("z*u^2=1".asFormula)(odePos) & onBranch(
                              (cutShowLbl, debug("Show z*u^2=1") & ls(DI)),
                              (cutUseLbl, debug("Use z*u^2=1") & DW(odePos) & ls(implyR) & (la(andL)*) & debug("Closing by QE") & QE)
                            ))
                          )
                          )
                        ),
                      (cutUseLbl, debug("Use diff. cut (2)") & DW(odePos) & debug("Off to QE") & QE)
                    ))
                )
                ),
              (cutUseLbl, debug("Use diff. cut (1)") & DW(odePos) & ls(implyR) & debug("Off to QE") & QE)
            )
          )
      )

    tactic
  }
}
