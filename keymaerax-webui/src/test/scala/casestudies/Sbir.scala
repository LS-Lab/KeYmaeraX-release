/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package casestudies

import java.io.File

import edu.cmu.cs.ls.keymaerax.core.Variable
import edu.cmu.cs.ls.keymaerax.launcher.KeYmaeraX
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXPrettyPrinter, KeYmaeraXProblemParser}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tactics.BranchLabels._
import edu.cmu.cs.ls.keymaerax.tactics.ODETactics._
import edu.cmu.cs.ls.keymaerax.tactics.SearchTacticsImpl._
import edu.cmu.cs.ls.keymaerax.tactics.TacticLibrary._
import edu.cmu.cs.ls.keymaerax.tactics.TacticLibrary.diffCutT
import edu.cmu.cs.ls.keymaerax.tactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.tactics.TactixLibrary.onBranch
import edu.cmu.cs.ls.keymaerax.tactics._
import edu.cmu.cs.ls.keymaerax.tags.SlowTest
import edu.cmu.cs.ls.keymaerax.tools.{Polya, Z3, Mathematica, KeYmaera}
import testHelper.ProvabilityTestHelper
import org.scalatest.{BeforeAndAfterEach, FlatSpec, Matchers}
import testHelper.ParserFactory._


import scala.language.postfixOps


import scala.collection.immutable.Map

/**
  * Created by ran on 11/13/15.
  */
@SlowTest
class Sbir extends FlatSpec with Matchers with BeforeAndAfterEach {

  val helper = new ProvabilityTestHelper((x) => println(x))
  val mathematicaConfig: Map[String, String] = helper.mathematicaConfig

  override def beforeEach() = {
    Tactics.KeYmaeraScheduler = new Interpreter(KeYmaera)
    Tactics.MathematicaScheduler = new Interpreter(new Mathematica)
    Tactics.MathematicaScheduler.init(mathematicaConfig)
    Tactics.KeYmaeraScheduler.init(Map())
    Tactics.Z3Scheduler = Some(new Interpreter(new Z3))
    Tactics.Z3Scheduler.get.init(Map())
    Tactics.PolyaScheduler = Some(new Interpreter(new Polya))
    Tactics.PolyaScheduler.get.init(Map())

  }

  override def afterEach() = {
    if (Tactics.Z3Scheduler != null && Tactics.Z3Scheduler.isDefined) Tactics.Z3Scheduler.get.shutdown()
    if (Tactics.PolyaScheduler != null && Tactics.PolyaScheduler.isDefined) Tactics.PolyaScheduler.get.shutdown()
    if (Tactics.MathematicaScheduler != null) Tactics.MathematicaScheduler.shutdown()
    if (Tactics.KeYmaeraScheduler != null) Tactics.KeYmaeraScheduler.shutdown()
    Tactics.PolyaScheduler = null
    Tactics.Z3Scheduler = null
    Tactics.MathematicaScheduler = null
    Tactics.KeYmaeraScheduler = null
  }

  "fixedwing_simple_max" should "prove" in {
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/sbir/fixedwing_simple_max.key"))

    val loopInv = """       dx^2+dy^2 = 1
                    |      & dz^2+dxy^2 = 1
                    |      & v>=Vmin
                    |      & theta <= Theta
                    |      & theta >= -Theta
                    |      & S >= max((v^2-Vmin^2)/(2*B) + 2*(Vmin^2)/(g*tanTheta), (v^2-Vmin^2)/(2*B) + 2*(Vmin^2)/(g*tanTheta)+Vmin*((Theta-abs(theta)/W-(v-Vmin)/B)))
                    |      & (abs(x-xo) >= max((v^2-Vmin^2)/(2*B) + 2*(Vmin^2)/(g*tanTheta), (v^2-Vmin^2)/(2*B) + 2*(Vmin^2)/(g*tanTheta)+Vmin*((Theta-abs(theta)/W-(v-Vmin)/B)))
                    |        | abs(y-yo) >= max((v^2-Vmin^2)/(2*B) + 2*(Vmin^2)/(g*tanTheta), (v^2-Vmin^2)/(2*B) + 2*(Vmin^2)/(g*tanTheta)+Vmin*((Theta-abs(theta)/W-(v-Vmin)/B))))""".stripMargin.asFormula

    val diffInv = "t>=0".asFormula :: "dx^2+dy^2 = 1".asFormula :: "dz^2+dxy^2 = 1".asFormula :: "v = v0 + a*t".asFormula :: "theta = theta0 + wt".asFormula :: Nil

    val speedCtrl = ls(composeb) & ls(testb) & ls(implyR) & ls(assignb)
    val rollAngleCtrl = ls(composeb) & ls(testb) & ls(implyR) & ls(assignb)
    val safeBrake = ls(testb) & ls(implyR) & ls(assignb)

    val plant = ls(diffCutT("t>=0".asFormula)) &  onBranch(
      (cutShowLbl, debugT("Show t_2>=0")
//        & la(hideT, "dx^2+dy^2=1&dz_0^2+dxy_0^2=1&v_0>=Vmin&theta_0<=Theta&theta_0>=-Theta&S>=max(((v_0^2-Vmin^2)/(2*B)+2*Vmin^2/(g*tanTheta),(v_0^2-Vmin^2)/(2*B)+2*Vmin^2/(g*tanTheta)+Vmin*(Theta-abs(theta_0)/W-(v_0-Vmin)/B)))&(abs(x_0-xo_0)>=max(((v_0^2-Vmin^2)/(2*B)+2*Vmin^2/(g*tanTheta),(v_0^2-Vmin^2)/(2*B)+2*Vmin^2/(g*tanTheta)+Vmin*(Theta-abs(theta_0)/W-(v_0-Vmin)/B)))|abs(y_0-yo_0)>=max(((v_0^2-Vmin^2)/(2*B)+2*Vmin^2/(g*tanTheta),(v_0^2-Vmin^2)/(2*B)+2*Vmin^2/(g*tanTheta)+Vmin*(Theta-abs(theta_0)/W-(v_0-Vmin)/B))))")
        /*& (ls(diffInvariantT)  | debugT("Diff. inv. t>=0 failed"))*/),
      (cutUseLbl, debugT("Use t_2>=0"))
    )



    val maneuver = ls(composeb) & ls(composeb) & ls(choiceb) & ls(andR) && (
      (debug("v=Vmin") & speedCtrl & ls(choiceb) & ls(andR)) && (
        (debug("theta=Theta") & rollAngleCtrl & safeBrake & plant),
        (debug("theta!=Theta") & ls(choiceb) & ls(andR) && (
          (debug("0<=theta<=Theta") & rollAngleCtrl & safeBrake),
          (debug("-Theta<=theta< 0") & rollAngleCtrl & safeBrake)
          ))
        ),
      (debug("v>=Vmin") & speedCtrl & ls(choiceb) & ls(andR)) && (
        (debug("theta=Theta") & rollAngleCtrl & safeBrake),
        (debug("theta!=Theta") & ls(choiceb) & ls(andR) && (
          (debug("0<=theta<=Theta") & rollAngleCtrl & safeBrake),
          (debug("-Theta<=theta< 0") & rollAngleCtrl & safeBrake)
          ))
        )
      )

    val tactic = ls(implyR) & (la(andL)*) & ls(I(loopInv)) & onBranch(
      (indInitLbl, debug("Base Case") & QE),
      (indUseCaseLbl, debug("Use Case") & ls(implyR) & (la(andL)*) & QE),
      (indStepLbl, debug("Step") & ls(implyR) & ls(composeb) & ls(composeb) & ls(choiceb) & ls(andR) && (
        (debug("brake on current curve") & maneuver),
        (debug("follow new curve"))
        ))
    )

    helper.runTactic(tactic, new RootNode(s)) shouldBe 'closed
  }

  //  "fixedwing_simple" should "prove" in {
  //    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/sbir/fixedwing_simple.key"))
  //
  //    val loopInv = """       dx^2+dy^2 = 1
  //                    |      & dz^2+dxy^2 = 1
  //                    |      & v>=Vmin
  //                    |      & theta <= Theta
  //                    |      & theta >= -Theta
  //                    |      & (((v-Vmin)/B >= (Theta-abs(theta))/W &
  //                    |        (S >= (v^2-Vmin^2)/(2*B) + 2*(Vmin^2)/(g*tanTheta)
  //                    |        & (abs(x-xo) >= (v^2-Vmin^2)/(2*B) + 2*(Vmin^2)/(g*tanTheta)
  //                    |          | abs(y-yo) >= (v^2-Vmin^2)/(2*B) + 2*(Vmin^2)/(g*tanTheta))
  //                    |        ))
  //                    |      | ((v-Vmin)/B < (Theta-abs(theta))/W &
  //                    |        (S >= (v-Vmin)^2/(2*B)+Vmin*(Theta-abs(theta))/W + 2*(Vmin^2)/(g*tanTheta)
  //                    |        & (abs(x-xo) >= (v-Vmin)^2/(2*B)+Vmin*(Theta-abs(theta))/W + 2*(Vmin^2)/(g*tanTheta)
  //                    |          | abs(y-yo) >= (v-Vmin)^2/(2*B)+Vmin*(Theta-abs(theta))/W + 2*(Vmin^2)/(g*tanTheta))
  //                    |        ))) """.stripMargin.asFormula
  //
  //    //    val diffInv = "t>=0".asFormula :: "dx^2+dy^2 = 1".asFormula :: "dz^2+dxy^2 = 1".asFormula :: "v = v0 + a*t".asFormula :: "theta = theta0 + wt".asFormula :: Nil
  //    val diffInv = "v = v0 + a*t".asFormula :: Nil
  //
  //    val stopVCtrl = ls(composeb) & ls(testb) & ls(implyR) & ls(assignb)
  //    val stopThetaCtrl = ls(composeb) & ls(testb) & ls(implyR) & ls(assignb)
  //    val stopCondCtrl = ls(testb)
  //    val resetT = ls(assignb)
  //
  //    val stopTactic = ls(composeb) & ls(composeb) & ls(choiceb) & ls(andR) && (
  //      (debug("v=Vmin") & stopVCtrl & ls(choiceb) & ls(andR) && (
  //        (debug("theta=Theta") & stopThetaCtrl & stopCondCtrl),
  //        (debug("theta!=Theta") /*& ls(choiceb) & ls(andR) && (
  //          (debug("0<=theta<=Theta") & stopThetaCtrl & stopCondCtrl),
  //          (debug("-Theta<=theta< 0") & stopThetaCtrl & stopCondCtrl)
  //          )*/)
  //        ) ),
  //      (debug("v>=Vmin") & stopVCtrl )
  //      )
  //
  //    val tactic = ls(implyR) & (la(andL)*) & ls(I(loopInv)) & onBranch(
  //      (indInitLbl, debug("Base Case") /* & QE */),
  //      (indUseCaseLbl, debug("Use Case") /* & ls(implyR) & (la(andL)*) & la(orL) && (
  //        (debug("tv>=tt") & QE),
  //        (debug("tv<tt") & QE)
  //        )*/),
  //      (indStepLbl, debug("Step") & ls(implyR) & ls(composeb) & ls(composeb) & ls(choiceb) & ls(andR) && (
  //        (debug("brake on current curve") & stopTactic),
  //        (debug("follow new curve"))
  //        ))
  //    )
  //
  //    helper.runTactic(tactic, new RootNode(s)) shouldBe 'closed
  //  }

  //  ignore should "prove fixedwing" in {
  //    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/sbir/fixedwing.key"))
  //    val loopInv = """       dx^2+dy^2 = 1
  //                    |      & dz^2+dxy^2 = 1
  //                    |      & v>=Vmin
  //                    |      & theta <= Theta
  //                    |      & theta >= -Theta
  //                    |      & (((v-Vmin)/B >= (Theta-abs(theta))/W &
  //                    |        (sqrdr^2 = ((v^2-Vmin^2)/(2*B))^2 + ((Vmin^2)/(g*tanTheta))^2
  //                    |        & S >= sqrdr + (Vmin^2)/(g*tanTheta)
  //                    |        & (abs(x-xo) >= (v^2-Vmin^2)/(2*B) + 2*(Vmin^2)/(g*tanTheta)
  //                    |          | abs(y-yo) >= (v^2-Vmin^2)/(2*B) + 2*(Vmin^2)/(g*tanTheta))
  //                    |        ))
  //                    |      | ((v-Vmin)/B < (Theta-abs(theta))/W &
  //                    |        (sqrdr^2 = ((v-Vmin)^2/(2*B)+Vmin*(Theta-abs(theta))/W)^2 + ((Vmin^2)/(g*tanTheta))^2
  //                    |        & S >= sqrdr + (Vmin^2)/(g*tanTheta)
  //                    |        & (abs(x-xo) >= (v-Vmin)^2/(2*B)+Vmin*(Theta-abs(theta))/W + 2*(Vmin^2)/(g*tanTheta)
  //                    |          | abs(y-yo) >= (v-Vmin)^2/(2*B)+Vmin*(Theta-abs(theta))/W + 2*(Vmin^2)/(g*tanTheta))
  //                    |        ))) """.stripMargin.asFormula
  //
  ////    val diffInv = "t>=0".asFormula :: "dx^2+dy^2 = 1".asFormula :: "dz^2+dxy^2 = 1".asFormula :: "v = v0 + a*t".asFormula :: "theta = theta0 + wt".asFormula :: Nil
  //    val diffInv = "v = v0 + a*t".asFormula :: Nil
  //
  //    val stopVCtrl = ls(composeb) & ls(testb) & ls(implyR) & ls(assignb)
  //    val stopThetaCtrl = ls(composeb) & ls(testb) & ls(implyR) & ls(assignb) & ls(assignb)
  //
  //    val stopTactic = ls(composeb) & ls(choiceb) & ls(andR) && (
  //      (debug("v=Vmin") & stopVCtrl & ls(choiceb) & ls(andR) && (
  //        (debug("theta=Theta") & stopThetaCtrl),
  //        (debug("theta!=Theta") & ls(choiceb) & ls(andR) && (
  //          (debug("0<=theta<=Theta") & stopThetaCtrl),
  //          (debug("-Theta<=theta< 0") & stopThetaCtrl)
  //          ))
  //        ) ),
  //      (debug("v>=Vmin") & stopVCtrl )
  //      )
  //
  //
  //
  //    val tactic = ls(implyR) & (la(andL)*) & ls(I(loopInv)) & onBranch(
  //      (indInitLbl, debug("Base Case") & QE),
  //      (indUseCaseLbl, debug("Use Case") & ls(implyR) & (la(andL)*) & la(orL) && (
  //        (debug("tv>=tt") & QE),
  //        (debug("tv<tt") & QE)
  //      )),
  //      (indStepLbl, debug("Step") & ls(implyR) & ls(composeb) & ls(composeb) & ls(choiceb) & ls(andR) && (
  //        (debug("brake on current curve") & stopTactic),
  //        (debug("follow new curve"))
  //        ))
  //    )
  //    helper.runTactic(tactic, new RootNode(s)) shouldBe 'closed
  //  }
}
