/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package casestudies

import edu.cmu.cs.ls.keymaerax.core.Variable
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tactics.BranchLabels._
import edu.cmu.cs.ls.keymaerax.tactics.SearchTacticsImpl.locateAnte
import edu.cmu.cs.ls.keymaerax.tactics.SearchTacticsImpl.locateSucc
import edu.cmu.cs.ls.keymaerax.tactics.Tactics.PositionTactic
import edu.cmu.cs.ls.keymaerax.tactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.tactics.TacticLibrary._
import edu.cmu.cs.ls.keymaerax.tactics.TactixLibrary.onBranch
import edu.cmu.cs.ls.keymaerax.tactics._
import edu.cmu.cs.ls.keymaerax.tools.{Polya, Z3, Mathematica, KeYmaera}
import org.scalatest.{BeforeAndAfterEach, FlatSpec, Matchers}
import edu.cmu.cs.ls.keymaerax.tags.SlowTest
import testHelper.ParserFactory._



import scala.language.postfixOps


import scala.collection.immutable.Map

/**
  * Created by ran on 11/13/15.
  *
  * @author Ran Ji
  */
@SlowTest
class Fixedwing extends FlatSpec with Matchers with BeforeAndAfterEach {

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

  /** Fixed wing model without bound: loitering case
    *
    * The helicopter will follow a loitering circle
    * v = Vmin & abs(theta) = Theta
    *
    * Proved in commit 15a1937 of fixedwing branch
    */
  /* "fixedwing_simple_loitering" */ ignore should "prove fixedwing_simple_loitering" in {
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/fixedwing/fixedwing_simple_loitering.key"))

    def ls(tactic: PositionTactic, fml: String*) =
      if (fml.isEmpty) locateSucc(tactic)
      else fml.map(f => locateSucc(tactic, _ == f.asFormula) | debugT("Unable to find formula " + f + " in succedent")).reduce(_ & _)
    def la(tactic: PositionTactic, fml: String*) =
      if (fml.isEmpty) locateAnte(tactic)
      else fml.map(f => locateAnte(tactic, _ == f.asFormula) | debugT("Unable to find formula " + f + " in antecedent")).reduce(_ & _)

    val loopInv = """        dx^2+dy^2 = 1
                    |      & dz^2+dxy^2 = 1
                    |      & v=Vmin
                    |      & ((theta=Theta & dxy=dXY & dz=dZ & (abs(x-xo-r*dy)>r | abs(y-yo+r*dx)>r))
                    |        | (theta=-Theta & dxy=-dXY & dz=dZ & (abs(x-xo+r*dy)>r | abs(y-yo-r*dx)>r)))""".stripMargin.asFormula

    val speedCtrl = ls(composeb) & ls(testb) & ls(implyR) & ls(composeb) & ls(assignb)
    val rollAngleCtrl = ls(composeb) & ls(testb) & ls(implyR) & ls(composeb) & ls(assignb)
    val safeBrake = ls(composeb) & ls(testb) & ls(implyR) & ls(assignb)

    def plant(a: Variable, w: Variable) =
      (la(andL)*) &
        ls(DC("t_2>=0".asFormula)) & onBranch(
        (cutShowLbl, debug("Show t_2>=0")
          & (ls(DI) | debug("DI. t_2>=0 failed"))),
        (cutUseLbl, debug("Use t_2>=0")
          & ls(DC("dx^2+dy^2=1".asFormula)) & onBranch(
          (cutShowLbl, debug("Show dx^2+dy^2=1")
            & (ls(DI) | debug("DI. dx^2+dy^2=1 failed"))),
          (cutUseLbl, debug("Use dx^2+dy^2=1")
            & ls(DC("dz_0^2+dxy_0^2=1".asFormula)) & onBranch(
            (cutShowLbl, debug("Show dz_0^2+dxy_0^2=1")
              & (ls(DI) | debug("DI. dz_0^2+dxy_0^2=1 failed"))),
            (cutUseLbl, debug("Use dz_0^2+dxy_0^2=1")
              & ls(DC(s"v_0=old(v_0)+${a.prettyString}*t_2".asFormula)) & onBranch(
              (cutShowLbl, debug("Show v_0=old(v_0)+a*t_2")
                & ls(Dconstify) & (ls(DI) | debug("DI. v_0=old(v_0)+a*t_2 failed"))),
              (cutUseLbl, debug("Use v_0=old(v_0)+a*t_2")
                & ls(DC(s"theta=old(theta)+${w.prettyString}*t_2".asFormula)) & onBranch(
                (cutShowLbl, debug("Show theta_0=old(theta_0)+w*t_2")
                  & ls(Dconstify) & (ls(DI) | debug("DI. theta_0=old(theta_0)+w*t_2 failed"))),
                (cutUseLbl, debug("Use theta_0=old(theta_0)+w*t_2")
                  & ls(DC("dxy_0=old(dxy_0) & dz_0=old(dz_0)".asFormula)) & onBranch(
                  (cutShowLbl, debug("Show dxy_0=old(dxy_0) & dz_0=old(dz_0)")
                    & (ls(DI) | debug("DI. dxy_0=old(dxy_0) & dz_0=old(dz_0) failed"))),
                  (cutUseLbl, debug("Use dxy_0=old(dxy_0) & dz_0=old(dz_0)")
                    )))))))))))
      )

    def plantCase1_1 =
      (la(andL)*) &
        ls(DC("x-r*dy=old(x)-r*old(dy) & y+r*dx=old(y)+r*old(dx)".asFormula)) & onBranch(
        (cutShowLbl, debug("Show x-r*dy=...")
          & ls(Dconstify) & (ls(DI) | debug("DI. x-r*dy=... failed"))),
        (cutUseLbl, debug("Use x-r*dy=...")
          & ls(DW) & ls(implyR) & (la(andL)*) & QE
          ))

    def plantCase2_2 =
      (la(andL)*) &
        ls(DC("x+r*dy=old(x)+r*old(dy) & y-r*dx=old(y)-r*old(dx)".asFormula)) & onBranch(
        (cutShowLbl, debug("Show x+r*dy=...")
          & ls(Dconstify) & (ls(DI) | debug("DI. x+r*dy=... failed"))),
        (cutUseLbl, debug("Use x+r*dy=...")
          & ls(DW) & ls(implyR) & (la(andL)*) & QE
          ))

    def splitProof = la(orL) && (
      (debug("case1: theta=Theta") & la(orL) && (
        (debug("case1_1: theta=Theta") & plantCase1_1),
        (debug("case1_2: theta=-Theta") & ls(DW) & ls(implyR) & (la(andL)*) & QE)
        )),
      (debug("case2: theta=-Theta") & la(orL) && (
        (debug("case2_1: theta=Theta") & ls(DW) & ls(implyR) & (la(andL)*) & QE),
        (debug("case2_2: theta=-Theta") & plantCase2_2)
        ))
      )

    val maneuver = speedCtrl & rollAngleCtrl & safeBrake & plant(Variable("a", Some(1)), Variable("w", Some(1))) & splitProof

    val tactic = ls(implyR) & (la(andL)*) & ls(I(loopInv)) & onBranch(
      (indInitLbl, debug("Base Case") & QE),
      (indUseCaseLbl, debug("Use Case") & ls(implyR) & (la(andL)*) & QE),
      (indStepLbl, debug("Step") & ls(implyR) & ls(composeb) & maneuver)
    )

    val result = helper.runTactic(tactic, new RootNode(s))
    Console.println("Open goals remaining: " + result.openGoals().length)
    result shouldBe 'closed
  }


  /** Fixed wing model without bound: maximum roll angle case
    *
    * The helicopter will first brake with the maximum power and then follow a loitering circle
    * initial speed: v >= Vmin
    * the roll angle has the maximum value: abs(theta) = Theta
    *
    * Proved in commit 15a1937 of fixedwing branch
    */
  /* "fixedwing_simple_maxroll" */ ignore should "prove fixedwing_simple_maxroll" in {
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/fixedwing/fixedwing_simple_maxroll.key"))

    def ls(tactic: PositionTactic, fml: String*) =
      if (fml.isEmpty) locateSucc(tactic)
      else fml.map(f => locateSucc(tactic, _ == f.asFormula) | debugT("Unable to find formula " + f + " in succedent")).reduce(_ & _)
    def la(tactic: PositionTactic, fml: String*) =
      if (fml.isEmpty) locateAnte(tactic)
      else fml.map(f => locateAnte(tactic, _ == f.asFormula) | debugT("Unable to find formula " + f + " in antecedent")).reduce(_ & _)

    val loopInv = """        dx^2+dy^2 = 1
                    |      & dz^2+dxy^2 = 1
                    |      & v>=Vmin
                    |      & ((theta=Theta & dxy=dXY & dz=dZ) | (theta=-Theta & dxy=-dXY & dz=dZ))
                    |      & ((abs(x-xo)>(v^2-Vmin^2)/(2*B)+2*r | abs(y-yo)>(v^2-Vmin^2)/(2*B)+2*r)
                    |        | (v=Vmin & theta=Theta & dxy=dXY & dz=dZ & (abs(x-xo-r*dy)>r | abs(y-yo+r*dx)>r))
                    |        | (v=Vmin & theta=-Theta & dxy=-dXY & dz=dZ & (abs(x-xo+r*dy)>r | abs(y-yo-r*dx)>r)))""".stripMargin.asFormula

    val speedCtrl = ls(composeb) & ls(testb) & ls(implyR) & ls(assignb)
    val rollAngleCtrl = ls(composeb) & ls(testb) & ls(implyR) & ls(assignb)
    val safeBrake = ls(testb) & ls(implyR) & ls(assignb)


    def plant(a: Variable, w: Variable) =
      (la(andL)*) &
        ls(DC("t_2>=0".asFormula)) & onBranch(
        (cutShowLbl, debug("Show t_2>=0")
          & (ls(DI) | debug("DI. t_2>=0 failed"))),
        (cutUseLbl, debug("Use t_2>=0")
          & ls(DC("dx^2+dy^2=1".asFormula)) & onBranch(
          (cutShowLbl, debug("Show dx^2+dy^2=1")
            & (ls(DI) | debug("DI. dx^2+dy^2=1 failed"))),
          (cutUseLbl, debug("Use dx^2+dy^2=1")
            & ls(DC("dz_0^2+dxy_0^2=1".asFormula)) & onBranch(
            (cutShowLbl, debug("Show dz_0^2+dxy_0^2=1")
              & (ls(DI) | debug("DI. dz_0^2+dxy_0^2=1 failed"))),
            (cutUseLbl, debug("Use dz_0^2+dxy_0^2=1")
              & ls(DC(s"v_0=old(v_0)+${a.prettyString}*t_2".asFormula)) & onBranch(
              (cutShowLbl, debug("Show v_0=old(v_0)+a*t_2")
                & ls(Dconstify) & (ls(DI) | debug("DI. v_0=old(v_0)+a*t_2 failed"))),
              (cutUseLbl, debug("Use v_0=old(v_0)+a*t_2")
                & ls(DC(s"theta_0=old(theta_0)+${w.prettyString}*t_2".asFormula)) & onBranch(
                (cutShowLbl, debug("Show theta_0=old(theta_0)+w*t_2")
                  & ls(Dconstify) & (ls(DI) | debug("DI. theta_0=old(theta_0)+w*t_2 failed"))),
                (cutUseLbl, debug("Use theta_0=old(theta_0)+w*t_2")
                  & ls(DC("dxy_0=old(dxy_0) & dz_0=old(dz_0)".asFormula)) & onBranch(
                  (cutShowLbl, debug("Show dxy_0=old(dxy_0) & dz_0=old(dz_0)")
                    & (ls(DI) | debug("DI. dxy_0=old(dxy_0) & dz_0=old(dz_0) failed"))),
                  (cutUseLbl, debug("Use dxy_0=old(dxy_0) & dz_0=old(dz_0)")
                    )))))))))))
      )

    /* local tactics for proving v=Vmin branch */
    def splitProofEqVmin = la(orL,"(abs(x-xo)>(v_0^2-Vmin^2)/(2*B)+2*r|abs(y-yo)>(v_0^2-Vmin^2)/(2*B)+2*r)|v_0=Vmin&theta_0=Theta&dxy_0=dXY&dz_0=dZ&(abs(x-xo-r*dy)>r|abs(y-yo+r*dx)>r)|v_0=Vmin&theta_0=-Theta&dxy_0=-dXY&dz_0=dZ&(abs(x-xo+r*dy)>r|abs(y-yo-r*dx)>r)") && (
      (debug("eqVminCase1: (abs(x-xo) | abs(y-yo))") & plantEqVminCase1),
      (debug("v=Vmin & abs(theta)=Theta") & la(orL, "v_0=Vmin&theta_0=Theta&dxy_0=dXY&dz_0=dZ&(abs(x-xo-r*dy)>r|abs(y-yo+r*dx)>r)|v_0=Vmin&theta_0=-Theta&dxy_0=-dXY&dz_0=dZ&(abs(x-xo+r*dy)>r|abs(y-yo-r*dx)>r)") && (
        (debug("eqVminCase2: v=Vmin & theta=Theta") & plantEqVminCase2),
        (debug("eqVminCase3: v=Vmin & theta=-Theta") & plantEqVminCase3)
        ))
      )

    def plantEqVminCase1 = la(orL, "theta_0=Theta&dxy_0=dXY&dz_0=dZ|theta_0=-Theta&dxy_0=-dXY&dz_0=dZ") && (
      (debug("case: theta_0=Theta") & plantEqVminCase2),
      (debug("case: theta_0=-Theta") & plantEqVminCase3)
      )

    def plantEqVminCase2 =
      (la(andL)*) &
        ls(DC("x-r*dy=old(x)-r*old(dy) & y+r*dx=old(y)+r*old(dx)".asFormula)) & onBranch(
        (cutShowLbl, debug("Show x-r*dy=...")
          & ls(Dconstify) & (ls(DI) | debug("DI. x-r*dy=... failed"))),
        (cutUseLbl, debug("Use x-r*dy=...")
          & ls(DW) & ls(implyR) & (la(andL)*) & QE
          ))

    def plantEqVminCase3 =
      (la(andL)*) &
        ls(DC("x+r*dy=old(x)+r*old(dy) & y-r*dx=old(y)-r*old(dx)".asFormula)) & onBranch(
        (cutShowLbl, debug("Show x+r*dy=...")
          & ls(Dconstify) & (ls(DI) | debug("DI. x+r*dy=... failed"))),
        (cutUseLbl, debug("Use x+r*dy=...")
          & ls(DW) & ls(implyR) & (la(andL)*) & QE
          ))

    /* local tactics for proving v>Vmin branch */
    def splitProofGtVmin = la(orL,"(abs(x-xo)>(v_0^2-Vmin^2)/(2*B)+2*r|abs(y-yo)>(v_0^2-Vmin^2)/(2*B)+2*r)|v_0=Vmin&theta_0=Theta&dxy_0=dXY&dz_0=dZ&(abs(x-xo-r*dy)>r|abs(y-yo+r*dx)>r)|v_0=Vmin&theta_0=-Theta&dxy_0=-dXY&dz_0=dZ&(abs(x-xo+r*dy)>r|abs(y-yo-r*dx)>r)") && (
      (debug("case1: (abs(x-xo) | abs(y-yo))") & plantGtVminCase1(Variable("a", Some(1)), Variable("w", Some(1)))),
      (debug("v=Vmin & abs(theta)=Theta") & la(orL, "v_0=Vmin&theta_0=Theta&dxy_0=dXY&dz_0=dZ&(abs(x-xo-r*dy)>r|abs(y-yo+r*dx)>r)|v_0=Vmin&theta_0=-Theta&dxy_0=-dXY&dz_0=dZ&(abs(x-xo+r*dy)>r|abs(y-yo-r*dx)>r)") && (
        (debug("case2: v=Vmin & theta=Theta") & ls(DW) & ls(implyR) & (la(andL)*) & QE),
        (debug("case3: v=Vmin & theta=-Theta") & ls(DW) & ls(implyR) & (la(andL)*) & QE)
        ))
      )

    def plantGtVminCase1(a: Variable, w: Variable) =
      ls(DC(s"x-old(x)<=t_2*(v_0-${a.prettyString}/2*t_2) & x-old(x)>=-t_2*(v_0-${a.prettyString}/2*t_2) & y-old(y)<=t_2*(v_0-${a.prettyString}/2*t_2) & y-old(y)>=-t_2*(v_0-${a.prettyString}/2*t_2)".asFormula)) & onBranch(
        (cutShowLbl, debug("Show x-old(x)...")
          & ls(Dconstify) & (ls(DI) | debug("DI. x-old(x)... failed"))),
        (cutUseLbl, debug("Use x-old(x)...")
          & ls(DW) & ls(implyR) & (la(andL)*) & QE
          ))


    /* tactics of the maneuver case */
    val maneuver = (ls(composeb)*) & ls(choiceb) & ls(andR) && (
      (debug("v=Vmin") & speedCtrl & rollAngleCtrl & safeBrake & la(hide, "(abs(x-xo)>(v_0^2-Vmin^2)/(2*B)+2*r|abs(y-yo)>(v_0^2-Vmin^2)/(2*B)+2*r)|v_0=Vmin&theta_0=Theta&dxy_0=dXY&dz_0=dZ&(abs(x-xo-r*dy)>r|abs(y-yo+r*dx)>r)|v_0=Vmin&theta_0=-Theta&dxy_0=-dXY&dz_0=dZ&(abs(x-xo+r*dy)>r|abs(y-yo-r*dx)>r)") & plant(Variable("a", Some(1)), Variable("w", Some(1))) & splitProofEqVmin),
      (debug("v>Vmin") & speedCtrl & rollAngleCtrl & safeBrake & la(hide, "(abs(x-xo)>(v_0^2-Vmin^2)/(2*B)+2*r|abs(y-yo)>(v_0^2-Vmin^2)/(2*B)+2*r)|v_0=Vmin&theta_0=Theta&dxy_0=dXY&dz_0=dZ&(abs(x-xo-r*dy)>r|abs(y-yo+r*dx)>r)|v_0=Vmin&theta_0=-Theta&dxy_0=-dXY&dz_0=dZ&(abs(x-xo+r*dy)>r|abs(y-yo-r*dx)>r)") & plant(Variable("a", Some(1)), Variable("w", Some(1))) & splitProofGtVmin)
      )


    val tactic = ls(implyR) & (la(andL)*) & ls(I(loopInv)) & onBranch(
      (indInitLbl, debug("Base Case") & QE),
      (indUseCaseLbl, debug("Use Case") & ls(implyR) & (la(andL)*) & QE),
      (indStepLbl, debug("Step") & ls(implyR) & ls(composeb) & maneuver)
    )

    val result = helper.runTactic(tactic, new RootNode(s))
    Console.println("Open goals remaining: " + result.openGoals().length)
    result shouldBe 'closed
  }

  /** Fixed wing model without bound
    *
    * The helicopter will first brake with the maximum power and then follow a loitering circle
    * initial speed: v >= Vmin, abs(theta)<=Theta
    *
    * Proved in commit 15a1937 of fixedwing branch
    */
  /* "fixedwing_simple_nobound" */ ignore should "prove fixedwing_simple_nobound" in {
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/fixedwing/fixedwing_simple_nobound.key"))

    def ls(tactic: PositionTactic, fml: String*) =
      if (fml.isEmpty) locateSucc(tactic)
      else fml.map(f => locateSucc(tactic, _ == f.asFormula) | debugT("Unable to find formula " + f + " in succedent")).reduce(_ & _)
    def la(tactic: PositionTactic, fml: String*) =
      if (fml.isEmpty) locateAnte(tactic)
      else fml.map(f => locateAnte(tactic, _ == f.asFormula) | debugT("Unable to find formula " + f + " in antecedent")).reduce(_ & _)


    val loopInv = """       dx^2+dy^2 = 1
                    |      & dz^2+dxy^2 = 1
                    |      & v>=Vmin
                    |      & theta <= Theta
                    |      & theta >= -Theta
                    |      & (((abs(x-xo)>(v^2-Vmin^2)/(2*B)+2*r & abs(x-xo)>(v^2-Vmin^2)/(2*B)+Vmin*((Theta-abs(theta))/W-(v-Vmin)/B)+2*r) | (abs(y-yo)>(v^2-Vmin^2)/(2*B)+2*r & abs(y-yo)>(v^2-Vmin^2)/(2*B)+Vmin*((Theta-abs(theta))/W-(v-Vmin)/B)+2*r))
                    |          | (v=Vmin & theta>=0 & theta<Theta & (abs(x-xo)>Vmin*(Theta-theta)/W+2*r | abs(y-yo)>Vmin*(Theta-theta)/W+2*r))
                    |          | (v=Vmin & theta<0 & theta>-Theta & (abs(x-xo)>Vmin*(Theta+theta)/W+2*r | abs(y-yo)>Vmin*(Theta+theta)/W+2*r))
                    |          | (v=Vmin & theta=Theta & dxy=dXY & dz=dZ & (abs(x-xo-r*dy)>r | abs(y-yo+r*dx)>r))
                    |          | (v=Vmin & theta=-Theta & dxy=-dXY & dz=dZ & (abs(x-xo+r*dy)>r | abs(y-yo-r*dx)>r)))""".stripMargin.asFormula

    def speedCtrl = ls(composeb) & ls(testb) & ls(implyR) & ls(assignb)
    def rollAngleCtrl = ls(composeb) & ls(testb) & ls(implyR) & ls(assignb)
    def safeBrake = ls(testb) & ls(implyR) & ls(assignb)

    def plantBrake(a: Variable, w: Variable) =
      (la(andL)*) &
        ls(DC("t_2>=0".asFormula)) & onBranch(
        (cutShowLbl, debug("Show t_2>=0")
          & (ls(DI) | debug("DI. t_2>=0 failed"))),
        (cutUseLbl, debug("Use t_2>=0")
          & ls(DC("dx^2+dy^2=1".asFormula)) & onBranch(
          (cutShowLbl, debug("Show dx^2+dy^2=1")
            & (ls(DI) | debug("DI. dx^2+dy^2=1 failed"))),
          (cutUseLbl, debug("Use dx^2+dy^2=1")
            & ls(DC("dz_0^2+dxy_0^2=1".asFormula)) & onBranch(
            (cutShowLbl, debug("Show dz_0^2+dxy_0^2=1")
              & (ls(DI) | debug("DI. dz_0^2+dxy_0^2=1 failed"))),
            (cutUseLbl, debug("Use dz_0^2+dxy_0^2=1")
              & ls(DC(s"v_0=old(v_0)+${a.prettyString}*t_2".asFormula)) & onBranch(
              (cutShowLbl, debug("Show v_0=old(v_0)+a*t_2")
                & ls(Dconstify) & (ls(DI) | debug("DI. v_0=old(v_0)+a*t_2 failed"))),
              (cutUseLbl, debug("Use v_0=old(v_0)+a*t_2")
                & ls(DC(s"theta_0=old(theta_0)+${w.prettyString}*t_2".asFormula)) & onBranch(
                (cutShowLbl, debug("Show theta_0=old(theta_0)+w*t_2")
                  & ls(Dconstify) & (ls(DI) | debug("DI. theta_0=old(theta_0)+w*t_2 failed"))),
                (cutUseLbl, debug("Use theta_0=old(theta_0)+w*t_2")
                  )))))))))
      )

    def plantNewCurve(a: Variable, w: Variable) =
      (la(andL)*) &
        ls(DC("t_2>=0".asFormula)) & onBranch(
        (cutShowLbl, debug("Show t_2>=0")
          & (ls(DI) | debug("DI. t_2>=0 failed"))),
        (cutUseLbl, debug("Use t_2>=0")
          & ls(DC("dx^2+dy^2=1".asFormula)) & onBranch(
          (cutShowLbl, debug("Show dx^2+dy^2=1")
            & (ls(DI) | debug("DI. dx^2+dy^2=1 failed"))),
          (cutUseLbl, debug("Use dx^2+dy^2=1")
            & ls(DC("dz_0^2+dxy_0^2=1".asFormula)) & onBranch(
            (cutShowLbl, debug("Show dz_0^2+dxy_0^2=1")
              & (ls(DI) | debug("DI. dz_0^2+dxy_0^2=1 failed"))),
            (cutUseLbl, debug("Use dz_0^2+dxy_0^2=1")
              & ls(DC(s"v_1=old(v_1)+${a.prettyString}*t_2".asFormula)) & onBranch(
              (cutShowLbl, debug("Show v_1=old(v_1)+a*t_2")
                &ls(Dconstify) & (ls(DI) | debug("DI. v_1=old(v_1)+a*t_2 failed"))),
              (cutUseLbl, debug("Use v_1=old(v_1)+a*t_2")
                & ls(DC(s"theta_1=old(theta_1)+${w.prettyString}*t_2".asFormula)) & onBranch(
                (cutShowLbl, debug("Show theta_1=old(theta_1)+w*t_2")
                  & ls(Dconstify) & (ls(DI) | debug("DI. theta_1=old(theta_1)+w*t_2 failed"))),
                (cutUseLbl, debug("Use theta_1=old(theta_1)+w*t_2")
                  )))))))))
      )

    /* local tactics for proving Goal1: v=Vmin & theta=Theta */
    def plantLoiteringPosTheta(a: Variable, w: Variable) =
      ls(DC("dxy_0=old(dxy_0) & dz_0=old(dz_0)".asFormula)) & onBranch(
        (cutShowLbl, debug("Show dxy_0=old(dxy_0) & dz_0=old(dz_0)")
          & (ls(DI) | debug("DI. xy_0=old(dxy_0) & dz_0=old(dz_0) failed"))),
        (cutUseLbl, debug("Use dxy_0=old(dxy_0) & dz_0=old(dz_0)")
          & splitProofLoiteringPosTheta
          ))

    def splitProofLoiteringPosTheta = la(orL, "(abs(x-xo)>(v_0^2-Vmin^2)/(2*B)+2*r&abs(x-xo)>(v_0^2-Vmin^2)/(2*B)+Vmin*((Theta-abs(theta_0))/W-(v_0-Vmin)/B)+2*r|abs(y-yo)>(v_0^2-Vmin^2)/(2*B)+2*r&abs(y-yo)>(v_0^2-Vmin^2)/(2*B)+Vmin*((Theta-abs(theta_0))/W-(v_0-Vmin)/B)+2*r)|v_0=Vmin&theta_0>=0&theta_0 < Theta&(abs(x-xo)>Vmin*(Theta-theta_0)/W+2*r|abs(y-yo)>Vmin*(Theta-theta_0)/W+2*r)|v_0=Vmin&theta_0 < 0&theta_0>-Theta&(abs(x-xo)>Vmin*(Theta+theta_0)/W+2*r|abs(y-yo)>Vmin*(Theta+theta_0)/W+2*r)|v_0=Vmin&theta_0=Theta&dxy_0=dXY&dz_0=dZ&(abs(x-xo-r*dy)>r|abs(y-yo+r*dx)>r)|v_0=Vmin&theta_0=-Theta&dxy_0=-dXY&dz_0=dZ&(abs(x-xo+r*dy)>r|abs(y-yo-r*dx)>r)") && (
      (debug("abs(x-xo)...") & plantLoiteringCasePosTheta),
      (debug("more...") & la(orL, "v_0=Vmin&theta_0>=0&theta_0 < Theta&(abs(x-xo)>Vmin*(Theta-theta_0)/W+2*r|abs(y-yo)>Vmin*(Theta-theta_0)/W+2*r)|v_0=Vmin&theta_0 < 0&theta_0>-Theta&(abs(x-xo)>Vmin*(Theta+theta_0)/W+2*r|abs(y-yo)>Vmin*(Theta+theta_0)/W+2*r)|v_0=Vmin&theta_0=Theta&dxy_0=dXY&dz_0=dZ&(abs(x-xo-r*dy)>r|abs(y-yo+r*dx)>r)|v_0=Vmin&theta_0=-Theta&dxy_0=-dXY&dz_0=dZ&(abs(x-xo+r*dy)>r|abs(y-yo-r*dx)>r)") && (
        (debug("v=Vmin & 0<=theta<Theta") & ls(DW) & ls(implyR) & (la(andL)*) & QE),
        (la(orL, "v_0=Vmin&theta_0 < 0&theta_0>-Theta&(abs(x-xo)>Vmin*(Theta+theta_0)/W+2*r|abs(y-yo)>Vmin*(Theta+theta_0)/W+2*r)|v_0=Vmin&theta_0=Theta&dxy_0=dXY&dz_0=dZ&(abs(x-xo-r*dy)>r|abs(y-yo+r*dx)>r)|v_0=Vmin&theta_0=-Theta&dxy_0=-dXY&dz_0=dZ&(abs(x-xo+r*dy)>r|abs(y-yo-r*dx)>r)") && (
          (debug("v=Vmin & -Theta<theta<0") & ls(DW) & ls(implyR) & (la(andL)*) & QE),
          (la(orL, "v_0=Vmin&theta_0=Theta&dxy_0=dXY&dz_0=dZ&(abs(x-xo-r*dy)>r|abs(y-yo+r*dx)>r)|v_0=Vmin&theta_0=-Theta&dxy_0=-dXY&dz_0=dZ&(abs(x-xo+r*dy)>r|abs(y-yo-r*dx)>r)") && (
            (debug("v=Vmin & theta_0=Theta") & plantLoiteringCasePosTheta),
            (debug("v=Vmin & theta_0=-Theta") & ls(DW) & ls(implyR) & (la(andL)*) & QE)
            ))
          ))
        ))
      )

    def plantLoiteringCasePosTheta =
      (la(andL)*) &
        ls(DC("x-r*dy=old(x)-r*old(dy) & y+r*dx=old(y)+r*old(dx)".asFormula)) & onBranch(
        (cutShowLbl, debug("Show x-r*dy=...")
          & ls(Dconstify) & (ls(DI) | debug("DI. x-r*dy=... failed"))),
        (cutUseLbl, debug("Use x-r*dy=...")
          & ls(DW) & ls(implyR) & (la(andL)*) & QE
          ))

    /* local tactics for proving Goal2: v=Vmin & theta=-Theta */
    def plantLoiteringNegTheta(a: Variable, w: Variable) =
      ls(DC("dxy_0=old(dxy_0) & dz_0=old(dz_0)".asFormula)) & onBranch(
        (cutShowLbl, debug("Show dxy_0=old(dxy_0) & dz_0=old(dz_0)")
          & (ls(DI) | debug("DI. xy_0=old(dxy_0) & dz_0=old(dz_0) failed"))),
        (cutUseLbl, debug("Use dxy_0=old(dxy_0) & dz_0=old(dz_0)")
          & splitProofLoiteringNegTheta
          ))

    def splitProofLoiteringNegTheta = la(orL, "(abs(x-xo)>(v_0^2-Vmin^2)/(2*B)+2*r&abs(x-xo)>(v_0^2-Vmin^2)/(2*B)+Vmin*((Theta-abs(theta_0))/W-(v_0-Vmin)/B)+2*r|abs(y-yo)>(v_0^2-Vmin^2)/(2*B)+2*r&abs(y-yo)>(v_0^2-Vmin^2)/(2*B)+Vmin*((Theta-abs(theta_0))/W-(v_0-Vmin)/B)+2*r)|v_0=Vmin&theta_0>=0&theta_0 < Theta&(abs(x-xo)>Vmin*(Theta-theta_0)/W+2*r|abs(y-yo)>Vmin*(Theta-theta_0)/W+2*r)|v_0=Vmin&theta_0 < 0&theta_0>-Theta&(abs(x-xo)>Vmin*(Theta+theta_0)/W+2*r|abs(y-yo)>Vmin*(Theta+theta_0)/W+2*r)|v_0=Vmin&theta_0=Theta&dxy_0=dXY&dz_0=dZ&(abs(x-xo-r*dy)>r|abs(y-yo+r*dx)>r)|v_0=Vmin&theta_0=-Theta&dxy_0=-dXY&dz_0=dZ&(abs(x-xo+r*dy)>r|abs(y-yo-r*dx)>r)") && (
      (debug("abs(x-xo)...") & plantLoiteringCaseNegTheta),
      (debug("more...") & la(orL, "v_0=Vmin&theta_0>=0&theta_0 < Theta&(abs(x-xo)>Vmin*(Theta-theta_0)/W+2*r|abs(y-yo)>Vmin*(Theta-theta_0)/W+2*r)|v_0=Vmin&theta_0 < 0&theta_0>-Theta&(abs(x-xo)>Vmin*(Theta+theta_0)/W+2*r|abs(y-yo)>Vmin*(Theta+theta_0)/W+2*r)|v_0=Vmin&theta_0=Theta&dxy_0=dXY&dz_0=dZ&(abs(x-xo-r*dy)>r|abs(y-yo+r*dx)>r)|v_0=Vmin&theta_0=-Theta&dxy_0=-dXY&dz_0=dZ&(abs(x-xo+r*dy)>r|abs(y-yo-r*dx)>r)") && (
        (debug("v=Vmin & 0<=theta<Theta") & ls(DW) & ls(implyR) & (la(andL)*) & QE),
        (la(orL, "v_0=Vmin&theta_0 < 0&theta_0>-Theta&(abs(x-xo)>Vmin*(Theta+theta_0)/W+2*r|abs(y-yo)>Vmin*(Theta+theta_0)/W+2*r)|v_0=Vmin&theta_0=Theta&dxy_0=dXY&dz_0=dZ&(abs(x-xo-r*dy)>r|abs(y-yo+r*dx)>r)|v_0=Vmin&theta_0=-Theta&dxy_0=-dXY&dz_0=dZ&(abs(x-xo+r*dy)>r|abs(y-yo-r*dx)>r)") && (
          (debug("v=Vmin & -Theta<theta<0") & ls(DW) & ls(implyR) & (la(andL)*) & QE),
          (la(orL, "v_0=Vmin&theta_0=Theta&dxy_0=dXY&dz_0=dZ&(abs(x-xo-r*dy)>r|abs(y-yo+r*dx)>r)|v_0=Vmin&theta_0=-Theta&dxy_0=-dXY&dz_0=dZ&(abs(x-xo+r*dy)>r|abs(y-yo-r*dx)>r)") && (
            (debug("v=Vmin & theta_0=Theta") & ls(DW) & ls(implyR) & (la(andL)*) & QE),
            (debug("v=Vmin & theta_0=-Theta") & plantLoiteringCaseNegTheta)
            ))
          ))
        ))
      )

    def plantLoiteringCaseNegTheta =
      (la(andL)*) &
        ls(DC("x+r*dy=old(x)+r*old(dy) & y-r*dx=old(y)-r*old(dx)".asFormula)) & onBranch(
        (cutShowLbl, debug("Show x+r*dy=...")
          & ls(Dconstify) & (ls(DI) | debug("DI. x+r*dy=... failed"))),
        (cutUseLbl, debug("Use x+r*dy=...")
          & ls(DW) & ls(implyR) & (la(andL)*) & QE
          ))

    /* local tactics for proving Goal3: v=Vmin & 0<=theta<Theta */
    def plantBTCPosRoll(a: Variable, w: Variable) = la(orL, "(abs(x-xo)>(v_0^2-Vmin^2)/(2*B)+2*r&abs(x-xo)>(v_0^2-Vmin^2)/(2*B)+Vmin*((Theta-abs(theta_0))/W-(v_0-Vmin)/B)+2*r|abs(y-yo)>(v_0^2-Vmin^2)/(2*B)+2*r&abs(y-yo)>(v_0^2-Vmin^2)/(2*B)+Vmin*((Theta-abs(theta_0))/W-(v_0-Vmin)/B)+2*r)|v_0=Vmin&theta_0>=0&theta_0 < Theta&(abs(x-xo)>Vmin*(Theta-theta_0)/W+2*r|abs(y-yo)>Vmin*(Theta-theta_0)/W+2*r)|v_0=Vmin&theta_0 < 0&theta_0>-Theta&(abs(x-xo)>Vmin*(Theta+theta_0)/W+2*r|abs(y-yo)>Vmin*(Theta+theta_0)/W+2*r)|v_0=Vmin&theta_0=Theta&dxy_0=dXY&dz_0=dZ&(abs(x-xo-r*dy)>r|abs(y-yo+r*dx)>r)|v_0=Vmin&theta_0=-Theta&dxy_0=-dXY&dz_0=dZ&(abs(x-xo+r*dy)>r|abs(y-yo-r*dx)>r)") && (
      (debug("abs(x-xo)...") & plantBTCPosRollEqVmin(a,w) ),
      (la(orL, "v_0=Vmin&theta_0>=0&theta_0 < Theta&(abs(x-xo)>Vmin*(Theta-theta_0)/W+2*r|abs(y-yo)>Vmin*(Theta-theta_0)/W+2*r)|v_0=Vmin&theta_0 < 0&theta_0>-Theta&(abs(x-xo)>Vmin*(Theta+theta_0)/W+2*r|abs(y-yo)>Vmin*(Theta+theta_0)/W+2*r)|v_0=Vmin&theta_0=Theta&dxy_0=dXY&dz_0=dZ&(abs(x-xo-r*dy)>r|abs(y-yo+r*dx)>r)|v_0=Vmin&theta_0=-Theta&dxy_0=-dXY&dz_0=dZ&(abs(x-xo+r*dy)>r|abs(y-yo-r*dx)>r)") && (
        (debug("v=Vmin & 0<=theta<Theta") & plantBTCPosRollEqVmin(a,w) ),
        (la(orL, "v_0=Vmin&theta_0 < 0&theta_0>-Theta&(abs(x-xo)>Vmin*(Theta+theta_0)/W+2*r|abs(y-yo)>Vmin*(Theta+theta_0)/W+2*r)|v_0=Vmin&theta_0=Theta&dxy_0=dXY&dz_0=dZ&(abs(x-xo-r*dy)>r|abs(y-yo+r*dx)>r)|v_0=Vmin&theta_0=-Theta&dxy_0=-dXY&dz_0=dZ&(abs(x-xo+r*dy)>r|abs(y-yo-r*dx)>r)") && (
          (debug("v=Vmin & -Theta<theta<0") & ls(DW) & ls(implyR) & (la(andL)*) & QE ),
          (la(orL, "v_0=Vmin&theta_0=Theta&dxy_0=dXY&dz_0=dZ&(abs(x-xo-r*dy)>r|abs(y-yo+r*dx)>r)|v_0=Vmin&theta_0=-Theta&dxy_0=-dXY&dz_0=dZ&(abs(x-xo+r*dy)>r|abs(y-yo-r*dx)>r)") && (
            (debug("v=Vmin & theta_0=Theta") & ls(DW) & ls(implyR) & (la(andL)*) & QE ),
            (debug("v=Vmin & theta_0=-Theta") & ls(DW) & ls(implyR) & (la(andL)*) & QE )
            ))
          ))
        ) )
      )

    def plantBTCPosRollEqVmin(a: Variable, w: Variable) =
      ls(DC("x-old(x)<=t_2*v_0 & x-old(x)>=-t_2*v_0 & y-old(y)<=t_2*v_0 & y-old(y)>=-t_2*v_0".asFormula)) & onBranch(
        (cutShowLbl, debug("Show x-old(x)...")
          & (ls(DI) | debug("DI. x-old(x)... failed"))),
        (cutUseLbl, debug("Use x-old(x)...")
          & ls(DW) & ls(implyR) & (la(andL)*) & debug("before QE") & QE
          ))

    /* local tactics for proving Goal4: v=Vmin & -Theta<theta<0 */
    def plantBTCNegRoll(a: Variable, w: Variable) = la(orL, "(abs(x-xo)>(v_0^2-Vmin^2)/(2*B)+2*r&abs(x-xo)>(v_0^2-Vmin^2)/(2*B)+Vmin*((Theta-abs(theta_0))/W-(v_0-Vmin)/B)+2*r|abs(y-yo)>(v_0^2-Vmin^2)/(2*B)+2*r&abs(y-yo)>(v_0^2-Vmin^2)/(2*B)+Vmin*((Theta-abs(theta_0))/W-(v_0-Vmin)/B)+2*r)|v_0=Vmin&theta_0>=0&theta_0 < Theta&(abs(x-xo)>Vmin*(Theta-theta_0)/W+2*r|abs(y-yo)>Vmin*(Theta-theta_0)/W+2*r)|v_0=Vmin&theta_0 < 0&theta_0>-Theta&(abs(x-xo)>Vmin*(Theta+theta_0)/W+2*r|abs(y-yo)>Vmin*(Theta+theta_0)/W+2*r)|v_0=Vmin&theta_0=Theta&dxy_0=dXY&dz_0=dZ&(abs(x-xo-r*dy)>r|abs(y-yo+r*dx)>r)|v_0=Vmin&theta_0=-Theta&dxy_0=-dXY&dz_0=dZ&(abs(x-xo+r*dy)>r|abs(y-yo-r*dx)>r)") && (
      (debug("abs(x-xo)...") & plantBTCNegRollEqVmin(a,w)),
      (la(orL, "v_0=Vmin&theta_0>=0&theta_0 < Theta&(abs(x-xo)>Vmin*(Theta-theta_0)/W+2*r|abs(y-yo)>Vmin*(Theta-theta_0)/W+2*r)|v_0=Vmin&theta_0 < 0&theta_0>-Theta&(abs(x-xo)>Vmin*(Theta+theta_0)/W+2*r|abs(y-yo)>Vmin*(Theta+theta_0)/W+2*r)|v_0=Vmin&theta_0=Theta&dxy_0=dXY&dz_0=dZ&(abs(x-xo-r*dy)>r|abs(y-yo+r*dx)>r)|v_0=Vmin&theta_0=-Theta&dxy_0=-dXY&dz_0=dZ&(abs(x-xo+r*dy)>r|abs(y-yo-r*dx)>r)") && (
        (debug("v=Vmin & 0<=theta<Theta")  & ls(DW) & ls(implyR) & (la(andL)*) & QE ),
        (la(orL, "v_0=Vmin&theta_0 < 0&theta_0>-Theta&(abs(x-xo)>Vmin*(Theta+theta_0)/W+2*r|abs(y-yo)>Vmin*(Theta+theta_0)/W+2*r)|v_0=Vmin&theta_0=Theta&dxy_0=dXY&dz_0=dZ&(abs(x-xo-r*dy)>r|abs(y-yo+r*dx)>r)|v_0=Vmin&theta_0=-Theta&dxy_0=-dXY&dz_0=dZ&(abs(x-xo+r*dy)>r|abs(y-yo-r*dx)>r)") && (
          (debug("v=Vmin & -Theta<theta<0") & plantBTCNegRollEqVmin(a,w) ),
          (la(orL, "v_0=Vmin&theta_0=Theta&dxy_0=dXY&dz_0=dZ&(abs(x-xo-r*dy)>r|abs(y-yo+r*dx)>r)|v_0=Vmin&theta_0=-Theta&dxy_0=-dXY&dz_0=dZ&(abs(x-xo+r*dy)>r|abs(y-yo-r*dx)>r)") && (
            (debug("v=Vmin & theta_0=Theta") & ls(DW) & ls(implyR) & (la(andL)*) & QE ),
            (debug("v=Vmin & theta_0=-Theta") & ls(DW) & ls(implyR) & (la(andL)*) & QE )
            ))
          ))
        ) )
      )

    def plantBTCNegRollEqVmin(a: Variable, w: Variable) =
      ls(DC("x-old(x)<=t_2*v_0 & x-old(x)>=-t_2*v_0 & y-old(y)<=t_2*v_0 & y-old(y)>=-t_2*v_0".asFormula)) & onBranch(
        (cutShowLbl, debug("Show x-old(x)...")
          & (ls(DI) | debug("DI. x-old(x)... failed"))),
        (cutUseLbl, debug("Use x-old(x)...")
          & ls(DW) & ls(implyR) & (la(andL)*) & debug("before QE") & QE
          ))

    /* local tactics for proving Goal5: v>Vmin & theta=Theta and Goal6: v>Vmin & theta=-Theta */
    def plantBTCMaxRoll(a: Variable, w: Variable) =
      ls(DC("dxy_0=old(dxy_0) & dz_0=old(dz_0)".asFormula)) & onBranch(
        (cutShowLbl, debug("Show dxy_0=old(dxy_0) & dz_0=old(dz_0)")
          & (ls(DI) | debug("DI. xy_0=old(dxy_0) & dz_0=old(dz_0) failed"))),
        (cutUseLbl, debug("Use dxy_0=old(dxy_0) & dz_0=old(dz_0)")
          & splitProofBTCMaxRoll(a,w)
          ))

    def splitProofBTCMaxRoll(a: Variable, w: Variable) = la(orL, "(abs(x-xo)>(v_0^2-Vmin^2)/(2*B)+2*r&abs(x-xo)>(v_0^2-Vmin^2)/(2*B)+Vmin*((Theta-abs(theta_0))/W-(v_0-Vmin)/B)+2*r|abs(y-yo)>(v_0^2-Vmin^2)/(2*B)+2*r&abs(y-yo)>(v_0^2-Vmin^2)/(2*B)+Vmin*((Theta-abs(theta_0))/W-(v_0-Vmin)/B)+2*r)|v_0=Vmin&theta_0>=0&theta_0 < Theta&(abs(x-xo)>Vmin*(Theta-theta_0)/W+2*r|abs(y-yo)>Vmin*(Theta-theta_0)/W+2*r)|v_0=Vmin&theta_0 < 0&theta_0>-Theta&(abs(x-xo)>Vmin*(Theta+theta_0)/W+2*r|abs(y-yo)>Vmin*(Theta+theta_0)/W+2*r)|v_0=Vmin&theta_0=Theta&dxy_0=dXY&dz_0=dZ&(abs(x-xo-r*dy)>r|abs(y-yo+r*dx)>r)|v_0=Vmin&theta_0=-Theta&dxy_0=-dXY&dz_0=dZ&(abs(x-xo+r*dy)>r|abs(y-yo-r*dx)>r)") && (
      (debug("abs(x-xo)...") & plantBTCGtVmin(a,w)),
      (la(orL, "v_0=Vmin&theta_0>=0&theta_0 < Theta&(abs(x-xo)>Vmin*(Theta-theta_0)/W+2*r|abs(y-yo)>Vmin*(Theta-theta_0)/W+2*r)|v_0=Vmin&theta_0 < 0&theta_0>-Theta&(abs(x-xo)>Vmin*(Theta+theta_0)/W+2*r|abs(y-yo)>Vmin*(Theta+theta_0)/W+2*r)|v_0=Vmin&theta_0=Theta&dxy_0=dXY&dz_0=dZ&(abs(x-xo-r*dy)>r|abs(y-yo+r*dx)>r)|v_0=Vmin&theta_0=-Theta&dxy_0=-dXY&dz_0=dZ&(abs(x-xo+r*dy)>r|abs(y-yo-r*dx)>r)") && (
        (debug("v=Vmin & 0<=theta<Theta") & ls(DW) & ls(implyR) & (la(andL)*) & QE),
        (la(orL, "v_0=Vmin&theta_0 < 0&theta_0>-Theta&(abs(x-xo)>Vmin*(Theta+theta_0)/W+2*r|abs(y-yo)>Vmin*(Theta+theta_0)/W+2*r)|v_0=Vmin&theta_0=Theta&dxy_0=dXY&dz_0=dZ&(abs(x-xo-r*dy)>r|abs(y-yo+r*dx)>r)|v_0=Vmin&theta_0=-Theta&dxy_0=-dXY&dz_0=dZ&(abs(x-xo+r*dy)>r|abs(y-yo-r*dx)>r)") && (
          (debug("v=Vmin & -Theta<theta<0") & ls(DW) & ls(implyR) & (la(andL)*) & QE),
          (la(orL, "v_0=Vmin&theta_0=Theta&dxy_0=dXY&dz_0=dZ&(abs(x-xo-r*dy)>r|abs(y-yo+r*dx)>r)|v_0=Vmin&theta_0=-Theta&dxy_0=-dXY&dz_0=dZ&(abs(x-xo+r*dy)>r|abs(y-yo-r*dx)>r)") && (
            (debug("v=Vmin & theta_0=Theta") & ls(DW) & ls(implyR) & (la(andL)*) & QE),
            (debug("v=Vmin & theta_0=-Theta") & ls(DW) & ls(implyR) & (la(andL)*) & QE)
            ))
          ))
        ) )
      )

    def plantBTCGtVmin(a: Variable, w: Variable) =
      ls(DC(s"x-old(x)<=t_2*(v_0-${a.prettyString}/2*t_2) & x-old(x)>=-t_2*(v_0-${a.prettyString}/2*t_2) & y-old(y)<=t_2*(v_0-${a.prettyString}/2*t_2) & y-old(y)>=-t_2*(v_0-${a.prettyString}/2*t_2)".asFormula)) & onBranch(
        (cutShowLbl, debug("Show x-old(x)...")
          & ls(Dconstify) & (ls(DI) | debug("DI. x-old(x)... failed"))),
        (cutUseLbl, debug("Use x-old(x)...")
          & ls(DW) & ls(implyR) & (la(andL)*) & QE
          ))

    /* local tactics for proving Goal7: v>Vmin & 0<=theta<Theta and Goal8: v>Vmin & -Theta<theta<0 */
    def plantBTCNonmaxRoll(a: Variable, w: Variable) = la(orL, "(abs(x-xo)>(v_0^2-Vmin^2)/(2*B)+2*r&abs(x-xo)>(v_0^2-Vmin^2)/(2*B)+Vmin*((Theta-abs(theta_0))/W-(v_0-Vmin)/B)+2*r|abs(y-yo)>(v_0^2-Vmin^2)/(2*B)+2*r&abs(y-yo)>(v_0^2-Vmin^2)/(2*B)+Vmin*((Theta-abs(theta_0))/W-(v_0-Vmin)/B)+2*r)|v_0=Vmin&theta_0>=0&theta_0 < Theta&(abs(x-xo)>Vmin*(Theta-theta_0)/W+2*r|abs(y-yo)>Vmin*(Theta-theta_0)/W+2*r)|v_0=Vmin&theta_0 < 0&theta_0>-Theta&(abs(x-xo)>Vmin*(Theta+theta_0)/W+2*r|abs(y-yo)>Vmin*(Theta+theta_0)/W+2*r)|v_0=Vmin&theta_0=Theta&dxy_0=dXY&dz_0=dZ&(abs(x-xo-r*dy)>r|abs(y-yo+r*dx)>r)|v_0=Vmin&theta_0=-Theta&dxy_0=-dXY&dz_0=dZ&(abs(x-xo+r*dy)>r|abs(y-yo-r*dx)>r)") && (
      (debug("abs(x-xo)...") & plantBTCGtVmin(a,w)),
      (la(orL, "v_0=Vmin&theta_0>=0&theta_0 < Theta&(abs(x-xo)>Vmin*(Theta-theta_0)/W+2*r|abs(y-yo)>Vmin*(Theta-theta_0)/W+2*r)|v_0=Vmin&theta_0 < 0&theta_0>-Theta&(abs(x-xo)>Vmin*(Theta+theta_0)/W+2*r|abs(y-yo)>Vmin*(Theta+theta_0)/W+2*r)|v_0=Vmin&theta_0=Theta&dxy_0=dXY&dz_0=dZ&(abs(x-xo-r*dy)>r|abs(y-yo+r*dx)>r)|v_0=Vmin&theta_0=-Theta&dxy_0=-dXY&dz_0=dZ&(abs(x-xo+r*dy)>r|abs(y-yo-r*dx)>r)") && (
        (debug("v=Vmin & 0<=theta<Theta") & ls(DW) & ls(implyR) & (la(andL)*) & QE),
        (la(orL, "v_0=Vmin&theta_0 < 0&theta_0>-Theta&(abs(x-xo)>Vmin*(Theta+theta_0)/W+2*r|abs(y-yo)>Vmin*(Theta+theta_0)/W+2*r)|v_0=Vmin&theta_0=Theta&dxy_0=dXY&dz_0=dZ&(abs(x-xo-r*dy)>r|abs(y-yo+r*dx)>r)|v_0=Vmin&theta_0=-Theta&dxy_0=-dXY&dz_0=dZ&(abs(x-xo+r*dy)>r|abs(y-yo-r*dx)>r)") && (
          (debug("v=Vmin & -Theta<theta<0") & ls(DW) & ls(implyR) & (la(andL)*) & QE),
          (la(orL, "v_0=Vmin&theta_0=Theta&dxy_0=dXY&dz_0=dZ&(abs(x-xo-r*dy)>r|abs(y-yo+r*dx)>r)|v_0=Vmin&theta_0=-Theta&dxy_0=-dXY&dz_0=dZ&(abs(x-xo+r*dy)>r|abs(y-yo-r*dx)>r)") && (
            (debug("v=Vmin & theta_0=Theta") & ls(DW) & ls(implyR) & (la(andL)*) & QE),
            (debug("v=Vmin & theta_0=-Theta") & ls(DW) & ls(implyR) & (la(andL)*) & QE)
            ))
          ))
        ) )
      )

    /* tactics of the maneuver case */
    val maneuver = (ls(composeb)*) & ls(choiceb) & ls(andR) && (
      (debug("v=Vmin") & speedCtrl & ls(choiceb) & ls(andR) && (
        (debug("theta=Theta") & rollAngleCtrl & safeBrake & debug("Goal1: v=Vmin & theta=Theta") & plantBrake(Variable("a", Some(1)), Variable("w", Some(1))) & plantLoiteringPosTheta(Variable("a", Some(1)), Variable("w", Some(1)))),
        (debug("theta!=Theta") & ls(choiceb) & ls(andR) && (
          (debug("theta=-Theta") & rollAngleCtrl & safeBrake & debug("Goal2: v=Vmin & theta=-Theta") & plantBrake(Variable("a", Some(1)), Variable("w", Some(1))) & plantLoiteringNegTheta(Variable("a", Some(1)), Variable("w", Some(1)))),
          (debug("abs(theta)!=Theta") & ls(choiceb) & ls(andR) && (
            (debug("0<=theta<Theta") & rollAngleCtrl & safeBrake & debug("Goal3: v=Vmin & 0<=theta<Theta") & plantBrake(Variable("a", Some(1)), Variable("w", Some(1))) & plantBTCPosRoll(Variable("a", Some(1)), Variable("w", Some(1)))),
            (debug("-Theta<theta<0") & rollAngleCtrl & safeBrake & debug("Goal4: v=Vmin & -Theta<theta<0") & plantBrake(Variable("a", Some(1)), Variable("w", Some(1))) & plantBTCNegRoll(Variable("a", Some(1)), Variable("w", Some(1))))
            )))))),
      (debug("v>Vmin") & speedCtrl & ls(choiceb) & ls(andR) && (
        (debug("theta=Theta") & rollAngleCtrl & safeBrake & debug("Goal5: v>Vmin & theta=Theta") & plantBrake(Variable("a", Some(1)), Variable("w", Some(1))) & plantBTCMaxRoll(Variable("a", Some(1)), Variable("w", Some(1)))),
        (debug("theta!=Theta") & ls(choiceb) & ls(andR) && (
          (debug("theta=-Theta") & rollAngleCtrl & safeBrake & debug("Goal6: v>Vmin & theta=-Theta") & plantBrake(Variable("a", Some(1)), Variable("w", Some(1))) & plantBTCMaxRoll(Variable("a", Some(1)), Variable("w", Some(1)))),
          (debug("abs(theta)!=Theta") & ls(choiceb) & ls(andR) && (
            (debug("0<=theta<Theta") & rollAngleCtrl & safeBrake & debug("Goal7: v>Vmin & 0<=theta<Theta") & plantBrake(Variable("a", Some(1)), Variable("w", Some(1))) & plantBTCNonmaxRoll(Variable("a", Some(1)), Variable("w", Some(1)))),
            (debug("-Theta<theta<0") & rollAngleCtrl & safeBrake & debug("Goal8: v>Vmin & -Theta<theta<0") & plantBrake(Variable("a", Some(1)), Variable("w", Some(1))) & plantBTCNonmaxRoll(Variable("a", Some(1)), Variable("w", Some(1))))
            ))))))
      )

    /* tactics of the case when helicopter follows a new safe curve */
    def newcurve = (la(andL)*) & ((ls(composeb) ~ ls(randomb) ~ ls(allR) ~ ls(composeb) ~ ls(testb) ~ ls(implyR))*) & ls(assignb)

    def plantNC(a: Variable, w: Variable) =
      ls(DC(s"x-old(x)<=t_2*(v_1-${a.prettyString}/2*t_2) & x-old(x)>=-t_2*(v_1-${a.prettyString}/2*t_2) & y-old(y)<=t_2*(v_1-${a.prettyString}/2*t_2) & y-old(y)>=-t_2*(v_1-${a.prettyString}/2*t_2)".asFormula)) & onBranch(
        (cutShowLbl, debug("Show x-old(x)...")
          & ls(Dconstify) & (ls(DI) | debug("DI. x-old(x)... failed"))),
        (cutUseLbl, debug("Use x-old(x)...")
          & ls(DW) & ls(implyR) & (la(andL)*) & ls(andR) && (
          QE,
          ls(andR) && (
            QE,
            ls(andR) && (
              QE,
              ls(andR) && (
                QE,
                ls(andR) && (
                  QE,
                  debug("last") & ls(orR) & ls(hide, "v_2=Vmin&theta_2>=0&theta_2 < Theta&(abs(x_0-xo_0)>Vmin*(Theta-theta_2)/W+2*r|abs(y_0-yo_0)>Vmin*(Theta-theta_2)/W+2*r)|v_2=Vmin&theta_2 < 0&theta_2>-Theta&(abs(x_0-xo_0)>Vmin*(Theta+theta_2)/W+2*r|abs(y_0-yo_0)>Vmin*(Theta+theta_2)/W+2*r)|v_2=Vmin&theta_2=Theta&dxy_1=dXY&dz_1=dZ&(abs(x_0-xo_0-r*dy_0)>r|abs(y_0-yo_0+r*dx_0)>r)|v_2=Vmin&theta_2=-Theta&dxy_1=-dXY&dz_1=dZ&(abs(x_0-xo_0+r*dy_0)>r|abs(y_0-yo_0-r*dx_0)>r)")
                    & la(hide, "(abs(x-xo)>(v_0^2-Vmin^2)/(2*B)+2*r&abs(x-xo)>(v_0^2-Vmin^2)/(2*B)+Vmin*((Theta-abs(theta_0))/W-(v_0-Vmin)/B)+2*r|abs(y-yo)>(v_0^2-Vmin^2)/(2*B)+2*r&abs(y-yo)>(v_0^2-Vmin^2)/(2*B)+Vmin*((Theta-abs(theta_0))/W-(v_0-Vmin)/B)+2*r)|v_0=Vmin&theta_0>=0&theta_0 < Theta&(abs(x-xo)>Vmin*(Theta-theta_0)/W+2*r|abs(y-yo)>Vmin*(Theta-theta_0)/W+2*r)|v_0=Vmin&theta_0 < 0&theta_0>-Theta&(abs(x-xo)>Vmin*(Theta+theta_0)/W+2*r|abs(y-yo)>Vmin*(Theta+theta_0)/W+2*r)|v_0=Vmin&theta_0=Theta&dxy_0=dXY&dz_0=dZ&(abs(x-xo-r*dy)>r|abs(y-yo+r*dx)>r)|v_0=Vmin&theta_0=-Theta&dxy_0=-dXY&dz_0=dZ&(abs(x-xo+r*dy)>r|abs(y-yo-r*dx)>r)")
                    & la(hide, "dz^2+dxy^2=1", "v>=Vmin", "theta<=Theta", "theta>=-Theta", "dZ^2+dXY^2=1", "dx^2+dy^2=1", "dz_0^2+dxy_0^2=1", "v_0>=Vmin", "theta_0<=Theta", "theta_0>=-Theta", "t_2=0", "dz_1^2+dxy_1^2=1", "dz_1^2+dxy_1^2=1", "dx_0^2+dy_0^2=1")
                    & la(hide, "g>0", "dZ>0", "dXY>0", "r=Vmin^2/(g*(dXY/dZ))")
                    & la(eqLeft(exhaustive = true), "v0_1()=v_1", "theta0_1()=theta_1", "x0_1()=x", "y0_1()=y") & la(hide, "v0_1()=v_1", "theta0_1()=theta_1", "x0_1()=x", "y0_1()=y")
                    & la(orL, "abs(x-xo_0)>(v_1^2-Vmin^2)/(2*B)+2*r+(A/B+1)*(A/2*ep^2+ep*v_1)&abs(x-xo_0)>(v_1^2-Vmin^2)/(2*B)+Vmin*((Theta-abs(theta_1))/W-(v_1-Vmin)/B)+2*r+(A/B+1)*(A/2*ep^2+ep*v_1)+Vmin*ep|abs(y-yo_0)>(v_1^2-Vmin^2)/(2*B)+2*r+(A/B+1)*(A/2*ep^2+ep*v_1)&abs(y-yo_0)>(v_1^2-Vmin^2)/(2*B)+Vmin*((Theta-abs(theta_1))/W-(v_1-Vmin)/B)+2*r+(A/B+1)*(A/2*ep^2+ep*v_1)+Vmin*ep")
                    && (
                    (debug("abs(x-xo_0)")
                      & ls(orR) & ls(hide, "abs(y_0-yo_0)>(v_2^2-Vmin^2)/(2*B)+2*r&abs(y_0-yo_0)>(v_2^2-Vmin^2)/(2*B)+Vmin*((Theta-abs(theta_2))/W-(v_2-Vmin)/B)+2*r")
                      & la(andL) & ls(andR) && (
                      (debug("reach Theta first") & la(hide, "abs(x-xo_0)>(v_1^2-Vmin^2)/(2*B)+Vmin*((Theta-abs(theta_1))/W-(v_1-Vmin)/B)+2*r+(A/B+1)*(A/2*ep^2+ep*v_1)+Vmin*ep")
                        & la(hide, "W>0", "Theta>0", "-W<=w", "w<=W", "-Theta<=theta_1", "theta_1<=Theta", "-Theta<=theta_2", "theta_2<=Theta", "theta_2=theta_1+w*t_3")
                        & la(hide, "y_0-y<=t_3*(v_2-a/2*t_3)", "y_0-y>=-t_3*(v_2-a/2*t_3)") & QE),
                      (debug("reach Vmin first") & la(hide, "abs(x-xo_0)>(v_1^2-Vmin^2)/(2*B)+2*r+(A/B+1)*(A/2*ep^2+ep*v_1)")
                        & la(hide, "y_0-y<=t_3*(v_2-a/2*t_3)", "y_0-y>=-t_3*(v_2-a/2*t_3)") & QE)
                      )
                      ),
                    (debug("abs(y-yo_0)")
                      & ls(orR) & ls(hide, "abs(x_0-xo_0)>(v_2^2-Vmin^2)/(2*B)+2*r&abs(x_0-xo_0)>(v_2^2-Vmin^2)/(2*B)+Vmin*((Theta-abs(theta_2))/W-(v_2-Vmin)/B)+2*r")
                      & la(andL) & ls(andR) && (
                      (debug("reach Theta first") & la(hide, "abs(y-yo_0)>(v_1^2-Vmin^2)/(2*B)+Vmin*((Theta-abs(theta_1))/W-(v_1-Vmin)/B)+2*r+(A/B+1)*(A/2*ep^2+ep*v_1)+Vmin*ep")
                        & la(hide, "W>0", "Theta>0", "-W<=w", "w<=W", "-Theta<=theta_1", "theta_1<=Theta", "-Theta<=theta_2", "theta_2<=Theta", "theta_2=theta_1+w*t_3")
                        & la(hide, "x_0-x<=t_3*(v_2-a/2*t_3)", "x_0-x>=-t_3*(v_2-a/2*t_3)") & QE),
                      (debug("reach Vmin first") & la(hide, "abs(y-yo_0)>(v_1^2-Vmin^2)/(2*B)+2*r+(A/B+1)*(A/2*ep^2+ep*v_1)")
                        & la(hide, "x_0-x<=t_3*(v_2-a/2*t_3)", "x_0-x>=-t_3*(v_2-a/2*t_3)") & QE)
                      )
                      )
                    )
                  )))))))

    val tactic = ls(implyR) & (la(andL)*) & ls(I(loopInv)) & onBranch(
      (indInitLbl, debug("Base Case") & QE),
      (indUseCaseLbl, debug("Use Case") & ls(implyR) & (la(andL)*) & QE),
      (indStepLbl, debug("Step") & ls(implyR) & ls(composeb) & ls(composeb) & ls(choiceb) & ls(andR) && (
        (debug("brake on current curve") & maneuver),
        (debug("follow new curve") & newcurve & debug("Goal9: new curve") & plantNewCurve(Variable("a"), Variable("w")) & plantNC(Variable("a"), Variable("w")))
        ))
    )

    val result = helper.runTactic(tactic, new RootNode(s))
    Console.println("Open goals remaining: " + result.openGoals().length)
    result shouldBe 'closed
  }

}

