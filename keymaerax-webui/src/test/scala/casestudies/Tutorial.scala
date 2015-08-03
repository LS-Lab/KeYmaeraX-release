/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
package casestudies

import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tactics.BranchLabels._
import edu.cmu.cs.ls.keymaerax.tactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.tactics._
import edu.cmu.cs.ls.keymaerax.tools.{Z3, Mathematica, KeYmaera}
import testHelper.ProvabilityTestHelper
import org.scalatest.{BeforeAndAfterEach, FlatSpec, Matchers}
import testHelper.ParserFactory._


import scala.language.postfixOps


import scala.collection.immutable.Map

/**
 * Created by smitschon 2/27/15.
 * @author Stefan Mitsch
 */
class Tutorial extends FlatSpec with Matchers with BeforeAndAfterEach {

  val helper = new ProvabilityTestHelper((x) => println(x))
  val mathematicaConfig : Map[String, String] = helper.mathematicaConfig

  override def beforeEach() = {
    Tactics.KeYmaeraScheduler = new Interpreter(KeYmaera)
    Tactics.MathematicaScheduler = new Interpreter(new Mathematica)
    Tactics.MathematicaScheduler.init(mathematicaConfig)
    Tactics.KeYmaeraScheduler.init(Map())
    Tactics.Z3Scheduler = Some(new Interpreter(new Z3))
    Tactics.Z3Scheduler.get.init(Map())
  }

  override def afterEach() = {
    Tactics.Z3Scheduler.get.shutdown()
    Tactics.MathematicaScheduler.shutdown()
    Tactics.KeYmaeraScheduler.shutdown()
    Tactics.Z3Scheduler = null
    Tactics.MathematicaScheduler = null
    Tactics.KeYmaeraScheduler = null
  }

  "Example 1" should "be provable" in {
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example1.key"))
    val tactic = ls(implyR) & la(andL) & ls(diffSolve) & ls(implyR) & QE
    helper.runTactic(tactic, new RootNode(s)) shouldBe 'closed
  }

  it should "be provable automatically with Mathematica" in {
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example1.key"))
    helper.runTactic(master, new RootNode(s)) shouldBe 'closed
  }

  it should "be provable automatically with Z3" in {
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example1.key"))
    helper.runTactic(master("Z3"), new RootNode(s)) shouldBe 'closed
  }

  "Example 1a" should "be provable" in {
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example1a.key"))
    val tactic = ls(implyR) & (la(andL)*) & ls(diffSolve) & ls(implyR) & QE
    helper.runTactic(tactic, new RootNode(s)) shouldBe 'closed
  }

  it should "be provable automatically with Mathematica" in {
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example1a.key"))
    helper.runTactic(master, new RootNode(s)) shouldBe 'closed
  }

  it should "be provable automatically with Z3" in {
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example1a.key"))
    helper.runTactic(master("Z3"), new RootNode(s)) shouldBe 'closed
  }

  "Example 2" should "be provable" in {
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example2.key"))

    val tactic = ls(implyR) & la(andL) & ls(I("v>=0".asFormula)) & onBranch(
      (indInitLbl, debug("Base Case") & (la(andL)*) & closeId),
      (indUseCaseLbl, debug("Use Case") & ls(implyR) & closeId),
      (indStepLbl, debug("Step") & ls(implyR) & ls(composeb) &
        ls(choiceb) & ls(andR) && (
        debug("Case 1") & ls(assignb),
        ls(choiceb) & ls(andR) && (
          debug("Case 2") & ls(assignb),
          debug("Case 3") & ls(assignb)
          )
        ) & ls(diffSolve) & ls(implyR) & QE)
    )

    helper.runTactic(tactic, new RootNode(s)) shouldBe 'closed
  }

  it should "be provable automatically with Mathematica" in {
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example2.key"))
    helper.runTactic(master(new Generate("v>=0".asFormula)), new RootNode(s)) shouldBe 'closed
  }

  it should "be provable automatically with Z3" in {
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example2.key"))
    helper.runTactic(master(new Generate("v>=0".asFormula), "Z3"), new RootNode(s)) shouldBe 'closed
  }

  // TODO not implemented yet: evolution domain must hold in the beginning
  ignore /*"Example 3a"*/ should "Example 3a be provable" in {
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example3a.key"))

    val plant = debug("plant") & ls(composeb) & ls(testb) & ls(implyR) & ls(choiceb) & ls(andR) &&
      (debug("evolution domain <=") & ls(diffSolve) & ls(implyR),
       debug("evolution domain >=") & ls(diffSolve) & ls(implyR))

    val tactic = ls(implyR) & (la(andL)*) &
      ls(I("v>=0 & x+v^2/(2*B) <= S".asFormula)) & onBranch(
      (indInitLbl, debug("Base Case") & (la(andL)*) & ls(andR) & QE),
      (indUseCaseLbl, debug("Use Case") & ls(implyR) & QE),
      (indStepLbl, debug("Step") & ls(implyR) & la(andL) & ls(composeb) & ls(choiceb) & ls(andR) && (
        debug("Case 1") & ls(composeb) & ls(testb) & ls(implyR) & ls(assignb),
        ls(choiceb) & ls(andR) && (
          debug("Case 2") & ls(composeb) & ls(testb) & ls(implyR) & ls(assignb),
          debug("Case 3") & ls(assignb)
          )
        ) & plant & (la(andL)*) & (ls(andR)*) & (closeId | QE)
      )
    )

    helper.runTactic(tactic, new RootNode(s)) shouldBe 'closed
  }

  // TODO not implemented yet: evolution domain must hold in the beginning, IfThenElse
  ignore /*"Example 4a"*/ should "Example 4a be provable" in {
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example4a.key"))

    val plant = debug("plant") & ls(composeb) & ls(testb) & ls(implyR) & ls(diffSolve) & ls(implyR)

    val tactic = ls(implyR) & (la(andL)*) &
      ls(I("v <= V".asFormula)) & onBranch(
      (indInitLbl, debug("Base Case") & QE),
      (indUseCaseLbl, debug("Use Case") & ls(implyR) & QE),
      (indStepLbl, debug("Step") & ls(implyR) & ls(composeb) & plant & QE)
    )

    helper.runTactic(tactic, new RootNode(s)) shouldBe 'closed
  }

  // TODO not implemented yet: evolution domain must hold in the beginning, IfThenElse
  ignore /*"Example 4b"*/ should "Example 4b be provable" in {
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example4b.key"))

    val plant = debug("plant") & ls(composeb) & ls(testb) & ls(implyR) & ls(diffSolve) & ls(implyR)

    val tactic = ls(implyR) & (la(andL)*) &
      ls(I("v <= V".asFormula)) & onBranch(
      (indInitLbl, debug("Base Case") & QE),
      (indUseCaseLbl, debug("Use Case") & ls(implyR) & QE),
      (indStepLbl, debug("Step") & ls(implyR) & ls(composeb) & ls(assignb) & plant & QE)
    )

    helper.runTactic(tactic, new RootNode(s)) shouldBe 'closed
  }

  // TODO not implemented yet: evolution domain must hold in the beginning, IfThenElse
  ignore /*"Example 4c"*/ should "Example 4c be provable" in {
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example4c.key"))

    val plant = debug("plant") & ls(composeb) & ls(testb) & ls(implyR) & ls(choiceb) & ls(andR) &
      ls(diffSolve) & ls(implyR)

    val tactic = ls(implyR) & (la(andL)*) &
      ls(I("v <= V".asFormula)) & onBranch(
      (indInitLbl, debug("Base Case") & QE),
      (indUseCaseLbl, debug("Use Case") & ls(implyR) & QE),
      (indStepLbl, debug("Step") & ls(implyR) & ls(composeb)
        )
    )

    helper.runTactic(tactic, new RootNode(s)) shouldBe 'closed
  }

  "Example 5 with simple control" should "be provable" in {
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example5_simplectrl.key"))

    val plant = debug("plant") & ls(composeb) & ls(assignb) &
      ls(diffSolve) & ls(implyR)

    val tactic = ls(implyR) & (la(andL)*) &
      ls(I("v >= 0 & x+v^2/(2*B) <= S".asFormula)) & onBranch(
      (indInitLbl, debug("Base Case") & ls(andR) & closeId),
      (indUseCaseLbl, debug("Use Case") & ls(implyR) & QE),
      (indStepLbl, debug("Step") & ls(implyR) & la(andL) & ls(composeb) & ls(assignb) & plant & QE)
    )

    helper.runTactic(tactic, new RootNode(s)) shouldBe 'closed
  }

  it should "be provable automatically with Mathematica" in {
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example5_simplectrl.key"))
    helper.runTactic(master(new Generate("v >= 0 & x+v^2/(2*B) <= S".asFormula), "Mathematica"), new RootNode(s)) shouldBe 'closed
  }

  it should "be provable automatically with Z3" in {
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example5_simplectrl.key"))
    helper.runTactic(master(new Generate("v >= 0 & x+v^2/(2*B) <= S".asFormula), "Z3"), new RootNode(s)) shouldBe 'closed
  }

  "Example 5" should "be provable" in {
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example5.key"))

    val plant = debug("plant") & ls(composeb) & ls(assignb) & ls(diffSolve) & ls(implyR)

    val tactic = ls(implyR) & (la(andL)*) &
      ls(I("v >= 0 & x+v^2/(2*B) <= S".asFormula)) & onBranch(
      (indInitLbl, debug("Base Case") & ls(andR) & closeId),
      (indUseCaseLbl, debug("Use Case") & ls(implyR) & QE),
      (indStepLbl, debug("Step") & ls(implyR) & la(andL) & ls(composeb) & ls(choiceb) & ls(andR) && (
        debug("Case 1") & ls(composeb) & ls(testb) & ls(implyR) & ls(assignb),
        ls(choiceb) & ls(andR) && (
          debug("Case 2") & ls(composeb) & ls(testb) & ls(implyR) & ls(assignb),
          debug("Case 3") & ls(assignb)
          )
        ) & plant & ls(andR) & (closeId | QE)
        )
    )

    helper.runTactic(tactic, new RootNode(s)) shouldBe 'closed
  }

  it should "be provable automatically with Mathematica" in {
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example5.key"))
    helper.runTactic(master(new Generate("v >= 0 & x+v^2/(2*B) <= S".asFormula), "Mathematica"), new RootNode(s)) shouldBe 'closed
  }

  it should "be provable automatically with Z3" in {
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example5.key"))
    helper.runTactic(master(new Generate("v >= 0 & x+v^2/(2*B) <= S".asFormula), "Z3"), new RootNode(s)) shouldBe 'closed
  }

  "Example 6" should "be provable" in {
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example6.key"))
    val plant = debug("plant") & ls(composeb) & ls(assignb) & ls(diffSolve) & ls(implyR)

    val tactic = ls(implyR) & (la(andL)*) &
      ls(I("v >= 0 & x+v^2/(2*B) <= S".asFormula)) & onBranch(
      (indInitLbl, debug("Base Case") & ls(andR) & closeId),
      (indUseCaseLbl, debug("Use Case") & ls(implyR) & QE),
      (indStepLbl, debug("Step") & ls(implyR) & la(andL) & ls(composeb) & ls(choiceb) & ls(andR) && (
        debug("Case 1") & ls(composeb) & ls(testb) & ls(implyR) & ls(composeb) & ls(randomb) & ls(allR) &
          ls(testb) & ls(implyR) & la(andL),
        ls(choiceb) & ls(andR) && (
          debug("Case 2") & ls(composeb) & ls(testb) & ls(implyR) & ls(assignb),
          debug("Case 3") & ls(assignb)
          )
        ) & plant & ls(andR) & (closeId | QE)
        )
    )

    helper.runTactic(tactic, new RootNode(s)) shouldBe 'closed
  }

  it should "be provable automatically with Mathematica" in {
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example6.key"))
    helper.runTactic(master(new Generate("v >= 0 & x+v^2/(2*B) <= S".asFormula), "Mathematica"), new RootNode(s)) shouldBe 'closed
  }

  it should "be provable automatically with Z3" in {
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example6.key"))
    helper.runTactic(master(new Generate("v >= 0 & x+v^2/(2*B) <= S".asFormula), "Z3"), new RootNode(s)) shouldBe 'closed
  }

  "Example 7" should "be provable" in {
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example7.key"))
    val plant = debug("plant") & ls(composeb) & ls(assignb) & ls(diffSolve) & ls(implyR)

    val tactic = ls(implyR) & (la(andL)*) &
      ls(I("v >= 0 & x+v^2/(2*b) <= S".asFormula)) & onBranch(
      (indInitLbl, debug("Base Case") & ls(andR) & closeId),
      (indUseCaseLbl, debug("Use Case") & ls(implyR) & QE),
      (indStepLbl, debug("Step") & ls(implyR) & la(andL) & ls(composeb) & ls(choiceb) & ls(andR) && (
        debug("Case 1") & ls(composeb) & ls(testb) & ls(implyR) & ls(composeb) & ls(randomb) & ls(allR) &
          ls(testb) & ls(implyR) & la(andL),
        ls(choiceb) & ls(andR) && (
          debug("Case 2") & ls(composeb) & ls(testb) & ls(implyR) & ls(assignb),
          debug("Case 3") & ls(composeb) & ls(randomb) & ls(allR) & ls(testb) & ls(implyR) & la(andL)
          )
        ) & plant & ls(andR) & (closeId | QE)
        )
    )

    helper.runTactic(tactic, new RootNode(s)) shouldBe 'closed
  }

  it should "be provable automatically with Mathematica" in {
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example7.key"))
    helper.runTactic(master(new Generate("v >= 0 & x+v^2/(2*b) <= S".asFormula), "Mathematica"), new RootNode(s)) shouldBe 'closed
  }

  it should "be provable automatically with Z3" in {
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example7.key"))
    helper.runTactic(master(new Generate("v >= 0 & x+v^2/(2*b) <= S".asFormula), "Z3"), new RootNode(s)) shouldBe 'closed
  }

  // TODO not yet implemented: differential inequalities
  // Example 8

  "Example 9a" should "be provable" in {
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example9a.key"))
    val tactic = ls(implyR) & (la(andL)*) & ls(DI)
    helper.runTactic(tactic, new RootNode(s)) shouldBe 'closed
  }

  //@todo Stefan (needs extended constify: our DCs talk about xm, S, which are not even mentioned in ODE)
  "Example 9b" should "be provable" in {
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example9b.key"))

    val plant = debug("Plant") & ls(Dconstify) & debug("Before Cut") &
      ls(DC("xm() <= x_0".asFormula)) & onBranch(
      (cutShowLbl, debug("Show cut 1") & ls(DI)),
      (cutUseLbl, debug("Use cut 1") & ls(DC("5/4*(x_0-xr())^2 + (x_0-xr())*v/2 + v^2/4 < ((S() - xm())/2)^2".asFormula)) & onBranch(
        (cutShowLbl, debug("Show cut 2") & ls(DI)),
        (cutUseLbl, debug("Use cut 2") & ls(DW) & ls(implyR) & debug("Result Weaken"))
          )
        )
      )

    val tactic = ls(implyR) & (la(andL)*) &
      ls(I("v >= 0 & xm <= x & xr = (xm + S)/2 & 5/4*(x-xr)^2 + (x-xr)*v/2 + v^2/4 < ((S - xm)/2)^2".asFormula)) & onBranch(
      (indInitLbl, debug("Base case") & (ls(andR)*) & closeId),
      (indStepLbl, debug("Step") & ls(implyR) & (la(andL)*) & ls(composeb) & ls(choiceb) & ls(andR) &&
        (debug("Case 1") & ls(composeb) & ls(assignb) & ls(composeb) & ls(assignb) & ls(testb) &
          ls(implyR) & debug("Result 1"),
         debug("Case 2") & ls(composeb) & ls(assignb) & ls (assignb) & debug("Result 2")
        ) & plant & (la(andL)*) & (ls(andR)*) & closeId
        ),
      (indUseCaseLbl, debug("Use case") & ls(implyR) & QE)
      )

    helper.runTactic(tactic, new RootNode(s)) shouldBe 'closed
  }

  "Example 10" should "be provable" in {
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example10.key"))

    val plant = ls(composeb) & ls(assignb) &
      ls(DC("c_2>=0".asFormula)) & onBranch(
        (cutShowLbl, debug("Show c>=0") &
          (la(hide, "abs(y_0-ly)+v_0^2/(2*B) < lw") ~
           la(hide, "abs(y_0-ly)+x+v_0^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v_0) < lw")) ~ ls(DI)),
        (cutUseLbl, debug("Use c>=0") &
          ls(DC("dx^2+dy^2=1".asFormula)) & onBranch(
          (cutShowLbl, debug("Show dx^2+dy^2=1") &
            (la(hide, "abs(y_0-ly)+v_0^2/(2*B) < lw") ~
             la(hide, "abs(y_0-ly)+x+v_0^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v_0) < lw")) ~ ls(DI)),
          (cutUseLbl, debug("Use dx^2+dy^2=1") &
            ls(DC("v_0=old(v_0)+a*c_2".asFormula)) & onBranch(
            (cutShowLbl, debug("Show v_0=old(v_0)+a*c_2") &
              (la(hide, "abs(y_0-ly)+v_0^2/(2*B) < lw") ~
               la(hide, "abs(y_0-ly)+x+v_0^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v_0) < lw")) ~ (ls(Dconstify) & ls(DI))),
            (cutUseLbl, debug("Use v_0=old(v_0)+a*c_2") &
              ls(DC("-c_2*(v_0 - a/2*c_2) <= x-old(x) & x-old(x) <= c_2*(v_0 - a/2*c_2)".asFormula)) & onBranch(
              (cutShowLbl, debug("Show ... <= x-old(x) <= ...") &
                (la(hide, "abs(y_0-ly)+v_0^2/(2*B) < lw") ~
                 la(hide, "abs(y_0-ly)+x+v_0^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v_0) < lw")) ~ (ls(Dconstify) & ls(DI))),
              (cutUseLbl, debug("Use ... <= x-old(x) <= ...") &
                ls(DC("-c_2*(v_0 - a/2*c_2) <= y_0-old(y_0) & y_0-old(y_0) <= c_2*(v_0 - a/2*c_2)".asFormula)) & onBranch(
                (cutShowLbl, debug("Show ... <= y_0-old(y_0) <= ...") &
                  (la(hide, "abs(y_0-ly)+v_0^2/(2*B) < lw") ~
                   la(hide, "abs(y_0-ly)+x+v_0^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v_0) < lw")) ~ (ls(Dconstify) & ls(DI))),
                (cutUseLbl, debug("Use ... <= y_0-old(y_0) <= ...") & ls(DW) & ls(implyR) & (la(andL)*) /* todo finish*/)
              ))
            ))
          ))
        ))
      )

    val tactic = ls(implyR) & (la(andL)*) &
      ls(I("v >= 0 & dx^2+dy^2 = 1 & r != 0 & abs(y-ly) + v^2/(2*B) < lw".asFormula)) & onBranch(
      (indInitLbl, debug("Base case") & (ls(andR)*) & closeId),
      (indStepLbl, debug("Step") & la(hideL, "abs(y-ly)+v^2/(2*B) < lw") & ls(implyR) & (la(andL)*) & ls(composeb) &
        ls(choiceb) & ls(andR) &&
        (debug("Case 1") & ls(composeb) & ls(testb) & ls(implyR) & ls(composeb) & ls(randomb) & ls(allR) &
          ls(composeb) & ls(testb) & ls(implyR) & (ls(composeb) & ls(randomb) & ls(allR))*2 & ls(testb) & ls(implyR) &
          debug("Result 1") & plant,
         ls(choiceb) & ls(andR) && (
           debug("Case 2") & ls(composeb) & ls(testb) & ls(implyR) & ls(composeb) & ls(assignb) & ls(assignb) &
             debug("Result 2"),
           debug("Case 3") & ls(composeb) & ls(randomb) & ls(allR) & ls(testb) & ls(implyR) & debug("Result 3")
           )
        )
      ),
      (indUseCaseLbl, debug("Use case") &
        la(hide, "abs(y-ly)+v^2/(2*B) < lw") & la(hide, "r!=0") & la(hide, "y=ly") & la(hide, "lw>0") &
        la(hide, "v>=0") & ls(implyR) & (la(andL)*) &
        abs(AntePosition(4).first.first) & QE)
    )

    helper.runTactic(tactic, new RootNode(s)) shouldBe 'closed
  }
}
