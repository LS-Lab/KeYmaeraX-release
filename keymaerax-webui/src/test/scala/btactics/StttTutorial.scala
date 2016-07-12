/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.{OnAll, TheType, UnificationMatch}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.DebuggingTactics.{print, printIndexed}
import edu.cmu.cs.ls.keymaerax.btactics.ArithmeticSimplification._
import edu.cmu.cs.ls.keymaerax.btactics.arithmetic.speculative.ArithmeticSpeculativeSimplification._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.SlowTest
import testHelper.ParserFactory._

import scala.collection.immutable._
import scala.language.postfixOps

/**
 * Tutorial test cases.
 *
 * @author Stefan Mitsch
 */
@SlowTest
class StttTutorial extends TacticTestBase {

  "Example 1" should "be provable" in withMathematica { implicit qeTool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example1.key"))
    val tactic = implyR('_) & andL('_) & DC("v>=0".asFormula)(1) <(
      /* use */ diffWeaken(1) & prop,
      /* show */ diffInd(qeTool)(1)
      )
    proveBy(s, tactic) shouldBe 'proved
  }

  it should "be provable with diffSolve" in withMathematica { implicit qeTool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example1.key"))
    val tactic = implyR('_) & andL('_) & diffSolve(None)(1) & QE
    proveBy(s, tactic) shouldBe 'proved
  }

  it should "be provable with master" in withMathematica { implicit qeTool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example1.key"))
    proveBy(s, master()) shouldBe 'proved
  }

  it should "be provable with diffInvariant" in withMathematica { implicit qeTool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example1.key"))
    val tactic = implyR('_) & andL('_) & diffInvariant("v>=0".asFormula)('R) & diffWeaken('R) & prop
    proveBy(s, tactic) shouldBe 'proved
  }

  "Example 1a" should "be provable" in withMathematica { implicit qeTool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example1a.key"))
    val tactic = implyR('_) & andL('_)*@TheType() & diffInvariant("v>=0".asFormula, "x>=old(x)".asFormula)(1) &
      exhaustiveEqR2L('L, "x0=x".asFormula) & diffWeaken(1) & exhaustiveEqL2R('L, "x_0=x0".asFormula) & prop

    proveBy(s, tactic) shouldBe 'proved
  }

  "Example 2" should "be provable with master and custom loop invariant" in withMathematica { implicit qeTool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example2.key"))
    val Imply(_, Box(loop, _)) = s.succ.head
    proveBy(s, master(new ConfigurableGenerate(Map((loop, "v>=0".asFormula))))) shouldBe 'proved
  }

  it should "be provable with master and loop invariant from file" in withMathematica { implicit qeTool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example2.key"))
    proveBy(s, master()) shouldBe 'proved
  }

  it should "be provable with abstract loop invariant" in withMathematica { implicit qeTool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example2.key"))

    val tactic = implyR('_) & andL('_)*@TheType() & loop("J(v)".asFormula)('R) <(
      skip,
      skip,
      chase('R) & prop & OnAll(diffSolve()('R) partial) partial
      ) &
      US(UnificationMatch("J(v)".asFormula, "v>=0".asFormula).usubst) &
      OnAll(close | QE)

    proveBy(s, tactic) shouldBe 'proved
  }

  "Example 3a" should "be provable with master and loop invariant from file" in withMathematica { implicit tool =>
    // // needs evolution domain at time 0
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example3a.key"))
    proveBy(s, master()) shouldBe 'proved
  }

  "Example3b" should "find correct safety condition" in withMathematica { implicit tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example3b.key"))
    val tactic = implyR('_) & andL('_)*@TheType() & chase('R) & normalize & OnAll(diffSolve()('R) partial) & print("Foo")
    val intermediate = proveBy(s, tactic)
    intermediate.subgoals should have size 3
    intermediate.subgoals(0) shouldBe Sequent(
      IndexedSeq("v_0>=0".asFormula, "A>0".asFormula, "B>0".asFormula, "true".asFormula, "x_0<=S".asFormula, "true".asFormula, "t__0=0".asFormula, "v_0>=0".asFormula),
      IndexedSeq("((v>=0&t_>=0)&v=A*t_+v_0)&x=1/2*(A*t_^2+2*t_*v_0+2*x_0)->x<=S".asFormula))
    intermediate.subgoals(1) shouldBe Sequent(
      IndexedSeq("v_0>=0".asFormula, "A>0".asFormula, "B>0".asFormula, "true".asFormula, "x_0<=S".asFormula, "v_0=0".asFormula, "t__0=0".asFormula, "v_0>=0".asFormula),
      IndexedSeq("((v>=0&t_>=0)&v=v_0)&x=t_*v_0+x_0->x<=S".asFormula))
    intermediate.subgoals(2) shouldBe Sequent(
      IndexedSeq("v_0>=0".asFormula, "A>0".asFormula, "B>0".asFormula, "true".asFormula, "x_0<=S".asFormula, "t__0=0".asFormula, "v_0>=0".asFormula),
      IndexedSeq("((v>=0&t_>=0)&v=-1*B*t_+v_0)&x=1/2*(-1*B*t_^2+2*t_*v_0+2*x_0)->x<=S".asFormula))

    val brake = proveBy(intermediate.subgoals(2), ToolTactics.partialQE)
    brake.subgoals should have size 1
    brake.subgoals.head shouldBe Sequent(
      IndexedSeq(),
      // here is our evolution domain constraint (substitute t_ = v/B into S>= ... ) -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------v------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------v
      IndexedSeq("v_0<=0|v_0>0&(t_<=0|t_>0&(((B<=0|(0 < B&B < t_^-1*v_0)&((S < x_0|(x_0<=S&S < 1/2*(-1*B*t_^2+2*t_*v_0+2*x_0))&((x < 1/2*(-1*B*t_^2+2*t_*v_0+2*x_0)|x=1/2*(-1*B*t_^2+2*t_*v_0+2*x_0)&((v < -1*B*t_+v_0|v=-1*B*t_+v_0&((t__0 < 0|t__0=0&A<=0)|t__0>0))|v>-1*B*t_+v_0))|x>1/2*(-1*B*t_^2+2*t_*v_0+2*x_0)))|S>=1/2*(-1*B*t_^2+2*t_*v_0+2*x_0)))|B=t_^-1*v_0&((S < x_0|(x_0<=S&S < 1/2*(-1*B*t_^2+2*t_*v_0+2*x_0))&((x < 1/2*(-1*B*t_^2+2*t_*v_0+2*x_0)|x=1/2*(-1*B*t_^2+2*t_*v_0+2*x_0)&((v < 0|v=0&((t__0 < 0|t__0=0&A<=0)|t__0>0))|v>0))|x>1/2*(-1*B*t_^2+2*t_*v_0+2*x_0)))|S>=1/2*(-1*B*t_^2+2*t_*v_0+2*x_0)))|B>t_^-1*v_0))".asFormula))
  }

  "Example 4a" should "be provable with master and loop invariant from file" in withMathematica { implicit tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example4a.key"))
    proveBy(s, master()) shouldBe 'proved
  }

  "Example 4b" should "be provable with master and loop invariant from file" in withMathematica { implicit tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example4b.key"))
    proveBy(s, master()) shouldBe 'proved
  }

  "Example 4c" should "be provable with master and loop invariant from file" in withMathematica { implicit tool =>
    // needs evolution domain at time 0
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example4c.key"))
    proveBy(s, master()) shouldBe 'proved
  }

  "Example 5 with simple control" should "be provable" in withMathematica { implicit tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example5_simplectrl.key"))

    val plant = print("plant") & composeb('R) & assignb('R) &
      diffSolve(None)('R) & implyR('R)

    val tactic = implyR('R) & (andL('L)*@TheType()) &
      loop("v >= 0 & x+v^2/(2*B) <= S".asFormula)('R) <(
      print("Base Case") & andR('R) & OnAll(closeId),
      print("Use Case") & QE,
      print("Step") & andL('L) & composeb('R) & assignb('R) & plant & QE
    )

    proveBy(s, tactic) shouldBe 'proved
  }

  it should "be provable automatically with Mathematica" in withMathematica { implicit qeTool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example5_simplectrl.key"))
    proveBy(s, master()) shouldBe 'proved
  }

  "Example 5" should "be provable automatically with Mathematica" in withMathematica { implicit qeTool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example5.key"))
    proveBy(s, master()) shouldBe 'proved
  }

  it should "be provable with chase etc" in withMathematica { implicit tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example5.key"))

    val tactic = implyR('R) & andL('L)*@TheType() &
      loop("v >= 0 & x+v^2/(2*B) <= S".asFormula)('R) <(
        printIndexed("Base case") & andR('R) & OnAll(closeId),
        printIndexed("Use case") & QE,
        printIndexed("Step") & chase('R) & normalize & printIndexed("Normalized") & OnAll(diffSolve()('R) partial) &
          printIndexed("After diffSolve") & OnAll(QE)
        )

    proveBy(s, tactic) shouldBe 'proved
  }

  it should "be provable with abstract loop invariant" in withMathematica { implicit qeTool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example5.key"))

    val tactic = implyR('R) & andL('L)*@TheType() &
      loop("J(v,x,B,S)".asFormula)('R) <(
        skip,
        skip,
        chase('R) & normalize & OnAll(diffSolve()('R) partial) partial
        ) &
      US(UnificationMatch("J(v,x,B,S)".asFormula, "v >= 0 & x+v^2/(2*B) <= S".asFormula).usubst) &
      OnAll(close | QE)

    proveBy(s, tactic) shouldBe 'proved
  }

  "Example 6" should "be provable automatically with Mathematica" in withMathematica { implicit qeTool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example6.key"))
    proveBy(s, master()) shouldBe 'proved
  }

  "Example 7" should "be provable automatically with Mathematica" in withMathematica { implicit qeTool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example7.key"))
    proveBy(s, master()) shouldBe 'proved
  }

  ignore /*"Example 8"*/ should "Example 8 be provable automatically with Mathematica" in withMathematica { implicit qeTool =>
    // x' <= a*d
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example8.key"))
    proveBy(s, master()) shouldBe 'proved
  }

  "Example 9a" should "be provable" in withMathematica { implicit tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example9a.key"))
    val tactic = implyR('R) & andL('L)*@TheType() & diffInd(tool, 'full)('R)
    proveBy(s, tactic) shouldBe 'proved
  }

  "Example 9b" should "be provable" in withMathematica { implicit qeTool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example9b.key"))

    val ode =
      // xr = (xm+S)/2
      diffInvariant("xm<=x".asFormula, "5/4*(x-(xm+S)/2)^2 + (x-(xm+S)/2)*v/2 + v^2/4 < ((S-xm)/2)^2".asFormula)('R) &
      diffWeaken('R)

    val tactic = implyR('R) & andL('L)*@TheType() &
      loop("v >= 0 & xm <= x & xr = (xm + S)/2 & 5/4*(x-xr)^2 + (x-xr)*v/2 + v^2/4 < ((S - xm)/2)^2".asFormula)('R) <(
        print("Base case") & (andR('R) <(closeId, skip))*@TheType() & closeId,
        print("Use case") & QE,
        print("Step") & andL('L)*@TheType() & chase('R) & andR('R) <(
          allR('R) & implyR('R)*@TheType() & ode & implyR('R) & andL('L)*@TheType() & printIndexed("Foo") & QE,
          ode & printIndexed("Bar") & QE
        )
      )

    proveBy(s, tactic) shouldBe 'proved
  }

  "Example 10" should "be provable" in withMathematica { implicit tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example10.key"))

    def ode(a: String) = diffInvariant("c>=0".asFormula, "dx^2+dy^2=1".asFormula, s"v=old(v)+$a*c".asFormula,
      s"-c*(v-$a/2*c) <= y - old(y) & y - old(y) <= c*(v-$a/2*c)".asFormula)('R) &
      exhaustiveEqR2L(hide=true)('Llast)*2 /* old(y)=y, old(v)=v */ & andL('_)*@TheType() & diffWeaken('R)

    val tactic = implyR('R) & andL('L)*@TheType() &
      loop("v >= 0 & dx^2+dy^2 = 1 & r != 0 & abs(y-ly) + v^2/(2*b) < lw".asFormula)('R) <(
        print("Base case") & speculativeQE,
        print("Use case") & speculativeQE,
        print("Step") & chase('R) & normalize & printIndexed("Normalized") <(
          printIndexed("Acc") & hideL(-9, "abs(y-ly)+v^2/(2*b) < lw".asFormula) & ode("a") &
            alphaRule*@TheType() &
            printIndexed("Before replaceTransform") & replaceTransform("ep".asTerm, "c".asTerm)(-8) &
            prop & OnAll(speculativeQE),
          printIndexed("Stop") & ode("0") & prop & OnAll(speculativeQE),
          printIndexed("Brake") & ode("a") & prop & OnAll(speculativeQE)
          )
        )

    proveBy(s, tactic) shouldBe 'proved
  }

}
