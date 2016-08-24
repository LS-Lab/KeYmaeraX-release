/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.{OnAll, UnificationMatch}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.DebuggingTactics.{print, printIndexed}
import edu.cmu.cs.ls.keymaerax.btactics.ArithmeticSimplification._
import edu.cmu.cs.ls.keymaerax.btactics.arithmetic.speculative.ArithmeticSpeculativeSimplification._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXProblemParser
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

  "Example 1" should "be provable" in withMathematica { qeTool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example1.key")).mkString
    val tactic = implyR('_) & andL('_) & DC("v>=0".asFormula)(1) <(
      /* use */ diffWeaken(1) & prop,
      /* show */ diffInd()(1)
      )
    db.proveBy(modelContent, tactic) shouldBe 'proved
  }}

  it should "be provable with diffSolve" in withMathematica { qeTool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example1.key")).mkString
    val tactic = implyR('_) & andL('_) & diffSolve(None)(1) & QE
    db.proveBy(modelContent, tactic) shouldBe 'proved
  }}

  it should "be provable with master" in withMathematica { qeTool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example1.key")).mkString
    db.proveBy(modelContent, master()) shouldBe 'proved
  }}

  it should "be provable with diffInvariant" in withMathematica { qeTool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example1.key")).mkString
    val tactic = implyR('_) & andL('_) & diffInvariant("v>=0".asFormula)('R) & diffWeaken('R) & prop
    db.proveBy(modelContent, tactic) shouldBe 'proved
  }}

  "Example 1a" should "be provable" in withMathematica { qeTool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example1a.key")).mkString
    val tactic = implyR('_) & (andL('_)*) & diffCut("v>=0".asFormula)(1) & Idioms.<(
      diffCut("x>=old(x)".asFormula)(1) & Idioms.<(
        exhaustiveEqR2L('L, "x0=x".asFormula) & diffWeaken(1) & exhaustiveEqL2R('L, "x_0=x0".asFormula) & prop,
        diffInd()(1)
      ),
      diffInd()(1)
    )

    db.proveBy(modelContent, tactic) shouldBe 'proved
  }}

  it should "be provable with multi-arg invariant" in withMathematica { qeTool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example1a.key")).mkString
    val tactic = implyR('_) & (andL('_)*) & diffInvariant("v>=0".asFormula, "x>=old(x)".asFormula)(1) &
      exhaustiveEqR2L('L, "x0=x".asFormula) & diffWeaken(1) & exhaustiveEqL2R('L, "x_0=x0".asFormula) & prop

    //@todo multi-argument diffInvariant not yet supported by TacticExtraction/BelleParser
//    db.proveBy(modelContent, tactic) shouldBe 'proved
    proveBy(KeYmaeraXProblemParser(modelContent), tactic) shouldBe 'proved
  }}

  "Example 2" should "be provable with master and custom loop invariant" in withMathematica { qeTool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example2.key")).mkString
    val Imply(_, Box(loop, _)) = KeYmaeraXProblemParser(modelContent)
    db.proveBy(modelContent, master(new ConfigurableGenerate(Map((loop, "v>=0".asFormula))))) shouldBe 'proved
  }}

  it should "be provable with master and loop invariant from file" in withMathematica { qeTool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example2.key")).mkString
    db.proveBy(modelContent, master()) shouldBe 'proved
  }}

  it should "be provable with abstract loop invariant" in withMathematica { qeTool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example2.key")).mkString

    val tactic = implyR('_) & (andL('_)*) & loop("J(v)".asFormula)('R) <(
      skip,
      skip,
      chase('R) & prop & OnAll(diffSolve()('R) partial) partial
      ) &
      US(UnificationMatch("J(v)".asFormula, "v>=0".asFormula).usubst) &
      OnAll(close | QE)

    //@todo tactic extraction/belle parser | combinator
    //db.proveBy(modelContent, tactic) shouldBe 'proved
    proveBy(KeYmaeraXProblemParser(modelContent), tactic) shouldBe 'proved
  }}

  "Example 3a" should "be provable with master and loop invariant from file" in withMathematica { tool => withDatabase { db =>
    // // needs evolution domain at time 0
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example3a.key")).mkString
    db.proveBy(modelContent, master()) shouldBe 'proved
  }}

  "Example3b" should "find correct safety condition" in withMathematica { tool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example3b.key")).mkString
    val tactic = implyR('_) & (andL('_)*) & chase('R) & normalize & OnAll(diffSolve()('R) partial) & print("Foo")
    val intermediate = db.proveBy(modelContent, tactic)
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

    val brake = proveBy(intermediate.subgoals(2), TactixLibrary.partialQE)
    brake.subgoals should have size 1
    brake.subgoals.head shouldBe Sequent(
      IndexedSeq(),
      // here is our evolution domain constraint (substitute t_ = v/B into S>= ... ) -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------v------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------v
      IndexedSeq("v_0<=0|v_0>0&(t_<=0|t_>0&(((B<=0|(0 < B&B < t_^-1*v_0)&((S < x_0|(x_0<=S&S < 1/2*(-1*B*t_^2+2*t_*v_0+2*x_0))&((x < 1/2*(-1*B*t_^2+2*t_*v_0+2*x_0)|x=1/2*(-1*B*t_^2+2*t_*v_0+2*x_0)&((v < -1*B*t_+v_0|v=-1*B*t_+v_0&((t__0 < 0|t__0=0&A<=0)|t__0>0))|v>-1*B*t_+v_0))|x>1/2*(-1*B*t_^2+2*t_*v_0+2*x_0)))|S>=1/2*(-1*B*t_^2+2*t_*v_0+2*x_0)))|B=t_^-1*v_0&((S < x_0|(x_0<=S&S < 1/2*(-1*B*t_^2+2*t_*v_0+2*x_0))&((x < 1/2*(-1*B*t_^2+2*t_*v_0+2*x_0)|x=1/2*(-1*B*t_^2+2*t_*v_0+2*x_0)&((v < 0|v=0&((t__0 < 0|t__0=0&A<=0)|t__0>0))|v>0))|x>1/2*(-1*B*t_^2+2*t_*v_0+2*x_0)))|S>=1/2*(-1*B*t_^2+2*t_*v_0+2*x_0)))|B>t_^-1*v_0))".asFormula))
  }}

  "Example 4a" should "be provable with master and loop invariant from file" in withMathematica { tool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example4a.key")).mkString
    db.proveBy(modelContent, master()) shouldBe 'proved
  }}

  "Example 4b" should "be provable with master and loop invariant from file" in withMathematica { tool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example4b.key")).mkString
    db.proveBy(modelContent, master()) shouldBe 'proved
  }}

  "Example 4c" should "be provable with master and loop invariant from file" in withMathematica { tool => withDatabase { db =>
    // needs evolution domain at time 0
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example4c.key")).mkString
    db.proveBy(modelContent, master()) shouldBe 'proved
  }}

  "Example 5 with simple control" should "be provable" in withMathematica { tool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example5_simplectrl.key")).mkString

    val plant = print("plant") & composeb('R) & assignb('R) &
      diffSolve(None)('R) & implyR('R)

    val tactic = implyR('R) & (andL('L)*) &
      loop("v >= 0 & x+v^2/(2*B) <= S".asFormula)('R) <(
      print("Base Case") & andR('R) & OnAll(closeId),
      print("Use Case") & QE,
      print("Step") & andL('L) & composeb('R) & assignb('R) & plant & QE
    )

    db.proveBy(modelContent, tactic) shouldBe 'proved
  }}

  it should "be provable automatically with Mathematica" in withMathematica { qeTool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example5_simplectrl.key")).mkString
    db.proveBy(modelContent, master()) shouldBe 'proved
  }}

  "Example 5" should "be provable automatically with Mathematica" in withMathematica { qeTool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example5.key")).mkString
    db.proveBy(modelContent, master()) shouldBe 'proved
  }}

  it should "be provable with chase etc" in withMathematica { tool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example5.key")).mkString

    val tactic = implyR('R) & (andL('L)*) &
      loop("v >= 0 & x+v^2/(2*B) <= S".asFormula)('R) <(
        printIndexed("Base case") & andR('R) & OnAll(closeId),
        printIndexed("Use case") & QE,
        printIndexed("Step") & chase('R) & normalize & printIndexed("Normalized") & OnAll(diffSolve()('R) partial) &
          printIndexed("After diffSolve") & OnAll(QE)
        )

    db.proveBy(modelContent, tactic) shouldBe 'proved
  }}

  ignore should "be provable with abstract loop invariant" in withMathematica { qeTool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example5.key"))

    val tactic = implyR('R) & (andL('L)*) &
      loop("J(v,x,B,S)".asFormula)('R) <(
        skip,
        skip,
        chase('R) & normalize & OnAll(diffSolve()('R) partial) partial
        ) &
      US(UnificationMatch("J(v,x,B,S)".asFormula, "v >= 0 & x+v^2/(2*B) <= S".asFormula).usubst) &
      OnAll(close | QE)

    proveBy(s, tactic) shouldBe 'proved
  }

  "Example 6" should "be provable automatically with Mathematica" in withMathematica { qeTool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example6.key")).mkString
    db.proveBy(modelContent, master()) shouldBe 'proved
  }}

  "Example 7" should "be provable automatically with Mathematica" in withMathematica { qeTool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example7.key")).mkString
    db.proveBy(modelContent, master()) shouldBe 'proved
  }}

  ignore /*"Example 8"*/ should "Example 8 be provable automatically with Mathematica" in withMathematica { qeTool =>
    // x' <= a*d
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example8.key"))
    proveBy(s, master()) shouldBe 'proved
  }

  "Example 9a" should "be provable" in withMathematica { tool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example9a.key")).mkString
    val tactic = implyR('R) & (andL('L)*) & diffInd('full)('R)
    db.proveBy(modelContent, tactic) shouldBe 'proved
  }}

  "Example 9b" should "be provable" in withMathematica { qeTool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example9b.key")).mkString

    val ode =
      // xr = (xm+S)/2
      diffInvariant("xm<=x".asFormula, "5/4*(x-(xm+S)/2)^2 + (x-(xm+S)/2)*v/2 + v^2/4 < ((S-xm)/2)^2".asFormula)('R) &
      diffWeaken('R)

    val tactic = implyR('R) & (andL('L)*) &
      loop("v >= 0 & xm <= x & xr = (xm + S)/2 & 5/4*(x-xr)^2 + (x-xr)*v/2 + v^2/4 < ((S - xm)/2)^2".asFormula)('R) <(
        print("Base case") & ((andR('R) <(closeId, skip))*) & closeId,
        print("Use case") & QE,
        print("Step") & (andL('L)*) & chase('R) & andR('R) <(
          allR('R) & (implyR('R)*) & ode & implyR('R) & (andL('L)*) & printIndexed("Foo") & QE,
          ode & printIndexed("Bar") & QE
        )
      )

    //@todo tactic extraction/parsing does not work for this example yet (could not retrieve executable 1 from the database. Caused by: 1)
    //db.proveBy(modelContent, tactic) shouldBe 'proved
    proveBy(KeYmaeraXProblemParser(modelContent), tactic) shouldBe 'proved
  }}

  "Example 10" should "be provable" in withMathematica { tool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example10.key")).mkString

    def ode(a: String) =
      diffCut("c>=0".asFormula)(1) & Idioms.<(
        diffCut("dx^2+dy^2=1".asFormula)(1) & Idioms.<(
          diffCut(s"v=old(v)+$a*c".asFormula)(1) & Idioms.<(
            diffCut(s"-c*(v-$a/2*c) <= y - old(y) & y - old(y) <= c*(v-$a/2*c)".asFormula)(1) & Idioms.<(
              skip,
              diffInd()(1)
            ),
            diffInd()(1)),
          diffInd()(1)),
        diffInd()(1)
        ) & exhaustiveEqR2L(hide=true)('Llast)*2 /* old(y)=y, old(v)=v */ & (andL('_)*) & diffWeaken('R)

    val tactic = implyR('R) & (andL('L)*) &
      loop("v >= 0 & dx^2+dy^2 = 1 & r != 0 & abs(y-ly) + v^2/(2*b) < lw".asFormula)('R) <(
        print("Base case") & speculativeQE,
        print("Use case") & speculativeQE,
        print("Step") & chase('R) & normalize & printIndexed("Normalized") <(
          printIndexed("Acc") & hideL(-9, "abs(y-ly)+v^2/(2*b) < lw".asFormula) & ode("a") &
            (alphaRule*) &
            printIndexed("Before replaceTransform") & replaceTransform("ep".asTerm, "c".asTerm)(-8) &
            prop & OnAll(speculativeQE),
          printIndexed("Stop") & ode("0") & prop & OnAll(speculativeQE),
          printIndexed("Brake") & ode("a") & prop & OnAll(speculativeQE)
          )
        )

    //@todo tactic extraction/belle parser | combinator problem?
    //db.proveBy(modelContent, tactic) shouldBe 'proved
    proveBy(KeYmaeraXProblemParser(modelContent), tactic) shouldBe 'proved
  }}

  it should "be provable with multi-arg diff. invariant" in withMathematica { tool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example10.key")).mkString

    def ode(a: String) = diffInvariant("c>=0".asFormula, "dx^2+dy^2=1".asFormula, s"v=old(v)+$a*c".asFormula,
      s"-c*(v-$a/2*c) <= y - old(y) & y - old(y) <= c*(v-$a/2*c)".asFormula)('R) &
      exhaustiveEqR2L(hide=true)('Llast)*2 /* old(y)=y, old(v)=v */ & (andL('_)*) & diffWeaken('R)

    val tactic = implyR('R) & (andL('L)*) &
      loop("v >= 0 & dx^2+dy^2 = 1 & r != 0 & abs(y-ly) + v^2/(2*b) < lw".asFormula)('R) <(
        print("Base case") & speculativeQE,
        print("Use case") & speculativeQE,
        print("Step") & chase('R) & normalize & printIndexed("Normalized") <(
          printIndexed("Acc") & hideL(-9, "abs(y-ly)+v^2/(2*b) < lw".asFormula) & ode("a") &
            (alphaRule*) &
            printIndexed("Before replaceTransform") & replaceTransform("ep".asTerm, "c".asTerm)(-8) &
            prop & OnAll(speculativeQE),
          printIndexed("Stop") & ode("0") & prop & OnAll(speculativeQE),
          printIndexed("Brake") & ode("a") & prop & OnAll(speculativeQE)
          )
        )

    //@todo proves correctly, but doesn't extract correctly (multi-argument diffInvariant)
    //db.proveBy(modelContent, tactic) shouldBe 'proved
    proveBy(KeYmaeraXProblemParser(modelContent), tactic) shouldBe 'proved
  }}

}
