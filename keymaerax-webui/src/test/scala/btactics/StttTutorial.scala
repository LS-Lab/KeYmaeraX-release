/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.bellerophon.{OnAll, UnificationMatch}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.DebuggingTactics.{print, printIndexed}
import edu.cmu.cs.ls.keymaerax.btactics.ArithmeticSimplification._
import edu.cmu.cs.ls.keymaerax.btactics.arithmetic.speculative.ArithmeticSpeculativeSimplification._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXProblemParser
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.SlowTest
import testHelper.KeYmaeraXTestTags.TodoTest
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
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example1.kyx")).mkString
    val tactic = implyR('_) & andL('_) & DC("v>=0".asFormula)(1) <(
      /* use */ diffWeaken(1) & prop,
      /* show */ diffInd()(1)
      )
    db.proveBy(modelContent, tactic) shouldBe 'proved
  }}

  it should "be provable from parsed tactic" in withMathematica { qeTool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example1.kyx")).mkString
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example1.kyt")).mkString)
    db.proveBy(modelContent, tactic) shouldBe 'proved
  }}

  it should "be provable from parsed tactic with Z3" in withZ3 { qeTool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example1.kyx")).mkString
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example1.kyt")).mkString)
    db.proveBy(modelContent, tactic) shouldBe 'proved
  }}

  it should "be provable with diffSolve" in withMathematica { qeTool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example1.kyx")).mkString
    val tactic = implyR('_) & andL('_) & diffSolve(1) & QE
    db.proveBy(modelContent, tactic) shouldBe 'proved
  }}

  it should "be provable with master" in withMathematica { qeTool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example1.kyx")).mkString
    db.proveBy(modelContent, master()) shouldBe 'proved
  }}

  it should "be provable with diffInvariant" in withMathematica { qeTool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example1.kyx")).mkString
    val tactic = implyR('_) & andL('_) & diffInvariant("v>=0".asFormula)('R) & diffWeaken('R) & prop
    db.proveBy(modelContent, tactic) shouldBe 'proved
  }}

  "Example 1a" should "be provable" in withMathematica { qeTool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example1a.kyx")).mkString
    val tactic = implyR('_) & (andL('_)*) & diffCut("v>=0".asFormula)(1) & Idioms.<(
      diffCut("x>=old(x)".asFormula)(1) & Idioms.<(
        diffWeaken(1) & exhaustiveEqL2R('L, "x0=x_0".asFormula) & prop,
        diffInd()(1)
      ),
      diffInd()(1)
    )

    db.proveBy(modelContent, tactic) shouldBe 'proved
  }}

  it should "be provable with multi-arg invariant" in withMathematica { qeTool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example1a.kyx")).mkString
    val tactic = implyR('_) & (andL('_)*) & diffInvariant("v>=0".asFormula, "x>=old(x)".asFormula)(1) &
      diffWeaken(1) & exhaustiveEqL2R('L, "x0=x_0".asFormula) & prop

    //@todo multi-argument diffInvariant not yet supported by TacticExtraction/BelleParser
//    db.proveBy(modelContent, tactic) shouldBe 'proved
    proveBy(KeYmaeraXProblemParser(modelContent), tactic) shouldBe 'proved
  }}

  "Example 2" should "be provable with master and custom loop invariant" in withMathematica { qeTool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example2.kyx")).mkString
    val Imply(_, Box(loop, _)) = KeYmaeraXProblemParser(modelContent)
    db.proveBy(modelContent, master(new ConfigurableGenerator(Map((loop, "v>=0".asFormula))))) shouldBe 'proved
  }}

  it should "be provable with master and loop invariant from file" in withMathematica { qeTool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example2.kyx")).mkString
    db.proveBy(modelContent, master()) shouldBe 'proved
  }}

  it should "be provable with abstract loop invariant" taggedAs(TodoTest) ignore withMathematica { qeTool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example2.kyx")).mkString

    val tactic = implyR('_) & (andL('_)*) & loop("J(v)".asFormula)('R) <(
      skip,
      skip,
      chase('R) & prop & OnAll(diffSolve('R) partial) partial
      ) &
      US(UnificationMatch("J(v)".asFormula, "v>=0".asFormula).usubst) &
      OnAll(close | QE)

    //@todo Rewrite the US tactic in terms of the Bellerophon language, not arbitrary scala code.
    db.proveBy(modelContent, tactic) shouldBe 'proved
  }}

  it should "be provable from parsed tactic" in withMathematica { qeTool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example2.kyx")).mkString
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example2.kyt")).mkString)
    db.proveBy(modelContent, tactic) shouldBe 'proved
  }}

  it should "be provable from parsed tactic with Z3" in withZ3 { qeTool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example2.kyx")).mkString
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example2.kyt")).mkString)
    db.proveBy(modelContent, tactic) shouldBe 'proved
  }}

  "Example 3a" should "be provable with master and loop invariant from file" in withMathematica { tool => withDatabase { db =>
    // // needs evolution domain at time 0
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example3a.kyx")).mkString
    db.proveBy(modelContent, master()) shouldBe 'proved
  }}

  it should "be provable from parsed tactic" in withMathematica { qeTool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example3a.kyx")).mkString
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example3a.kyt")).mkString)
    db.proveBy(modelContent, tactic) shouldBe 'proved
  }}

  it should "be provable from parsed tactic with Z3" in withZ3 { qeTool => withDatabase { db =>
    //@todo ODE does not have time at the point where we're asking the integrator
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example3a.kyx")).mkString
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example3a.kyt")).mkString)
    db.proveBy(modelContent, tactic) shouldBe 'proved
  }}

  "Example3b" should "find correct safety condition" in withMathematica { tool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example3b.kyx")).mkString
    val tactic = implyR('_) & (andL('_)*) & chase('R) & normalize & OnAll(diffSolve('R))
    val intermediate = db.proveBy(modelContent, tactic)
    intermediate.subgoals should have size 3
    intermediate.subgoals(0) shouldBe Sequent(
      IndexedSeq("v>=0".asFormula, "A>0".asFormula, "B>0".asFormula, "true".asFormula, "x<=S".asFormula, "true".asFormula),
      IndexedSeq("\\forall t_ (t_>=0 -> \\forall s_ (0<=s_ & s_<=t_ -> A*s_+v>=0) -> A/2*t_^2+v*t_+x<=S)".asFormula))
    intermediate.subgoals(1) shouldBe Sequent(
      IndexedSeq("v>=0".asFormula, "A>0".asFormula, "B>0".asFormula, "true".asFormula, "x<=S".asFormula, "v=0".asFormula),
      IndexedSeq("\\forall t_ (t_>=0 -> \\forall s_ (0<=s_ & s_<=t_ -> v>=0) -> v*t_+x<=S)".asFormula))
    intermediate.subgoals(2) shouldBe Sequent(
      IndexedSeq("v>=0".asFormula, "A>0".asFormula, "B>0".asFormula, "true".asFormula, "x<=S".asFormula),
      IndexedSeq("\\forall t_ (t_>=0 -> \\forall s_ (0<=s_ & s_<=t_ -> (-B)*s_+v>=0) -> (-B)/2*t_^2+v*t_+x<=S)".asFormula))

    val brake = proveBy(intermediate.subgoals(2), TactixLibrary.partialQE)
    brake.subgoals should have size 1
    brake.subgoals.head shouldBe Sequent(
      IndexedSeq(),
      // here is our evolution domain constraint -------------------------------------------------------------------v
      IndexedSeq("(S < x|S=x&(v<=0|v>0&(B<=0|B>0&A<=0)))|S>x&(v<=0|v>0&((B<=0|(0 < B&B < v^2*(2*S+-2*x)^-1)&A<=0)|B>=v^2*(2*S+-2*x)^-1))".asFormula))
  }}

  it should "stop at correct spot when tactic is parsed from file" in withMathematica { tool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example3b.kyx")).mkString
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example3b.kyt")).mkString)
    val intermediate = db.proveBy(modelContent, tactic)
    intermediate.subgoals should have size 3
    intermediate.subgoals(0) shouldBe Sequent(
      IndexedSeq("v>=0".asFormula, "A>0".asFormula, "B>0".asFormula, "true".asFormula, "x<=S".asFormula, "true".asFormula),
      IndexedSeq("\\forall t_ (t_>=0 -> \\forall s_ (0<=s_ & s_<=t_ -> A*s_+v>=0) -> A/2*t_^2+v*t_+x<=S)".asFormula))
    intermediate.subgoals(1) shouldBe Sequent(
      IndexedSeq("v>=0".asFormula, "A>0".asFormula, "B>0".asFormula, "true".asFormula, "x<=S".asFormula, "v=0".asFormula),
      IndexedSeq("\\forall t_ (t_>=0 -> \\forall s_ (0<=s_ & s_<=t_ -> v>=0) -> v*t_+x<=S)".asFormula))
    intermediate.subgoals(2) shouldBe Sequent(
      IndexedSeq("v>=0".asFormula, "A>0".asFormula, "B>0".asFormula, "true".asFormula, "x<=S".asFormula),
      IndexedSeq("\\forall t_ (t_>=0 -> \\forall s_ (0<=s_ & s_<=t_ -> (-B)*s_+v>=0) -> (-B)/2*t_^2+v*t_+x<=S)".asFormula))
  }}

  "Example 4a" should "be provable with master and loop invariant from file" in withMathematica { tool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example4a.kyx")).mkString
    db.proveBy(modelContent, master()) shouldBe 'proved
  }}

  it should "be provable from parsed tactic" in withMathematica { qeTool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example4a.kyx")).mkString
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example4a.kyt")).mkString)
    db.proveBy(modelContent, tactic) shouldBe 'proved
  }}

  it should "be provable from parsed tactic with Z3" in withZ3 { qeTool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example4a.kyx")).mkString
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example4a.kyt")).mkString)
    db.proveBy(modelContent, tactic) shouldBe 'proved
  }}

  "Example 4b" should "be provable with master and loop invariant from file" in withMathematica { tool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example4b.kyx")).mkString
    db.proveBy(modelContent, master()) shouldBe 'proved
  }}

  it should "be provable from parsed tactic" in withMathematica { qeTool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example4b.kyx")).mkString
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example4b.kyt")).mkString)
    db.proveBy(modelContent, tactic) shouldBe 'proved
  }}

  it should "be provable from parsed tactic with Z3" in withZ3 { qeTool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example4b.kyx")).mkString
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example4b.kyt")).mkString)
    db.proveBy(modelContent, tactic) shouldBe 'proved
  }}

  "Example 4c" should "be provable with master and loop invariant from file" in withMathematica { tool => withDatabase { db =>
    // needs evolution domain at time 0
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example4c.kyx")).mkString
    db.proveBy(modelContent, master()) shouldBe 'proved
  }}

  it should "be provable from parsed tactic" in withMathematica { qeTool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example4c.kyx")).mkString
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example4c.kyt")).mkString)
    db.proveBy(modelContent, tactic) shouldBe 'proved
  }}

  it should "be provable from parsed tactic with Z3" in withZ3 { qeTool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example4c.kyx")).mkString
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example4c.kyt")).mkString)
    db.proveBy(modelContent, tactic) shouldBe 'proved
  }}

  "Example 5 with simple control" should "be provable" in withMathematica { tool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example5_simplectrl.kyx")).mkString

    val plant = print("plant") & composeb('R) & assignb('R) & diffSolve('R)

    val tactic = implyR('R) & (andL('L)*) &
      loop("v >= 0 & x+v^2/(2*B) <= S".asFormula)('R) <(
      print("Base Case") & andR('R) & OnAll(closeId),
      print("Use Case") & QE,
      print("Step") & andL('L) & composeb('R) & assignb('R) & plant & QE
    )

    db.proveBy(modelContent, tactic) shouldBe 'proved
  }}

  it should "be provable automatically with Mathematica" in withMathematica { qeTool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example5_simplectrl.kyx")).mkString
    db.proveBy(modelContent, master()) shouldBe 'proved
  }}

  "Example 5" should "be provable automatically with Mathematica" in withMathematica { qeTool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example5.kyx")).mkString
    db.proveBy(modelContent, master()) shouldBe 'proved
  }}

  it should "be provable from parsed tactic" in withMathematica { qeTool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example5.kyx")).mkString
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example5.kyt")).mkString)
    db.proveBy(modelContent, tactic) shouldBe 'proved
  }}

  it should "be provable from parsed tactic with Z3" in withZ3 { qeTool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example5.kyx")).mkString
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example5.kyt")).mkString)
    db.proveBy(modelContent, tactic) shouldBe 'proved
  }}

  it should "be provable with chase etc" in withMathematica { tool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example5.kyx")).mkString

    val tactic = implyR('R) & (andL('L)*) &
      loop("v >= 0 & x+v^2/(2*B) <= S".asFormula)('R) <(
        printIndexed("Base case") & andR('R) & OnAll(closeId),
        printIndexed("Use case") & QE,
        printIndexed("Step") & chase('R) & printIndexed("After chase") & normalize & printIndexed("Normalized") & OnAll(diffSolve('R) partial) &
          printIndexed("After diffSolve") & OnAll(QE)
        )

    db.proveBy(modelContent, tactic) shouldBe 'proved
  }}

  it should "be provable with abstract loop invariant" ignore withMathematica { qeTool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example5.kyx"))

    val tactic = implyR('R) & (andL('L)*) &
      loop("J(v,x,B,S)".asFormula)('R) <(
        skip,
        skip,
        chase('R) & normalize & OnAll(diffSolve('R) partial) partial
        ) &
      US(UnificationMatch("J(v,x,B,S)".asFormula, "v >= 0 & x+v^2/(2*B) <= S".asFormula).usubst) &
      OnAll(close | QE)

    proveBy(s, tactic) shouldBe 'proved
  }

  "Example 6" should "be provable automatically with Mathematica" in withMathematica { qeTool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example6.kyx")).mkString
    db.proveBy(modelContent, master()) shouldBe 'proved
  }}

  it should "be provable from parsed tactic" in withMathematica { qeTool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example6.kyx")).mkString
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example6.kyt")).mkString)
    db.proveBy(modelContent, tactic) shouldBe 'proved
  }}

  it should "be provable from parsed tactic with Z3" in withZ3 { qeTool => withDatabase { db =>
    //@todo Integrator finds the wrong time (ODE has user-defined t' and our internal t_' that we always add)
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example6.kyx")).mkString
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example6.kyt")).mkString)
    db.proveBy(modelContent, tactic) shouldBe 'proved
  }}

  "Example 7" should "be provable automatically with Mathematica" in withMathematica { qeTool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example7.kyx")).mkString
    db.proveBy(modelContent, master()) shouldBe 'proved
  }}

  it should "be provable from parsed tactic" in withMathematica { qeTool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example7.kyx")).mkString
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example7.kyt")).mkString)
    db.proveBy(modelContent, tactic) shouldBe 'proved
  }}

  it should "be provable from parsed tactic with Z3" in withZ3 { qeTool => withDatabase { db =>
    //@todo Integrator finds the wrong time (ODE has user-defined t' and our internal t_' that we always add)
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example7.kyx")).mkString
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example7.kyt")).mkString)
    db.proveBy(modelContent, tactic) shouldBe 'proved
  }}

  "Example 8" should "be provable automatically with Mathematica" ignore withMathematica { qeTool =>
    // x' <= a*d
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example8.kyx"))
    proveBy(s, master()) shouldBe 'proved
  }

  "Example 9a" should "be provable" in withMathematica { tool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example9a.kyx")).mkString
    val tactic = implyR('R) & (andL('L)*) & diffInd('full)('R)
    db.proveBy(modelContent, tactic) shouldBe 'proved
  }}

  it should "be provable from parsed tactic" in withMathematica { qeTool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example9a.kyx")).mkString
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example9a.kyt")).mkString)
    db.proveBy(modelContent, tactic) shouldBe 'proved
  }}

  it should "be provable from parsed tactic with Z3" in withZ3 { qeTool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example9a.kyx")).mkString
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example9a.kyt")).mkString)
    db.proveBy(modelContent, tactic) shouldBe 'proved
  }}

  "Example 9b" should "be provable" in withMathematica { qeTool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example9b.kyx")).mkString

    val ode =
      // xr = (xm+S)/2
      diffInvariant("xm<=x".asFormula)('R) &
      diffInvariant("5/4*(x-(xm+S)/2)^2 + (x-(xm+S)/2)*v/2 + v^2/4 < ((S-xm)/2)^2".asFormula)('R) &
      diffWeaken('R)

    val tactic = implyR('R) & (andL('L)*) &
      loop("v >= 0 & xm <= x & xr = (xm + S)/2 & 5/4*(x-xr)^2 + (x-xr)*v/2 + v^2/4 < ((S - xm)/2)^2".asFormula)('R) <(
        print("Base case") & ((andR('R) <(closeId, skip))*) & closeId,
        print("Use case") & QE,
        print("Step") & (andL('L)*) & chase('R) & andR('R) <(
          allR('R) & (implyR('R)*) & ode & implyR('R) & (andL('L)*) & printIndexed("Foo") & QE,
          implyR('R) & ode & printIndexed("Bar") & QE
        )
      )

    db.proveBy(modelContent, tactic) shouldBe 'proved
  }}

  it should "be provable from parsed tactic" in withMathematica { qeTool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example9b.kyx")).mkString
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example9b.kyt")).mkString)
    db.proveBy(modelContent, tactic) shouldBe 'proved
  }}

  it should "be provable from parsed tactic with Z3" in withZ3 { qeTool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example9b.kyx")).mkString
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example9b.kyt")).mkString)
    db.proveBy(modelContent, tactic) shouldBe 'proved
  }}

  "Example 10" should "be provable" in withMathematica { tool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example10.kyx")).mkString

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
        ) & (andL('L)*) & diffWeaken('R)

    val tactic = implyR('R) & (andL('L)*) &
      loop("v >= 0 & dx^2+dy^2 = 1 & r != 0 & abs(y-ly) + v^2/(2*b) < lw".asFormula)('R) <(
        print("Base case") & speculativeQE,
        print("Use case") & speculativeQE,
        print("Step") & chase('R) & normalize & printIndexed("Normalized") <(
          //@todo position assertions not yet stored and extracted
          printIndexed("Acc") & hideL(-9/*, "abs(y-ly)+v^2/(2*b) < lw".asFormula*/) & ode("a") &
            (alphaRule*) &
            printIndexed("Before replaceTransform") & replaceTransform("ep".asTerm, "c".asTerm)(-8) &
            prop & OnAll(speculativeQE),
          printIndexed("Stop") & ode("0") & prop & OnAll(speculativeQE),
          printIndexed("Brake") & ode("a") & prop & OnAll(speculativeQE)
          )
        )

    db.proveBy(modelContent, tactic) shouldBe 'proved
  }}

  it should "be provable with multi-arg diff. invariant" in withMathematica { tool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example10.kyx")).mkString

    def ode(a: String) = diffInvariant("c>=0".asFormula, "dx^2+dy^2=1".asFormula, s"v=old(v)+$a*c".asFormula,
      s"-c*(v-$a/2*c) <= y - old(y) & y - old(y) <= c*(v-$a/2*c)".asFormula)('R) & diffWeaken('R)

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

    //@todo multi-argument diffInvariant not yet supported by TacticExtraction/BelleParser
    //db.proveBy(modelContent, tactic) shouldBe 'proved
    proveBy(KeYmaeraXProblemParser(modelContent), tactic) shouldBe 'proved
  }}

  it should "be provable from parsed tactic" in withMathematica { qeTool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example10.kyx")).mkString
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example10.kyt")).mkString)
    db.proveBy(modelContent, tactic) shouldBe 'proved
  }}

  it should "be provable from parsed tactic with Z3" in withZ3 { qeTool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example10.kyx")).mkString
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example10.kyt")).mkString)
    db.proveBy(modelContent, tactic) shouldBe 'proved
  }}

}
