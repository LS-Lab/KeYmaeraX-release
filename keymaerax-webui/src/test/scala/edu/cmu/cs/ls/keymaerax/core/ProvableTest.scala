/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/

package edu.cmu.cs.ls.keymaerax.core

import edu.cmu.cs.ls.keymaerax.btactics.RandomFormula
import edu.cmu.cs.ls.keymaerax.tags.{CheckinTest, SummaryTest}
import testHelper.KeYmaeraXTestTags._

import scala.collection.immutable._
import edu.cmu.cs.ls.keymaerax.core._
import org.scalatest.{FlatSpec, Matchers, TagAnnotation}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig

/**
 * Test Provable constructions
 * @author Andre Platzer
  * @todo more exhaustive tests needed
 */
@CheckinTest
@SummaryTest
class ProvableTest extends FlatSpec with Matchers {
  "Provable" should "close trivial proofs" in {
    import scala.collection.immutable._
    val verum = new Sequent(IndexedSeq(), IndexedSeq(True))
    // conjecture
    val provable = ProvableSig.startProof(verum)
    // construct a proof
    val proving = provable(CloseTrue(SuccPos(0)), 0)
    // check if proof successful
    if (proving.isProved) println("Successfully proved " + proving.proved)
    proving.isProved should be (true)
  }

  it should "glue trivial proofs forward" in {
    import scala.collection.immutable._
    val verum = new Sequent(IndexedSeq(), IndexedSeq(True))
    // conjecture
    val provable = ProvableSig.startProof(verum)
    // construct a proof
    val proving = provable(CloseTrue(SuccPos(0)), 0)
    // check if proof successful
    if (proving.isProved) println("Successfully proved " + proving.proved)
    proving.isProved should be (true)

    val more = new Sequent(IndexedSeq(), IndexedSeq(Imply(Greater(Variable("x"), Number(5)), True)))
    // another conjecture
    val moreProvable = ProvableSig.startProof(more)
    // construct another (partial) proof
    val moreProving = moreProvable(ImplyRight(SuccPos(0)), 0)(HideLeft(AntePos(0)), 0)
    moreProving.isProved should be (false)
    // merge proofs by gluing their Provables together
    val mergedProving = moreProving(proving, 0)
    // check if proof successful
    if (mergedProving.isProved) println("Successfully proved " + mergedProving.proved)
    mergedProving.isProved should be (true)
  }

  it should "glue trivial proofs backward" in {
    import scala.collection.immutable._
    val more = new Sequent(IndexedSeq(), IndexedSeq(Imply(Greater(Variable("x"), Number(5)), True)))
    // another conjecture
    val moreProvable = ProvableSig.startProof(more)
    // construct another (partial) proof
    val moreProving = moreProvable(ImplyRight(SuccPos(0)), 0)(HideLeft(AntePos(0)), 0)
    moreProving.isProved should be (false)

    val verum = new Sequent(IndexedSeq(), IndexedSeq(True))
    // conjecture
    val provable = ProvableSig.startProof(verum)
    // construct a proof
    val proving = provable(CloseTrue(SuccPos(0)), 0)
    // check if proof successful
    if (proving.isProved) println("Successfully proved " + proving.proved)
    proving.isProved should be (true)

    // merge proofs by gluing their Provables together
    val mergedProving = moreProving(proving, 0)
    // check if proof successful
    if (mergedProving.isProved) println("Successfully proved " + mergedProving.proved)
    mergedProving.isProved should be (true)
  }

/**
 * Proves in a tableaux-style goal-directed backward sequent order:
 * {{{
 *                      *
 *                 ----------- CloseTrue
 *     *               |- true
 * ----------ax    ----------- WL
 * x>0 |- x>0      x>0 |- true
 * ---------------------------- &R
 *     x>0  |-  x>0 & true
 * ---------------------------- ->R
 *     |-  x>0 ->  x>0 & true
 * }}}
 */
  it should "do proofs in backward sequent order of x>0 -> x>0 & true" in {
    import scala.collection.immutable._
    val fm = Greater(Variable("x"), Number(5))
    // |- x>5 -> x>5 & true
    val finGoal = new Sequent(IndexedSeq(), IndexedSeq(Imply(fm, And(fm, True))))
    // conjecture
    val finProvable = ProvableSig.startProof(finGoal)
    // construct a proof
    val proof = finProvable(
      ImplyRight(SuccPos(0)), 0)(
        AndRight(SuccPos(0)), 0)(
        HideLeft(AntePos(0)), 1)(
        CloseTrue(SuccPos(0)), 1)(
        Close(AntePos(0), SuccPos(0)), 0)
    proof.isProved should be (true)
    proof.proved should be (finGoal)
  }

  /**
   * Proves in a forward Hilbert-style order:
   * {{{
   *                      *
   *                 ----------- CloseTrue
   *     *               |- true
   * ----------ax    ----------- WL
   * x>0 |- x>0      x>0 |- true
   * ---------------------------- &R
   *     x>0  |-  x>0 & true
   * ---------------------------- ->R
   *     |-  x>0 ->  x>0 & true
   * }}}
   */
  it should "glue proofs in forward Hilbert order of x>0 -> x>0 & true" in {
    import scala.collection.immutable._
    val fm = Greater(Variable("x"), Number(5))
    // x>0 |- x>0
    val left = ProvableSig.startProof(Sequent(IndexedSeq(fm), IndexedSeq(fm)))(
      Close(AntePos(0), SuccPos(0)), 0)
    // |- true
    val right = ProvableSig.startProof(Sequent(IndexedSeq(), IndexedSeq(True)))(
      CloseTrue(SuccPos(0)), 0)
    val right2 = ProvableSig.startProof(Sequent(IndexedSeq(fm), IndexedSeq(True)))(
      HideLeft(AntePos(0)), 0) (right, 0)
    val merged = ProvableSig.startProof(Sequent(IndexedSeq(fm), IndexedSeq(And(fm, True))))(
      AndRight(SuccPos(0)), 0) (
      left, 0)(
        right2, 0)
    // gluing order irrelevant
    merged should be (ProvableSig.startProof(Sequent(IndexedSeq(fm), IndexedSeq(And(fm, True))))(
      AndRight(SuccPos(0)), 0) (
      right2, 1)(
        left, 0))
    // |- x>5 -> x>5 & true
    val finGoal = new Sequent(IndexedSeq(), IndexedSeq(Imply(fm, And(fm, True))))
    val proof = ProvableSig.startProof(finGoal)(
      ImplyRight(SuccPos(0)), 0) (merged, 0)
    proof.isProved should be (true)
    proof.proved should be (finGoal)
  }

  /**
   * Proves in a direct forward Hilbert-style order:
   * {{{
   *                      *
   *                 ----------- CloseTrue
   *     *               |- true
   * ----------ax    ----------- WL
   * x>0 |- x>0      x>0 |- true
   * ---------------------------- &R
   *     x>0  |-  x>0 & true
   * ---------------------------- ->R
   *     |-  x>0 ->  x>0 & true
   * }}}
   */
  it should "forward proofs in Hilbert order of x>0 -> x>0 & true (direct)" in {
    import scala.collection.immutable._
    val fm = Greater(Variable("x"), Number(5))
    // proof of x>5 |- x>5 & true merges left and right branch by AndRight
    val proof = ProvableSig.startProof(Sequent(IndexedSeq(fm), IndexedSeq(And(fm, True))))(
      AndRight(SuccPos(0)), 0) (
      // left branch: x>5 |- x>5
      ProvableSig.startProof(Sequent(IndexedSeq(fm), IndexedSeq(fm)))(
        Close(AntePos(0), SuccPos(0)), 0),
      0)(
        //right branch: |- true
        ProvableSig.startProof(Sequent(IndexedSeq(), IndexedSeq(True)))(
          CloseTrue(SuccPos(0)), 0)(
            // x>5 |- true
            Sequent(IndexedSeq(fm), IndexedSeq(True)), HideLeft(AntePos(0))),
        0)(
        // |- x>5 -> x>5 & true
        new Sequent(IndexedSeq(), IndexedSeq(Imply(fm, And(fm, True)))),
        ImplyRight(SuccPos(0))
      )
    proof.isProved should be (true)
    proof.proved should be (new Sequent(IndexedSeq(), IndexedSeq(Imply(fm, And(fm, True)))))
  }

  /**
   * Proves in a mixed yoyo order both forward and backward and up and down.
   * {{{
   *                      *
   *                 ----------- CloseTrue
   *     *               |- true
   * ----------ax    ----------- WL
   * x>0 |- x>0      x>0 |- true
   * ---------------------------- &R
   *     x>0  |-  x>0 & true
   * ---------------------------- ->R
   *     |-  x>0 ->  x>0 & true
   * }}}
   * in the mixed order:
   * &R, WL
   * CloseTrue
   * ->R
   * ax
   */
  it should "glue proofs in mixed yoyo order of x>0 -> x>0 & true" in {
    import scala.collection.immutable._
    val fm = Greater(Variable("x"), Number(5))
    // x>5  |-  x>5 & true
    val mid = new Sequent(IndexedSeq(fm), IndexedSeq(And(fm, True)))
    // middle conjecture
    val midProvable = ProvableSig.startProof(mid)
    // construct a middle proof
    val midProof: ProvableSig = midProvable/*(ImplyRight(SuccPos(0)), 0)*/(
      AndRight(SuccPos(0)), 0)(
      HideLeft(AntePos(0)), 1)
    midProof.isProved should be (false)
    // right conjecture: True
    val right = new Sequent(IndexedSeq(), IndexedSeq(True))
    val rightProvable = ProvableSig.startProof(right)
    rightProvable.isProved should be (false)
    // construct a right proof
    val rightProof = rightProvable(CloseTrue(SuccPos(0)), 0)
    rightProof.isProved should be (true)
    // merge right proof into right branch of middle proof
    val mergeMidRight = midProof(rightProof, 1)
    mergeMidRight.isProved should be (false)
    // could finish proof of mid now
    val precloseProof = mergeMidRight(Close(AntePos(0), SuccPos(0)), 0)
    precloseProof.isProved should be (true)
    precloseProof.proved should be (mid)
    // add to the bottom of the proof
    // final conjecture: |- x>5 -> x>5&true
    val finGoal = new Sequent(IndexedSeq(), IndexedSeq(Imply(fm, And(fm, True))))
    val fin = ProvableSig.startProof(finGoal)
    // glue mergeMidRight intermediate proof forward as the partial proof of fin
    val finProof = fin(ImplyRight(SuccPos(0)), 0) (mergeMidRight, 0)
    finProof.isProved should be (false)
    finProof.subgoals.length should be (1)
    // finish remaining proof by proving remaining left goal
    val proved = finProof(Close(AntePos(0), SuccPos(0)), 0)
    proved.isProved should be (true)
    proved.proved should be (finGoal)
  }

  it should "not close different formulas by identity" in {
    import scala.collection.immutable._
    val fm = Greater(Variable("x"), Number(5))
    val fm1 = Less(Variable("x"), Number(5))
    // x>5 |- x>5
    val finGoal = new Sequent(IndexedSeq(fm), IndexedSeq(fm))
    val finProof = ProvableSig.startProof(finGoal)(
      Close(AntePos(0), SuccPos(0)), 0
    )
    finProof.isProved should be (true)
    finProof.proved should be (finGoal)
    // x<5 |- x>5
    val noGoal = new Sequent(IndexedSeq(fm1), IndexedSeq(fm))
    a [CoreException] shouldBe thrownBy(ProvableSig.startProof(noGoal)(
      Close(AntePos(0), SuccPos(0)), 0
    ))
  }

  "Forward Provable" should "continue correct consequence but refuse incorrect consequence" in {
    import scala.collection.immutable._
    val fm = Greater(Variable("x"), Number(5))
    // x>5 |- x>5 & true
    val finGoal = new Sequent(IndexedSeq(fm), IndexedSeq(And(fm, True)))
    // conjecture
    val finProvable = ProvableSig.startProof(finGoal)
    // construct a proof
    val proof = finProvable(
      AndRight(SuccPos(0)), 0)(
      HideLeft(AntePos(0)), 1)(
      CloseTrue(SuccPos(0)), 1)(
      Close(AntePos(0), SuccPos(0)), 0)
    proof.isProved should be (true)
    proof.proved should be (finGoal)

    // prolong forward
    // x>5 |- x>5 & true
    val goal = new Sequent(IndexedSeq(), IndexedSeq(Imply(fm, And(fm, True))))
    val finProof = proof(goal, ImplyRight(SuccPos(0)))
    finProof.isProved should be (true)
    finProof.proved should be (goal)
    // incorrectly prolong forward
    a [MatchError /*| CoreException*/] shouldBe thrownBy(proof(goal, AndRight(SuccPos(0))))
    a [MatchError /*| CoreException*/] shouldBe thrownBy(proof(goal, OrRight(SuccPos(0))))
    a [MatchError /*| CoreException*/] shouldBe thrownBy(proof(new Sequent(IndexedSeq(), IndexedSeq(Equiv(fm, And(fm, True)))), ImplyRight(SuccPos(0))))
    a [CoreException] shouldBe thrownBy(proof(new Sequent(IndexedSeq(), IndexedSeq(Imply(False, And(fm, True)))), ImplyRight(SuccPos(0))))
    a [CoreException] shouldBe thrownBy(proof(new Sequent(IndexedSeq(), IndexedSeq(Imply(fm, And(True, fm)))), ImplyRight(SuccPos(0))))
  }

  "Individual proof rules" should "refuse Skolemization clashes" in {
    println("Testing " + Skolemize(SuccPos(0)))
    val goal = ProvableSig.startProof(Sequent(IndexedSeq("p(x)".asFormula), IndexedSeq("\\forall x p(x)".asFormula)))
    a [SkolemClashException] shouldBe thrownBy (goal(Skolemize(SuccPos(0)), 0))
    val goal2 = ProvableSig.startProof(Sequent(IndexedSeq("x>=0".asFormula), IndexedSeq("\\forall x p(x)".asFormula)))
    a [SkolemClashException] shouldBe thrownBy (goal2(Skolemize(SuccPos(0)), 0))
    val goal3 = ProvableSig.startProof(Sequent(IndexedSeq("x>=0".asFormula), IndexedSeq("\\forall x x>=0".asFormula)))
    a [SkolemClashException] shouldBe thrownBy (goal3(Skolemize(SuccPos(0)), 0))
    val goal4 = ProvableSig.startProof(Sequent(IndexedSeq(), IndexedSeq("\\forall x x>=0".asFormula, "x<=0".asFormula)))
    a [SkolemClashException] shouldBe thrownBy (goal4(Skolemize(SuccPos(0)), 0))
  }

  it should "refuse bound renaming except at bound occurrences" in {
    val rens = BoundRenaming(Variable("y"),Variable("x"),SuccPos(0))
    println("Testing " + rens)
//    val goal = Provable.startProof(Sequent(Nil, IndexedSeq("p(y)".asFormula), IndexedSeq("\\forall y p(y)".asFormula)))
//    a [CoreException] shouldBe thrownBy (goal(rens, 0))
    val goal2 = ProvableSig.startProof(Sequent(IndexedSeq("p(x)".asFormula), IndexedSeq("x>=9".asFormula)))
    a [RenamingClashException] shouldBe thrownBy (goal2(BoundRenaming(Variable("x"),Variable("y"),SuccPos(0)), 0))
    val goal3 = ProvableSig.startProof(Sequent(IndexedSeq("p(x)".asFormula), IndexedSeq("p(x)".asFormula)))
    a [RenamingClashException] shouldBe thrownBy (goal3(rens, 0))
    val goal4 = ProvableSig.startProof(Sequent(IndexedSeq("p(x)".asFormula), IndexedSeq("[y:=9;z:=0;]z>=10".asFormula)))
    a [RenamingClashException] shouldBe thrownBy (goal4(rens, 0))
    val goal5 = ProvableSig.startProof(Sequent(IndexedSeq("p(x)".asFormula), IndexedSeq("[{y'=9}]y>=10".asFormula)))
    a [RenamingClashException] shouldBe thrownBy (goal5(rens, 0))
  }

  it should "report bound renaming clashes" in {
    val rens = BoundRenaming(Variable("y"),Variable("x"),SuccPos(0))
    val goal = ProvableSig.startProof(Sequent(IndexedSeq("true".asFormula), IndexedSeq("\\forall y y>=x".asFormula)))
    a [RenamingClashException] shouldBe thrownBy (goal(rens, 0))
  }

  //@todo all rules should have different toString
}
