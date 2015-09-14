/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/

import testHelper.KeYmaeraXTestTags._

import scala.collection.immutable._
import edu.cmu.cs.ls.keymaerax.core._
import org.scalatest.{Matchers, FlatSpec, TagAnnotation}

import scala.collection.immutable.Map

/**
 * Test Provable constructions
 * @author Andre Platzer
 */
//@todo @CheckinTest
class ProvableTest extends FlatSpec with Matchers {
  "Provable" should "close trivial proofs" in {
    import scala.collection.immutable._
    val verum = new Sequent(Seq(), IndexedSeq(), IndexedSeq(True))
    // conjecture
    val provable = Provable.startProof(verum)
    // construct a proof
    val proving = provable(CloseTrue(SuccPos(0)), 0)
    // check if proof successful
    if (proving.isProved) println("Successfully proved " + proving.proved)
    proving.isProved should be (true)
  }

  it should "glue trivial proofs forward" in {
    import scala.collection.immutable._
    val verum = new Sequent(Seq(), IndexedSeq(), IndexedSeq(True))
    // conjecture
    val provable = Provable.startProof(verum)
    // construct a proof
    val proving = provable(CloseTrue(SuccPos(0)), 0)
    // check if proof successful
    if (proving.isProved) println("Successfully proved " + proving.proved)
    proving.isProved should be (true)

    val more = new Sequent(Seq(), IndexedSeq(), IndexedSeq(Imply(Greater(Variable("x"), Number(5)), True)))
    // another conjecture
    val moreProvable = Provable.startProof(more)
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
    val more = new Sequent(Seq(), IndexedSeq(), IndexedSeq(Imply(Greater(Variable("x"), Number(5)), True)))
    // another conjecture
    val moreProvable = Provable.startProof(more)
    // construct another (partial) proof
    val moreProving = moreProvable(ImplyRight(SuccPos(0)), 0)(HideLeft(AntePos(0)), 0)
    moreProving.isProved should be (false)

    val verum = new Sequent(Seq(), IndexedSeq(), IndexedSeq(True))
    // conjecture
    val provable = Provable.startProof(verum)
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
    val finGoal = new Sequent(Seq(), IndexedSeq(), IndexedSeq(Imply(fm, And(fm, True))))
    // conjecture
    val finProvable = Provable.startProof(finGoal)
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
    val left = Provable.startProof(Sequent(Seq(), IndexedSeq(fm), IndexedSeq(fm)))(
      Close(AntePos(0), SuccPos(0)), 0)
    // |- true
    val right = Provable.startProof(Sequent(Seq(), IndexedSeq(), IndexedSeq(True)))(
      CloseTrue(SuccPos(0)), 0)
    val right2 = Provable.startProof(Sequent(Seq(), IndexedSeq(fm), IndexedSeq(True)))(
      HideLeft(AntePos(0)), 0) (right, 0)
    val merged = Provable.startProof(Sequent(Seq(), IndexedSeq(fm), IndexedSeq(And(fm, True))))(
      AndRight(SuccPos(0)), 0) (
      left, 0)(
        right2, 0)
    // gluing order irrelevant
    merged should be (Provable.startProof(Sequent(Seq(), IndexedSeq(fm), IndexedSeq(And(fm, True))))(
      AndRight(SuccPos(0)), 0) (
      right2, 1)(
        left, 0))
    // |- x>5 -> x>5 & true
    val finGoal = new Sequent(Seq(), IndexedSeq(), IndexedSeq(Imply(fm, And(fm, True))))
    val proof = Provable.startProof(finGoal)(
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
    val proof = Provable.startProof(Sequent(Seq(), IndexedSeq(fm), IndexedSeq(And(fm, True))))(
      AndRight(SuccPos(0)), 0) (
      // left branch: x>5 |- x>5
      Provable.startProof(Sequent(Seq(), IndexedSeq(fm), IndexedSeq(fm)))(
        Close(AntePos(0), SuccPos(0)), 0),
      0)(
        //right branch: |- true
        Provable.startProof(Sequent(Seq(), IndexedSeq(), IndexedSeq(True)))(
          CloseTrue(SuccPos(0)), 0)(
            // x>5 |- true
            Sequent(Seq(), IndexedSeq(fm), IndexedSeq(True)), HideLeft(AntePos(0))),
        0)(
        // |- x>5 -> x>5 & true
        new Sequent(Seq(), IndexedSeq(), IndexedSeq(Imply(fm, And(fm, True)))),
        ImplyRight(SuccPos(0))
      )
    proof.isProved should be (true)
    proof.proved should be (new Sequent(Seq(), IndexedSeq(), IndexedSeq(Imply(fm, And(fm, True)))))
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
    val mid = new Sequent(Seq(), IndexedSeq(fm), IndexedSeq(And(fm, True)))
    // middle conjecture
    val midProvable = Provable.startProof(mid)
    // construct a middle proof
    val midProof: Provable = midProvable/*(ImplyRight(SuccPos(0)), 0)*/(
      AndRight(SuccPos(0)), 0)(
      HideLeft(AntePos(0)), 1)
    midProof.isProved should be (false)
    // right conjecture: True
    val right = new Sequent(Seq(), IndexedSeq(), IndexedSeq(True))
    val rightProvable = Provable.startProof(right)
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
    val finGoal = new Sequent(Seq(), IndexedSeq(), IndexedSeq(Imply(fm, And(fm, True))))
    val fin = Provable.startProof(finGoal)
    // glue mergeMidRight intermediate proof forward as the partial proof of fin
    val finProof = fin(ImplyRight(SuccPos(0)), 0) (mergeMidRight, 0)
    finProof.isProved should be (false)
    finProof.subgoals.length should be (1)
    // finish remaining proof by proving remaining left goal
    val proved = finProof(Close(AntePos(0), SuccPos(0)), 0)
    proved.isProved should be (true)
    proved.proved should be (finGoal)
  }
}
