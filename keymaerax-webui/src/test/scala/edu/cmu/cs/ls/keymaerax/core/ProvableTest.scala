/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.core

import edu.cmu.cs.ls.keymaerax.{Configuration, FileConfiguration}
import edu.cmu.cs.ls.keymaerax.bellerophon.LazySequentialInterpreter
import edu.cmu.cs.ls.keymaerax.tags.{CheckinTest, SummaryTest}

import scala.collection.immutable._
import org.scalatest.{BeforeAndAfterAll, FlatSpec, Matchers}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tools.KeYmaeraXTool

/**
 * Test Provable constructions
 * @author
 *   Andre Platzer
 * @todo
 *   more exhaustive tests needed
 */
@CheckinTest @SummaryTest
class ProvableTest extends FlatSpec with Matchers with BeforeAndAfterAll {
  override def beforeAll(): Unit = {
    Configuration.setConfiguration(FileConfiguration)
    KeYmaeraXTool.init(Map(
      KeYmaeraXTool.INIT_DERIVATION_INFO_REGISTRY -> "false",
      KeYmaeraXTool.INTERPRETER -> LazySequentialInterpreter.getClass.getSimpleName,
    ))
  }

  "Provable" should "close trivial proofs" in {
    import scala.collection.immutable._
    val verum = Sequent(IndexedSeq(), IndexedSeq(True))
    // conjecture
    val provable = ProvableSig.startPlainProof(verum)
    // construct a proof
    val proving = provable(CloseTrue(SuccPos(0)), 0)
    // check if proof successful
    if (proving.isProved) println("Successfully proved " + proving.proved)
    proving.isProved should be(true)
    proving.steps shouldBe 1
  }

  it should "glue trivial proofs forward" in {
    import scala.collection.immutable._
    val verum = Sequent(IndexedSeq(), IndexedSeq(True))
    // conjecture
    val provable = ProvableSig.startPlainProof(verum)
    // construct a proof
    val proving = provable(CloseTrue(SuccPos(0)), 0)
    // check if proof successful
    if (proving.isProved) println("Successfully proved " + proving.proved)
    proving.isProved should be(true)
    proving.steps shouldBe 1

    val more = Sequent(IndexedSeq(), IndexedSeq(Imply(Greater(Variable("x"), Number(5)), True)))
    // another conjecture
    val moreProvable = ProvableSig.startPlainProof(more)
    // construct another (partial) proof
    val moreProving = moreProvable(ImplyRight(SuccPos(0)), 0)(HideLeft(AntePos(0)), 0)
    moreProving.isProved should be(false)
    moreProving.steps shouldBe 2
    // merge proofs by gluing their Provables together
    val mergedProving = moreProving(proving, 0)
    // check if proof successful
    if (mergedProving.isProved) println("Successfully proved " + mergedProving.proved)
    mergedProving.isProved should be(true)
    mergedProving.steps shouldBe 3
  }

  it should "glue trivial proofs backward" in {
    import scala.collection.immutable._
    val more = Sequent(IndexedSeq(), IndexedSeq(Imply(Greater(Variable("x"), Number(5)), True)))
    // another conjecture
    val moreProvable = ProvableSig.startPlainProof(more)
    // construct another (partial) proof
    val moreProving = moreProvable(ImplyRight(SuccPos(0)), 0)(HideLeft(AntePos(0)), 0)
    moreProving.isProved should be(false)
    moreProving.steps shouldBe 2

    val verum = Sequent(IndexedSeq(), IndexedSeq(True))
    // conjecture
    val provable = ProvableSig.startPlainProof(verum)
    // construct a proof
    val proving = provable(CloseTrue(SuccPos(0)), 0)
    // check if proof successful
    if (proving.isProved) println("Successfully proved " + proving.proved)
    proving.isProved should be(true)
    proving.steps shouldBe 1

    // merge proofs by gluing their Provables together
    val mergedProving = moreProving(proving, 0)
    // check if proof successful
    if (mergedProving.isProved) println("Successfully proved " + mergedProving.proved)
    mergedProving.isProved should be(true)
    mergedProving.steps shouldBe 3

    val otherProving = moreProving.sub(0)(CloseTrue(SuccPos(0)), 0)
    otherProving shouldBe Symbol("proved")
    otherProving.steps shouldBe 1
    val otherMergedProving = moreProving(otherProving, 0)
    otherMergedProving shouldBe Symbol("proved")
    otherMergedProving.steps shouldBe 3
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
    val finGoal = Sequent(IndexedSeq(), IndexedSeq(Imply(fm, And(fm, True))))
    // conjecture
    val finProvable = ProvableSig.startPlainProof(finGoal)
    // construct a proof
    val proof = finProvable(ImplyRight(SuccPos(0)), 0)(AndRight(SuccPos(0)), 0)(HideLeft(AntePos(0)), 1)(
      CloseTrue(SuccPos(0)),
      1,
    )(Close(AntePos(0), SuccPos(0)), 0)
    proof.isProved should be(true)
    proof.proved should be(finGoal)
    proof.steps shouldBe 5
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
    val left = ProvableSig.startPlainProof(Sequent(IndexedSeq(fm), IndexedSeq(fm)))(Close(AntePos(0), SuccPos(0)), 0)
    // |- true
    val right = ProvableSig.startPlainProof(Sequent(IndexedSeq(), IndexedSeq(True)))(CloseTrue(SuccPos(0)), 0)
    val right2 = ProvableSig
      .startPlainProof(Sequent(IndexedSeq(fm), IndexedSeq(True)))(HideLeft(AntePos(0)), 0)(right, 0)
    val merged = ProvableSig
      .startPlainProof(Sequent(IndexedSeq(fm), IndexedSeq(And(fm, True))))(AndRight(SuccPos(0)), 0)(left, 0)(right2, 0)
    // gluing order irrelevant
    merged should be(
      ProvableSig.startPlainProof(Sequent(IndexedSeq(fm), IndexedSeq(And(fm, True))))(AndRight(SuccPos(0)), 0)(
        right2,
        1,
      )(left, 0)
    )
    // |- x>5 -> x>5 & true
    val finGoal = Sequent(IndexedSeq(), IndexedSeq(Imply(fm, And(fm, True))))
    val proof = ProvableSig.startPlainProof(finGoal)(ImplyRight(SuccPos(0)), 0)(merged, 0)
    proof.isProved should be(true)
    proof.proved should be(finGoal)
    proof.steps shouldBe 5
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
    val proof = ProvableSig
      .startPlainProof(Sequent(IndexedSeq(fm), IndexedSeq(And(fm, True))))(AndRight(SuccPos(0)), 0)(
        // left branch: x>5 |- x>5
        ProvableSig.startPlainProof(Sequent(IndexedSeq(fm), IndexedSeq(fm)))(Close(AntePos(0), SuccPos(0)), 0),
        0,
      )(
        // right branch: |- true
        ProvableSig.startPlainProof(Sequent(IndexedSeq(), IndexedSeq(True)))(CloseTrue(SuccPos(0)), 0)(
          // x>5 |- true
          Sequent(IndexedSeq(fm), IndexedSeq(True)),
          HideLeft(AntePos(0)),
        ),
        0,
      )(
        // |- x>5 -> x>5 & true
        Sequent(IndexedSeq(), IndexedSeq(Imply(fm, And(fm, True)))),
        ImplyRight(SuccPos(0)),
      )
    proof.isProved should be(true)
    proof.proved should be(Sequent(IndexedSeq(), IndexedSeq(Imply(fm, And(fm, True)))))
    proof.steps shouldBe 5
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
   * in the mixed order: &R, WL CloseTrue ->R ax
   */
  it should "glue proofs in mixed yoyo order of x>0 -> x>0 & true" in {
    import scala.collection.immutable._
    val fm = Greater(Variable("x"), Number(5))
    // x>5  |-  x>5 & true
    val mid = Sequent(IndexedSeq(fm), IndexedSeq(And(fm, True)))
    // middle conjecture
    val midProvable = ProvableSig.startPlainProof(mid)
    // construct a middle proof
    val midProof: ProvableSig =
      midProvable /*(ImplyRight(SuccPos(0)), 0)*/ (AndRight(SuccPos(0)), 0)(HideLeft(AntePos(0)), 1)
    midProof.isProved should be(false)
    // right conjecture: True
    val right = Sequent(IndexedSeq(), IndexedSeq(True))
    val rightProvable = ProvableSig.startPlainProof(right)
    rightProvable.isProved should be(false)
    // construct a right proof
    val rightProof = rightProvable(CloseTrue(SuccPos(0)), 0)
    rightProof.isProved should be(true)
    // merge right proof into right branch of middle proof
    val mergeMidRight = midProof(rightProof, 1)
    mergeMidRight.isProved should be(false)
    // could finish proof of mid now
    val precloseProof = mergeMidRight(Close(AntePos(0), SuccPos(0)), 0)
    precloseProof.isProved should be(true)
    precloseProof.proved should be(mid)
    // add to the bottom of the proof
    // final conjecture: |- x>5 -> x>5&true
    val finGoal = Sequent(IndexedSeq(), IndexedSeq(Imply(fm, And(fm, True))))
    val fin = ProvableSig.startPlainProof(finGoal)
    // glue mergeMidRight intermediate proof forward as the partial proof of fin
    val finProof = fin(ImplyRight(SuccPos(0)), 0)(mergeMidRight, 0)
    finProof.isProved should be(false)
    finProof.subgoals.length should be(1)
    // finish remaining proof by proving remaining left goal
    val proved = finProof(Close(AntePos(0), SuccPos(0)), 0)
    proved.isProved should be(true)
    proved.proved should be(finGoal)
    proved.steps shouldBe 5
  }

  it should "not close different formulas by identity" in {
    import scala.collection.immutable._
    val fm = Greater(Variable("x"), Number(5))
    val fm1 = Less(Variable("x"), Number(5))
    // x>5 |- x>5
    val finGoal = Sequent(IndexedSeq(fm), IndexedSeq(fm))
    val finProof = ProvableSig.startPlainProof(finGoal)(Close(AntePos(0), SuccPos(0)), 0)
    finProof.isProved should be(true)
    finProof.proved should be(finGoal)
    // x<5 |- x>5
    val noGoal = Sequent(IndexedSeq(fm1), IndexedSeq(fm))
    a[CoreException] shouldBe thrownBy(ProvableSig.startPlainProof(noGoal)(Close(AntePos(0), SuccPos(0)), 0))
  }

  it should "print to storage string" in {
    // @note including hashCodes, since those are expected to be stable due to case classes and case objects
    Provable.toStorageString(Provable.startProof("x>0 -> x>0".asFormula)) shouldBe
      """  ==>  ((x) > ((0)))->((x) > ((0)))
        |\from     ==>  ((x) > ((0)))->((x) > ((0)))
        |\qed::edfb8475b8dd8b609ca95a5dccfc4bbf""".stripMargin
    Provable.toStorageString(Provable.startProof("x>0, y>0 ==> x>0".asSequent)) shouldBe
      """(x) > ((0)) :: (y) > ((0))
        |  ==>  (x) > ((0))
        |\from   (x) > ((0)) :: (y) > ((0))
        |  ==>  (x) > ((0))
        |\qed::d0a1dfc51350c263e39bc5fba13192c1""".stripMargin
    Provable.toStorageString(Provable.startProof("[{x'=2,y'=3}]x>0, y>0 ==> y>0".asSequent)) shouldBe
      """[{x'=(2),y'=(3)}]((x) > ((0))) :: (y) > ((0))
        |  ==>  (y) > ((0))
        |\from   [{x'=(2),y'=(3)}]((x) > ((0))) :: (y) > ((0))
        |  ==>  (y) > ((0))
        |\qed::89558f43bbaf60af25d6d699604fe9b5""".stripMargin
    Provable.toStorageString(Provable.startProof("true".asFormula)(CloseTrue(SuccPos(0)), 0)) shouldBe
      """  ==>  true
        |\qed::e02d96fbea9765496a14c7459b48a40d""".stripMargin
    Provable.toStorageString(Provable.startProof("x>0 & y>0".asFormula)(AndRight(SuccPos(0)), 0)) shouldBe
      """  ==>  ((x) > ((0)))&((y) > ((0)))
        |\from     ==>  (x) > ((0))
        |\from     ==>  (y) > ((0))
        |\qed::221cbcbb08844a1b786dae89e903e458""".stripMargin
  }

  it should "parse from storage string" in {
    {
      val p = Provable.startProof("x>0 -> x>0".asFormula)
      Provable.fromStorageString(Provable.toStorageString(p)) shouldBe p
    }
    {
      val p = Provable.startProof("x>0, y>0 ==> x>0".asSequent)
      Provable.fromStorageString(Provable.toStorageString(p)) shouldBe p
    }
    {
      val p = Provable.startProof("[{x'=2,y'=3}]x>0, y>0 ==> y>0".asSequent)
      Provable.fromStorageString(Provable.toStorageString(p)) shouldBe p
    }
    {
      val p = Provable.startProof("true".asFormula)(CloseTrue(SuccPos(0)), 0)
      Provable.fromStorageString(Provable.toStorageString(p)) shouldBe p
    }
    {
      val p = Provable.startProof("x>0 & y>0".asFormula)(AndRight(SuccPos(0)), 0)
      Provable.fromStorageString(Provable.toStorageString(p)) shouldBe p
    }
  }

  "Forward Provable" should "continue correct consequence but refuse incorrect consequence" in {
    import scala.collection.immutable._
    val fm = Greater(Variable("x"), Number(5))
    // x>5 |- x>5 & true
    val finGoal = Sequent(IndexedSeq(fm), IndexedSeq(And(fm, True)))
    // conjecture
    val finProvable = ProvableSig.startPlainProof(finGoal)
    // construct a proof
    val proof = finProvable(AndRight(SuccPos(0)), 0)(HideLeft(AntePos(0)), 1)(CloseTrue(SuccPos(0)), 1)(
      Close(AntePos(0), SuccPos(0)),
      0,
    )
    proof.isProved should be(true)
    proof.proved should be(finGoal)
    proof.steps shouldBe 4

    // prolong forward
    // x>5 |- x>5 & true
    val goal = Sequent(IndexedSeq(), IndexedSeq(Imply(fm, And(fm, True))))
    val finProof = proof(goal, ImplyRight(SuccPos(0)))
    finProof.isProved should be(true)
    finProof.proved should be(goal)
    finProof.steps shouldBe 5
    // incorrectly prolong forward
    a[MatchError /*| CoreException*/ ] shouldBe thrownBy(proof(goal, AndRight(SuccPos(0))))
    a[MatchError /*| CoreException*/ ] shouldBe thrownBy(proof(goal, OrRight(SuccPos(0))))
    a[MatchError /*| CoreException*/ ] shouldBe
      thrownBy(proof(Sequent(IndexedSeq(), IndexedSeq(Equiv(fm, And(fm, True)))), ImplyRight(SuccPos(0))))
    a[CoreException] shouldBe
      thrownBy(proof(Sequent(IndexedSeq(), IndexedSeq(Imply(False, And(fm, True)))), ImplyRight(SuccPos(0))))
    a[CoreException] shouldBe
      thrownBy(proof(Sequent(IndexedSeq(), IndexedSeq(Imply(fm, And(True, fm)))), ImplyRight(SuccPos(0))))
  }

  "Individual proof rules" should "refuse Skolemization clashes" in {
    println("Testing " + Skolemize(SuccPos(0)))
    val goal = ProvableSig
      .startPlainProof(Sequent(IndexedSeq("p(x)".asFormula), IndexedSeq("\\forall x p(x)".asFormula)))
    a[SkolemClashException] shouldBe thrownBy(goal(Skolemize(SuccPos(0)), 0))
    val goal2 = ProvableSig
      .startPlainProof(Sequent(IndexedSeq("x>=0".asFormula), IndexedSeq("\\forall x p(x)".asFormula)))
    a[SkolemClashException] shouldBe thrownBy(goal2(Skolemize(SuccPos(0)), 0))
    val goal3 = ProvableSig
      .startPlainProof(Sequent(IndexedSeq("x>=0".asFormula), IndexedSeq("\\forall x x>=0".asFormula)))
    a[SkolemClashException] shouldBe thrownBy(goal3(Skolemize(SuccPos(0)), 0))
    val goal4 = ProvableSig
      .startPlainProof(Sequent(IndexedSeq(), IndexedSeq("\\forall x x>=0".asFormula, "x<=0".asFormula)))
    a[SkolemClashException] shouldBe thrownBy(goal4(Skolemize(SuccPos(0)), 0))
  }

  it should "refuse bound renaming except at bound occurrences" in {
    val rens = BoundRenaming(Variable("y"), Variable("x"), SuccPos(0))
    println("Testing " + rens)
//    val goal = Provable.startPlainProof(Sequent(Nil, IndexedSeq("p(y)".asFormula), IndexedSeq("\\forall y p(y)".asFormula)))
//    a [CoreException] shouldBe thrownBy (goal(rens, 0))
    val goal2 = ProvableSig.startPlainProof(Sequent(IndexedSeq("p(x)".asFormula), IndexedSeq("x>=9".asFormula)))
    a[RenamingClashException] shouldBe thrownBy(goal2(BoundRenaming(Variable("x"), Variable("y"), SuccPos(0)), 0))
    val goal3 = ProvableSig.startPlainProof(Sequent(IndexedSeq("p(x)".asFormula), IndexedSeq("p(x)".asFormula)))
    a[RenamingClashException] shouldBe thrownBy(goal3(rens, 0))
    val goal4 = ProvableSig
      .startPlainProof(Sequent(IndexedSeq("p(x)".asFormula), IndexedSeq("[y:=9;z:=0;]z>=10".asFormula)))
    a[RenamingClashException] shouldBe thrownBy(goal4(rens, 0))
    val goal5 = ProvableSig
      .startPlainProof(Sequent(IndexedSeq("p(x)".asFormula), IndexedSeq("[{y'=9}]y>=10".asFormula)))
    a[RenamingClashException] shouldBe thrownBy(goal5(rens, 0))
  }

  it should "report bound renaming clashes" in {
    val rens = BoundRenaming(Variable("y"), Variable("x"), SuccPos(0))
    val goal = ProvableSig
      .startPlainProof(Sequent(IndexedSeq("true".asFormula), IndexedSeq("\\forall y y>=x".asFormula)))
    a[RenamingClashException] shouldBe thrownBy(goal(rens, 0))
  }

  // @todo all rules should have different toString
}
