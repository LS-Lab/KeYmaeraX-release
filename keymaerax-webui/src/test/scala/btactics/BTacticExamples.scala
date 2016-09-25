/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.PosInExpr
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tags.SummaryTest
import scala.collection.immutable._

import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

/**
 * Tactic Examples with different proof styles.
 * @author Andre Platzer
 */
@SummaryTest
class BTacticExamples extends TacticTestBase  {

  "Explicit Proof Certificates" should "prove !!p() <-> p()" in {
    import edu.cmu.cs.ls.keymaerax.core._
    // explicit proof certificate construction of |- !!p() <-> p()
    val proof = (Provable.startProof(
      Sequent(IndexedSeq(), IndexedSeq("!!p() <-> p()".asFormula)))
      (EquivRight(SuccPos(0)), 0)
      // right branch
      (NotRight(SuccPos(0)), 1)
      (NotLeft(AntePos(1)), 1)
      (Close(AntePos(0),SuccPos(0)), 1)
      // left branch
      (NotLeft(AntePos(0)), 0)
      (NotRight(SuccPos(1)), 0)
      (Close(AntePos(0),SuccPos(0)), 0)
      )
    proof shouldBe 'proved
    proof.proved shouldBe Sequent(IndexedSeq(), IndexedSeq("!!p() <-> p()".asFormula))
  }


  "Explicit Proof" should "prove !!p() <-> p()" in {
    import TactixLibrary._
    // Explicit proof tactic for |- !!p() <-> p()
    val proof = TactixLibrary.proveBy(
      Sequent(IndexedSeq(), IndexedSeq("!!p() <-> p()".asFormula)),
      equivR(SuccPos(0)) <(
        (notL(AntePos(0)) &
            notR(SuccPos(1)) &
            closeId)
        ,
        (notR(SuccPos(0)) &
          notL(AntePos(1)) &
          closeId)
      )
    )
    proof shouldBe 'proved
    proof.proved shouldBe Sequent(IndexedSeq(), IndexedSeq("!!p() <-> p()".asFormula))
  }

  it should "prove !!p() <-> p() with modern index" in {
    import TactixLibrary._
    // Explicit proof tactic for |- !!p() <-> p()
    val proof = TactixLibrary.proveBy(
      Sequent(IndexedSeq(), IndexedSeq("!!p() <-> p()".asFormula)),
      equivR(1) <(
        (notL(-1) &
          notR(2) &
          closeId)
        ,
        (notR(1) &
          notL(-2) &
          closeId)
        )
    )
    proof shouldBe 'proved
    proof.proved shouldBe Sequent(IndexedSeq(), IndexedSeq("!!p() <-> p()".asFormula))
  }


  //@todo more tests like this because this is one of the few simple tests that fails when master/prop have the * inside the OnAll instead of outside the OnAll.
  "Proof by Search" should "prove (p() & q()) & r() <-> p() & (q() & r())" in {
    import TactixLibrary._
    // Proof by search of |- (p() & q()) & r() <-> p() & (q() & r())
    val proof = TactixLibrary.proveBy(
      Sequent(IndexedSeq(), IndexedSeq("(p() & q()) & r() <-> p() & (q() & r())".asFormula)),
      prop
    )
    proof shouldBe 'proved
    proof.proved shouldBe Sequent(IndexedSeq(), IndexedSeq("(p() & q()) & r() <-> p() & (q() & r())".asFormula))
  }

}
