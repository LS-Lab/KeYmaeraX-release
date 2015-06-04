import edu.cmu.cs.ls.keymaerax.core._
import org.scalatest.{Matchers, FlatSpec}

import scala.collection.immutable.Map

/**
 * @author aplatzer
 */
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

    val more = new Sequent(Seq(), IndexedSeq(), IndexedSeq(Imply(Greater(Variable("x",None, Real), Number(5)), True)))
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
    val more = new Sequent(Seq(), IndexedSeq(), IndexedSeq(Imply(Greater(Variable("x",None, Real), Number(5)), True)))
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
}
