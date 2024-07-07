/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics

import org.keymaerax.bellerophon._
import org.keymaerax.btactics.SequentCalculus._
import org.keymaerax.core._
import org.keymaerax.hydra.DBAbstractionObj
import org.keymaerax.infrastruct.PosInExpr
import org.keymaerax.parser.KeYmaeraXPrettyPrinter
import org.keymaerax.parser.StringConverter._
import org.keymaerax.pt.ProvableSig
import org.keymaerax.tacticsinterface.TraceRecordingListener
import org.scalatest.Ignore

import scala.collection.immutable._

/**
 * Tests whether execution traces are recorded in the DB in the format expected and with sufficient detail to support
 * the desired operations.
 *
 * Created by bbohrer on 11/23/15.
 */
@Ignore
class TraceRecordingTests extends TacticTestBase {
  val db = DBAbstractionObj.testDatabase
  // @todo fill in reasonable data, this is bogus
  private val u = 999
  val listener = new TraceRecordingListener(
    db,
    1337,
    Some(u),
    ProvableSig.startPlainProof(True),
    0,
    false,
    "TODO",
    constructGlobalProvable = true,
  )
  override val theInterpreter = ExhaustiveSequentialInterpreter(Seq(listener))
  object TestLib extends UnifyUSCalculus

  override def beforeEach() = { PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter.pp) }

  override def proveBy(s: Sequent, tactic: BelleExpr): ProvableSig = {
    val v = BelleProvable.plain(ProvableSig.startPlainProof(s))
    theInterpreter(tactic, v) match {
      case BelleProvable(provable, _) => provable
      case r => fail("Unexpected tactic result " + r)
    }
  }
  "IOListener" should "Not Crash" in withTactics {
    val t1 = System.nanoTime()
    proveBy(
      Sequent(IndexedSeq("x>5".asFormula), IndexedSeq("[x:=x+1;][x:=2*x;]x>1".asFormula)),
      TestLib.useAt(Ax.composeb, PosInExpr(1 :: Nil))(SuccPos(0)),
    ).subgoals should contain only Sequent(IndexedSeq("x>5".asFormula), IndexedSeq("[x:=x+1;x:=2*x;]x>1".asFormula))
    val t2 = System.nanoTime()
    println("My time: " + (t2 - t1) / 1000000000.0)
  }

  /* Same sequent and proof as the mockup for the new proof tree UI. Should give us a good sense of whether this code
   * can support the new UI or not. */
  it should "handle branching proofs" in withTactics {
    proveBy(
      Sequent(IndexedSeq(), IndexedSeq("(z>5) -> ((x < 5) & true) & (2 > y)".asFormula)),
      implyR(SuccPos(0)) & andR(SuccPos(0)),
    )
  }

  it should "support multiple proof steps" in withTactics {
    val provable =
      proveBy(Sequent(IndexedSeq(), IndexedSeq("(z>5) -> ((x < 5) & true) & (2 > y)".asFormula)), implyR(SuccPos(0)))
    proveBy(provable.subgoals.head, andR(SuccPos(0)))
  }
}
