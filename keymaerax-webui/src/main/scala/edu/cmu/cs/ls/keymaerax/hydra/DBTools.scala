/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra

import edu.cmu.cs.ls.keymaerax.bellerophon.IOListener
import edu.cmu.cs.ls.keymaerax.tacticsinterface.TraceRecordingListener

import scala.collection.immutable.{Nil, Seq}

object DBTools {

  /** A listener that stores proof steps in the database `db` for proof `proofId`. */
  def listener(
      db: DBAbstraction,
      constructGlobalProvable: Boolean = false,
      codeName: String => String = s => s,
      additionalListeners: Seq[IOListener] = Nil,
  )(proofId: Int)(tacticName: String, parentInTrace: Int, branch: Int): Seq[IOListener] = {
    val trace = db.getExecutionSteps(proofId).sortBy(_.stepId)
    assert(
      -1 <= parentInTrace && parentInTrace < trace.length,
      "Invalid trace index " + parentInTrace + ", expected -1<=i<trace.length",
    )
    val parentStep: Option[Int] = if (parentInTrace < 0) None else trace(parentInTrace).stepId
    val globalProvable = parentStep match {
      case None => db.getProvable(db.getProofInfo(proofId).provableId.get).provable
      case Some(sId) => db.getExecutionStep(proofId, sId).map(_.local).get
    }
    new TraceRecordingListener(
      db,
      proofId,
      parentStep,
      globalProvable,
      branch,
      recursive = false,
      codeName(tacticName),
      constructGlobalProvable,
    ) :: Nil ++ additionalListeners
  }

}
