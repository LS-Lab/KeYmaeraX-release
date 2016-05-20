package edu.cmu.cs.ls.keymaerax.tools

import edu.cmu.cs.ls.keymaerax.core.Evidence

// require favoring immutable Seqs for unmodifiable Lemma evidence

import scala.collection.immutable

/**
 * Created by aplatzer on 8/24/15.
 */
case class ToolEvidence(info : immutable.Map[String,String]) extends Evidence {
  override def toString: String =
    "Tool.\n  " + info.map(entry => entry._1 + " \"\"\"\"" + entry._2 + "\"\"\"\"").mkString("\n  ") + "\nEnd."
}
