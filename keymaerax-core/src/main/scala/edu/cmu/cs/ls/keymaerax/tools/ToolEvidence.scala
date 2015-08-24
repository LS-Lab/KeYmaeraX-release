package edu.cmu.cs.ls.keymaerax.tools

import edu.cmu.cs.ls.keymaerax.core.Evidence

/**
 * Created by aplatzer on 8/24/15.
 */
case class ToolEvidence(info : Map[String,String]) extends Evidence {
  override def toString: String =
    "Tool.\n  " + info.map(entry => entry._1 + " \"\"\"\"" + entry._2 + "\"\"\"\"").mkString("\n  ") + "\nEnd."
}
