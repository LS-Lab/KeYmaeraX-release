package edu.cmu.cs.ls.keymaerax.tools

import edu.cmu.cs.ls.keymaerax.core.Evidence
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXLexer

// require favoring immutable Seqs for unmodifiable Lemma evidence

import scala.collection.immutable

/**
 * Created by aplatzer on 8/24/15.
 */
case class ToolEvidence(info: immutable.List[(String,String)]) extends Evidence {
  override def toString: String =
    "Tool.\n  " + info.map(entry => entry._1 + " \"\"\"\"" + entry._2 + "\"\"\"\"").mkString("\n  ") + "\nEnd."

  /** Equality modulo CRLF == LF in the evidence values (Lexer normalizes, so parsed evidence disagrees with in-memory evidence) */
  override def equals(e: Any): Boolean = e match {
    case other: ToolEvidence => info.length == other.info.length && info.zip(other.info).forall {
      case ((k1,v1), (k2,v2)) => k1 == k2 && KeYmaeraXLexer.normalizeNewlines(v1) == KeYmaeraXLexer.normalizeNewlines(v2)
      case _ => false
    }
    case _ => false
  }

  override def hashCode: Int = info.map({ case (k,v) => (k, KeYmaeraXLexer.normalizeNewlines(v))}).hashCode()
}
