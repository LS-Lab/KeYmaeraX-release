package edu.cmu.cs.ls.keymaera.hydra

import edu.cmu.cs.ls.keymaera.core.{RootNode, Formula, Sequent, ProofNode}
import edu.cmu.cs.ls.keymaera.parser.KeYmaeraParser

/**
 * Created by jdq on 6/12/14.
 */
object KeYmaeraInterface {

  def parseProblem(content: String): ProofNode = {
    new KeYmaeraParser().runParser(content) match {
      case f: Formula =>
        val seq = Sequent(List(), collection.immutable.IndexedSeq[Formula](), collection.immutable.IndexedSeq[Formula](f) )
        new RootNode(seq)
      case a => throw new IllegalStateException("Parsing the input did not result in a formula but in: " + a)
    }
  }
}
