/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package testHelper

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.ArchiveParser

/**
 * Created by ran on 2/4/15.
 * @author
 *   Ran Ji
 * @author
 *   Stefan Mitsch
 */
object ParserFactory {

  /**
   * Returns the sequent from an input stream. Substitutes function declarations.
   * @param in
   *   The input stream.
   * @return
   *   The sequent.
   */
  def parseToSequent(in: java.io.InputStream): Sequent = parseToSequent(io.Source.fromInputStream(in).mkString)

  /** Parses from a string, substitutes function declarations. */
  def parseToSequent(in: String): Sequent = {
    Sequent(
      collection.immutable.IndexedSeq[Formula](),
      collection.immutable.IndexedSeq[Formula](ArchiveParser.parseAsFormula(in)),
    )
  }
}
