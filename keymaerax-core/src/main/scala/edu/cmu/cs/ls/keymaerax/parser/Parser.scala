/**
 * Differential Dynamic Logic parser for concrete KeYmaera X notation.
 * @author aplatzer
 * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981, 2015."
 */
package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.core._

/**
 * Parser interface for KeYmaera X.
 * @author aplatzer
 */
trait Parser extends (String => Expression) {

  def termParser: (String => Term)

  def formulaParser: (String => Formula)

  def programParser: (String => Program)

  def differentialProgramParser: (String => DifferentialProgram)
}
