/**
 * Differential Dynamic Logic expression pretty printing.
 * @author aplatzer
 * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981, 2015."
 * @see "Andre Platzer. The complete proof theory of hybrid systems. ACM/IEEE Symposium on Logic in Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 541-550. IEEE 2012"
 */
package edu.cmu.cs.ls.keymaerax.core

object PrettyPrinter {
  private var pp: PrettyPrinter = new PrettyPrinter {
    def stringify(term: Term) = term.canonicalString
    def stringify(formula: Formula) = formula.canonicalString
    def stringify(program: Program) = program.canonicalString
  }

  def printer: PrettyPrinter = pp

  /**
   * Set a new pretty printer to be used from now on.
   * @param printer
   */
  def setPrinter(printer: PrettyPrinter) = {pp = printer}
}

/**
 * A pretty printer for differential dynamic logic is essentially a function from Expressions to Strings.
 * @author aplatzer
 */
trait PrettyPrinter extends (Expression => String) {

  /** Pretty-print expression to a string */
  def apply(expr: Expression): String = stringify(expr)

  /** Pretty-print expression to a string */
  def stringify(expr: Expression): String = expr match {
    case t: Term => stringify(t)
    case f: Formula => stringify(f)
    case p: Program => stringify(p)
  }

  /** Pretty-print term to a string */
  def stringify(term: Term): String

  /** Pretty-print formula to a string */
  def stringify(formula: Formula): String

  /** Pretty-print program to a string */
  def stringify(program: Program): String
}
