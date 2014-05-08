package edu.cmu.cs.ls.keymaera.tools

import edu.cmu.cs.ls.keymaera.core._

/**
 * A base class for tools
 * @author Nathan Fulton
 */
trait Tool {
}


trait QETool {
  def qe(formula : Formula) : Expr
}
