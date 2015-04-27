package edu.cmu.cs.ls.keymaera.tools

import edu.cmu.cs.ls.keymaera.core.{Formula, QETool}

/**
 * Polya quantifier elimination tool.
 *
 * Created by smitsch on 4/27/15.
 * @author Ran Ji
 * @author Stefan Mitsch
 */
class Polya extends ToolBase("Polya") with QETool {
  private val polya = new PolyaSolver

  override def qe(formula: Formula): Formula = polya.qe(formula)
  override def qeInOut(formula: Formula): (Formula, String, String) = polya.qeInOut(formula)
}
