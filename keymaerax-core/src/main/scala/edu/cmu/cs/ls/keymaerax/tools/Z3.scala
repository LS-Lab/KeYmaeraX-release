package edu.cmu.cs.ls.keymaerax.tools

import edu.cmu.cs.ls.keymaerax.core.{Formula, QETool}

/**
 * Z3 quantifier elimination tool.
 *
 * Created by smitsch on 4/27/15.
 * @author Ran Ji
 * @author Stefan Mitsch
 */
class Z3 extends ToolBase("Z3") with QETool {
  private val z3 = new Z3Solver

  override def qe(formula: Formula): Formula = z3.qe(formula)
  override def qeInOut(formula: Formula): (Formula, String, String) = z3.qeInOut(formula)
}
