package edu.cmu.cs.ls.keymaera.tests

import edu.cmu.cs.ls.keymaera.core._

object TermTests {

  def test {
      val p = new FormulaName("p")
      val q = new FormulaName("q")
      Implies(p, q)
  }

}

// vim: set ts=4 sw=4 et:
