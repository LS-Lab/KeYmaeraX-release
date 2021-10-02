/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.codegen

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._

/**
  * Generates formula and term evaluation C code. `termContainer` configures the location where primitive terms are
  * looked up (e.g., structs).
  * @author Stefan Mitsch
  * @author Ran Ji
  */
class PythonFormulaTermGenerator(termContainer: Expression => String) extends FormulaTermGenerator(termContainer) {
  override def apply(expr: Expression, stateVars: Set[BaseVariable], inputVars: Set[BaseVariable],
                     modelName: String): (String, String) = expr match {
    case f: Formula if f.isFOL => PythonPrettyPrinter(compileFormula(f))
    case t: Term => PythonPrettyPrinter(compileTerm(t))
  }

  /** @inheritdoc */
  override def nameIdentifier(s: NamedSymbol): String = PythonPrettyPrinter.nameIdentifier(s)

  /** @inheritdoc */
  override def printSort(s: Sort): String = PythonPrettyPrinter.printSort(s)
}
