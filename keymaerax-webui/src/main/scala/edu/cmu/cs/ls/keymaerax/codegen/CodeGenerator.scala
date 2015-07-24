/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.codegen

import edu.cmu.cs.ls.keymaerax.core.{Variable, Expression}

/**
 * Generate executable code from a differential dynamic logic expression.
 */
trait CodeGenerator extends (Expression => String) {
  /** Generate code */
  def apply(expr: Expression): String
  /** Generate code using the given list of variables as parameters in that order */
  //@todo def apply(expr: Expression, vars: List[Variable]): String
}

class CodeGenerationException(s: String) extends Exception(s)
