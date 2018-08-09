/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.codegen

import edu.cmu.cs.ls.keymaerax.core.{BaseVariable, Expression}

/**
  * Generate executable code from a differential dynamic logic expression. Returns a tuple (Definitions, Body), where
  * `body` computes `expression` using the sub-routines in `definitions`.
  */
trait CodeGenerator extends (Expression => (String, String)) {
  /** Translate expression `expr` into code. All symbols in `expr` are treated as constant parameters. */
  def apply(expr: Expression): (String, String) = apply(expr, Set(), Set(), "")
  /** Translate expression `expr` into code. Symbols in `stateVars` are treated as mutable states, all others are constant parameters. */
  def apply(expr: Expression, stateVars: Set[BaseVariable]): (String, String) = apply(expr, stateVars, Set(), "")
  /** Translate expression `expr` into code. Symbols in `stateVars` are treated as mutable states, all others are constant parameters.
    * `inputVars` is a subset of `stateVars` whose value is nondeterministically chosen in the original program. */
  def apply(expr: Expression, stateVars: Set[BaseVariable], inputVars: Set[BaseVariable]): (String, String) = apply(expr, stateVars, inputVars, "")
  /** Translate expression `expr` into code. Symbols in `stateVars` are treated as mutable states, all others are constant parameters.
    * `inputVars` is a subset of `stateVars` whose value is nondeterministically chosen in the original program.
    * The model name `modelName` is added to the file header comment. */
  def apply(expr: Expression, stateVars: Set[BaseVariable], inputVars: Set[BaseVariable], modelName: String): (String, String)
}

class CodeGenerationException(s: String) extends Exception(s)
