package edu.cmu.cs.ls.keymaerax.codegeneration

import edu.cmu.cs.ls.keymaerax.core.Expression

/**
 * Created by ran on 7/1/15.
 */
trait CodeGenerator extends (Expression => String) {
  def apply(kExpr: Expression): String
}

class CodeGenerationException(s: String) extends Exception(s)
