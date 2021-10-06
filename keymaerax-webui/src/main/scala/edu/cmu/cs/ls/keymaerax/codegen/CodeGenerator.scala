/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.codegen

import edu.cmu.cs.ls.keymaerax.core.{AssignAny, BaseVariable, Expression, Function, NamedSymbol, Program, Real, StaticSemantics, Tuple, Unit}
import edu.cmu.cs.ls.keymaerax.infrastruct.ExpressionTraversal.{ExpressionTraversalFunction, StopTraversal}
import edu.cmu.cs.ls.keymaerax.infrastruct.{ExpressionTraversal, PosInExpr}
import edu.cmu.cs.ls.keymaerax.parser.InterpretedSymbols

object CodeGenerator {
  /**
    * Returns a set of names (excluding names in `exclude` and interpreted functions) that are immutable parameters of the
    * expression `expr`. */
  def getParameters(expr: Expression, exclude: Set[BaseVariable]): Set[NamedSymbol] =
    StaticSemantics.symbols(expr)
      .filter({
        case InterpretedSymbols.absF | InterpretedSymbols.minF | InterpretedSymbols.maxF => false
        case Function(name, _, Unit, _, _) => !exclude.exists(v => v.name == name.stripSuffix("post"))
        case BaseVariable(name, _, _) => !exclude.exists(v => v.name == name.stripSuffix("post"))
        case _ => false //@note any other function or differential symbol
      })

  /** Returns a set of names whose values are chosen nondeterministically in the program `expr` (empty if `expr` is not
    * a program). */
  def getInputs(expr: Expression): Set[BaseVariable] = expr match {
    case prg: Program =>
      val inputs = scala.collection.mutable.Set[BaseVariable]()
      ExpressionTraversal.traverse(new ExpressionTraversalFunction {
        override def preP(p: PosInExpr, e: Program): Either[Option[StopTraversal], Program] = e match {
          case AssignAny(v: BaseVariable) => inputs += v; Left(None)
          case _ => Left(None)
        }
      }, prg)
      inputs.toSet
    case _ => Set()
  }

  /** Indicates whether the name `f` is an interpreted function symbol. */
  def isInterpreted(f: NamedSymbol) : Boolean = f match {
    case Function(_, _, _, _, interpreted) => interpreted
    case _ => false
  }
}

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
