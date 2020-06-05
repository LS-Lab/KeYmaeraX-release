/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.macros

/** Information on the arguments, their names and sorts, that an axiom/rule/tactic requires as input. */
sealed trait ArgInfo {
  /** Argument sort. */
  val sort: String
  /** Argument name. */
  val name: String
  /** A list of allowed fresh symbols. */
  val allowsFresh: List[String]
}
case class FormulaArg (override val name: String, override val allowsFresh: List[String] = Nil) extends ArgInfo {
  val sort = "formula"
}

case class GeneratorArg (override val name: String) extends ArgInfo {
  val sort = "generator"
  override val allowsFresh: List[String] = Nil
}

class ExpressionArg (override val name: String, override val allowsFresh: List[String] = Nil) extends ArgInfo {
  val sort = "expression"
}

class TermArg (override val name: String, override val allowsFresh: List[String] = Nil) extends ExpressionArg (name, allowsFresh) {
  override val sort = "term"
}

case class VariableArg (override val name: String, override val allowsFresh: List[String] = Nil) extends TermArg (name, allowsFresh) {
  override val sort = "variable"
}

case class NumberArg (override val name: String, override val allowsFresh: List[String] = Nil) extends TermArg (name, allowsFresh) {
  override val sort = "number"
}

case class StringArg (override val name: String, override val allowsFresh: List[String] = Nil) extends ArgInfo {
  val sort = "string"
}

case class SubstitutionArg (override val name: String, override val allowsFresh: List[String] = Nil) extends ArgInfo {
  val sort = "subst"
}

case class PosInExprArg (override val name: String, override val allowsFresh: List[String] = Nil) extends ArgInfo {
  val sort = "posinexpr"
}

case class OptionArg(arg: ArgInfo) extends ArgInfo {
  val name: String = arg.name
  val sort: String = "option[" + arg.sort + "]"
  val allowsFresh: List[String] = arg.allowsFresh
}
@deprecated("Until lists are actually added to the concrete syntax of Bellerophon.", "4.2b1")
case class ListArg (arg: ArgInfo) extends ArgInfo {
  val name: String = arg.name
  val sort: String = "list[" + arg.sort + "]"
  val allowsFresh: List[String] = arg.allowsFresh
}

