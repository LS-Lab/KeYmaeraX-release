/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.core.Expression

/** Information on the arguments, their names and sorts, that an axiom/rule/tactic requires as input. */
sealed trait ArgInfo {
  /** Argument sort. */
  val sort: String
  /** Argument name. */
  val name: String
  /** A list of allowed fresh symbols. */
  val allowsFresh: List[String]
  /** Converts an expression into the required format of the tactic (default: no-op). Returns either the converted
    * expression or an error message. */
  def convert(e: Expression): Either[Expression, String] = Left(e)
}
case class FormulaArg (override val name: String, override val allowsFresh: List[String] = Nil) extends ArgInfo {
  val sort = "formula"
}
case class VariableArg (override val name: String, override val allowsFresh: List[String] = Nil) extends ArgInfo {
  val sort = "variable"
}
case class ExpressionArg (override val name: String, override val allowsFresh: List[String] = Nil,
                          converter: Expression => Either[Expression, String] = e => Left(e)) extends ArgInfo {
  val sort = "expression"
  override def convert(e: Expression): Either[Expression, String] = converter(e)
}
case class TermArg (override val name: String, override val allowsFresh: List[String] = Nil) extends ArgInfo {
  val sort = "term"
}
case class StringArg (override val name: String, override val allowsFresh: List[String] = Nil) extends ArgInfo {
  val sort = "string"
}
case class SubstitutionArg (override val name: String, override val allowsFresh: List[String] = Nil) extends ArgInfo {
  val sort = "subst"
}
case class OptionArg(arg: ArgInfo) extends ArgInfo {
  val name: String = arg.name
  val sort: String = "option[" + arg.sort + "]"
  val allowsFresh: List[String] = arg.allowsFresh
}
@deprecated("Until lists are actually added to the concrete syntax of Bellerophon.", "4.2b1")
case class ListArg (override val name: String, elementSort: String, override val allowsFresh: List[String] = Nil) extends ArgInfo {
  val sort = "list"
}

