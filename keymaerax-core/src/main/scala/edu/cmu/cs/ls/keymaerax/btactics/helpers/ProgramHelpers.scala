/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics.helpers

import edu.cmu.cs.ls.keymaerax.core._

/**
  * @author Nathan Fulton
  */
object ProgramHelpers {
  def decomposeChoices(program: Program): List[Program] = program match {
    case Choice(l,r) => decomposeChoices(l) ++ decomposeChoices(r)
    case _ => program :: Nil
  }

  /** Returns true iff the program is of form {{{?H; a:=t}}} or of form {{{a:=t}}}*/
  def optionallyGuardedAssignments(p: Program) = p match {
    case Compose(Test(_), assignments) => sequenceOfAssignments(assignments)
    case _ => sequenceOfAssignments(p)
  }

  def sequenceOfAssignments(p: Program): Boolean = p match {
    case x:Assign => true
    case x:AssignAny => true
    case Compose(l,r) => sequenceOfAssignments(l) && sequenceOfAssignments(r)
    case _ => false
  }

  def containsAssignmentTo(program: Program, x: Variable): Boolean = program match {
    case Compose(l,r) => containsAssignmentTo(l, x) || containsAssignmentTo(r, x)
    case Assign(y, _) => x==y
    case AssignAny(y) => x==y
    case _ => false
  }
}
