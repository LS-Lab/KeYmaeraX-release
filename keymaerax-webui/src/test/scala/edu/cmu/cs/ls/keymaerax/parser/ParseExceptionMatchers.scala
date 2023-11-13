/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.parser

import org.scalatest.matchers.{MatchResult, Matcher}

trait ParseExceptionMatchers {

  class ExceptionPointsAtLocationMatcher(line: Int, column: Int) extends Matcher[ParseException] {
    override def apply(left: ParseException): MatchResult = {
      val loc = left.loc
      MatchResult(
        loc.line == line && loc.column == column,
        s"Expected location $line:$column does not match actual location ${loc.line}:${loc.column}.",
        s"Expected location $line:$column matches actual location."
      )
    }
  }

  class ExceptionMessageMentionsMatcher(part: String) extends Matcher[ParseException] {
    override def apply(left: ParseException): MatchResult = {
      val msg = left.getMessage
      MatchResult(
        msg.toLowerCase().contains(part.toLowerCase()),
        s"""Actual message "$msg" does not mention "$part".""",
        s"""Actual message "$msg" does mention "$part"."""
      )
    }
  }

  /**
   * Matches the location the [[ParseException]] refers to.
   * @param line The number of the line the parser error occurred in.
   * @param column The number of the column where the error occurred.
   * @return A [[Matcher]] matching [[ParseException]] on lhs.
   */
  def pointAt(line: Int, column: Int) = new ExceptionPointsAtLocationMatcher(line, column)

  /**
   * Matches a [[ParseException]] whenever it mentions a specified substring in its error message.
   * Matching is performed completely case-insensitive.
   * @param part The substring the exceptions message should contain.
   * @return A [[Matcher]] matching [[ParseException]] on lhs.
   */
  def mention(part: String) = new ExceptionMessageMentionsMatcher(part)

}

object ParseExceptionMatchers extends ParseExceptionMatchers