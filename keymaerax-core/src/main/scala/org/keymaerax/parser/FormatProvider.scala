/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.parser

import org.keymaerax.core.Expression

trait FormatProvider {

  /**
   * Prints whitespace and checks that the remaining format string starts with `check` (literally). Advances the format
   * string past `check`.
   */
  def printWS(check: String = ""): String

  /** Prints whitespace prefix and formats `next` according to the format string. */
  def print(next: String): String
}

/** Stateful format provider to read off whitespace and line breaks from a pretty-printed string. */
abstract class PrettyPrintFormatProvider(format: String, wsPrinter: String => String) extends FormatProvider {
  private val LINEINDENT = "\\n(\\s*)".r
  private val SPACES = "\\s+".r

  private var processedFormat = format

  /** Advances the format string `format` to the first non-whitespace character and returns the whitespace prefix. */
  def advanceWS(): String = {
    LINEINDENT.findPrefixMatchOf(processedFormat) match {
      case Some(m) =>
        processedFormat = processedFormat.substring(m.end)
        m.matched
      case None => SPACES.findPrefixMatchOf(processedFormat) match {
          case Some(m) =>
            processedFormat = processedFormat.substring(m.end)
            m.matched
          case None => ""
        }
    }
  }

  /**
   * Prints whitespace and checks that the remaining format string starts with `check` (literally). Advances the format
   * string past `check`.
   */
  def printWS(check: String = ""): String = {
    val result = wsPrinter(advanceWS())
    assert(processedFormat.startsWith(check), s"'$processedFormat' did not start with '$check'")
    processedFormat = processedFormat.substring(check.length)
    result
  }

  /** Prints whitespace prefix and formats `next` according to the format string. */
  def print(next: String): String = {
    wsPrinter(advanceWS()) +
      next.map(c => printWS(if (c != ' ') c.toString else "") + c).reduceOption(_ + _).getOrElse("")
  }
}

/** Noop format provider. */
class NoneFormatProvider extends FormatProvider {
  override def printWS(check: String): String = ""
  override def print(next: String): String = next
}
