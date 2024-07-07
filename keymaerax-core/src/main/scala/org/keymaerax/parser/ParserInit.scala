/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.parser

import org.keymaerax.Configuration

/** Initializes the parser. */
object ParserInit {

  /** Initializes the parser from configuration. */
  def fromConfig(): Parser = Configuration.getString(Configuration.Keys.PARSER) match {
    case Some("KeYmaeraXParser") | None => KeYmaeraXParser.parser
    case Some("DLParser") => DLParser
    case Some(parserId) => throw new IllegalArgumentException(
        "Unknown parser " + parserId + "; please use one of DLParser or KeYmaeraXParser"
      )
  }

  /** A parser that the DLParser uses to double-check its results. */
  def checkAgainstFromConfig(): Option[Parser] =
    Configuration.getString(Configuration.Keys.CHECK_AGAINST_PARSER) match {
      case None | Some("") => None
      case Some("KeYmaeraXParser") => Some(KeYmaeraXParser.parser)
      case Some("DLParser") => Some(DLParser)
      case Some(parserId) => throw new IllegalArgumentException(
          "Unknown parser " + parserId + "; please use one of DLParser or KeYmaeraXParser"
        )
    }
}
