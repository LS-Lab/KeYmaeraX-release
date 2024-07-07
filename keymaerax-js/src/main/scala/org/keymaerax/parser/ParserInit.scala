/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package org.keymaerax.parser

import org.keymaerax.Configuration

/** Initializes the parser. */
object ParserInit {
  /** Initializes the parser from configuration. */
  def fromConfig(): Parser = Configuration.getString(Configuration.Keys.PARSER) match {
    case Some("DLParser") | None => DLParser
    case Some(parserId) => throw new IllegalArgumentException("Unknown parser " + parserId + "; please use KeYmaeraXParser")
  }
  /** A parser that the DLParser uses to double-check its results. */
  def checkAgainstFromConfig(): Option[Parser] = None
}
