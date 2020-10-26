/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax

import org.slf4j.{Logger, LoggerFactory}

/** Provides a class-specific logger. */
trait Logging {
  val logger: Logger = LoggerFactory.getLogger(getClass)
}
