/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.cli

import org.apache.logging.log4j.core.config.{ConfigurationFactory, Configurator}
import org.keymaerax.Configuration

import java.net.URI

object GlobalLoggingSetup {

  /**
   * Configure the global logging according to the current [[Configuration]].
   *
   * @param verbosity
   *   How much to log. A verbosity of 0 is the default, while higher values make the output increasingly more verbose.
   */
  def configureLogger(verbosity: Int = 0): Unit = {
    val configUri = verbosity match {
      case n if n <= 0 => return
      case 1 => URI.create("classpath:log4j2-debug.xml")
      case _ => URI.create("classpath:log4j2-trace.xml")
    }

    val config = ConfigurationFactory.getInstance().getConfiguration(null, null, configUri)
    Configurator.reconfigure(config)
  }
}
