/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.cli

import org.keymaerax.info.Version

/** Light-weight evidence header for file artifacts produced by KeYmaera X. */
object EvidencePrinter {

  /** Generate a header stamping the source of a generated file */
  // @todo Of course this has a security attack for non-letter characters like end of comments from command line
  def stampHead(args: Seq[String]): String = {
    val commandLineOptions = nocomment(args.mkString(" "))
    s"/* @evidence: generated by KeYmaeraX $Version $commandLineOptions */\n\n"
  }

  /** Replace C-style line-comments in command line (from wildcard paths) */
  private def nocomment(s: String): String = s.replace("/*", "/STAR").replace("*/", "STAR/")
}