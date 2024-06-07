/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax

import java.net.URI

/**
 * Information about the KeYmaera X project.
 *
 * This object centralizes project information like the name, domain, and home page URL. Whenever this information is
 * needed, the corresponding field of this object should be used. This helps prevent inconsistencies and makes it easier
 * to change the information.
 */
package object info {

  /** The full project name, including correct case and whitespace. */
  val FullName = "KeYmaera X"

  /** A version of the name that is safe to use in technical contexts (e.g. file names). */
  val TechnicalName = "keymaerax"

  /** The current project version. */
  val Version: VersionNumber = VersionNumber.parse(BuildInfo.version)

  /** The full name and version of the project. */
  val FullNameAndVersion = s"$FullName $Version"

  val Website = new URI("https://keymaerax.org/")

  /** Domain used to uniquely identify the project. */
  // TODO Switch to keymaerax.org and move all source files as well
  val Domain = "keymaerax.ls.cs.cmu.edu"

  val DomainReversed = Domain.split('.').reverseIterator.mkString(".")

  /** The full copyright text, taken from the `COPYRIGHT.txt` file. */
  val FullCopyright = BuildInfo.copyright.stripLineEnd

  /** A single line of copyright information. */
  val ShortCopyright = BuildInfo.copyright.linesIterator.find(line => line.startsWith("Copyright")).get

  /** The full license, taken from the `LICENSE.txt` file. */
  val License = BuildInfo.license.stripLineEnd
}
