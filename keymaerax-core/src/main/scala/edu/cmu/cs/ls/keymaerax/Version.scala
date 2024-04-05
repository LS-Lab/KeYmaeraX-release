/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax

/** A version parsed into its constituent components. */
case class Version(major: Int, minor: Int, patch: Int) extends Ordered[Version] {
  override def compare(that: Version): Int = {
    import scala.math.Ordered.orderingToOrdered
    (this.major, this.minor, this.patch) compare (that.major, that.minor, that.patch)
  }

  override def toString: String = s"$major.$minor.$patch"
}

object Version {

  /** This KeYmaera X instance's version, parsed from [[edu.cmu.cs.ls.keymaerax.core.VERSION]]. */
  val CURRENT: Version = Version.parse(edu.cmu.cs.ls.keymaerax.core.VERSION)

  /**
   * Parse a version from a string with the format `<major>.<minor>.<patch>`. The fields `major`, `minor`, `patch` are
   * positive integers with at least one digit and no additional leading zeroes.
   *
   * If you need the current version, use [[CURRENT]] instead of parsing [[edu.cmu.cs.ls.keymaerax.core.VERSION]].
   *
   * @throws IllegalArgumentException
   *   invalid version string
   */
  def parse(s: String): Version = {
    val versionFormat = """^(?<major>0|[1-9][0-9]*)\.(?<minor>0|[1-9][0-9]*)\.(?<patch>0|[1-9][0-9]*)$""".r
    val matched = versionFormat.findFirstMatchIn(s) match {
      case Some(m) => m
      case None => throw new IllegalArgumentException(s"Invalid version string $s")
    }

    try {
      // These conversions could still fail because the numbers could be too large.
      val major = matched.group("major").toInt
      val minor = matched.group("minor").toInt
      val patch = matched.group("patch").toInt
      Version(major, minor, patch)
    } catch { case _: NumberFormatException => throw new IllegalArgumentException(s"Invalid version string $s") }
  }
}
