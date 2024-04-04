/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax

// TODO Either get rid of letter and incr or make version format more general

/** A version parsed into its constituent components. */
case class Version(major: Int, minor: Int, rev: Int, letter: Option[Char], incr: Option[Int]) extends Ordered[Version] {
  override def compare(that: Version): Int = {
    if (major != that.major) major.compareTo(that.major)
    else if (minor != that.minor) minor.compareTo(that.minor)
    else if (rev != that.rev) rev.compareTo(that.rev) // undefined rev == -1, so 4.0 (.-1) < 4.0.0 < 4.0.1
    else if (letter.isEmpty && that.letter.isDefined) 1 // 4.0b < 4.0
    else if (letter.isDefined && that.letter.isEmpty) -1
    else if (letter != that.letter) letter.get.compareTo(that.letter.get)
    else if (incr.isEmpty && that.incr.isDefined) 1 // 4.0a1 < 4.0a
    else if (incr.isDefined && that.incr.isEmpty) -1
    else if (incr != that.incr) incr.get.compareTo(that.incr.get) // 4.0b1 < 4.0b2
    else 0
  }
}

object Version {

  /** This KeYmaera X instance's version, parsed from [[edu.cmu.cs.ls.keymaerax.core.VERSION]]. */
  val CURRENT: Version = Version.parse(edu.cmu.cs.ls.keymaerax.core.VERSION)

  /**
   * Parse a version from a string.
   *
   * The string must have one of these formats:
   *   1. `<major>.<minor>`
   *   1. `<major>.<minor>.<rev>`
   *   1. `<major>.<minor><letter>`
   *   1. `<major>.<minor><letter><incr>`
   *
   * The fields `major`, `minor`, `rev` are positive integers with at least one digit. The field `letter` is a single
   * character. The field `incr` is a single digit.
   *
   * If you need the current version, use [[CURRENT]] instead of parsing [[edu.cmu.cs.ls.keymaerax.core.VERSION]].
   *
   * @throws IllegalArgumentException
   *   invalid version string
   */
  def parse(s: String): Version = {
    val versionFormat = """^(?<major>\d+)\.(?<minor>\d+)((?<letter>\w)(?<incr>\d)?|\.(?<rev>\d+))?$""".r
    val matched = versionFormat.findFirstMatchIn(s) match {
      case Some(m) => m
      case None => throw new IllegalArgumentException(s"Invalid version string $s")
    }

    val major: Int = matched.group("major").toInt
    val minor: Int = matched.group("minor").toInt
    val letter: Option[Char] = Option(matched.group("letter")).map(s => s.charAt(0))
    val incr: Option[Int] = Option(matched.group("incr")).map(s => s.toInt)
    val rev: Int = Option(matched.group("rev")).map(s => s.toInt).getOrElse(-1)

    Version(major, minor, rev, letter, incr)
  }
}
