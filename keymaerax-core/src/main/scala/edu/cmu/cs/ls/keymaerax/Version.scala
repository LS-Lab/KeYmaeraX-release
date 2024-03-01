/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax

object Version {
  case class VersionString(major: Int, minor: Int, rev: Int, letter: Option[Char], incr: Option[Int]) {
    def <(that: VersionString): Boolean = compareTo(that) == -1
    def >(that: VersionString): Boolean = compareTo(that) == 1
    def >=(that: VersionString): Boolean = !(this < that)
    def <=(that: VersionString): Boolean = !(this > that)
    def !=(that: VersionString): Boolean = !this.equals(that)

    def compareTo(that: VersionString): Int = {
      if (major != that.major) major.compareTo(that.major)
      else if (minor != that.minor) minor.compareTo(that.minor)
      else if (rev != that.rev) rev.compareTo(that.rev) // @note undefined rev == -1, 4.0.1 > 4.0.0 > 4.0 (.-1)
      else if (letter.isEmpty && that.letter.isDefined) 1 // 4.0 > 4.0b
      else if (letter.isDefined && that.letter.isEmpty) -1
      else if (letter != that.letter) letter.get.compareTo(that.letter.get)
      else if (incr.isEmpty && that.incr.isDefined) 1 // 4.0a > 4.0a1
      else if (incr.isDefined && that.incr.isEmpty) -1
      else if (incr != that.incr) incr.get.compareTo(that.incr.get) // 4.0b2 > 4.0b1
      else 0
    }
  }

  def apply(s: String): VersionString = {
    val versionFormat = """^(?<major>\d+)\.(?<minor>\d+)((?<letter>\w)(?<incr>\d)?|\.(?<rev>\d+))?$""".r
    val matchedOpt = versionFormat.findFirstMatchIn(s)
    require(matchedOpt.isDefined, s"Unexpected version string $s")
    val matched = matchedOpt.get

    val major: Int = matched.group("major").toInt
    val minor: Int = matched.group("minor").toInt
    val letter: Option[Char] = Option(matched.group("letter")).map(s => s.charAt(0))
    val incr: Option[Int] = Option(matched.group("incr")).map(s => s.toInt)
    val rev: Int = Option(matched.group("rev")).map(s => s.toInt).getOrElse(-1)

    VersionString(major, minor, rev, letter, incr)
  }

}
