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
      else if (rev != that.rev) rev.compareTo(that.rev) //@note undefined rev == -1, 4.0.1 > 4.0.0 > 4.0 (.-1)
      else if (letter.isEmpty && that.letter.isDefined) 1 //4.0 > 4.0b
      else if (letter.isDefined && that.letter.isEmpty) -1
      else if (letter != that.letter) letter.get.compareTo(that.letter.get)
      else if (incr.isEmpty && that.incr.isDefined) 1 //4.0a > 4.0a1
      else if (incr.isDefined && that.incr.isEmpty) -1
      else if (incr != that.incr) incr.get.compareTo(that.incr.get) //4.0b2 > 4.0b1
      else 0
    }
  }

  def apply(s: String): VersionString = {
    val versionFormat = """^(\d+)\.(\d+)(?:(?:(\w)(\d?)|\.(\d+))?)$""".r("major", "minor", "letter", "incr", "rev")
    require(s.matches(versionFormat.regex), s"Unexpected version string $s")
    // only 1 match
    val m = versionFormat.findAllIn(s).matchData.toList.head
    val major: Int = m.group("major").toInt
    val minor: Int = m.group("minor").toInt
    val letter: Option[Char] = m.group("letter") match { case null => None case "" => None case l if l.length == 1 => Some(l.charAt(0)) }
    val incr: Option[Int]   = m.group("incr") match { case null => None case "" => None case i => Some(i.toInt) }
    val rev: Int = m.group("rev") match { case null => -1 case "" => -1 case r => r.toInt }

    VersionString(major, minor, rev, letter, incr)
  }

}
