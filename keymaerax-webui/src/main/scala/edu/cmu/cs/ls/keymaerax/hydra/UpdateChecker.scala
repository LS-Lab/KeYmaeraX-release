package edu.cmu.cs.ls.keymaerax.hydra

import org.apache.logging.log4j.scala.Logging
import spray.json._
import spray.json.DefaultJsonProtocol._

/**
  * The JSON should be a http://keymaerax.org/version.json and should look like:
  * {{{
  *   {
  *     "version": "A_VERSION_STRING",
  *     "oldestAcceptableDB": "A_VERSION_STRING"
  *   }
  * }}}

  * where the value of {{{"version"}}} is the latest stable release
  * and the value of {{{"oldestAcceptableDB"}}} is the last version number where the DB schema changed.
  *
  * A_VERSION_STRING should have one of the formats following:
  * {{{
  *   X.X
  *   X.X.X
  *   X.XbX
*   }}}
  * where X is a natural number.
  *
  * @author Nathan Fulton
  */
object UpdateChecker extends Logging {

  def needDatabaseUpgrade(databaseVersion: String) : Option[Boolean] = {
    downloadDBVersion match {
      case Some(oldestAcceptableDBVersion) =>
        Some(StringToVersion(databaseVersion) < StringToVersion(oldestAcceptableDBVersion))
      case None => None
    }
  }

  /**
    * Returns a pair containing:
    *   * a boolean flag that is set to true whenever the current version equals the latest version number
    *   * the latest version number according to KeYmaeraX.org/version.json
    * or else None if we could not determine the most recent version (e.g., because we have no network connection).
    */
  def getVersionStatus() : Option[(Boolean, String)] = {
    downloadCurrentVersion match {
      case Some(current) => Some((current == edu.cmu.cs.ls.keymaerax.core.VERSION, current))
      case None          => None
    }
  }

  /** Returns an option containing a boolean value indicating whether KeYmaera X is up to date, or None if current version info could not be downloaded. */
  def upToDate() : Option[Boolean] = getVersionStatus() match {
    case Some((latest, version)) => Some(latest)
    case None => None
  }

  /** Returns an option containing the version number of the latest KeYmaera X release, or None if current version info could not be downloaded. */
  def latestVersion() : Option[String] = getVersionStatus() match {
    case Some((latest, version)) => Some(version)
    case None => None
  }

  private lazy val downloadDBVersion : Option[String] = {
    try {
      val json = scala.io.Source.fromInputStream(getClass.getResourceAsStream("/sql/upgradescripts.json")).mkString
      val versionString = json.parseJson.asJsObject.fields("minVersion").convertTo[String]
      logger.info("Oldest compatible database version: " + versionString)
      Some(versionString)
    } catch {
      case _: Throwable => None
    }
  }

  /** Returns the current version # in keymaerax.org/version.json, or None if the contents cannot be downloaded/parsed. */
  private lazy val downloadCurrentVersion: Option[String] = {
    try {
      val json = JsonParser(scala.io.Source.fromURL("http://keymaerax.org/version.json").mkString)
      val version = json.asJsObject.getFields("version")
      if (version.isEmpty)
        throw new Exception("version.json does not contain a version key.")
      else {
        val versionString = version.last.toString.replace("\"", "")
        Some(versionString)
      }
    }
    catch {
      case e: Throwable => None
    }
  }

}

case class VersionString(major: Int, minor: Int, rev: Int, letter: Option[Char], incr: Option[Int]) {
  def <(that: VersionString) = compareTo(that) == -1
  def >(that: VersionString) = compareTo(that) == 1
  def >=(that: VersionString) = !(this < that)
  def <=(that: VersionString) = !(this > that)
  def !=(that: VersionString) = !this.equals(that)

  def compareTo(that: VersionString) = {
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

object StringToVersion {
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
