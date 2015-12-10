package edu.cmu.cs.ls.keymaerax.hydra

import spray.json._

/**
  * @author Nathan Fulton
  */
object UpdateChecker {

  def needDatabaseUpgrade(installedVersion: String = edu.cmu.cs.ls.keymaerax.core.VERSION) : Option[Boolean] = {
    downloadDBVersion() match {
      case Some(oldestAcceptableDBVersion) =>
        Some(StringToVersion(installedVersion) < StringToVersion(oldestAcceptableDBVersion))
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
    downloadCurrentVersion() match {
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

  private def downloadDBVersion() : Option[String] = {
    try {
      val json = JsonParser(scala.io.Source.fromURL("http://keymaerax.org/version.json").mkString)
      if(json.asJsObject.getFields("oldestAcceptableDB").isEmpty)
        throw new Exception("version.json does not contain a DBVersion key.")
      else {
        val versionString = json.asJsObject.getFields("oldestAcceptableDB").last.toString.replace("\"", "")
        println("Got oldestAcceptableDB string: " + versionString)
        Some(versionString)
      }
    }
    catch {
      case e: Throwable => None
    }
  }

  /** Returns the current version # in keymaerax.org/version.json, or None if the contents cannot be downloaded/parsed. */
  private def downloadCurrentVersion() : Option[String] = {
    try {
      val json = JsonParser(scala.io.Source.fromURL("http://keymaerax.org/version.json").mkString)
      if(json.asJsObject.getFields("version").isEmpty)
        throw new Exception("version.json does not contain a version key.")
      else {
        val versionString = json.asJsObject.getFields("version").last.toString.replace("\"", "")
        println("Got version string: " + versionString)
        Some(versionString)
      }
    }
    catch {
      case e: Throwable => None
    }
  }

}

case class VersionString(major: Int, minor: Int, letter: Option[Char], incr: Option[Int]) {
  require(letter.isDefined == incr.isDefined)

  def <(that: VersionString) = compareTo(that) == -1
  def >(that: VersionString) = compareTo(that) == 1
  def >=(that: VersionString) = !(this < that)
  def <=(that: VersionString) = !(this > that)

  def compareTo(that: VersionString) = {
    if(major > that.major) 1
    else if(major < that.major) -1
    else if(minor > that.minor) 1
    else if(minor < that.minor) -1
    else if(letter.isEmpty && !that.letter.isEmpty) 1 //4.0 > 4.0b
    else if(!letter.isEmpty && that.letter.isEmpty) -1
    else if(letter.get == 'b' && that.letter.get == 'a') 1 //4.0b > 4.0a
    else if(letter.get == 'a' && that.letter.get == 'b') -1
    else incr.get.compareTo(that.incr.get) //4.0b2 > b.0b1
  }
}

object StringToVersion {
  def apply(s: String): VersionString = {
    val (major, d1) = {
      val parts = s.split("\\.")
      (parts(0).toInt, parts(1))
    }

    val (minor: Int, letter: Option[Char], incr: Option[Int]) = {
      if(d1.contains("a") || d1.contains("b")) {
        val parts = d1.split("a|b")
        val letter = if (d1.contains("a")) 'a' else if (d1.contains("b")) 'b' else ???
        (parts(0).toInt, Some(letter), Some(parts(1).toInt))
      }
      else {
        (d1.toInt, None, None)
      }
    }
    VersionString(major, minor, letter, incr)
  }
}
