package edu.cmu.cs.ls.keymaerax.hydra

import spray.json._

/**
  * @author Nathan Fulton
  */
object UpdateChecker {
  /**
    * Returns a pair containing:
    *   * a boolean flag that is set to true whenever the current version equals the latest version number
    *   * the latest version number according to KeYmaeraX.org/version.json
    * or else None if we could not determine the most recent version (e.g., because we have no network connection).
    */
  def apply() : Option[(Boolean, String)] = {
    downloadCurrentVersion() match {
      case Some(current) => Some((current == edu.cmu.cs.ls.keymaerax.core.VERSION, current))
      case None          => None
    }
  }

  /** Returns an option containing a boolean value indicating whether KeYmaera X is up to date, or None if current version info could not be downloaded. */
  def upToDate() : Option[Boolean] = apply() match {
    case Some((latest, version)) => Some(latest)
    case None => None
  }

  /** Returns an option containing the version number of the latest KeYmaera X release, or None if current version info could not be downloaded. */
  def latestVersion() : Option[String] = apply() match {
    case Some((latest, version)) => Some(version)
    case None => None
  }

  /** Returns the current version # in keymaerax.org/version.json, or None if the contents cannot be downloaded/parsed. */
  private def downloadCurrentVersion() : Option[String] = {
    try {
      val json = JsonParser(scala.io.Source.fromURL("http://keymaerax.org/version.json").mkString)
      if(json.asJsObject.getFields("version").isEmpty)
        throw new Exception("version.json does not contain a version key.")
      else {
        val versionString = json.asJsObject.getFields("version").last
        Some(versionString.toString)
      }
    }
    catch {
      case e: Throwable => None
    }
  }
}
