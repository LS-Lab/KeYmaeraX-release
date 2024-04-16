/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax

import java.net.{SocketTimeoutException, URL}

import spray.json.DefaultJsonProtocol._
import spray.json._

/**
 * The JSON should be a https://keymaerax.org/version.json and should look like:
 * {{{
 *   {
 *     "version": "A_VERSION_STRING",
 *     "oldestAcceptableDB": "A_VERSION_STRING"
 *   }
 * }}}
 *
 * where the value of {{{"version"}}} is the latest stable release and the value of {{{"oldestAcceptableDB"}}} is the
 * last version number where the DB schema changed.
 *
 * A_VERSION_STRING should have one of the formats following:
 * {{{
 *   X.X
 *   X.X.X
 *   X.XbX
 * }}}
 * where X is a natural number.
 *
 * @author
 *   Nathan Fulton
 */
object UpdateChecker extends Logging {

  /**
   * Indicates whether `databaseVersion` is outdated (i.e. older than expected by this KeYmaera X) and needs upgrading.
   */
  def needDatabaseUpgrade(databaseVersion: String): Option[Boolean] = {
    minDBVersion match {
      case Some(oldestAcceptableDBVersion) => Some(Version(databaseVersion) < Version(oldestAcceptableDBVersion))
      case None => None
    }
  }

  /**
   * Returns a pair containing:
   *   - a boolean flag that is set to true whenever the current version equals the latest version number
   *   - the latest version number according to KeYmaeraX.org/version.json
   * or else None if we could not determine the most recent version (e.g., because we have no network connection).
   */
  def getVersionStatus: Option[(Boolean, String)] = {
    downloadCurrentVersion match {
      case Some(current) => Some((current == edu.cmu.cs.ls.keymaerax.core.VERSION, current))
      case None => None
    }
  }

  /**
   * Returns an option containing a boolean value indicating whether KeYmaera X is up to date, or None if current
   * version info could not be downloaded.
   */
  def upToDate(): Option[Boolean] = getVersionStatus match {
    case Some((latest, _)) => Some(latest)
    case None => None
  }

  /**
   * Returns an option containing the version number of the latest KeYmaera X release, or None if current version info
   * could not be downloaded.
   */
  def latestVersion(): Option[String] = getVersionStatus match {
    case Some((_, version)) => Some(version)
    case None => None
  }

  private lazy val minDBVersion: Option[String] = {
    try {
      val json = scala.io.Source.fromInputStream(getClass.getResourceAsStream("/sql/upgradescripts.json")).mkString
      val versionString = json.parseJson.asJsObject.fields("minVersion").convertTo[String]
      logger.debug("Compatible database versions: " + versionString + "+")
      Some(versionString)
    } catch { case _: Throwable => None }
  }

  /**
   * Returns the current version # in keymaerax.org/version.json, or None if the contents cannot be downloaded/parsed.
   */
  private lazy val downloadCurrentVersion: Option[String] = {
    try {
      readWithTimeout("https://keymaerax.org/version.json", 3000) match {
        case None => None
        case Some(string) =>
          val json = JsonParser(string)
          val version = json.asJsObject.getFields("version")
          if (version.isEmpty) throw new Exception("version.json does not contain a version key.")
          else {
            val versionString = version.last.toString.replace("\"", "")
            Some(versionString)
          }
      }
    } catch { case _: Throwable => None }
  }

  /** Read contents of url or None if unreachable within given timeout in milliseconds */
  private def readWithTimeout(url: String, timeout: Int): Option[String] =
    try {
      // like scala.io.Source.fromURL(url).mkString but with timeout
      val conn = new URL(url).openConnection()
      conn.setConnectTimeout(timeout)
      conn.setReadTimeout(timeout)
      val source = conn.getInputStream
      val read = scala.io.Source.fromInputStream(source).mkString
      if (source != null) source.close()
      Some(read)
    } catch { case _: SocketTimeoutException => None }

}
