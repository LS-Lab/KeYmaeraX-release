/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax

import edu.cmu.cs.ls.keymaerax.core.VERSION
import spray.json.DefaultJsonProtocol._
import spray.json._

import java.net.URI
import java.time.Duration
import scala.io.{Codec, Source}

/**
 * Uses the JSON file at [[https://keymaerax.org/version.json]] to check whether a new update is available. The JSON
 * should have a field called `version` that is the version of the latest stable release.
 *
 * @author
 *   Nathan Fulton
 */
object UpdateChecker extends Logging {

  /**
   * Whether this KeYmaera X instance is using the latest version, or [[None]] if version info could not be retrieved.
   */
  // TODO Compare using VersionString instead of == on Strings
  lazy val upToDate: Option[Boolean] = latestVersion.map(_ == VERSION)

  /** The version number of the latest KeYmaera X release, or [[None]] if version info could not be retrieved. */
  lazy val latestVersion: Option[String] = fetchLatestVersion()

  /** Queries [[https://keymaerax.org/version.json]] and returns the version number. */
  // TODO Return a VersionString instead
  private def fetchLatestVersion(): Option[String] =
    try {
      val uri = new URI("https://keymaerax.org/version.json")
      val timeout = Duration.ofSeconds(3)
      val versionString = fetchStringFromUri(uri, timeout).parseJson.asJsObject.fields("version").convertTo[String]
      Some(versionString)
    } catch { case _: Throwable => None }

  /**
   * Fetch a string from a URL.
   *
   * Similar to [[Source.fromURI]], but with timeout.
   */
  private def fetchStringFromUri(uri: URI, timeout: Duration): String = {
    val conn = uri.toURL.openConnection()

    val timeoutMillis = timeout.toMillis.toInt
    conn.setConnectTimeout(timeoutMillis)
    conn.setReadTimeout(timeoutMillis)

    val source = Source.fromInputStream(conn.getInputStream)(Codec.UTF8)
    val data = source.mkString
    source.close()
    data
  }

  /**
   * Indicates whether `databaseVersion` is outdated (i.e. older than expected by this KeYmaera X) and needs upgrading.
   */
  def needDatabaseUpgrade(databaseVersion: String): Option[Boolean] = {
    minDBVersion match {
      case Some(oldestAcceptableDBVersion) =>
        Some(Version.parse(databaseVersion) < Version.parse(oldestAcceptableDBVersion))
      case None => None
    }
  }

  private lazy val minDBVersion: Option[String] = {
    try {
      val json = scala.io.Source.fromInputStream(getClass.getResourceAsStream("/sql/upgradescripts.json")).mkString
      val versionString = json.parseJson.asJsObject.fields("minVersion").convertTo[String]
      logger.debug("Compatible database versions: " + versionString + "+")
      Some(versionString)
    } catch { case _: Throwable => None }
  }
}
