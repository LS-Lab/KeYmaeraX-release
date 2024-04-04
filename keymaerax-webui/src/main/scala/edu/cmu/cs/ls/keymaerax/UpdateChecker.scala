/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax

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
   *
   * If this KeYmaera X instance's version number is newer than the latest version, it is also considered up-to-date.
   * This may happen during development or testing of a new version.
   */
  lazy val upToDate: Option[Boolean] = latestVersion.map(_ >= Version.CURRENT)

  /** The version number of the latest KeYmaera X release, or [[None]] if version info could not be retrieved. */
  lazy val latestVersion: Option[Version] = latestVersionInfo.map(_._2)

  /** The version number of the latest KeYmaera X release, or [[None]] if version info could not be retrieved. */
  lazy val latestVersionString: Option[String] = latestVersionInfo.map(_._1)

  private lazy val latestVersionInfo: Option[(String, Version)] = fetchLatestVersionInfo()

  /** Queries [[https://keymaerax.org/version.json]] and returns the version number. */
  private def fetchLatestVersionInfo(): Option[(String, Version)] =
    try {
      val uri = new URI("https://keymaerax.org/version.json")
      val timeout = Duration.ofSeconds(3)
      val versionString = fetchStringFromUri(uri, timeout).parseJson.asJsObject.fields("version").convertTo[String]
      Some((versionString, Version.parse(versionString)))
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

  /** Indicates whether `dbVersion` is outdated (i.e. older than expected by this KeYmaera X) and needs upgrading. */
  def dbUpgradeRequired(dbVersion: Version): Option[Boolean] = { oldestAcceptableDbVersion.map(dbVersion < _) }

  private lazy val oldestAcceptableDbVersion: Option[Version] =
    try {
      val versionString = Source
        .fromResource("/sql/upgradescripts.json")(Codec.UTF8)
        .mkString
        .parseJson
        .asJsObject
        .fields("minVersion")
        .convertTo[String]

      Some(Version.parse(versionString))
    } catch { case _: Throwable => None }
}
