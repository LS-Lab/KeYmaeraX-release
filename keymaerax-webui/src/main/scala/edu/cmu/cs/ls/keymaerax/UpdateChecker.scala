/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax

import edu.cmu.cs.ls.keymaerax.info.VersionNumber
import spray.json.DefaultJsonProtocol._
import spray.json._

import java.net.URI
import java.time.Duration
import scala.io.{Codec, Source}

/**
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
  lazy val upToDate: Option[Boolean] = latestVersion.map(_ >= VersionNumber.CURRENT)

  /** The version number of the latest KeYmaera X release, or [[None]] if version info could not be retrieved. */
  lazy val latestVersion: Option[VersionNumber] = fetchLatestVersion()

  /**
   * Queries the [[https://github.com/LS-Lab/KeYmaeraX-release/releases GitHub releases]] and returns the latest
   * release's tag name as version number.
   *
   * We might want to publish bug fix releases for older versions in-between releases for the latest version. If we just
   * fetched the latest release, we might not get the latest version number. Because of this, more than one release is
   * queried and the highest version number found is returned.
   *
   * @return
   *   Version number of the latest release, or [[None]] if anything went wrong.
   */
  private def fetchLatestVersion(): Option[VersionNumber] =
    try {
      // https://docs.github.com/en/rest/releases/releases?apiVersion=2022-11-28#list-releases
      val owner = "LS-Lab"
      val repo = "KeYmaeraX-release"
      val amount = 32 // Max value according to API docs is 100
      val uri = new URI(s"https://api.github.com/repos/$owner/$repo/releases?per_page=$amount")

      val timeout = Duration.ofSeconds(3)
      val releases = fetchStringFromUri(uri, timeout).parseJson.convertTo[List[JsObject]]

      releases
        .filter(r => !r.fields("draft").convertTo[Boolean])
        .filter(r => !r.fields("prerelease").convertTo[Boolean])
        .map(r => r.fields("tag_name").convertTo[String])
        .flatMap(VersionNumber.parseOption)
        .maxOption
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
  def dbUpgradeRequired(dbVersion: VersionNumber): Option[Boolean] = { oldestAcceptableDbVersion.map(dbVersion < _) }

  private lazy val oldestAcceptableDbVersion: Option[VersionNumber] =
    try {
      val versionString = Source
        .fromResource("/sql/upgradescripts.json")(Codec.UTF8)
        .mkString
        .parseJson
        .asJsObject
        .fields("minVersion")
        .convertTo[String]

      Some(VersionNumber.parse(versionString))
    } catch { case _: Throwable => None }
}
