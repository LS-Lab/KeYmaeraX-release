/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.cli

import org.keymaerax.info.{Version, VersionNumber}
import org.keymaerax.{Configuration, Logging}

import java.io.IOException
import java.nio.file.attribute.BasicFileAttributes
import java.nio.file.{FileVisitResult, Files, NoSuchFileException, Path, SimpleFileVisitor}
import scala.util.Try

object LemmaCacheChecks extends Logging {
  private def versionFile(cacheDir: Path): Path = cacheDir.resolve("VERSION")

  /** Clear the cache if it was created by a different version of KeYmaera X. */
  def clearCacheIfDeprecated(): Unit = {
    val cacheDir = Path.of(Configuration.path(Configuration.Keys.LEMMA_CACHE_PATH))

    // If we can't read the version, just erase the cache.
    val version = Try {
      val versionStr = Files.readString(versionFile(cacheDir))
      VersionNumber.parse(versionStr.trim)
    }.toOption

    if (version.contains(Version)) return

    clearCache(cacheDir)
  }

  /** Create an empty cache with current version file at the path, removing any existing cache in the process. */
  private def clearCache(cacheDir: Path): Unit = {
    logger.info("Clearing your cache because of an update.")

    createDirectory(cacheDir.getParent)
    deleteDirectory(cacheDir)
    createDirectory(cacheDir)

    try Files.writeString(versionFile(cacheDir), Version.toString)
    catch {
      case e: Exception => throw new Exception(s"Failed to create version file in ${cacheDir.toAbsolutePath}: $e")
    }
  }

  /** Create a directory and all its parents. */
  private def createDirectory(dir: Path) = {
    try Files.createDirectories(dir)
    catch { case e: Exception => throw new Exception(s"Failed to create directory ${dir.toAbsolutePath}: $e") }
  }

  /** Recursively delete a directory. */
  private def deleteDirectory(dir: Path) = {
    try Files.walkFileTree(
        dir,
        new SimpleFileVisitor[Path] {
          override def visitFile(file: Path, attrs: BasicFileAttributes): FileVisitResult = {
            Files.deleteIfExists(file)
            FileVisitResult.CONTINUE
          }
          override def postVisitDirectory(dir: Path, exc: IOException): FileVisitResult = {
            Files.deleteIfExists(dir)
            FileVisitResult.CONTINUE
          }
        },
      )
    catch {
      case _: NoSuchFileException => // Nothing to do, the directory does not exist
      case e: Exception => throw new Exception(s"Failed to delete directory ${dir.toAbsolutePath}: $e")
    }
  }
}
