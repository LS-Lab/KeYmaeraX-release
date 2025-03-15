/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

/**
 * @author
 *   Stefan Mitsch
 * @note
 *   Code Review: 2016-08-16
 */
package org.keymaerax.lemma

import org.keymaerax.info.{Version, VersionNumber}
import org.keymaerax.{Configuration, Logging}

import java.io.{File, IOException}
import java.nio.file.attribute.BasicFileAttributes
import java.nio.file.{FileVisitResult, Files, NoSuchFileException, Path, SimpleFileVisitor}
import scala.util.matching.Regex

/**
 * File-based lemma DB implementation. Stores one lemma per file in the user's home directory under
 * `.keymaerax/cache/lemmadb/` directory. Lemma file names are created automatically and in a thread-safe manner.
 *
 * @note
 *   Prefer LemmaDBFactory.lemmaDB over instantiating directly to get an instance of a lemma database and ensure thread
 *   safety.
 *
 * Created by smitsch on 4/27/15.
 * @author
 *   Stefan Mitsch
 * @author
 *   Brandon Bohrer
 */
class FileLemmaDB extends LemmaDBBase with Logging {

  /** The configured cache path (@todo needs to by lazy? or could be made class val?) */
  private lazy val cachePath = Path.of(Configuration.path(Configuration.Keys.LEMMA_CACHE_PATH))

  /**
   * Matches special characters in lemma names that might be problematic in file names (typically: whitespace, :, .).
   */
  private val SANITIZE_REGEX = "[^\\w\\-" + Regex.quote(File.separator) + "]"

  /** File handle to lemma database (creates parent directories if non-existent). */
  private lazy val lemmadbpath: Path = {
    val file = cachePath.resolve("lemmadb")
    Files.createDirectories(file)
    file
  }

  /** Replaces special file characters with _. */
  private def sanitize(id: LemmaID): LemmaID = id.replaceAll(SANITIZE_REGEX, "_")

  /** Returns the File representing lemma `id`. */
  private def file(id: LemmaID): Path = lemmadbpath.resolve(sanitize(id) + ".alp")

  /** Returns the File representing the folder `id`. */
  private def folder(id: LemmaID): Path = lemmadbpath.resolve(sanitize(id))

  /** @inheritdoc */
  final override def contains(lemmaID: LemmaID): Boolean = Files.exists(file(lemmaID))

  /** @inheritdoc */
  final override def createLemma(): LemmaID = {
    val f = Files.createTempFile(lemmadbpath, "lemma", ".alp")
    f.getFileName.toString.stripSuffix(".alp")
  }

  /** @inheritdoc */
  final override def readLemmas(ids: List[LemmaID]): Option[List[String]] = flatOpt(ids.map({ lemmaID =>
    val f = file(lemmaID)
    if (Files.exists(f)) Some(Files.readString(f)) else None
  }))

  /** @inheritdoc */
  final override def writeLemma(id: LemmaID, lemma: String): Unit = synchronized {
    val f = file(id)
    Files.createDirectories(f.getParent)
    Files.writeString(f, lemma)
  }

  /** @inheritdoc */
  final override def remove(id: String): Unit = {
    val f = file(id)
    Files.deleteIfExists(f)
  }

  /** @inheritdoc */
  final override def removeAll(folderName: String): Unit = {
    val f = folder(folderName)
    deleteDirectory(f)
  }

  /** @inheritdoc */
  final override def deleteDatabase(): Unit = {
    deleteDirectory(lemmadbpath)
    // @note make paths again to make sure subsequent additions to database work
    Files.createDirectories(lemmadbpath)
    Files.writeString(cachePath.resolve("VERSION"), Version.toString)
  }

  /** @inheritdoc */
  final override def version(): VersionNumber = {
    val file = cachePath.resolve("VERSION")
    if (!Files.exists(file)) return VersionNumber(0, 0, 0)
    VersionNumber.parse(Files.readString(file))
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
