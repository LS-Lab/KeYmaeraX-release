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
package edu.cmu.cs.ls.keymaerax.lemma

import edu.cmu.cs.ls.keymaerax.{Configuration, Logging, Version}

import java.io.{File, IOException, PrintWriter}
import scala.reflect.io.Directory
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
  private lazy val cachePath = Configuration.path(Configuration.Keys.LEMMA_CACHE_PATH)

  /**
   * Matches special characters in lemma names that might be problematic in file names (typically: whitespace, :, .).
   */
  private val SANITIZE_REGEX = "[^\\w\\-" + Regex.quote(File.separator) + "]"

  /** File handle to lemma database (creates parent directories if non-existent). */
  private lazy val lemmadbpath: File = {
    val file = new File(cachePath + File.separator + "lemmadb")
    if (!file.exists() && !file.mkdirs()) logger
      .warn("WARNING: FileLemmaDB cache did not get created: " + file.getAbsolutePath)
    file
  }

  /** Replaces special file characters with _. */
  private def sanitize(id: LemmaID): LemmaID = id.replaceAll(SANITIZE_REGEX, "_")

  /** Returns the File representing lemma `id`. */
  private def file(id: LemmaID): File = new File(lemmadbpath, sanitize(id) + ".alp")

  /** Returns the File representing the folder `id`. */
  private def folder(id: LemmaID): Directory = new Directory(new File(lemmadbpath, sanitize(id)))

  /** Reads the file `f` into a string. */
  private def read(f: File): String = {
    val src = scala.io.Source.fromFile(f, edu.cmu.cs.ls.keymaerax.core.ENCODING)
    try { src.mkString }
    finally { src.close() }
  }

  /** Writes `text` to the file `f`. */
  private def write(f: File, text: String): Unit = {
    val w = new PrintWriter(f, edu.cmu.cs.ls.keymaerax.core.ENCODING)
    try { w.write(text) }
    finally { w.close() }
  }

  /** @inheritdoc */
  final override def contains(lemmaID: LemmaID): Boolean = file(lemmaID).exists

  /** @inheritdoc */
  final override def createLemma(): LemmaID = {
    val f = File.createTempFile("lemma", ".alp", lemmadbpath)
    f.getName.substring(0, f.getName.length - ".alp".length)
  }

  /** @inheritdoc */
  final override def readLemmas(ids: List[LemmaID]): Option[List[String]] = flatOpt(ids.map({ lemmaID =>
    val f = file(lemmaID)
    if (f.exists()) Some(read(f)) else None
  }))

  /** @inheritdoc */
  final override def writeLemma(id: LemmaID, lemma: String): Unit = synchronized {
    val f = file(id)
    if (!f.getParentFile.exists() && !f.getParentFile.mkdirs())
      throw new IllegalStateException("Unable to create lemma " + id)
    write(f, lemma)
  }

  /** @inheritdoc */
  final override def remove(id: String): Unit = {
    val f = file(id)
    if (f.exists && !f.delete()) throw new IOException("File deletion for " + file(id) + " was not successful")
  }

  /** @inheritdoc */
  final override def removeAll(folderName: String): Unit = {
    val f = folder(folderName)
    if (f.exists && !f.deleteRecursively())
      throw new IOException("File deletion for " + file(folderName) + " was not successful")
  }

  /** @inheritdoc */
  final override def deleteDatabase(): Unit = {
    lemmadbpath.listFiles().foreach(_.delete())
    lemmadbpath.delete()
    // @note make paths again to make sure subsequent additions to database work
    lemmadbpath.mkdirs()
    write(new File(cachePath + File.separator + "VERSION"), Version.CURRENT.toString)
  }

  /** @inheritdoc */
  final override def version(): Version = {
    val file = new File(cachePath + File.separator + "VERSION")
    if (!file.exists()) return Version(0, 0, 0)
    assert(file.canRead, s"Cache VERSION file exists but is not readable: ${file.getAbsolutePath}")
    Version.parse(read(file))
  }
}
