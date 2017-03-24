/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
/**
 * @author Stefan Mitsch
 * @note Code Review: 2016-08-16
 */
package edu.cmu.cs.ls.keymaerax.lemma

import java.io.{File, IOException, PrintWriter}

import edu.cmu.cs.ls.keymaerax.core.Lemma
import edu.cmu.cs.ls.keymaerax.parser._

/**
 * File-based lemma DB implementation. Stores one lemma per file in the user's KeYmaera X home directory under
 * cache/lemmadb/. Lemma file names are created automatically and in a thread-safe manner.
 *
 * @note Prefer LemmaDBFactory.lemmaDB over instantiating directly to get an instance of a lemma database and ensure
 *       thread safety.
 *
 * Created by smitsch on 4/27/15.
 * @author Stefan Mitsch
 * @author Brandon Bohrer
 */

class FileLemmaDB extends LemmaDBBase {
  private lazy val cachePath = System.getProperty("user.home") + File.separator + ".keymaerax" + File.separator + "cache"

  private lazy val lemmadbpath: File = {
    val file = new File(cachePath + File.separator + "lemmadb")
    if (!file.exists() && !file.mkdirs()) println("WARNING: FileLemmaDB cache did not get created: " + file.getAbsolutePath)
    file
  }

  private def file(id:LemmaID):File = new File(lemmadbpath, id + ".alp")

  def readLemmas(ids: List[LemmaID]):Option[List[String]] = {
    flatOpt(ids.map{lemmaID =>
      val f = file(lemmaID)
      if (f.exists()) {
        Some(scala.io.Source.fromFile(f).mkString)
      } else None})
  }

  def writeLemma(id: LemmaID, lemma:String): Unit = {
    val f = file(id)
    if (!f.getParentFile.exists() && !f.getParentFile.mkdirs()) throw new IllegalStateException("Unable to create lemma " + id)
    val pw = new PrintWriter(f)
    pw.write(lemma)
    pw.close()
  }

  def createLemma():LemmaID = {
    val f = File.createTempFile("lemma",".alp",lemmadbpath)
    f.getName.substring(0, f.getName.length-".alp".length)
  }

  override def remove(id: String): Unit =
    if (!file(id).delete()) throw new IOException("File deletion for " + file(id) + " was not successful")

  override def deleteDatabase(): Unit = {
    lemmadbpath.listFiles().foreach(_.delete())
    lemmadbpath.delete()
    //@note make paths again to make sure subsequent additions to database work
    lemmadbpath.mkdirs()
  }

  override def version(): String = {
    val file = new File(cachePath + File.separator + "VERSION")
    if(!file.exists()) {
      "0.0"
    }
    else {
      assert(file.canRead, s"Cache VERSION file exists but is not readable: ${file.getAbsolutePath}")
      scala.io.Source.fromFile(file).mkString
    }
  }
}