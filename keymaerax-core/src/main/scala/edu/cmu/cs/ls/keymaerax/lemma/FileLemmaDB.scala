/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
/**
 * @author Stefan Mitsch
 * @note Code Review: 2016-08-02
 */
package edu.cmu.cs.ls.keymaerax.lemma

import java.io.{File, PrintWriter}

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
 */
class FileLemmaDB extends LemmaDB {

  private lazy val lemmadbpath: File = {
    val file = new File(System.getProperty("user.home") + File.separator +
      ".keymaerax" + File.separator + "cache" + File.separator + "lemmadb")
    if (!file.exists() && !file.mkdirs()) println("WARNING: FileLemmaDB cache did not get created: " + file.getAbsolutePath)
    file
  }

  /** Get the file in which lemmaID is supposed to be stored */
  private def fileFor(lemmaID: LemmaID): File = new File(lemmadbpath, lemmaID + ".alp")

  override def contains(lemmaID: LemmaID): Boolean = fileFor(lemmaID).exists()

  override def get(lemmaID: LemmaID): Option[Lemma] = {
    val file = fileFor(lemmaID)
    if (file.exists()) {
      Some(Lemma.fromString(scala.io.Source.fromFile(file).mkString))
    } else None
  }

  override def add(lemma: Lemma): LemmaID = {
    val (id, file) = this.synchronized {
      // synchronize to make sure concurrent uses use new file names
      lemma.name match {
        case Some(n) =>
          require(isUniqueLemmaName(n) || get(n) == Some(lemma),
            "Lemma name '" + n + ".alp' must be unique, or file content must be the identical lemma: \n" + lemma)
          val file = new File(lemmadbpath, n + ".alp")
          if (isUniqueLemmaName(n)) file.createNewFile()
          (n, file)
        case None =>
          val (newId, newFile) = getUniqueLemmaFile
          newFile.createNewFile()
          (newId, newFile)
      }
    } ensuring(r => r._2.exists(), "the file to be stored in exists now and cannot be claimed concurrently again")
    saveProof(file, lemma, id)
    id
  }

  override def remove(lemmaName: LemmaID): Boolean =
    try {fileFor(lemmaName).delete()}
    //@todo return value seems wrong
    finally {false}

  private def isUniqueLemmaName(name: LemmaID): Boolean =
    !fileFor(name).exists()

  private def getUniqueLemmaFile: (String, File) = {
    val f = File.createTempFile("lemma",".alp",lemmadbpath)
    (f.getName.substring(0, f.getName.length-".alp".length), f)
  }

  private def saveProof(file: File, lemma: Lemma, id: String): Unit = {
    //@see[[edu.cmu.cs.ls.keymaerax.core.Lemma]]
    val lemmaToAdd = addRequiredEvidence(lemma)

    val parse = KeYmaeraXExtendedLemmaParser(lemmaToAdd.toString)
    assert(parse._1 == lemma.name, "reparse of printed lemma's name should be identical to original lemma")
    assert(parse._2 == lemma.fact.conclusion +: lemma.fact.subgoals, s"reparse of printed lemma's fact ${lemma.fact.conclusion +: lemma.fact.subgoals }should be identical to original lemma ${parse._2}")

    val pw = new PrintWriter(file)
    pw.write(lemmaToAdd.toString)
    pw.close()

    val lemmaFromDB = get(id)
    if (lemmaFromDB != Some(lemmaToAdd)) {
      file.delete()
      throw new IllegalStateException("Lemma in DB differed from lemma in memory -> deleted for lemma " + id)
    }
    // assertion duplicates condition and throw statement
    assert(lemmaFromDB == Some(lemmaToAdd), "Lemma stored in DB should be identical to lemma in memory " + lemmaToAdd)
  }

  override def deleteDatabase(): Unit = {
    lemmadbpath.delete()
    //@note make paths again to make sure subsequent additions to database work
    lemmadbpath.mkdirs()
  }
}
