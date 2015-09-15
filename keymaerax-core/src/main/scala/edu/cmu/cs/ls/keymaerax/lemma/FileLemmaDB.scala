/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
/**
 * @author Stefan Mitsch
 * @note Code Review: 2015-05-01
 */
package edu.cmu.cs.ls.keymaerax.lemma

import java.io.{File, PrintWriter}

import edu.cmu.cs.ls.keymaerax.core.{Lemma, LemmaDB}
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
    if (!file.mkdirs()) println("WARNING: FileLemmaDB cache did not get created: " + file.getAbsolutePath)
    file
  }

  override def contains(lemmaID: LemmaID): Boolean = new File(lemmadbpath, lemmaID + ".alp").exists()

  override def get(lemmaID: LemmaID): Option[Lemma] = {
    val file = new File(lemmadbpath, lemmaID + ".alp")
    if (file.exists()) {
      Some(Lemma.fromString(scala.io.Source.fromFile(file).mkString))
    } else None
  }

  override def add(lemma: Lemma): LemmaID = {
    require(lemma.fact.isProved, "Only proved lemmas are currently supported, no open subgoals")
    val (id, file) = this.synchronized {
      // synchronize to make sure concurrent uses use new file names
      lemma.name match {
        case Some(n) =>
          require(isUniqueLemmaName(n), "Duplicate lemma name " + n)
          (n, new File(lemmadbpath, n + ".alp"))
        case None =>
          val (newId, newFile) = getUniqueLemmaFile()
          newFile.createNewFile
          (newId, newFile)
      }
    }
    saveProof(file, lemma, id)
    id
  }

  private def isUniqueLemmaName(name: String): Boolean =
    !new File(lemmadbpath, name + ".alp").exists()

  private def getUniqueLemmaFile(idx: Int = 0): (String, File) = {
    val id = "QE" + idx.toString
    val f = new File(lemmadbpath, id + ".alp")
    if (f.exists()) getUniqueLemmaFile(idx + 1)
    else (id, f)
  }

  private def saveProof(file: File, lemma: Lemma, id: String): Unit = {
    //@see[[edu.cmu.cs.ls.keymaerax.core.Lemma]]
    assert(lemma.fact.conclusion.ante.isEmpty && lemma.fact.conclusion.succ.size == 1, "expected lemma form should have no antecedent and exactly one succedent formula " + lemma)
    assert(KeYmaeraXLemmaParser(lemma.toString) == (lemma.name, lemma.fact.conclusion.succ.head, lemma.evidence.head),
      "reparse of printed lemma should be identical to original lemma " + lemma)

    val pw = new PrintWriter(file)
    pw.write("/** KeYmaera X " + edu.cmu.cs.ls.keymaerax.core.VERSION + " */")
    pw.write(lemma.toString)
    pw.close()

    val lemmaFromDB = get(id)
    if (lemmaFromDB.isEmpty || lemmaFromDB.get != lemma) {
      file.delete()
      throw new IllegalStateException("Lemma in DB differed from lemma in memory -> deleted")
    }
    // assertion duplicates condition and throw statement
    assert(lemmaFromDB.isDefined && lemmaFromDB.get == lemma, "Lemma stored in DB should be identical to lemma in memory " + lemma)
  }

  override def deleteDatabase(): Unit = {
    lemmadbpath.delete()
  }
}
