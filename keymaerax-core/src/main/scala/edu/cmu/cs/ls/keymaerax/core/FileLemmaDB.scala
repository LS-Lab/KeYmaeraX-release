/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
/**
 * @author Stefan Mitsch
 * @note Code Review: 2015-05-01
 */
package edu.cmu.cs.ls.keymaerax.core

import scala.collection.immutable

import java.io.File
import java.io.PrintWriter

import edu.cmu.cs.ls.keymaerax.parser._

/**
 * File-based lemma DB implementation. Stores one lemma per file in the user's KeYmaera X home directory under
 * cache/lemmadb/. Lemma file names are created automatically and in a thread-safe manner.
 *
 * Instantiate (parameter-less constructor) to get access to lemmas. All instances will have the same view on the
 * lemmas.
 *
 * Created by smitsch on 4/27/15.
 * @author Stefan Mitsch
 */
class FileLemmaDB extends LemmaDB {

  private lazy val lemmadbpath: File = {
    val file = new File(System.getProperty("user.home") + File.separator +
      ".keymaerax" + File.separator + "cache" + File.separator + "lemmadb")
    file.mkdirs
    file
  }

  override def contains(lemmaID: LemmaID): Boolean = new File(lemmadbpath, lemmaID + ".alp").exists()

  override def get(lemmaID: LemmaID): Option[Lemma] = {
    val file = new File(lemmadbpath, lemmaID + ".alp")
    if (file.exists()) {
      val (name, formula, evidence) = KeYmaeraXLemmaParser(scala.io.Source.fromFile(file).mkString)
      // @note this means, all lemma DB implementations have to be part of the core
      //@TODO Code Review: Any way of checking/certifying this to remove it from the core?
      val fact = Provable.toolFact(new Sequent(Nil,
        immutable.IndexedSeq(),
        immutable.IndexedSeq(formula)))
      Some(Lemma(fact, evidence :: Nil, name))
    } else None
  }

  private[core] override def add(lemma: Lemma): LemmaID = {
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

}
