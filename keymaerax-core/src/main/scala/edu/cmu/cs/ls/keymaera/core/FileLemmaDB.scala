package edu.cmu.cs.ls.keymaera.core

import scala.collection.immutable

import java.io.File
import java.io.PrintWriter

import edu.cmu.cs.ls.keymaera.parser._

/**
 * File-based lemma DB implementation.
 *
 * Created by smitsch on 4/27/15.
 * @author Stefan Mitsch
 */
class FileLemmaDB extends LemmaDB {

  private lazy val lemmadbpath: File = {
    val file = new File(System.getProperty("user.home") + File.separator +
      ".keymaera" + File.separator + "cache" + File.separator + "lemmadb")
    file.mkdirs
    file
  }

  override def contains(lemmaID: LemmaID): Boolean = new File(lemmadbpath, lemmaID + ".alp").exists()

  override def get(lemmaID: LemmaID): Option[Lemma] = {
    val parser = new KeYmaeraParser()
    val file = new File(lemmadbpath, lemmaID + ".alp")
    if (file.exists()) {
      val knowledge = parser.ProofFileParser.runParser(scala.io.Source.fromFile(file).mkString)
      val (name, formula, evidence) = LoadedKnowledgeTools.fromName(knowledge)(lemmaID + ".alp").head match {
        case LoadedLemma(n, f, e) => (n, f, e)
        case _ => throw new IllegalStateException("ID " + lemmaID + " does not identify a lemma")
      }
      // TODO this means, all lemma DB implementations have to be part of the core
      // TODO Code Review: Any way of checking/certifying this to remove it from the core?
      val fact = Provable.toolFact(new Sequent(Nil,
        immutable.IndexedSeq(),
        immutable.IndexedSeq(formula)))
      Some(Lemma(fact, evidence, Some(name)))
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
    saveProof(file, lemma.fact.conclusion.succ.head, lemma.evidence)
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

  private def saveProof(file: File, f: Formula, ev: List[Evidence]): Unit = {
    val namesToDeclare = StaticSemantics.symbols(f) -- StaticSemantics(f).bv.toSymbolSet ++ StaticSemantics(f).fv.toSymbolSet
    val header = new KeYmaeraPrettyPrinter(ParseSymbols).proofHeader(namesToDeclare.toList)
    val fString = new KeYmaeraPrettyPrinter(ParseSymbols).stringify(f)

    val fileContents = header + "Lemma " + "\"" + file.getName + "\"." + "\n" +
      fString + "\nEnd.\n" + ev.map(KeYmaeraPrettyPrinter.stringifyEvidence).mkString("\n")

    val pw = new PrintWriter(file)
    pw.write(fileContents)
    //@TODO Code Review: Read and parse file again. Compare with f.
    pw.close()
  }
}
