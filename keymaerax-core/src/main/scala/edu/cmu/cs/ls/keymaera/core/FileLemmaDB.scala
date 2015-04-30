package edu.cmu.cs.ls.keymaera.core

import java.io.File

import edu.cmu.cs.ls.keymaera.parser._

/**
 * File-based lemma DB implementation.
 *
 * Created by smitsch on 4/27/15.
 * @author Stefan Mitsch
 */
class FileLemmaDB extends LemmaDB {

  private lazy val lemmadbpath: java.io.File = {
    val file = new java.io.File(System.getProperty("user.home") + java.io.File.separator +
      ".keymaera" + java.io.File.separator + "cache" + java.io.File.separator + "lemmadb")
    file.mkdirs
    file
  }

  override def contains(lemmaID: String): Boolean = new java.io.File(lemmadbpath, lemmaID + ".alp").exists()

  override def get(lemmaID: String): Option[Lemma] = {
    val parser = new KeYmaeraParser()
    val file = new File(lemmadbpath, lemmaID + ".alp")
    if (file.exists()) {
      val knowledge = parser.ProofFileParser.runParser(scala.io.Source.fromFile(file).mkString)
      val (name, formula, evidence) = LoadedKnowledgeTools.fromName(knowledge)(lemmaID + ".alp").head match {
        case LoadedLemma(n, f, e) => (n, f, e)
        case _ => throw new IllegalStateException("ID " + lemmaID + " does not identify a lemma")
      }
      // TODO this means, all lemma DB implementations have to be part of the core
      val fact = Provable.toolFact(new Sequent(Nil,
        scala.collection.immutable.IndexedSeq(),
        scala.collection.immutable.IndexedSeq(formula)))
      Some(Lemma(fact, evidence, Some(name)))
    } else None
  }

  private[core] override def add(lemma: Lemma): String = {
    val (id, file) = this.synchronized {
      // synchronize to make sure concurrent uses use new file names
      lemma.name match {
        case Some(n) =>
          require(isUniqueLemmaName(n), "Duplicate lemma name " + n)
          (n, new java.io.File(lemmadbpath, n + ".alp"))
        case None =>
          val (newId, newFile) = getUniqueLemmaFile()
          newFile.createNewFile
          (newId, newFile)
      }
    }
    saveProof(file, lemma.fact.conclusion.succ.head, lemma.evidence)
    id
  }

  private def isUniqueLemmaName(name: String): Boolean = {
    val f = new java.io.File(lemmadbpath, name + ".alp")
    !f.exists()
  }

  private def getUniqueLemmaFile(idx: Int = 0): (String, java.io.File) = {
    val id = "QE" + idx.toString
    val f = new java.io.File(lemmadbpath, id + ".alp")
    if(f.exists()) getUniqueLemmaFile(idx + 1)
    else (id, f)
  }

  private def saveProof(file: java.io.File, f: Formula, ev: List[Evidence]): Unit = {
    val namesToDeclare = StaticSemantics.symbols(f) -- StaticSemantics(f).bv.toSymbolSet
    val header = new KeYmaeraPrettyPrinter(ParseSymbols).proofHeader(namesToDeclare.toList)
    val fString = new KeYmaeraPrettyPrinter(ParseSymbols).stringify(f)

    val fileContents = header + "Lemma " + "\"" + file.getName + "\"." + "\n" +
      fString + "\nEnd.\n" + ev.map(KeYmaeraPrettyPrinter.stringifyEvidence).mkString("\n")

    val pw = new java.io.PrintWriter(file)
    pw.write(fileContents)
    //@TODO Read and parse file again. Compare with f.
    pw.close()
  }
}
