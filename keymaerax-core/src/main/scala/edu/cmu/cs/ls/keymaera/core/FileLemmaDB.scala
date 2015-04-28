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
  // TODO need not be part of the core, but how to make trusted if outside?

  private lazy val lemmadbpath = {
    val file = new java.io.File(System.getProperty("user.home") + java.io.File.separator +
      ".keymaera" + java.io.File.separator + "cache" + java.io.File.separator + "lemmadb")
    file.mkdirs
    file
  }

  override def getLemmaConclusion(lemmaID: String): Formula = {
    val parser = new KeYmaeraParser()
    val file = new File(lemmadbpath, lemmaID + ".alp")
    val knowledge = parser.ProofFileParser.runParser(scala.io.Source.fromFile(file).mkString)
    LoadedKnowledgeTools.fromName(knowledge)(lemmaID + ".alp").head.formula
  }

  override def addLemma(conclusion: Formula, evidence: (String, String)): Option[String] = {
    def getUniqueLemmaFile(idx: Int = 0): (String, java.io.File) = {
      val id = "QE" + idx.toString
      val f = new java.io.File(lemmadbpath, id + ".alp")
      if(f.exists()) getUniqueLemmaFile(idx + 1)
      else (id, f)
    }
    val (id, file) = LookupLemma.synchronized {
      // synchronize on file creation to make sure concurrent uses use new file names
      val (newId, newFile) = getUniqueLemmaFile()
      newFile.createNewFile
      (newId, newFile)
    }
    saveProof(file, conclusion, new ToolEvidence(Map("input" -> evidence._1, "output" -> evidence._2)))
    Some(id)
  }

  private def saveProof(file: java.io.File, f: Formula, ev: Evidence) = {
    val namesToDeclare = StaticSemantics.symbols(f) -- StaticSemantics(f).bv.toSymbolSet
    val header = new KeYmaeraPrettyPrinter(ParseSymbols).proofHeader(namesToDeclare.toList)
    val fString = new KeYmaeraPrettyPrinter(ParseSymbols).stringify(f)

    val fileContents = header + "Lemma " + "\"" + file.getName + "\"." + "\n" +
      fString + "\nEnd.\n" + KeYmaeraPrettyPrinter.stringifyEvidence(ev)

    val pw = new java.io.PrintWriter(file)
    pw.write(fileContents)
    //@TODO Read and parse file again. Compare with f.
    pw.close()
  }
}
