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
 * File-based lemma DB implementation.
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
      val (name, formula, (toolInput, toolOutput)) = KeYmaeraXLemmaParser(scala.io.Source.fromFile(file).mkString)
      val evidence = List(ToolEvidence(Map(toolInput -> toolOutput)))
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
    val header = proofHeader(namesToDeclare.toList)
    val fString = KeYmaeraXPrettyPrinter(f)

    val fileContents = header + "Lemma " + "\"" + file.getName + "\"." + "\n" +
      fString + "\nEnd.\n" + ev.map(stringifyEvidence).mkString("\n")

    val pw = new PrintWriter(file)
    pw.write(fileContents)
    //@TODO Code Review: Read and parse file again. Compare with f.
    pw.close()
  }

  private def proofHeader(ns : List[NamedSymbol]) : String = {
    val varDecls = ns.map({
      case Variable(n, i, s) => sortProofPrinter(s) + " " + n + printIndex(i) + "."
      case DifferentialSymbol(x) =>
        /*implicitly declared by their corresponding variables*/
        if (!ns.contains(x)) sortProofPrinter(x.s) + " " + x.n + printIndex(x.i) + "." else ""
      case Function(n, i, Unit, s) => sortProofPrinter(s) + " " + n + printIndex(i) + "()" + "."
      case Function(n, i, d, s) => sortProofPrinter(s) + " " + n + printIndex(i) + "(" + sortProofPrinter(d) + ")" + "."
    })
    "Variables.\n" + varDecls.mkString("\n") + "\nEnd.\n"
  }

  private def sortProofPrinter(s:Sort):String = s match {
    case Bool        => "T"
    case Trafo       => "P"
    case Real        => "T"
    case Unit        => "Void"
    case _: ObjectSort => ???
  }

  private def printIndex(index: Option[Int]) = index match {
    case None => ""
    case Some(i) => "_" + i
  }

  private def stringifyEvidence(e:Evidence) = e match {
    case e : ProofEvidence => ??? //TODO
    case e : ExternalEvidence => "External.\n\t" + e.file.toString + "\nEnd."
    case e : ToolEvidence => "Tool.\n\t" + e.info.map( p => p._1 + "\t\"" + p._2 + "\"").mkString("\n\t") + "\nEnd."
  }

}
