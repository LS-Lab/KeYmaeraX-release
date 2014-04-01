/*
 * KeYmaera4 proof files
 * @author Nathan Fulton
 */

package edu.cmu.cs.ls.keymaera.core

import java.io.File

sealed trait Evidence
case class ProofEvidence(proof : ProofStep)            extends Evidence
case class ToolEvidence(info : Map[String,String])     extends Evidence
case class ExternalEvidence(file:File)                 extends Evidence

sealed trait LoadedKnowledge
case class LoadedAxiom(val name : String, val formula : Formula) extends LoadedKnowledge
case class LoadedLemma(val name : String, formula : Formula, evidence : List[Evidence]) extends LoadedKnowledge

class LoadedLemmaLibrary(lemmas : List[LoadedLemma], axioms : List[LoadedLemma]) {
  def fromName(n : String) = {
    //Prefer axioms to lemmas.
    val someAxiom = axioms.find(ax => ax.name.equals(n))
    val someLemma = lemmas.find(le => le.name.equals(n))
    someAxiom match {
      case Some(ax) => ax
      case None     => someLemma match {
        case Some(le) => le
        case None     => ???
      }
    } 
  }
}
 
