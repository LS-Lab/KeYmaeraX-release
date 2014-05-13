/*
 * This file contains data structures targeted by the KeYmaera proof parser.
 * This file probably belongs in the parser namespace instead of the core TODO
 * @author Nathan Fulton
 */

package edu.cmu.cs.ls.keymaera.parser

import java.io.File
import edu.cmu.cs.ls.keymaera.core._

sealed trait Evidence
case class ProofEvidence(proof : List[LoadedBranch])   extends Evidence
case class ToolEvidence(info : Map[String,String])     extends Evidence
case class ExternalEvidence(file:File)                 extends Evidence

object LoadedKnowledgeTools {
  /**
   * LoadedKnowledge List -> String -> LoadedKnowledge List
   * @returns All evidence associated with the name.
   */
  def fromName(knowledge : List[LoadedKnowledge])(n:String) = {
    knowledge.filter(_ match {
      case LoadedAxiom(name, formula)           => n.equals(name)
      case LoadedLemma(name, formula, evidence) => n.equals(name)
    })
  }
}
sealed class LoadedKnowledge(val name : String, val formula : Formula)
case class LoadedAxiom(val name : String, 
    val formula : Formula) extends LoadedKnowledge(name,formula)

case class LoadedLemma(val name : String, 
    val formula : Formula, 
    val evidence : List[Evidence]) extends LoadedKnowledge(name,formula)

class LoadedBranch(val name : String, val rules : List[LoadedRule]) {
  def getProof : ProofNode = ??? //TODO
}

class LoadedRule(val name : String, info : List[LoadedRuleInfo]) 
{
  /**
   * Converts a LoadedRule into a proof (in the sense of the core data structure)
   */
  def getProof : ProofNode = {
    //Proceed according to the name of the rule.
    if(this.isAxiom) {
      getAxiom
    }
    else {
      ??? //TODO convert LoadedRuleInfo into a proof.
    }
  }
  
  val isAxiom = {
    val matchingAxioms = Axiom.axioms.filter(ax => ax._1.equals(name))
    !matchingAxioms.isEmpty
  }
  
  def getAxiom : ProofNode = {
    if(isAxiom) {
      //formula
      val ax = Axiom.axioms.filter(ax => ax._1.equals(name)).last._2
      ??? //TODO
    }
    else {
      throw new Exception("Requested axiom " + name + " but this is not an axiom")
    }
  }
}

sealed trait LoadedRuleInfo {
  def fromName(name:String, value:String) = name match {
    case "formula" => TargetedFormula(Integer.parseInt(value))
    case "tool" => ToolUsed(value)
    case "nodenum" => NodeNum(Integer.parseInt(value))
    case "TargetedTerms" => {
      val values = value.split(""",""").map(Integer.parseInt(_))
      TargetedTerms(List() ++ values)
    }
  }
}
case class TargetedFormula(n : Int) extends LoadedRuleInfo
case class ToolUsed(name : String) extends LoadedRuleInfo
case class NodeNum(n : Int) extends LoadedRuleInfo
case class TargetedTerms(ns : List[Int]) extends LoadedRuleInfo
case class EmptyRule() extends LoadedRuleInfo
