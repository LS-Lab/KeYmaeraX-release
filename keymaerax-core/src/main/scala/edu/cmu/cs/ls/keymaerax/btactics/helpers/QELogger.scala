/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics.helpers

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, BuiltInTactic, DependentTactic, SingleGoalDependentTactic}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.ToolTactics
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig

import scala.collection.mutable.ListBuffer
import scala.io.Source

/**
  * Helper tools to log QE calls
  */
object QELogger {
  /* A simple measure of complexity on a first-order sequent
   - Used in QE logger to skip over trivial goals like 0 + 0 = 0
  */
  def measure(t:Term) : Int = {
    t match {
      case n:Number => 0
      case a:AtomicTerm => 1
      case f:FuncOf => 1+measure(f.child)
      case u:UnaryCompositeTerm => 1+measure(u.child)
      case b:BinaryCompositeTerm => 1+measure(b.left)+measure(b.right)
    }
  }

  def measure(f:Formula) : Int = {
    f match {
      case c:ComparisonFormula => 1+measure(c.left)+measure(c.right)
      case a:AtomicFormula => 1
      case u:UnaryCompositeFormula => 1 + measure(u.child)
      case b:BinaryCompositeFormula => 1 + measure(b.left) + measure(b.right)
      case q:Quantified => 1+ measure(q.child)
      // Not allowed in QE calls
      // case m:Modal => 1+measure(m.program) + measure(m.child)
      // case p:PredOf => 1+measure(p.child)
      // case p:PredicationalOf => 1 + measure(p.child)
    }
  }

  def measure(s:Sequent) : Int = s.succ.map(measure).sum + s.ante.map(measure).sum

  /**
    *   A simple Logging facility
    *   The sequents are separated by a separator (@ (optional name))
    *
    *   @
    *   Seq_1
    *   @ bla
    *   Seq_2
    *   ...
    *
    *   Sequents with the same name are grouped together when the file is re-parsed
    */
  private val defaultPath = System.getProperty("user.home") + "/.keymaerax/QElog.txt"

  def clearLog(filename: String = defaultPath) : Unit = {
    try {
      val f = scala.tools.nsc.io.File(filename)
      f.delete()
    }
    catch {
      case ex: Exception => println("Failed to delete log")
    }
  }

  def logSequent(s:Sequent, name :String, filename:String = defaultPath): Unit = {
    try {
      val f = scala.tools.nsc.io.File(filename)
      val namestr = "@"+name+"\n"
      f.appendAll(namestr+s.toString+"\n")
    }
    catch {
      case ex: Exception => println("Failed to record sequent")
    }
  }

  def parseLog(filename:String = defaultPath) : Map[String,List[Sequent]] = {
    var curString = ""
    var curName = ""
    var seqMap = new ListBuffer[(String,Sequent)]()
    try {
      for (line <- Source.fromFile(filename).getLines()) {
        if(line.startsWith("@")) {
          if (curString!="") {
              seqMap += ((curName,curString.asSequent))
          }
          curName = line.substring(1)
          curString = ""
        }
        else
          curString += line
      }
      if (curString!="")
        seqMap += ((curName,curString.asSequent))

    } catch {
      case ex: Exception => println("File I/O exception")
    }
    return seqMap.toList.groupBy(_._1).mapValues(_.map(_._2))
  }

  type LogConfig = (Int,String)

  def measureRecordQE(lb:LogConfig = (0,"") ): BuiltInTactic = new BuiltInTactic("logQE") {
      override def result(pr: ProvableSig): ProvableSig = {
        if(pr.subgoals.length==1) {
          val sequent = pr.subgoals(0)
          if (measure(sequent) > lb._1)
            logSequent(sequent, lb._2)
        }
        pr
      }
    }

  private var logTactic = nil

  def getLogTactic : BelleExpr = logTactic

  //This bakes the recorder into the QE tactic, so it will record every single QE call, including internal ones made by
  //e.g. the ODE solver
  def enableLogging(loglevel:LogConfig = (100,"") ) : Unit = {
    logTactic = measureRecordQE(loglevel)
  }

  def disableLogging() : Unit = {
    logTactic = nil
  }

}
