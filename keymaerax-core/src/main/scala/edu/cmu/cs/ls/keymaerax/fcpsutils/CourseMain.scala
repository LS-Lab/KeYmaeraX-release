package edu.cmu.cs.ls.keymaerax.fcpsutils

import java.io.File

import edu.cmu.cs.ls.keymaerax.bellerophon.BTacticParser
import edu.cmu.cs.ls.keymaerax.btactics.{NoneGenerate, TactixLibrary, DerivedAxioms}
import edu.cmu.cs.ls.keymaerax.core.Formula
import edu.cmu.cs.ls.keymaerax.parser.ParseException
import edu.cmu.cs.ls.keymaerax.tools.Mathematica

/**
  * Created by nfulton on 1/17/16.
  */
object CourseMain {
  implicit def qeTool = new Mathematica()
  DerivedAxioms.qeTool = qeTool
  TactixLibrary.tool = qeTool

  def main(input : Array[String]) = {
    val args : Map[String, ArgValue] = GetOpt(Map(
      "bparse" -> StrArgType(),
      "tparse" -> StrArgType(),
      "exists" -> StrArgType(),
      "is-exported-db" -> StrArgType()
    ))(input)

    try {
      args.foreach(pv => {
        val parameterName = pv._1
        val value = pv._2
        if (parameterName == "bparse") parseProblemFileOrFail(value)
        else if (parameterName == "tparse") parseTacticFileOrFail(value)
        else if (parameterName == "exists") fileExistsOrFail(value)
        else if (parameterName == "is-exported-db") isExportedDatabaseOrFail(value)
      })
      System.exit(0)
    }
    catch {
      case e : Error => {
        e.printStackTrace()
        System.exit(-1)
      }
    }
  }

  /** Returns string contained within value */
  private def fileExistsOrFail(v : ArgValue) : String = {
    val fileName = v.asInstanceOf[StringValue].s
    assert({
      val file = new File(fileName)
      file.exists() && file.canRead()
    }, s"File named ${fileName} should exist and be readable.")
    fileName
  }

  private def parseTacticFileOrFail(v: ArgValue) = {
    val fileName = fileExistsOrFail(v)
    BTacticParser(scala.io.Source.fromFile(new File(fileName)).mkString, false, Some(new NoneGenerate[Formula]())) match {
      case Some(e) => //ok
      case None => throw new Exception(s"Tactic in ${fileName} did not parse")
    }
  }

  private def parseProblemFileOrFail(v: ArgValue) = {
    val fileName = fileExistsOrFail(v)
    try {
      edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXProblemParser(scala.io.Source.fromFile(fileName).mkString)
    }
    catch {
      case e : ParseException => {
        println(s"Auto-grader failed because file ${fileName} needs to exist and parse but failed to parse.")
        e.printStackTrace()
        System.exit(-1)
      }
      case e : Error => {
        println(s"Unkown error encountered while parsing ${fileName}")
        System.exit(-1)
      }
    }
  }

  private def isExportedDatabaseOrFail(v : ArgValue) = {
    fileExistsOrFail(v)
  }
}