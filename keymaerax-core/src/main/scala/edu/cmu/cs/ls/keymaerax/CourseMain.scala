package edu.cmu.cs.ls.keymaerax

import edu.cmu.cs.ls.keymaerax.parser.ParseException

/**
  * Created by nfulton on 1/17/16.
  */
object CourseMain {
  def main(input : Array[String]) = {
    val args : Map[String, ArgValue] = GetOpt(Map(
      "--bparse" -> StrArgType(),
      "--tparse" -> StrArgType(),
      "--exists" -> StrArgType(),
      "--is-exported-db" -> StrArgType()
    ))(input)

    args.foreach(pv => {
      val parameterName = pv._1
      val value         = pv._2
      else if(parameterName == "bparse") parseProblemFileOrFail(value)
      else if(parameterName == "tparse") parseTacticFileOrFail(value)
      else if(parameterName == "exists") fileExistsOrFail(value)
      else if(parameterName == "is-exported-db") isExportedDatabaseOrFail(value)
    })
  }

  /** Returns string contained within value */
  private def fileExistsOrFail(v : ArgValue) : String = {
    val fileName = v.asInstanceOf[StringValue].s
    assert({
      val file = new java.io.File(fileName)
      file.exists() && file.canRead()
    }, s"File named ${fileName} should exist and be readable.")
    fileName
  }

  private def parseTacticFileOrFail(v: ArgValue) = {
    val fileName = fileExistsOrFail(v)
    println(s"Skipping parser check for tactic file ${fileName}!")
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
      case e : _ => {
        println(s"Unkown error encountered while parsing ${fileName}")
        System.exit(-1)
      }
    }
  }

  private def isExportedDatabaseOrFail(v : ArgValue) = {
    fileExistsOrFail(v)
  }
}

/**
  * Like Perl's GetOpt::Long. Kinda.
  * Created by nfulton on 1/25/16.
  */
object GetOpt extends (Map[String, ArgType] => Array[String] => Map[String, ArgValue]) {
  def apply(args : Map[String, ArgType]) = (input: Array[String]) => {
    var returnValue : Map[String, ArgValue] = Map()
    var imod = input

    //Process each element of the input array.
    while(!imod.isEmpty) {
      val parameterName = imod(0).replaceAll("^--", "")
      assert(args.keySet.contains(parameterName))

      if(args(parameterName).isInstanceOf[FlagType]) {
        returnValue = returnValue + (parameterName -> FlagValue(true))
        imod = imod.drop(1) //flags have no values, so just drop the name.
      }
      else {
        assert(imod.length >= 2)
        val parameterValue = imod(1)
        returnValue = returnValue + (parameterName -> args(parameterName).toArgValue(parameterValue))
        imod = imod.drop(2) //drop both the name and the value
      }
    }

    //Ensure that only flag values are missing and default all flags to false.
    val missingKeys = args.keySet.filter(!returnValue.keySet.contains(_))
    missingKeys.map(missingKey => {
      assert(args(missingKey).isInstanceOf[FlagType])
      returnValue += (missingKey.replaceAll("^--", "") -> FlagValue(false))
    })

    returnValue
  }
}


sealed trait ArgType {
  def toArgValue[T](v : T) : ArgValue
}
case class StrArgType() extends ArgType {
  def toArgValue[T](v : T) : ArgValue = {
    assert(v.isInstanceOf[String])
    StringValue(v.asInstanceOf[String])
  }
}
case class FlagType() extends ArgType {
  def toArgValue[T](v : T) : ArgValue = {
    assert(v.isInstanceOf[Boolean])
    FlagValue(v.asInstanceOf[Boolean])
  }
}

sealed trait ArgValue
case class StringValue(s: String) extends ArgValue
case class FlagValue(b : Boolean) extends ArgValue