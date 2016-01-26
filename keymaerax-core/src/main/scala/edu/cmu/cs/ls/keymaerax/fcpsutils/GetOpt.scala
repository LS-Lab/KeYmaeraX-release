package edu.cmu.cs.ls.keymaerax.fcpsutils

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
      assert(args.keySet.contains(parameterName), s"Unknown argument ${parameterName}")

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
      if(args(missingKey).isInstanceOf[FlagType])
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