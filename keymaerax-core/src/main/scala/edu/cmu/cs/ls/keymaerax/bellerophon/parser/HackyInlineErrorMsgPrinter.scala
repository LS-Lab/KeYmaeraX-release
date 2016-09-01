package edu.cmu.cs.ls.keymaerax.bellerophon.parser

import edu.cmu.cs.ls.keymaerax.parser.{Location, Region, UnknownLocation}

/**
  * Prints the model with the problematic portion underlined and a message displayed.
  * @author Nathan Fulton
  */
//@todo : @deprecated("This should be replaced with a proper pretty-printer that takes a bellexpr instead of a string and handles all locations properly", "4.1b2")
private[keymaerax] object HackyInlineErrorMsgPrinter {
  def apply(input: String, location: Location, message: String) : String = {
    "\n" + (input.split("\n").zipWithIndex.foldLeft("")((result, next) => {
      if(next._2 == location.begin.line-1) {
        result + next._1 + "\n" + alignWith(location, message) + "\n"
      }
      else result + next._1 + "\n"
    }))
  }

  private def alignWith(location: Location, message: String) = location match {
    case Region(l,c,el,ec) => {
      if(l != el) ???
      var result = ""
      for(i <- 1 until c) result = result + " "
      for(i <- 0 until ec-c) result = result + "^"
      result = result + message
      result
    }
    case UnknownLocation => ???
    case _ => ???
  }
}
