package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.core._

/**
 * Implicit conversions from strings into core data structures.
 * Created by smitsch on 1/8/15.
 * @author Stefan Mitsch
 * @author aplatzer
 */
object StringConverter {
  import scala.language.implicitConversions
  implicit def StringToStringConverter(s: String): StringConverter = new StringConverter(s)
}

class StringConverter(val s: String) {
  def asExpr: Expression = KeYmaeraXParser(s)

  def asTerm: Term = KeYmaeraXParser.termParser(s)

  def asNamedSymbol: NamedSymbol = KeYmaeraXParser(s) match {
    case ns: NamedSymbol => ns
    case _ => throw new IllegalArgumentException("Input " + s + " is not a named symbol")
  }

  def asVariable: Variable = KeYmaeraXParser.termParser(s) match {
    case v: Variable => v
    case _ => throw new IllegalArgumentException("Input " + s + " is not a variable")
  }

  def asFormula: Formula = KeYmaeraXParser.formulaParser(s)

  def asProgram: Program = KeYmaeraXParser.programParser(s)
}