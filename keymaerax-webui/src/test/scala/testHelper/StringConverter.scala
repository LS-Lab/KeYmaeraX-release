package testHelper

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXParser, KeYmaeraParser}

/**
 * Implicit conversions from strings into core data structures.
 * Created by smitsch on 1/8/15.
 * @author Stefan Mitsch
 */
object StringConverter {
  import scala.language.implicitConversions
  implicit def StringToStringConverter(s: String): StringConverter = new StringConverter(s)
}

class StringConverter(val s: String) {
  def asExpr: Expression = KeYmaeraXParser(s)

  def asTerm: Term = KeYmaeraXParser(s) match {
    case t: Term => t
    case _ => throw new IllegalArgumentException("Input " + s + " is not a term")
  }

  def asNamedSymbol: NamedSymbol = KeYmaeraXParser(s) match {
    case ns: NamedSymbol => ns
    case _ => throw new IllegalArgumentException("Input " + s + " is not a named symbol")
  }

  def asVariable: Variable = KeYmaeraXParser(s) match {
    case v: Variable => v
    case _ => throw new IllegalArgumentException("Input " + s + " is not a variable")
  }

  def asFormula: Formula = KeYmaeraXParser(s) match {
    case f: Formula => f
    case _ => throw new IllegalArgumentException("Input " + s + " is not a formula")
  }

  def asProgram: Program = KeYmaeraXParser(s) match {
    case prg: Program => prg
    case _ => throw new IllegalArgumentException("Input " + s + " is not a program")
  }
}