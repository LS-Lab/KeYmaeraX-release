package testHelper

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraParser

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
  def asExpr: Expression = new KeYmaeraParser().parseBareExpression(s) match {
    case Some(e) => e
    case None => throw new IllegalArgumentException(s + " is not an Expr")
  }
  def asTerm: Term = new KeYmaeraParser().parseBareTerm(s) match {
    case Some(t) => t
    case None => throw new IllegalArgumentException(s + " is not a Term")
  }
  def asNamedSymbol: NamedSymbol = new KeYmaeraParser().parseBareTerm(s) match {
    case Some(t) => t.asInstanceOf[NamedSymbol]
    case None => throw new IllegalArgumentException(s + " is not a Term")
  }
  def asVariable: Variable = new KeYmaeraParser().parseBareTerm(s) match {
    case Some(t) => t.asInstanceOf[Variable]
    case None => throw new IllegalArgumentException(s + " is not a Variable")
  }
  def asFormula: Formula = new KeYmaeraParser().parseBareFormulaUnquantified(s)

  def asProgram: Program = new KeYmaeraParser().parseBareExpression("[" + s + "] true") match {
    case Some(Box(p, f)) => p
    case None => throw new IllegalArgumentException(s + " is not a Program")
  }
}