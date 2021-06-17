package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, BelleLabel, BelleTopLevelLabel}
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.core._

/**
 * Implicit conversions from strings into core data structures.
 * Created by smitsch on 1/8/15.
 * @author Stefan Mitsch
 * @author Andre Platzer
 */
object StringConverter {
  import scala.language.implicitConversions
  implicit def StringToStringConverter(s: String): StringConverter = new StringConverter(s)
}

/** Conversions of string `s` to core/tactic data structures. */
class StringConverter(val s: String) {
  /** Converts to an expression. */
  def asExpr: Expression = Parser(s)

  /** Converts to a term. */
  def asTerm: Term = Parser.parser.termParser(s)

  /** Converts to a named symbol. */
  def asNamedSymbol: NamedSymbol = Parser(s) match {
    case ns: NamedSymbol => ns
    case _ => throw new IllegalArgumentException("Input " + s + " is not a named symbol")
  }

  /** Converts to a variable. */
  def asVariable: Variable = Parser.parser.termParser(s) match {
    case v: Variable => v
    case _ => throw new IllegalArgumentException("Input " + s + " is not a variable")
  }

  /** Converts to a function symbol (elaborates variables). */
  def asFunction: Function = Parser.parser.termParser(s) match {
    case v: Variable  => Function(v.name, v.index, Unit, Real, interp=None)
    case FuncOf(f, _) => f
    case _ => throw new IllegalArgumentException("Input " + s + " is not a function")
  }

  /** Converts to a formula. */
  def asFormula: Formula = Parser.parser.formulaParser(s)

  /** Converts to a program or game. */
  def asProgram: Program = Parser.parser.programParser(s)

  /** Converts to a differential program. */
  def asDifferentialProgram: DifferentialProgram = Parser.parser.differentialProgramParser(s)

  /** Converts to a tactic. */
  def asTactic: BelleExpr = BelleParser(s)

  /** Converts to a sequent. */
  def asSequent: Sequent = Parser.parser.sequentParser(s)

  /** Converts to a substitution pair. */
  def asSubstitutionPair: SubstitutionPair = UnificationSubstitutionParser.parseSubstitutionPair(s)

  /** Converts to proof state labels. */
  def asLabel: BelleLabel = BelleLabel.fromString(s) match {
    case l :: Nil => l
    case _ => throw new IllegalArgumentException(s + " is not a single label")
  }
  /** Converts to proof state top-level label. */
  def asTopLevelLabel: BelleTopLevelLabel = BelleLabel.fromString(s) match {
    case (l: BelleTopLevelLabel) :: Nil => l
    case _ => throw new IllegalArgumentException(s + " is not a single top-level label")
  }
  /** Converts to proof state labels. */
  def asLabels: List[BelleLabel] = BelleLabel.fromString(s)
}
