package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, BelleLabel, BelleTopLevelLabel}
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.FormulaTools

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

  /** Converts a `::` separated list of expressions. */
  def asExprList[T <: Expression]: List[T] = {
    def convert(elements: Array[String]): List[T] = elements.map(new StringConverter(_).asExpr.asInstanceOf[T]).toList
    val elements = s.split("::")
    if (elements.last.trim == "nil") convert(elements.dropRight(1))
    else convert(elements)
  }

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
    case v: Variable  => Function(v.name, v.index, Unit, Real, interpreted=false)
    case FuncOf(f, _) => f
    case _ => throw new IllegalArgumentException("Input " + s + " is not a function")
  }

  /** Converts to a formula. */
  def asFormula: Formula = Parser.parser.formulaParser(s)

  /** Converts to a list of formulas (formulas comma-separated in input). */
  def asFormulaList: List[Formula] = SequentParser.parseFormulaList(s)

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

  /** Converts a stringified list of substitution pairs to a declaration object. */
  def asDeclaration: Declaration = {
    def fnPredToNameSignature(fn: Function, arg: Term, repl: Expression): (Name, Signature) = {
      val args =
        if (fn.domain == Unit) Nil
        else FormulaTools.argumentList(arg).map({ case n: NamedSymbol => Name(n.name, n.index) -> n.sort })
      Name(fn.name, fn.index) -> Signature(Some(fn.domain), fn.sort, Some(args), Some(repl), UnknownLocation)
    }
    def prgToNameSignature(n: NamedSymbol, repl: Expression): (Name, Signature) = n match {
      case _: ProgramConst | _: SystemConst =>
        Name(n.name, n.index) -> Signature(None, Trafo, None, Some(repl), UnknownLocation)
    }

    Declaration(s.trim.stripSuffix("nil").trim.stripSuffix("::").split("::").
        map(new StringConverter(_).asSubstitutionPair).map({
      case SubstitutionPair(FuncOf(fn: Function, arg), repl) => fnPredToNameSignature(fn, arg, repl)
      case SubstitutionPair(PredOf(fn: Function, arg), repl) => fnPredToNameSignature(fn, arg, repl)
      case SubstitutionPair(p: ProgramConst, repl) => prgToNameSignature(p, repl)
      case SubstitutionPair(p: SystemConst, repl) => prgToNameSignature(p, repl)
      case _ => throw new IllegalArgumentException("Converter currently supports functions/predicates/program+system constants")
    }).toMap)
  }

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
