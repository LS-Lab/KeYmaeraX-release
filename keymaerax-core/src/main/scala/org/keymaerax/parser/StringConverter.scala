/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.parser

import org.keymaerax.bellerophon.{BelleExpr, BelleLabel, BelleTopLevelLabel}
import org.keymaerax.core._
import org.keymaerax.infrastruct.Augmentors.ExpressionAugmentor
import org.keymaerax.infrastruct.FormulaTools

/**
 * Implicit conversions from strings into core data structures. Created by smitsch on 1/8/15.
 * @author
 *   Stefan Mitsch
 * @author
 *   Andre Platzer
 */
object StringConverter {
  import scala.language.implicitConversions
  implicit def StringToStringConverter(s: String): StringConverter = new StringConverter(s)
}

/** Conversions of string `s` to core/tactic data structures. */
class StringConverter(val s: String) {

  /** Converts to an expression. */
  def asExpr: Expression = asExpr(InterpretedSymbols.mathKyxDefs)
  def asExpr(defs: Declaration): Expression = elaborate(defs)(Parser(s))

  /** Converts to a term. */
  def asTerm: Term = asTerm(InterpretedSymbols.mathKyxDefs)
  def asTerm(defs: Declaration): Term = elaborate(defs)(Parser.parser.termParser(s))
  def asPlainTerm: Term = asTerm(Declaration(Map.empty))

  /** Converts to a named symbol. */
  def asNamedSymbol: NamedSymbol = asNamedSymbol(InterpretedSymbols.mathKyxDefs)
  def asNamedSymbol(defs: Declaration): NamedSymbol = elaborate(defs)(Parser(s) match {
    case ns: NamedSymbol => ns
    case _ => throw new IllegalArgumentException("Input " + s + " is not a named symbol")
  })
  def asPlainNamedSymbol: NamedSymbol = asNamedSymbol(Declaration(Map.empty))

  /** Converts to a variable. */
  def asVariable: Variable = Parser.parser.termParser(s) match {
    case v: Variable => v
    case _ => throw new IllegalArgumentException("Input " + s + " is not a variable")
  }

  /** Converts to a function symbol (elaborates variables). */
  def asFunction: Function = asFunction(InterpretedSymbols.mathKyxDefs)
  def asFunction(defs: Declaration): Function = elaborate(defs)(Parser.parser.termParser(s) match {
    case v: Variable => Function(v.name, v.index, Unit, Real, interp = None)
    case FuncOf(f, _) => f
    case _ => throw new IllegalArgumentException("Input " + s + " is not a function")
  })
  def asPlainFunction: Function = asFunction(Declaration(Map.empty))

  /** Converts to a formula. */
  def asFormula: Formula = asFormula(InterpretedSymbols.mathKyxDefs)

  /** Converst to a formula using the definitions `defs`. */
  def asFormula(defs: Declaration): Formula = elaborate(defs)(Parser.parser.formulaParser(s))
  def asPlainFormula: Formula = asFormula(Declaration(Map.empty))

  /** Converts to a list of formulas (formulas comma-separated in input). */
  def asFormulaList: List[Formula] = asFormulaList(InterpretedSymbols.mathKyxDefs)
  def asFormulaList(defs: Declaration): List[Formula] = SequentParser.parseFormulaList(s).map(elaborate(defs))

  /** Converts to a program or game. */
  def asProgram: Program = asProgram(InterpretedSymbols.mathKyxDefs)
  def asProgram(defs: Declaration): Program = elaborate(defs)(Parser.parser.programParser(s))
  def asPlainProgram: Program = asProgram(Declaration(Map.empty))

  /** Converts to a differential program. */
  def asDifferentialProgram: DifferentialProgram = asDifferentialProgram(InterpretedSymbols.mathKyxDefs)
  def asDifferentialProgram(defs: Declaration): DifferentialProgram =
    elaborate(defs)(Parser.parser.differentialProgramParser(s))
  def asPlainDifferentialProgram: DifferentialProgram = asDifferentialProgram(Declaration(Map.empty))

  /** Converts to a tactic. */
  def asTactic: BelleExpr = ArchiveParser.tacticParser(s)

  /** Converts to a tactic using definitions `defs` to elaborate symbols. */
  def asTactic(defs: Declaration): BelleExpr = ArchiveParser.tacticParser(s, defs)

  /** Converts to a sequent. */
  def asSequent: Sequent = asSequent(InterpretedSymbols.mathKyxDefs)
  def asSequent(defs: Declaration): Sequent = {
    val seq = Parser.parser.sequentParser(s)
    Sequent(seq.ante.map(f => elaborate(defs)(f)), seq.succ.map(f => elaborate(defs)(f)))
  }
  def asPlainSequent: Sequent = asSequent(Declaration(Map.empty))

  /** Converts to a substitution pair. */
  def asSubstitutionPair: SubstitutionPair = asSubstitutionPair(InterpretedSymbols.mathKyxDefs)
  def asSubstitutionPair(defs: Declaration): SubstitutionPair = {
    val sp = UnificationSubstitutionParser.parseSubstitutionPair(s)
    SubstitutionPair(elaborate(defs)(sp.what), elaborate(defs)(sp.repl))
  }
  def asPlainSubstitutionPair: SubstitutionPair = asSubstitutionPair(Declaration(Map.empty))

  /** Converts a stringified list of substitution pairs to a declaration object. */
  def asDeclaration: Declaration = asDeclaration(InterpretedSymbols.mathKyxDefs)
  def asDeclaration(defs: Declaration): Declaration = {
    def fnToNameSignature(fn: Function, arg: Term, repl: Expression, sp: List[SubstitutionPair]): (Name, Signature) = {
      val args =
        if (fn.domain == Unit) Nil
        else FormulaTools.argumentList(arg).map({ case n: NamedSymbol => Name(n.name, n.index) -> n.sort })
      val elabRepl = elaborate(defs)(repl.elaborateToFunctions(
        sp.flatMap({
            case SubstitutionPair(FuncOf(pn, _), _) => Some(pn)
            case SubstitutionPair(PredOf(pn, _), _) => Some(pn)
            case _ => None
          })
          .toSet
      ))
      Name(fn.name, fn.index) ->
        Signature(Some(fn.domain), elabRepl.sort, Some(args), Right(Some(elabRepl)), UnknownLocation)
    }
    def prgToNameSignature(n: NamedSymbol, repl: Expression): (Name, Signature) = n match {
      case _: ProgramConst | _: SystemConst => Name(n.name, n.index) ->
          Signature(None, Trafo, None, Right(Some(repl)), UnknownLocation)
    }

    val sp = s
      .trim
      .stripSuffix("nil")
      .trim
      .stripSuffix("::")
      .split("::")
      .map(new StringConverter(_).asSubstitutionPair)
      .toList

    Declaration(
      sp.map({
          case SubstitutionPair(FuncOf(fn: Function, arg), repl) =>
            fnToNameSignature(fn, arg, elaborate(defs)(repl), sp)
          case SubstitutionPair(PredOf(fn: Function, arg), repl) =>
            fnToNameSignature(fn, arg, elaborate(defs)(repl), sp)
          case SubstitutionPair(p: ProgramConst, repl) => prgToNameSignature(p, elaborate(defs)(repl))
          case SubstitutionPair(p: SystemConst, repl) => prgToNameSignature(p, elaborate(defs)(repl))
          case _ => throw new IllegalArgumentException(
              "Converter currently supports functions/predicates/program+system constants"
            )
        })
        .toMap
    )
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

  /** Elaborates expression `e` according to definitions `defs`. */
  private def elaborate[T <: Expression](defs: Declaration)(e: T): T =
    // defs.implicitSubst(defs.elaborateToSystemConsts(defs.elaborateToFunctions(e)))
    defs.implicitSubst(e)
}
