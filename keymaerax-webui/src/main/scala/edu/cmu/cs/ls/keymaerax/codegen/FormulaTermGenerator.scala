/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.codegen

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors.FormulaAugmentor
import edu.cmu.cs.ls.keymaerax.parser.{Declaration, KeYmaeraXPrettyPrinter}

/**
 * Generates formula and term evaluation code. `termContainer` configures the location where primitive terms are looked
 * up (e.g., structs, classes).
 *
 * @author
 *   Stefan Mitsch
 * @author
 *   Ran Ji
 */
abstract class FormulaTermGenerator(termContainer: Expression => String, defs: Declaration) extends CodeGenerator {

  /** Identifier corresponding to a NamedSymbol */
  protected def nameIdentifier(s: NamedSymbol): String

  /** Prints the sort `s`. */
  protected def printSort(s: Sort): String

  /** Compile a term to an expression evaluating it (in the same arithmetic). */
  protected def compileTerm(t: Term): CTerm = {
    require(
      t.sort == Real || t.sort == Unit || t.sort.isInstanceOf[Tuple],
      "Expected sort Real, but got unsupported sort " + t.sort,
    )
    t match {
      case Nothing => CNothing
      case Neg(c) => CNeg(compileTerm(c))
      case Plus(l, r) => CPlus(compileTerm(l), compileTerm(r))
      case Minus(l, r) => CMinus(compileTerm(l), compileTerm(r))
      case Times(l, r) => CTimes(compileTerm(l), compileTerm(r))
      case Divide(l, r) => CDivide(compileTerm(l), compileTerm(r))
      case Power(l, r) => compilePower(l, r)
      // atomic terms
      case Number(n) =>
        assert(
          n.isDecimalDouble || n.isValidLong,
          throw new CodeGenerationException("Term " + KeYmaeraXPrettyPrinter(t) + " contains illegal-precision numbers"),
        )
        // @note assume the final compiler will detect representation-size errors
        CNumber(n)
      case t: Variable if t.name.endsWith("post") =>
        CVariable(termContainer(t) + nameIdentifier(BaseVariable(t.name.stripSuffix("post"), t.index, t.sort)))
      case t: Variable if !t.name.endsWith("post") => CVariable(termContainer(t) + nameIdentifier(t))
      case FuncOf(Function(fname, None, Unit, Real, None), Nothing) if fname == CEpsilon.name => CEpsilon
      // @note _idx are aliases for the same post variable, todo: preprocess with tactic
      case t @ FuncOf(fn @ Function(fname, fidx, fdom, fsort, fintr), Nothing) =>
        if (fname.endsWith("post")) {
          CVariable(termContainer(t) + nameIdentifier(Function(fname.stripSuffix("post"), fidx, fdom, fsort, fintr)))
        } else if (defs.substs.exists(_.what == t)) {
          // defined function
          CUnaryFunction(nameIdentifier(fn), CNothing)
        } else {
          // parameter or input
          CVariable(termContainer(t) + nameIdentifier(fn))
        }
      case FuncOf(fn, child) => nameIdentifier(fn) match {
          case "abs" => CAbs(compileTerm(child))
          case "min" => val CPair(l, r) = compileTerm(child); CMin(l, r)
          case "max" => val CPair(l, r) = compileTerm(child); CMax(l, r)
          case _ => CUnaryFunction(nameIdentifier(fn), compileTerm(child))
        }
      case Pair(l, r) => CPair(compileTerm(l), compileTerm(r))
      case _ => throw new CodeGenerationException("Conversion of term " + t.prettyString + " is not defined")
    }
  }

  /**
   * Compile exponentials
   * @param base
   *   base of the exponential
   * @param exp
   *   index of the exponential
   * @return
   *   simplified generation of exponential
   */
  protected def compilePower(base: Term, exp: Term): CTerm = {
    if (base.equals(Number(0))) {
      // @todo since when is that the case?
      println("[warning] generating 0^0")
      if (exp.equals(Number(0))) CNumber(1.0) // 0^0 =1
      else CNumber(0.0) // 0^x = 0
    } else {
      exp match {
        case Number(n) =>
          if (n.isValidInt) {
            // index is integer
            if (n.intValue == 0) {
              // index is 0, x^0 = 1
              //            assert(!base.equals(Number(0)), throw new CodeGenerationException("Conversion of 0^0 is not defined"))
              CNumber(1.0)
            } else if (n.intValue > 0) {
              // index n is a positive integer, expand n times of *
              val ba: CTerm = compileTerm(base)
              (1 until n.intValue).foldLeft(ba)((b, _) => CTimes(ba, b))
            } else
              CDivide(CNumber(1.0), compilePower(base, Number(n.underlying().negate()))) // index is negative integer
          } else CPower(compileTerm(base), compileTerm(exp)) // index is not integer, use pow function in C
        case Neg(Number(n)) => CDivide(CNumber(1.0), compilePower(base, Number(n))) // index is negative
        case _ => CPower(compileTerm(base), compileTerm(exp))
      }
    }
  }

  /** Compile a formula to a C expression checking it (in the same arithmetic) */
  protected def compileFormula(f: Formula): CFormula = {
    f match {
      case PredOf(fn, args) => CPredicate(nameIdentifier(fn), compileTerm(args))
      case Not(ff) => CNot(compileFormula(ff))
      case And(l, r) => CAnd(compileFormula(l), compileFormula(r))
      case Or(l, r) => COr(compileFormula(l), compileFormula(r))
      // @todo the following two transformations of formulas should be done by a tactic and just asserted here that these cases no longer happen.
      case Imply(l, r) => compileFormula(Or(Not(l), r))
      case Equiv(l, r) => compileFormula(And(Imply(l, r), Imply(r, l)))
      case Equal(l, r) => CEqual(compileTerm(l), compileTerm(r))
      case NotEqual(l, r) => CNotEqual(compileTerm(l), compileTerm(r))
      case Greater(l, r) => CGreater(compileTerm(l), compileTerm(r))
      case GreaterEqual(l, r) => CGreaterEqual(compileTerm(l), compileTerm(r))
      case Less(l, r) => CLess(compileTerm(l), compileTerm(r))
      case LessEqual(l, r) => CLessEqual(compileTerm(l), compileTerm(r))
      case True => CTrue
      case False => CFalse
      case t: Modal => CFormulaComment(t.prettyString)
      case t: Forall => CFormulaComment(t.prettyString)
      case t: Exists => CFormulaComment(t.prettyString)
      case _ =>
        throw new CodeGenerationException("Conversion of formula " + KeYmaeraXPrettyPrinter(f) + " is not defined")
    }
  }
}

/** Converts formulas and terms according to `prettyPrinter`. Uses `termContainer` to refer to arguments. */
class GenericFormulaTermGenerator(
    prettyPrinter: CodePrettyPrinter,
    termContainer: Expression => String,
    defs: Declaration,
) extends FormulaTermGenerator(termContainer, defs) {

  /** @inheritdoc */
  override def apply(
      expr: Expression,
      stateVars: Set[BaseVariable],
      inputVars: Set[BaseVariable],
      modelName: String,
  ): (String, String) = expr match {
    case f: Formula if f.isFOL => prettyPrinter(compileFormula(f))
    case t: Term => prettyPrinter(compileTerm(t))
  }

  /** @inheritdoc */
  override def nameIdentifier(s: NamedSymbol): String = prettyPrinter.nameIdentifier(s)

  /** @inheritdoc */
  override def printSort(s: Sort): String = prettyPrinter.printSort(s)
}
