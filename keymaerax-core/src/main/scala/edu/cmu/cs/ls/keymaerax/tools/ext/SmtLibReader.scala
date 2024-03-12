/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.tools.ext

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.InterpretedSymbols
import edu.cmu.cs.ls.keymaerax.tools.ConversionException
import edu.cmu.cs.ls.keymaerax.tools.qe.DefaultSMTConverter
import smtlib.theories.{Core, Reals}
import smtlib.trees.Commands.{Logic, _}
import smtlib.trees.Terms.{Attribute, FunctionApplication, Identifier, QualifiedIdentifier, SKeyword, SSymbol}
import smtlib.trees.Terms

import java.io.{Reader, StringReader}
import scala.collection.mutable.ListBuffer

/** Reads [[Expression]]s from SMT-LIB format: converts every (assert X) statement into an expression. */
object SmtLibReader {
  val USCORE: String = "uscore"

  /** Reads a formula from an input containing a single (assert). */
  def readAssert(s: String): (Formula, Map[String, String]) = {
    read(new StringReader(s)) match {
      case ((f: Formula) :: Nil, info) => (f, info)
      case _ => throw new IllegalArgumentException("Not a single formula: " + s)
    }
  }

  /** Reads a formula. */
  def readFml(s: String): Formula = readExpr(s, convertFormula(_)(Map.empty))

  /** Reads a term. */
  def readTerm(s: String): Term = readExpr(s, convertTerm(_)(Map.empty))

  /** Reads an expression using `convert` to turn it into the desired kind. */
  private def readExpr[T <: Expression](s: String, convert: Terms.Term => T): T = {
    val r = new StringReader(s)
    val lexer = new smtlib.lexer.Lexer(r)
    val parser = new smtlib.parser.Parser(lexer)
    val term = parser.parseTerm
    convert(term)
  }

  /** Reads expressions occurring in `(assert ...)` statements in the input provided by reader `r`. */
  def read(r: Reader): (List[Expression], Map[String, String]) = {
    val lexer = new smtlib.lexer.Lexer(r)
    val parser = new smtlib.parser.Parser(lexer)
    val cmds = new ListBuffer[Command]
    var cmd = parser.parseCommand
    while (cmd != null) {
      cmds.append(cmd)
      cmd = parser.parseCommand
    }
    val infos = scala.collection.mutable.Map.empty[String, String]
    cmds.foreach({
      case SetInfo(Attribute(SKeyword(k), Some(SSymbol(v)))) => infos(k) = v
      case SetLogic(logic) => infos("logic") = Logic.asString(logic)
      case _ => // ignore
    })

    val definedFuns = cmds
      .filter(_.isInstanceOf[DefineFun])
      .map({
        case DefineFun(FunDef(SSymbol(name), _, _, body)) => name -> convertFormula(body)(Map.empty)
        case _ => ???
      })
      .toMap

    (cmds.filter(_.isInstanceOf[Assert]).map({ case Assert(t) => convertFormula(t)(definedFuns) }).toList, infos.toMap)
  }

  /** Sanitizes names by replacing `_`with [[USCORE]]. */
  private def sanitize(name: String): String = { name.replace("_", USCORE) }

  /** Converts a formula. */
  def convertFormula(t: Terms.Term)(implicit defs: Map[String, Expression]): Formula = t match {
    case Core.True() => True
    case Core.False() => False
    case Reals.LessThan(l, r) => Less(convertTerm(l), convertTerm(r))
    case Reals.LessEquals(l, r) => LessEqual(convertTerm(l), convertTerm(r))
    case Reals.GreaterThan(l, r) => Greater(convertTerm(l), convertTerm(r))
    case Reals.GreaterEquals(l, r) => GreaterEqual(convertTerm(l), convertTerm(r))
    case Core.Equals(l, r) => Equal(convertTerm(l), convertTerm(r))
    case Core.Not(p) => Not(convertFormula(p))
    case Core.And(l, r) => And(convertFormula(l), convertFormula(r))
    case Core.Or(l, r) => Or(convertFormula(l), convertFormula(r))
    case Core.Implies(l, r) => Imply(convertFormula(l), convertFormula(r))
    case Core.Xor(l, r) =>
      val cl = convertFormula(l)
      val cr = convertFormula(r)
      Or(And(cl, Not(cr)), And(Not(cl), cr))
    case FunctionApplication(QualifiedIdentifier(Identifier(SSymbol("equiv"), Nil), None), terms) =>
      assert(terms.size == 2, "Equiv expected between exactly 2 formulas")
      Equiv(convertFormula(terms(0)), convertFormula(terms(1)))
    // unary and n-ary operators
    case FunctionApplication(QualifiedIdentifier(Identifier(SSymbol(op), Nil), None), terms) =>
      assert(terms.nonEmpty, "Unary/n-ary and expects at least 1 argument")
      val converted = terms.map(convertFormula)
      converted
        .reduceRightOption(op match {
          case "and" => And
          case "or" => Or
        })
        .getOrElse(converted.head)
    case Terms.Exists(sv, svs, t) =>
      (sv +: svs).foldLeft(convertFormula(t))({ case (f, v) => Exists(convertVar(v) :: Nil, f) })
    case Terms.Forall(sv, svs, t) =>
      (sv +: svs).foldLeft(convertFormula(t))({ case (f, v) => Forall(convertVar(v) :: Nil, f) })
    case QualifiedIdentifier(Identifier(SSymbol(name), Nil), _) => defs(name).asInstanceOf[Formula]
  }

  /** Converts a term. */
  def convertTerm(t: Terms.Term)(implicit defs: Map[String, Expression]): Term = t match {
    case Reals.NumeralLit(n) => Number(BigDecimal(n))
    case Reals.DecimalLit(n) => if (n.isValidLong) Number(BigDecimal(n.longValue)) else Number(n)
    case QualifiedIdentifier(Terms.Identifier(Terms.SSymbol(name), Nil), None) =>
      if (name.startsWith("-")) {
        // workaround for parser bug
        Neg(Number(BigDecimal(name.stripPrefix("-").trim)))
      } else
        try {
          DefaultSMTConverter.nameFromIdentifier(name) match {
            case v: Variable => v // @note also differential symbols
            case f: Function => FuncOf(f, Nothing)
          }
        } catch {
          case _: ConversionException =>
            // @todo functions vs. variables in non-KeYmaera X generated SMT-Lib input
            Variable(sanitize(name))
        }
    case Reals.Neg(c) => Neg(convertTerm(c))
    case Reals.Add(l, r) => Plus(convertTerm(l), convertTerm(r))
    case Reals.Sub(l, r) => Minus(convertTerm(l), convertTerm(r))
    case Reals.Mul(l, r) => Times(convertTerm(l), convertTerm(r))
    case Reals.Div(l, r) => Divide(convertTerm(l), convertTerm(r))
    // pow
    case FunctionApplication(QualifiedIdentifier(Identifier(SSymbol("^"), Nil), None), s :: t :: Nil) =>
      Power(convertTerm(s), convertTerm(t))
    // interpreted functions
    case FunctionApplication(QualifiedIdentifier(Identifier(SSymbol("absolute"), Nil), None), s :: Nil) =>
      FuncOf(InterpretedSymbols.absF, convertTerm(s))
    case FunctionApplication(QualifiedIdentifier(Identifier(SSymbol("minimum"), Nil), None), s :: t :: Nil) =>
      FuncOf(InterpretedSymbols.minF, Pair(convertTerm(s), convertTerm(t)))
    case FunctionApplication(QualifiedIdentifier(Identifier(SSymbol("maximum"), Nil), None), s :: t :: Nil) =>
      FuncOf(InterpretedSymbols.maxF, Pair(convertTerm(s), convertTerm(t)))
    // nary operators
    case FunctionApplication(QualifiedIdentifier(Identifier(SSymbol("*"), Nil), None), t :: Nil) => convertTerm(t)
    case FunctionApplication(QualifiedIdentifier(Identifier(SSymbol("*"), Nil), None), terms) =>
      terms.map(convertTerm).reduce(Times)
    case FunctionApplication(QualifiedIdentifier(Identifier(SSymbol("+"), Nil), None), t :: Nil) => convertTerm(t)
    case FunctionApplication(QualifiedIdentifier(Identifier(SSymbol("+"), Nil), None), terms) =>
      terms.map(convertTerm).reduce(Plus)
    case QualifiedIdentifier(Identifier(SSymbol(name), Nil), _) => defs(name).asInstanceOf[Term]
  }

  /** Converts a variable. */
  private def convertVar(t: Terms.SortedVar): Variable = t match {
    case Terms.SortedVar(Terms.SSymbol(name), sort) if Reals.RealSort.unapply(sort) =>
      DefaultSMTConverter.nameFromIdentifier(name) match {
        case v: BaseVariable => v
        case f => throw new IllegalArgumentException("Expected a variable, but got " + f.prettyString)
      }
  }
}
