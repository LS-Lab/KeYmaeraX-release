/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics.macros

import scala.reflect.macros.{blackbox, whitebox}

object AnnotationCommon {
  type ExprPos = List[Int]

  def toArgInfo(name: String, tpe: String, allowFresh: List[String])(implicit c: blackbox.Context): ArgInfo = {
    val first = tpe.indexOf('[')
    val last = tpe.lastIndexOf(']')
    if (first != -1 && last != -1) {
      val (tpeFun, tpeArg) = (tpe.slice(0, first).trim.toLowerCase, tpe.slice(first + 1, last).trim.toLowerCase)
      tpeFun match {
        case "list" => ListArg(toArgInfo(name, tpeArg, allowFresh))
        case "option" => OptionArg(toArgInfo(name, tpeArg, allowFresh))
        case s => c.abort(c.enclosingPosition, "Unexpected type constructor: " + s + ", should be option[] or list[]")
      }
    } else {
      tpe.trim.toLowerCase match {
        case "variable" => VariableArg(name, allowFresh)
        case "term" => TermArg(name, allowFresh)
        case "formula" => FormulaArg(name, allowFresh)
        case "number" => NumberArg(name, allowFresh)
        case "string" => StringArg(name, allowFresh)
        case "expression" => ExpressionArg(name, allowFresh)
        case "substitution" => SubstitutionArg(name, allowFresh)
        case s => c.abort(
            c.enclosingPosition,
            "Unexpected type name: " + s +
              ", should be number, string, substitution, variable, term, formula, expression, list[t], or option[t]",
          )
      }
    }
  }
  def parseAI(s: String)(implicit c: blackbox.Context): ArgInfo = {
    val iCln = s.lastIndexOf(':')
    if (iCln < 0) c.abort(c.enclosingPosition, "Invalid argument type descriptor:" + s)
    val (id, tpe) = (s.take(iCln), s.takeRight(s.length - (iCln + 1)))
    val first = id.indexOf('[')
    val last = id.lastIndexOf(']')
    val (name, allowFresh) =
      if (first != -1 && last != -1) (id.slice(0, first).trim, id.slice(first + 1, last).split(',').toList.map(_.trim))
      else (id.trim, Nil)
    toArgInfo(name, tpe.trim, allowFresh)
  }
  def parseAIs(str: String)(implicit c: blackbox.Context): List[ArgInfo] = {
    val s = str.filter(c => !(c == '\n' || c == '\r'))
    if (s.isEmpty) Nil else s.split(";;").toList.map(s => parseAI(s.trim))
  }
  def toNonneg(s: String)(implicit c: blackbox.Context): Int = {
    val i =
      try { s.toInt }
      catch { case t: Throwable => c.abort(c.enclosingPosition, "Could not convert position " + s + " to integer") }
    if (i < 0) c.abort(c.enclosingPosition, "Position needs to be nonnegative, got: " + i) else i
  }
  def parsePos(s: String)(implicit c: blackbox.Context): ExprPos = {
    if (s == "*" || s == "") Nil else s.split("\\.").toList.map(toNonneg)
  }
  def parsePoses(s: String)(implicit c: blackbox.Context): List[ExprPos] = {
    if (s == "") Nil else s.split(";").toList.map(parsePos)
  }

  def astForArgInfo(ai: ArgInfo)(implicit c: blackbox.Context): c.universe.Tree = {
    import c.universe._
    ai match {
      case GeneratorArg(name) => q"""new org.keymaerax.btactics.macros.GeneratorArg($name)"""
      case VariableArg(name, allowsFresh) => q"""new org.keymaerax.btactics.macros.VariableArg($name, $allowsFresh)"""
      case NumberArg(name, allowsFresh) => q"""new org.keymaerax.btactics.macros.NumberArg($name, $allowsFresh)"""
      case StringArg(name, allowsFresh) => q"""new org.keymaerax.btactics.macros.StringArg($name, $allowsFresh)"""
      case PosInExprArg(name, allowsFresh) => q"""new org.keymaerax.btactics.macros.PosInExprArg($name, $allowsFresh)"""
      case SubstitutionArg(name, allowsFresh) =>
        q"""new org.keymaerax.btactics.macros.SubstitutionArg($name, $allowsFresh)"""
      case OptionArg(arg) => q"""new org.keymaerax.btactics.macros.OptionArg(${astForArgInfo(arg)})"""
      case FormulaArg(name, allowsFresh) => q"""new org.keymaerax.btactics.macros.FormulaArg($name, $allowsFresh)"""
      case ListArg(arg) => q"""new org.keymaerax.btactics.macros.ListArg(${astForArgInfo(arg)})"""
      case ta: TermArg => q"""new org.keymaerax.btactics.macros.TermArg(${ta.name}, ${ta.allowsFresh})"""
      case ea: ExpressionArg => q"""new org.keymaerax.btactics.macros.ExpressionArg (${ea.name}, ${ea.allowsFresh})"""
    }
  }

  private def astForDisplayLevel(level: DisplayLevel)(implicit c: blackbox.Context): c.universe.Tree = {
    import c.universe._
    level match {
      case DisplayLevelInternal => q"org.keymaerax.btactics.macros.DisplayLevelInternal"
      case DisplayLevelBrowse => q"org.keymaerax.btactics.macros.DisplayLevelBrowse"
      case DisplayLevelMenu => q"org.keymaerax.btactics.macros.DisplayLevelMenu"
      case DisplayLevelAll => q"org.keymaerax.btactics.macros.DisplayLevelAll"
    }
  }

  private def astForDisplaySequent(sequent: DisplaySequent)(implicit c: blackbox.Context): c.universe.Tree = {
    import c.universe._

    val DisplaySequent(ante, succ, isClosed) = sequent
    q"""new org.keymaerax.btactics.macros.DisplaySequent(
      ante = $ante,
      succ = $succ,
      isClosed = $isClosed,
    )"""
  }

  def astForDisplayInfo(displayInfo: DisplayInfo)(implicit c: blackbox.Context): c.universe.Tree = {
    import c.universe._

    displayInfo match {
      case SimpleDisplayInfo(name, nameAscii, nameLong, level) =>
        q"""new org.keymaerax.btactics.macros.SimpleDisplayInfo(
          name = $name,
          nameAscii = $nameAscii,
          nameLong = $nameLong,
          level = ${astForDisplayLevel(level)},
        )"""

      case RuleDisplayInfo(name, nameAscii, nameLong, level, conclusion, premises, inputGenerator) =>
        q"""new org.keymaerax.btactics.macros.RuleDisplayInfo(
          name = $name,
          nameAscii = $nameAscii,
          nameLong = $nameLong,
          level = ${astForDisplayLevel(level)},
          conclusion = ${astForDisplaySequent(conclusion)},
          premises = ${premises.map(astForDisplaySequent)},
          inputGenerator = $inputGenerator,
        )"""

      case TacticDisplayInfo(
            name,
            nameAscii,
            nameLong,
            level,
            conclusion,
            premises,
            ctxConclusion,
            ctxPremises,
            inputGenerator,
          ) => q"""new org.keymaerax.btactics.macros.TacticDisplayInfo(
          name = $name,
          nameAscii = $nameAscii,
          nameLong = $nameLong,
          level = ${astForDisplayLevel(level)},
          conclusion = ${astForDisplaySequent(conclusion)},
          premises = ${premises.map(astForDisplaySequent)},
          ctxConclusion = ${astForDisplaySequent(ctxConclusion)},
          ctxPremises = ${ctxPremises.map(astForDisplaySequent)},
          inputGenerator = $inputGenerator,
        )"""

      case AxiomDisplayInfo(name, nameAscii, nameLong, level, formula) =>
        q"""new org.keymaerax.btactics.macros.AxiomDisplayInfo(
          name = $name,
          nameAscii = $nameAscii,
          nameLong = $nameLong,
          level = ${astForDisplayLevel(level)},
          formula = $formula,
        )"""

      case InputAxiomDisplayInfo(name, nameAscii, nameLong, level, formula, input) =>
        q"""new org.keymaerax.btactics.macros.InputAxiomDisplayInfo(
          name = $name,
          nameAscii = $nameAscii,
          nameLong = $nameLong,
          level = ${astForDisplayLevel(level)},
          formula = $formula,
          input = ${input.map(astForArgInfo)},
        )"""
    }
  }

  def astForUnifier(unifier: Unifier)(implicit c: blackbox.Context): c.universe.Tree = {
    import c.universe._
    unifier match {
      case UnifierFull => q"org.keymaerax.btactics.macros.UnifierFull"
      case UnifierLinear => q"org.keymaerax.btactics.macros.UnifierLinear"
      case UnifierSurjective => q"org.keymaerax.btactics.macros.UnifierSurjective"
      case UnifierSurjectiveLinear => q"org.keymaerax.btactics.macros.UnifierSurjectiveLinear"
      case UnifierSurjectiveLinearPretend => q"org.keymaerax.btactics.macros.UnifierSurjectiveLinearPretend"
    }
  }

  def getName(name: String)(implicit c: whitebox.Context): String = {
    val valid = "^[a-zA-Z0-9_]*$".r.matches(name)
    if (!valid) c.abort(c.enclosingPosition, "name must consist only of a-z, A-Z, 0-9, _")

    name
  }

  def getDisplayName(displayName: Option[String], name: String)(implicit c: whitebox.Context): String = {
    if (displayName.contains(name)) c.warning(c.enclosingPosition, "redundant displayName")

    displayName.getOrElse(name)
  }

  def getDisplayNameAscii(displayNameAscii: Option[String], displayName: String)(implicit
      c: whitebox.Context
  ): String = {
    if (displayNameAscii.contains(displayName)) c.warning(c.enclosingPosition, "redundant displayNameAscii")

    val result = displayNameAscii.getOrElse(displayName)

    val isPrintableAscii = result.codePoints().allMatch(c => 0x20 <= c && c <= 0x7e)
    if (!isPrintableAscii) {
      c.abort(c.enclosingPosition, "displayNameAscii contains characters outside the printable ASCII range")
    }

    result
  }

  def getDisplayNameLong(displayNameLong: Option[String], displayName: String)(implicit c: whitebox.Context): String = {
    if (displayNameLong.contains(displayName)) c.warning(c.enclosingPosition, "redundant displayNameLong")

    displayNameLong.getOrElse(displayName)
  }

  /** Elaborate the display formula from a raw unicode string that may contain HTML tags to HTML. */
  // TODO Figure out how to get rid of this
  def renderDisplayFormula(displayFormula: String) = displayFormula
    .replace("<", "&lt;")
    .replace(">", "&gt;")
    .replaceAll("&lt;(/?(\\w+))&gt;", "<$1>") // undo escaping HTML tags
    .replaceFirst("__", "<span class=\"k4-axiom-key\">").replaceFirst("__", "</span>")
}
