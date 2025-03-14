/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics.macros

object AnnotationCommon {
  type ExprPos = List[Int]

  def toArgInfo(name: String, tpe: String, allowFresh: List[String]): ArgInfo = {
    val first = tpe.indexOf('[')
    val last = tpe.lastIndexOf(']')
    if (first != -1 && last != -1) {
      val (tpeFun, tpeArg) = (tpe.slice(0, first).trim.toLowerCase, tpe.slice(first + 1, last).trim.toLowerCase)
      tpeFun match {
        case "list" => ListArg(toArgInfo(name, tpeArg, allowFresh))
        case "option" => OptionArg(toArgInfo(name, tpeArg, allowFresh))
        case s => throw new Exception(s"Unexpected type constructor: $s, should be option[] or list[]")
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
        case s => throw new Exception(
            s"Unexpected type name: $s, should be number, string, substitution, variable, term, formula, expression, list[t], or option[t]"
          )
      }
    }
  }
  def parseAI(s: String): ArgInfo = {
    val iCln = s.lastIndexOf(':')
    require(iCln >= 0, s"Invalid argument type descriptor: $s")
    val (id, tpe) = (s.take(iCln), s.takeRight(s.length - (iCln + 1)))
    val first = id.indexOf('[')
    val last = id.lastIndexOf(']')
    val (name, allowFresh) =
      if (first != -1 && last != -1) (id.slice(0, first).trim, id.slice(first + 1, last).split(',').toList.map(_.trim))
      else (id.trim, Nil)
    toArgInfo(name, tpe.trim, allowFresh)
  }
  def parseAIs(str: String): List[ArgInfo] = {
    val s = str.filter(c => !(c == '\n' || c == '\r'))
    if (s.isEmpty) Nil else s.split(";;").toList.map(s => parseAI(s.trim))
  }
  def toNonneg(s: String): Int = {
    val i =
      try { s.toInt }
      catch { case _: NumberFormatException => throw new Exception(s"Could not convert position $s to integer") }
    require(i >= 0, s"Position needs to be nonnegative, got: $i")
    i
  }
  def parsePos(s: String): ExprPos = { if (s == "*" || s == "") Nil else s.split("\\.").toList.map(toNonneg) }
  def parsePoses(s: String): List[ExprPos] = { if (s == "") Nil else s.split(";").toList.map(parsePos) }

  def axiomDisplayInfo(
      name: String,
      nameAscii: Option[String],
      nameLong: Option[String],
      level: DisplayLevel,
      conclusion: String,
      inputs: String,
  ): DisplayInfo = {
    val pInputs: List[ArgInfo] = parseAIs(inputs)

    val names = DisplayNames.createWithChecks(name = name, nameAscii = nameAscii, nameLong = nameLong)

    (conclusion, pInputs) match {
      case ("", Nil) => SimpleDisplayInfo(names = names, level = level)
      case ("", _) => throw new Exception("axiom with inputs must have a conclusion")
      case (fml, Nil) => AxiomDisplayInfo(names = names, level = level, formula = renderDisplayFormula(fml))
      case (fml, input) => InputAxiomDisplayInfo(names = names, level = level, formula = fml, input = input)
    }
  }

  def ruleDisplayInfo(
      name: String,
      nameAscii: Option[String],
      nameLong: Option[String],
      level: DisplayLevel,
      premises: String,
      conclusion: String,
  ): DisplayInfo = {
    val pPremises = DisplaySequent.parseMany(premises)
    val pConclusionOpt = Some(conclusion).filter(_.nonEmpty).map(DisplaySequent.parse)

    val names = DisplayNames.createWithChecks(name = name, nameAscii = nameAscii, nameLong = nameLong)

    (pPremises, pConclusionOpt) match {
      case (Nil, None) => SimpleDisplayInfo(names = names, level = level)
      case (prem, Some(conc)) =>
        RuleDisplayInfo(names = names, level = level, conclusion = conc, premises = prem, inputGenerator = None)
      case _ => throw new Exception("proof rule with premises must have a conclusion")
    }
  }

  def tacticDisplayInfo(
      inputs: List[ArgInfo],
      inputGenerator: Option[String],
      name: String,
      nameAscii: Option[String],
      nameLong: Option[String],
      level: DisplayLevel,
      premises: String,
      conclusion: String,
      contextPremises: String,
      contextConclusion: String,
  ): DisplayInfo = {
    val pPremises = DisplaySequent.parseMany(premises)
    val pConclusionOpt = Some(conclusion).filter(_.nonEmpty).map(DisplaySequent.parse)
    val pContextPremises = DisplaySequent.parseMany(contextPremises)
    val pContextConclusionOpt = Some(contextConclusion).filter(_.nonEmpty).map(DisplaySequent.parse)

    val names = DisplayNames.createWithChecks(name = name, nameAscii = nameAscii, nameLong = nameLong)

    (inputs, pPremises, pConclusionOpt, pContextPremises, pContextConclusionOpt) match {
      case (_, Nil, None, _, _) => SimpleDisplayInfo(names = names, level = level)

      case (Nil, Nil, Some(_), _, _) =>
        AxiomDisplayInfo(names = names, level = level, formula = renderDisplayFormula(conclusion))

      case (ins, Nil, Some(_), _, _) if ins.nonEmpty =>
        InputAxiomDisplayInfo(names = names, level = level, formula = conclusion, input = inputs)

      case (_, prems, Some(concl), Nil, None) if prems.nonEmpty =>
        RuleDisplayInfo(
          names = names,
          level = level,
          conclusion = concl,
          premises = prems,
          inputGenerator = inputGenerator,
        )

      case (_, prem, Some(concl), ctxPrem, Some(ctxConcl)) if prem.nonEmpty && ctxPrem.nonEmpty =>
        TacticDisplayInfo(
          names = names,
          level = level,
          conclusion = concl,
          premises = prem,
          ctxConclusion = ctxConcl,
          ctxPremises = ctxPrem,
          inputGenerator = inputGenerator,
        )

      case _ => throw new Exception("tactic with premises or inputs must have a conclusion")
    }
  }

  /** Elaborate the display formula from a raw unicode string that may contain HTML tags to HTML. */
  // TODO Figure out how to get rid of this
  private def renderDisplayFormula(displayFormula: String) = displayFormula
    .replace("<", "&lt;")
    .replace(">", "&gt;")
    .replaceAll("&lt;(/?(\\w+))&gt;", "<$1>") // undo escaping HTML tags
    .replaceFirst("__", "<span class=\"k4-axiom-key\">").replaceFirst("__", "</span>")
}
