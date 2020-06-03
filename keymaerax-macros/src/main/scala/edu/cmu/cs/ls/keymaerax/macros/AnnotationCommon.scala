package edu.cmu.cs.ls.keymaerax.macros

import edu.cmu.cs.ls.keymaerax.macros.Axiom.ExprPos

import scala.reflect.macros.whitebox

object AnnotationCommon {
  def toArgInfo(name: String, tpe: String, allowFresh: List[String])(implicit c: whitebox.Context): ArgInfo = {
    import c.universe._
    val first = tpe.indexOf('[')
    val last = tpe.lastIndexOf(']')
    if (first != -1 && last != -1) {
      val (tpeFun, tpeArg) = (tpe.slice(0, first).trim.toLowerCase, tpe.slice(first + 1, last).trim.toLowerCase)
      tpeFun match {
        case "list" => ListArg(name, tpeArg, allowFresh)
        case "option" => OptionArg(toArgInfo(name, tpeArg, allowFresh))
        case s => c.abort(c.enclosingPosition, "Unexpected type constructor: " + s + ", should be option[] or list[]")
      }
    } else {
      tpe match {
        case "variable" => VariableArg(name, allowFresh)
        case "term" => new TermArg(name, allowFresh)
        case "formula" => FormulaArg(name, allowFresh)
        case "number" => NumberArg(name, allowFresh)
        case "string" => StringArg(name, allowFresh)
        case "expression" => new ExpressionArg(name, allowFresh)
        case "substitution" => SubstitutionArg(name, allowFresh)
        case s => c.abort(c.enclosingPosition, "Unexpected type name: " + s + ", should be number, string, substitution, variable, term, formula, expression, list[t], or option[t]")
      }
    }
  }
  def parseAI(s: String)(implicit c: whitebox.Context): ArgInfo = {
    s.split(":").toList match {
      case id :: tpe :: Nil =>
        val first = id.indexOf('[')
        val last = id.lastIndexOf(']')
        val (name, allowFresh) =
          if (first != -1 && last != -1)
            (id.slice(0, first), id.slice(first+1, last).split(',').toList)
          else (id, Nil)
        toArgInfo(name, tpe, allowFresh)
      case ss => c.abort(c.enclosingPosition, "Invalid argument type descriptor:" + s)
    }
  }
  def parseAIs(s: String)(implicit c: whitebox.Context): List[ArgInfo] = {
    if (s.isEmpty) Nil
    else s.split(";;").toList.map(parseAI)
  }
  def parseSequent(str: String)(implicit c: whitebox.Context): SequentDisplay = {
    if(str == "*") {
      SequentDisplay(Nil, Nil, isClosed = true)
    } else {
      str.split("\\|-").toList match {
        case ante :: succ :: Nil =>
          val (a, s) = (ante.split(",").toList, succ.split(",").toList)
          SequentDisplay(a, s)
        case succ :: Nil =>
          val s = succ.split(",").toList
          SequentDisplay(Nil, s)
        case ss => c.abort(c.enclosingPosition, "Expected at most one |- in sequent, got: " + ss)
      }
    }
  }
  def parseSequents(s: String)(implicit c: whitebox.Context): List[SequentDisplay] = {
    if (s.isEmpty) Nil
    else s.split(";;").toList.map(parseSequent)
  }
  def toNonneg(s: String)(implicit c: whitebox.Context): Int = {
    val i =
      try {
         s.toInt
      } catch {
        case t: Throwable => c.abort(c.enclosingPosition, "Could not convert position " + s + " to integer")
      }
    if (i < 0) c.abort(c.enclosingPosition, "Position needs to be nonnegative, got: " + i)
    else i
  }
  def parsePos(s: String)(implicit c: whitebox.Context): ExprPos = {
    if(s == "*" || s == "") Nil
    else s.split("\\.").toList.map(toNonneg)
  }
  def parsePoses(s: String)(implicit c: whitebox.Context): List[ExprPos] = {
    if(s == "") Nil
    else s.split(";").toList.map(parsePos)
  }

  // Abstract syntax trees for string and string list literals
  def literal(s: String)(implicit c: whitebox.Context): c.universe.Tree = c.universe.Literal(c.universe.Constant(s))
  def literals(ss: List[String])(implicit c: whitebox.Context): c.universe.Tree = {
    import c.universe._
    q"""List(..${ss.map((s: String) => literal(s))})"""
  }
  // Abstract syntax trees for all the display info data structures
  def convAIs(ais: List[ArgInfo])(implicit c: whitebox.Context): c.universe.Tree = {
    import c.universe._
    q"""List(..${ais.map((ai:ArgInfo) => convAI(ai))})"""
  }
  def convAI(ai: ArgInfo)(implicit c: whitebox.Context): c.universe.Tree = {
    import c.universe._
    ai match {
      case VariableArg(name, allowsFresh) => q"""new edu.cmu.cs.ls.keymaerax.macros.VariableArg(${literal(name)}, ${literals(allowsFresh)})"""
      case NumberArg(name, allowsFresh) => q"""new edu.cmu.cs.ls.keymaerax.macros.NumberArg(${literal(name)}, ${literals(allowsFresh)})"""
      case StringArg(name, allowsFresh) => q"""new edu.cmu.cs.ls.keymaerax.macros.StringArg(${literal(name)}, ${literals(allowsFresh)})"""
      case SubstitutionArg(name, allowsFresh) => q"""new edu.cmu.cs.ls.keymaerax.macros.SubstitutionArg(${literal(name)}, ${literals(allowsFresh)})"""
      case OptionArg(arg) => q"""new edu.cmu.cs.ls.keymaerax.macros.OptionArg(${convAI(arg)})"""
      case FormulaArg(name, allowsFresh) => q"""new edu.cmu.cs.ls.keymaerax.macros.FormulaArg(${literal(name)}, ${literals(allowsFresh)})"""
      case ListArg(name, sort, allowsFresh) => q"""new edu.cmu.cs.ls.keymaerax.macros.ListArg(${literal(name)}, ${literal(sort)}, ${literals(allowsFresh)})"""
      case ta: TermArg => q"""new edu.cmu.cs.ls.keymaerax.macros.TermArg(${literal(ta.name)}, ${literals{ta.allowsFresh}})"""
      case ea: ExpressionArg => q"""new edu.cmu.cs.ls.keymaerax.macros.ExpressionArg (${literal(ea.name)}, ${literals(ea.allowsFresh)})"""
    }
  }
  def convSD(sd: SequentDisplay)(implicit c: whitebox.Context): c.universe.Tree = {
    import c.universe._
    val SequentDisplay(ante: List[String], succ: List[String], isClosed: Boolean) = sd
    q"""new SequentDisplay($ante, $succ, $isClosed)"""
  }
  def convDI(di: DisplayInfo)(implicit c: whitebox.Context): c.universe.Tree = {
    import c.universe._
    di match {
      case SimpleDisplayInfo(name, asciiName) => q"""new edu.cmu.cs.ls.keymaerax.macros.SimpleDisplayInfo(${literal(name)}, ${literal(asciiName)})"""
      case RuleDisplayInfo(names, conclusion, premises)  =>
        val namesTree = convDI(names)
        val conclusionTree = convSD(conclusion)
        val premiseTrees = premises.map((sd: SequentDisplay) => convSD(sd))
        q"""new edu.cmu.cs.ls.keymaerax.macros.RuleDisplayInfo(${namesTree}, ${conclusionTree}, ${premiseTrees})"""
      case AxiomDisplayInfo(names: SimpleDisplayInfo, displayFormula: String) =>
        q"""new edu.cmu.cs.ls.keymaerax.macros.AxiomDisplayInfo(${convDI(names)}, ${literal(displayFormula)})"""
      case InputAxiomDisplayInfo(names: SimpleDisplayInfo, displayFormula: String, input: List[ArgInfo]) =>
        q"""new edu.cmu.cs.ls.keymaerax.macros.InputAxiomDisplayInfo(${convDI(names)}, ${literal(displayFormula)}, ${convAIs(input)})"""
    }
  }
  def sequentDisplayFromObj(a: Any)(implicit c: whitebox.Context): SequentDisplay = {
    a match {
      case (ante: List[String], succ: List[String]) => SequentDisplay(ante, succ)
      case sd: SequentDisplay => sd
      case e => c.abort(c.enclosingPosition, "Expected SequentDisplay, got: " + e)
    }
  }
  def foldParams(c: whitebox.Context, paramNames: List[String])(acc: (Int, Boolean, Map[String, c.universe.Tree]), param: c.universe.Tree): (Int, Boolean, Map[String, c.universe.Tree]) = {
    import c.universe._
    val (idx, wereNamed, paramMap) = acc
    val (k, v, isNamed) = param match {
      case na: AssignOrNamedArg => {
        na.lhs match {
          case id: Ident => (id.name.decodedName.toString, na.rhs, true)
          case e => c.abort(c.enclosingPosition, "Expected argument name to be identifier, got: " + e)
        }
      }
      case t: Tree if !wereNamed => (paramNames(idx), t, false)
      case t: Tree => c.abort(c.enclosingPosition, "Positional argument " + t + " must appear before all named arguments")
    }
    (idx+1, isNamed || wereNamed, paramMap.+(k -> v))
  }

}
