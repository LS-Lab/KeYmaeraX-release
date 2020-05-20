/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.macros

import edu.cmu.cs.ls.keymaerax.macros.DerivedAxiom.ExprPos

import scala.annotation.StaticAnnotation
import scala.collection.immutable.Nil
import scala.language.experimental.macros
import scala.reflect.macros.whitebox


/**
 *  Annotation for derived axioms, which allows decentralized AxiomInfo
 *  @param names Display names
 *  @param formula Formula displayed for axioms
 *  @param inputs Display inputs for axiom-with-input
 *  @param codeName used to invoke axiom in tactics
 *  @param unifier  Which unifier to use for axiom: 'linear or 'full
 *  @param displayLevel Where to show the axiom: 'internal, 'browse, 'menu, 'all
 *  @author Brandon Bohrer
 *  */
class DerivedAxiom(val names: Any,
                   val codeName: String = "",
                   val formula: String = "",
                   val unifier: String = "full",
                   val displayLevel: String = "internal",
                   val inputs: String = "",
                   val key: ExprPos = Nil,
                   val recursor: List[ExprPos] = Nil
                  ) extends StaticAnnotation {
  // Annotation is implemented a macro; this is a necessary, reserved magic invocation which says DerivedAxiomAnnotation.impl is the macro body
  def macroTransform(annottees: Any*): Any = macro DerivedAxiom.impl
}

object DerivedAxiom {

  // Would just use PosInExpr but can't pull in core
  type ExprPos = List[Int]
  def impl(c: whitebox.Context)(annottees: c.Expr[Any]*): c.Expr[Any] = {
    import c.universe._
    def toArgInfo(name: String, tpe: String, allowFresh: List[String]): ArgInfo = {
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
    def parseAI(s: String): ArgInfo = {
      s.split(":").toList match {
        case id :: tpe :: Nil =>
          val first = id.indexOf('(')
          val last = id.lastIndexOf(')')
          val (name, allowFresh) =
            if (first != -1 && last != -1)
              (id.slice(0, first), id.slice(first+1, last).split(',').toList)
            else (id, Nil)
          toArgInfo(name, tpe, allowFresh)
        case ss => c.abort(c.enclosingPosition, "Invalid argument type descriptor:" + s)
      }
    }
    def parseAIs(s: String): List[ArgInfo] = {
      if (s.isEmpty) Nil
      else s.split(";;").toList.map(parseAI)
    }
    // Abstract syntax trees for string and string list literals
    def literal(s: String): Tree = Literal(Constant(s))
    def literals(ss: List[String]): Tree = q"""List(..${ss.map((s: String) => literal(s))})"""
    // Abstract syntax trees for all the display info data structures
    def convAIs(ais: List[ArgInfo]): Tree = {
      q"""List(..${ais.map((ai:ArgInfo) => convAI(ai))})"""
    }
    def convAI(ai: ArgInfo): Tree = {
      ai match {
      case VariableArg(name, allowsFresh) => q"""new VariableArg(${literal(name)}, ${literals(allowsFresh)})"""
      case NumberArg(name, allowsFresh) => q"""new NumberArg(${literal(name)}, ${literals(allowsFresh)})"""
      case StringArg(name, allowsFresh) => q"""new StringArg(${literal(name)}, ${literals(allowsFresh)})"""
      case SubstitutionArg(name, allowsFresh) => q"""new SubstitutionArg(${literal(name)}, ${literals(allowsFresh)})"""
      case OptionArg(arg) => q"""new OptionArg(${convAI(arg)})"""
        case FormulaArg(name, allowsFresh) => q"""new FormulaArg(${literal(name)}, ${literals(allowsFresh)})"""
        case ListArg(name, sort, allowsFresh) => q"""new ListArg(${literal(name)}, ${literal(sort)}, ${literals(allowsFresh)})"""
        case ta: TermArg => q"""new TermArg(${literal(ta.name)}, ${literals{ta.allowsFresh}})"""
        case ea: ExpressionArg => q"""new ExpressionArg (${literal(ea.name)}, ${literals(ea.allowsFresh)})"""
      }
    }
    def convSD(sd: SequentDisplay): Tree = {
      val SequentDisplay(ante: List[String], succ: List[String], isClosed: Boolean) = sd
      q"""new SequentDisplay($ante, $succ, $isClosed)"""
    }
    def convDI(di: DisplayInfo): Tree = {
      di match {
        case SimpleDisplayInfo(name, asciiName) => q"""new SimpleDisplayInfo(${literal(name)}, ${literal(asciiName)})"""
        case RuleDisplayInfo(names, conclusion, premises)  =>
          val namesTree = convDI(names)
          val conclusionTree = convSD(conclusion)
          val premiseTrees = premises.map((sd: SequentDisplay) => convSD(sd))
          q"""new RuleDisplayInfo(${namesTree}, ${conclusionTree}, ${premiseTrees})"""
        case AxiomDisplayInfo(names: SimpleDisplayInfo, displayFormula: String) =>
          q"""new AxiomDisplayInfo(${convDI(names)}, ${literal(displayFormula)})"""
        case InputAxiomDisplayInfo(names: SimpleDisplayInfo, displayFormula: String, input: List[ArgInfo]) =>
          q"""new InputAxiomDisplayInfo(${convDI(names)}, ${literal(displayFormula)}, ${convAIs(input)})"""
        }
      }
    def sequentDisplayFromObj(a: Any): SequentDisplay = {
      a match {
        case (ante: List[String], succ: List[String]) => SequentDisplay(ante, succ)
        case sd: SequentDisplay => sd
        case e => c.abort(c.enclosingPosition, "Expected SequentDisplay, got: " + e)
      }
    }
    val paramNames = List("names", "codeName", "formula", "unifier", "displayLevel", "inputs", "key", "recursor")
    def foldParams(acc: (Int, Boolean, Map[String, Tree]), param: Tree): (Int, Boolean, Map[String, Tree]) = {
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

    // Macro library does not allow directly passing arguments from annotation constructor to macro implementation.
    // Searching the prefix allows us to recover the arguments
    def getParams: (String, DisplayInfo, String, String, ExprPos, List[ExprPos]) = {
      // @TODO: What do ASTs look like when option arguments are omitted or passed by name?
      c.prefix.tree match {
        case q"new $annotation(..$params)" =>
          val defaultMap = Map(
            "codeName" -> Literal(Constant("")),
            "formula" -> Literal(Constant("")),
            "unifier" -> Literal(Constant("full")),
            "displayLevel" -> Literal(Constant("internal")),
            "key" -> q"""scala.collection.immutable.Nil""",
            "recursor" -> q"""scala.collection.immutable.Nil""",
            "inputs" -> Literal(Constant(""))
          )
          val (_idx, _wereNamed, paramMap) = params.foldLeft((0, false, defaultMap))({case (acc, x) => foldParams (acc, x)})
          val displayObj = c.eval[Any](c.Expr(paramMap("names")))
          val fml: String = c.eval[String](c.Expr(paramMap("formula")))
          val inputs: List[ArgInfo] = parseAIs(c.eval[String](c.Expr(paramMap("inputs"))))
          val codeName = c.eval[String](c.Expr(paramMap("codeName")))
          val unifier: String = c.eval[String](c.Expr(paramMap("unifier")))
          val displayLevel: String = c.eval[String](c.Expr(paramMap("displayLevel")))
          val key: ExprPos = c.eval[ExprPos](c.Expr(paramMap("key")))
          val recursor: List[ExprPos] = c.eval[List[ExprPos]](c.Expr(paramMap("recursor")))
          val simpleDisplay = displayObj match {
            case s: String => SimpleDisplayInfo(s, s)
            case (sl: String, sr: String) => SimpleDisplayInfo(sl, sr)
            case sdi: SimpleDisplayInfo => sdi
            case di => c.abort(c.enclosingPosition, "@DerivedAxiomAnnotation expected names: String or names: (String, String) or names: SimpleDisplayInfo, got: " + di)
          }
          val displayInfo = (fml, inputs, Nil, None) match {
            case ("", Nil, Nil, None) => simpleDisplay
            case (fml, Nil, Nil, None) if fml != "" => AxiomDisplayInfo(simpleDisplay, fml)
            case (fml, args, Nil, None) if fml != "" => InputAxiomDisplayInfo(simpleDisplay, fml, args)
            //case ("", Nil, premises, Some(conclusion)) => RuleDisplayInfo(simpleDisplay, conclusion, premises)
            case _ => c.abort(c.enclosingPosition, "Unsupported argument combination for @DerivedAxiom: either specify premisses and conclusion, or formula optionally with inputs, not both")
          }
          (codeName, displayInfo, unifier, displayLevel, key, recursor)
        case e => c.abort(c.enclosingPosition, "Excepted @DerivedAxiom(args), got: " + e)
      }
    }
    val (codeNameParam: String, display: DisplayInfo, unifier: String, displayLevel: String, key, recursor) = getParams
    // Annotation can only be attached to library functions for defining new axioms
    def correctName(t: Tree): Boolean = {
      t match {
        case id: Ident => {
          if (Set("derivedAxiom", "derivedFormula", "derivedAxiomFromFact", "derivedFact").contains(id.name.decodedName.toString)) true
          else c.abort(c.enclosingPosition, "Expected function name: one of {derivedAxiom, derivedFormula, derivedAxiomFromFact, derivedFact}, got: " + t + " of type " + t.getClass())
        }
        case t => c.abort(c.enclosingPosition, "Invalid annottee: Expected derivedAxiom string, got: " + t + " of type " + t.getClass())
      }
    }
    def paramCount(t: Tree): (Int, Int) = {
      t match {
        case id: Ident => {
          id.name.decodedName.toString match {
            case "derivedAxiom" | "derivedAxiomFromFact" | "derivedFormula" => (3, 4)
            case "derivedFact" => (2, 3)
            case _ => c.abort(c.enclosingPosition, "Expected function name: one of {derivedAxiom, derivedFormula, derivedAxiomFromFact, derivedFact}, got: " + t + " of type " + t.getClass())
          }
        }
        case t => c.abort(c.enclosingPosition, "Invalid annottee: Expected derivedAxiom string, got: " + t + " of type " + t.getClass())
      }
    }
    annottees map (_.tree) toList match {
      // Annottee must be a val declaration of an axiom
      case (valDecl: ValDef) :: Nil =>
        valDecl match {
          // val declaration must be an invocation of one of the functions for defining derived axioms and optionally can
          // have modifiers and type annotations
          case q"$mods val $declName: $tpt = $functionName( ..$params )" =>
            if (!correctName(functionName))
              c.abort(c.enclosingPosition, "Invalid annottee: Expected val name = <derivedAxiomFunction>(x1, x2, x3), got: " + functionName + " of type " + functionName.getClass())
            val (minParam, maxParam) = paramCount(functionName)
            if(params.length < minParam || params.length > maxParam)
              c.abort(c.enclosingPosition, s"Function $functionName had ${params.length} arguments, needs $minParam-$maxParam")
            // codeName is usually supplied, but can be taken from the bound identifier of the declaration by default
            val codeName = if(codeNameParam.nonEmpty) TermName(codeNameParam) else declName
            val storageName = TermName(codeName.toString.toLowerCase)
            // AST for literal strings for the names
            val codeString = Literal(Constant(codeName.decodedName.toString))
            val storageString = Literal(Constant(storageName.decodedName.toString))
            val canonString = params(0)
            // derivedAxiom functions allow an optional argument for the codeName, which we supply here
            val fullParams = params.take(minParam).:+(q"Some($storageString)")
            val fullRhs = q"$functionName( ..$fullParams)"
            // Tactic implementation of derived axiom is always useAt
            val expr = q"""({case () => edu.cmu.cs.ls.keymaerax.btactics.HilbertCalculus.useAt($canonString)})""" // : (Unit => Any)
            val unif = unifier match {case "full" => 'full case "linear" => 'linear case s => c.abort(c.enclosingPosition, "Unknown unifier " + s)}
            val dispLvl = displayLevel match {case "internal" => 'internal case "browse" => 'browse case "menu" => 'menu case "all" => 'all
              case s => c.abort(c.enclosingPosition, "Unknown display level " + s)}
            val info = q"""DerivedAxiomInfo(canonicalName = $canonString, display = ${convDI(display)}, codeName = $codeString, unifier = $unif, displayLevel = $dispLvl, key = $key, recursor = $recursor, theExpr = $expr)"""
            // Macro cannot introduce new statements or declarations, so introduce a library call which achieves our goal of registering
            // the axiom info to the global axiom info table
            val application = q"edu.cmu.cs.ls.keymaerax.macros.DerivationInfo.register($fullRhs, $info)"
            val lemmaType = tq"edu.cmu.cs.ls.keymaerax.lemma.Lemma"
            c.Expr[Nothing](q"""$mods val $declName: $lemmaType = $application""")
          case q"$mods val $cName: $tpt = $functionName( ..$params )" => c.abort(c.enclosingPosition, "Expected derivedAxiom with 3 parameters, got:" + params.length)

        }
      case t => c.abort(c.enclosingPosition, "Invalid annottee: Expected val declaration got: " + t.head + " of type: " + t.head.getClass())
    }
  }
}