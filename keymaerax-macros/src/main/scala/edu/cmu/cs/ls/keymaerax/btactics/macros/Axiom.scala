/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics.macros

import edu.cmu.cs.ls.keymaerax.btactics.macros.AnnotationCommon.{
  convDI,
  foldParams,
  parseAIs,
  parsePos,
  parsePoses,
  ExprPos,
}

import scala.annotation.StaticAnnotation
import scala.language.experimental.macros
import scala.reflect.macros.whitebox

/**
 * Axiom Annotation for core axioms and derived axioms, which allows decentralized [[AxiomInfo]]. This annotation can
 * only be applied to val declarations whose right-hand-sides are applications of [[derivedAxiom]] or related functions,
 * see [[Ax]] for examples.
 * @param names
 *   Display names to render in the user interface. If two names are given, the first is Unicode and the second ASCII.
 *   If one ASCII name is given, it is also used as the Unicode name. Unicode names are useful for display to end users,
 *   ASCII names appear to be better-supported in error messages. Optional, defaults to `codeName`
 * @param codeName
 *   You usually don't need to specify this argument, especially for axioms. Permanent unique code name used to invoke
 *   this axiom in tactics as a string and for Lemma storage. `codeName` will be inferred from the val that is annotated
 *   by this `@Axiom` and is usually recommended to be identical to it. The exception is when you wish to have different
 *   arguments in the parsed Bellerophon language than does your implementation. In this case it is conventional to
 *   write a declaration `val <name>X = <name>(...)` with codeName `<name>` which converts arguments as needed.
 * @param longDisplayName
 *   Descriptive name used in longer menus. Should be a short, grammatical English phrase. Optional, defaults to Unicode
 *   name
 * @param conclusion
 *   Formula string displayed for axioms as html with unicode in the user interface. For axioms with (non-position)
 *   inputs, the conclusion must mention each input. Sequent syntax is optionally supported: `A, B |- C, D`
 * @param unifier
 *   Which unifier to use for axiom: `"surjective"` or `"linear"` or `"surjlinear"` or `"surjlinearpretend"` or
 *   `"full"`.
 *   [[edu.cmu.cs.ls.keymaerax.btactics.UnifyUSCalculus#matcherFor(edu.cmu.cs.ls.keymaerax.btactics.macros.ProvableInfo)]]
 * @param displayLevel
 *   Where to show the axiom: "internal" (not on UI at all), "browse", "menu", "all" (on UI everywhere)
 * @param inputs
 *   Display inputs for axiom-with-input as type declarations, e.g., "C:Formula" for cut. Arguments are separated with
 *   ;; and allowed fresh variables are given in square brackets, for example E[y,x,y']:Formula;; P[y]:Formula are the
 *   arguments to tactic dG. Supported types: Expression, Formula, Term, Variable, Number, String, Substitution, List[],
 *   Option[]
 * @param key
 *   The position of the subexpression in this formula that will be unified against when using this axiom. The notation
 *   is as in [[edu.cmu.cs.ls.keymaerax.infrastruct.PosInExpr]] for
 *   [[edu.cmu.cs.ls.keymaerax.btactics.UnifyUSCalculus.useAt]]/[[edu.cmu.cs.ls.keymaerax.btactics.UnifyUSCalculus.useFor]].
 *   - Default key="0" is the left child.
 *   - Root key="" is the full formula.
 *   - key="1" is the right child.
 *   - key="0.1.1" is the right child of the right child of the left child.
 * @param recursor
 *   The ;-separated list of relative subpositions in the resulting formulas that will be chased away next. The notation
 *   is as in [[edu.cmu.cs.ls.keymaerax.infrastruct.PosInExpr]] for
 *   [[edu.cmu.cs.ls.keymaerax.btactics.UnifyUSCalculus.chase]]. The resulting subexpressions will be considered in the
 *   order of the ;-separated list.
 *   - Default `recursor=""` means no recursion so stop chasing.
 *   - `recursor="*"` considers the full resulting formula.
 *   - `recursor="0;1"` first considers the left child then the right child.
 *   - `recursor="1;*"` first considers the right child then the whole subformula.
 *   - `recursor="1"` only considers the right child.
 *   - `recursor="0.0;1.1"` first considers the left child of the left child, then the right child of the right child.
 *   - `recursor="0.1.1;0.1;*"` first considers the right child of the right child of the left child, then the right
 *     child of the left child, then the whole formula.
 * @author
 *   Brandon Bohrer
 * @see
 *   [[AxiomInfo]]
 */
class Axiom(
    val names: Any,
    val codeName: String = "",
    val longDisplayName: String = "",
    val conclusion: String = "",
    val unifier: String = "full",
    val displayLevel: String = "internal",
    val inputs: String = "",
    val key: String = "0",
    val recursor: String = "",
) extends StaticAnnotation {
  // Annotation is implemented a macro; this is a necessary, reserved magic invocation which says DerivedAxiomAnnotation.impl is the macro body
  def macroTransform(annottees: Any*): Any = macro AxiomImpl.apply
}

class AxiomImpl(val c: whitebox.Context) {
  import c.universe._
  // Would just use PosInExpr but can't pull in core
  def apply(annottees: c.Expr[Any]*): c.Expr[Any] = {
    val paramNames =
      List("names", "codeName", "longDisplayName", "conclusion", "unifier", "displayLevel", "inputs", "key", "recursor")
    def getLiteral(t: Tree): String = {
      t match {
        case Literal(Constant(s: String)) => s
        case t => c.abort(c.enclosingPosition, "Expected string literal, got: " + t)
      }
    }
    // Macro library does not allow directly passing arguments from annotation constructor to macro implementation.
    // Searching the prefix allows us to recover the arguments
    def getParams: (String, String, DisplayInfo, String, String, ExprPos, List[ExprPos]) = {
      c.prefix.tree match {
        case q"new $annotation(..$params)" =>
          val defaultMap: Map[String, Tree] = Map(
            "codeName" -> Literal(Constant("")),
            "longDisplayName" -> Literal(Constant("")),
            "conclusion" -> Literal(Constant("")),
            "unifier" -> Literal(Constant("full")),
            "displayLevel" -> Literal(Constant("internal")),
            "key" -> Literal(Constant("0")),
            "recursor" -> Literal(Constant("")),
            "inputs" -> Literal(Constant("")),
          )
          val (_idx, _wereNamed, paramMap) = params.foldLeft((0, false, defaultMap))({ case (acc, x) =>
            foldParams(c, paramNames)(acc, x)
          })
          val simpleDisplay = paramMap("names") match {
            case q"""(${Literal(Constant(sl: String))}, ${Literal(Constant(sr: String))})""" =>
              SimpleDisplayInfo(sl, sr)
            case Literal(Constant(s: String)) => SimpleDisplayInfo(s, s)
            // case sdi: SimpleDisplayInfo => sdi
            case di => c.abort(
                c.enclosingPosition,
                "@Axiom expected names: String or names: (String, String) or names: SimpleDisplayInfo, got: " + di,
              )
          }
          val (concl, inputString, codeName, longDisplayName, unifier, displayLevel, keyString, recursorString) = (
            getLiteral(paramMap("conclusion")),
            getLiteral(paramMap("inputs")),
            getLiteral(paramMap("codeName")),
            getLiteral(paramMap("longDisplayName")),
            getLiteral(paramMap("unifier")),
            getLiteral(paramMap("displayLevel")),
            getLiteral(paramMap("key")),
            getLiteral(paramMap("recursor")),
          )
          val inputs: List[ArgInfo] = parseAIs(inputString)(c)
          val key = parsePos(keyString)(c)
          val recursor = parsePoses(recursorString)(c)
          val displayInfo = (concl, inputs) match {
            case ("", Nil) => simpleDisplay
            case (fml, Nil) if fml != "" => AxiomDisplayInfo.render(simpleDisplay, fml)
            case (fml, args) if fml != "" => InputAxiomDisplayInfo(simpleDisplay, fml, args)
            // case ("", Nil, premises, Some(conclusion)) => RuleDisplayInfo(simpleDisplay, conclusion, premises)
            case _ => c.abort(
                c.enclosingPosition,
                "Unsupported argument combination for @Axiom: axioms with inputs must have conclusion specified",
              )
          }
          (codeName, longDisplayName, displayInfo, unifier, displayLevel, key, recursor)
        case e => c.abort(c.enclosingPosition, "Excepted @Axiom(args), got: " + e)
      }
    }
    val (
      codeNameParam: String,
      longDisplayNameParam: String,
      display: DisplayInfo,
      unifier: String,
      displayLevel: String,
      key,
      recursor,
    ) = getParams
    // Annotation can only be attached to library functions for defining new axioms
    def correctName(t: c.universe.Tree): Boolean = {
      t match {
        case id: Ident => {
          if (
            Set("coreAxiom", "derivedAxiom", "derivedFormula", "derivedAxiomFromFact", "derivedFact")
              .contains(id.name.decodedName.toString)
          ) true
          else c.abort(
            c.enclosingPosition,
            "Expected function name: one of {coreAxiom, derivedAxiom, derivedFormula, derivedAxiomFromFact, derivedFact}, got: " +
              t + " of type " + t.getClass(),
          )
        }
        case t => c.abort(
            c.enclosingPosition,
            "Invalid annottee: Expected axiom function, got: " + t + " of type " + t.getClass(),
          )
      }
    }
    def paramCount(t: c.universe.Tree): (Int, Int) = {
      t match {
        case id: Ident => {
          id.name.decodedName.toString match {
            case "coreAxiom" => (1, 1)
            case "derivedAxiom" | "derivedAxiomFromFact" | "derivedFormula" => (3, 4)
            case "derivedFact" => (2, 3)
            case _ => c.abort(
                c.enclosingPosition,
                "Expected function name: one of {coreAxiom, derivedAxiom, derivedFormula, derivedAxiomFromFact, derivedFact}, got: " +
                  t + " of type " + t.getClass(),
              )
          }
        }
        case t => c.abort(
            c.enclosingPosition,
            "Invalid annottee: Expected derivedAxiom string, got: " + t + " of type " + t.getClass(),
          )
      }
    }
    annottees.map(_.tree).toList match {
      // Annottee must be a val declaration of an axiom
      case (valDecl: ValDef) :: Nil => valDecl match {
          // val declaration must be an invocation of one of the functions for defining derived axioms and optionally can
          // have modifiers and type annotations
          case q"$mods val $declName: $tpt = $functionName( ..$params )" =>
            if (!correctName(functionName)) c.abort(
              c.enclosingPosition,
              "Invalid annottee: Expected val name = <derivedAxiomFunction>(x1, x2, x3), got: " + functionName +
                " of type " + functionName.getClass(),
            )
            val (minParam, maxParam) = paramCount(functionName)
            val isCore = (minParam == maxParam)
            if (params.length < minParam || params.length > maxParam) c.abort(
              c.enclosingPosition,
              s"Function $functionName had ${params.length} arguments, needs $minParam-$maxParam",
            )
            // codeName is usually supplied, but can be taken from the bound identifier of the declaration by default
            val codeName = if (codeNameParam.nonEmpty) TermName(codeNameParam) else declName
            if (codeName.toString.exists(c => c == '\"')) c
              .abort(c.enclosingPosition, "Identifier " + codeName + " must not contain escape characters")
            // display name defaults to ascii name if not provided
            val longDisplayName = Literal(Constant(
              if (longDisplayNameParam.nonEmpty) longDisplayNameParam
              else if (display.name.nonEmpty) display.name
              else codeName.decodedName.toString
            ))
            val storageName = TermName(codeName.toString.toLowerCase)
            // AST for literal strings for the names
            val codeString = Literal(Constant(codeName.decodedName.toString))
            val storageString = Literal(Constant(storageName.decodedName.toString))
            val canonString = params(0)
            // derivedAxiom functions allow an optional argument for the codeName, which we supply here
            val fullParams = if (isCore) params else params.take(minParam).:+(q"Some($storageString)")
            val fullRhs = q"$functionName( ..$fullParams)"
            // Tactic implementation of derived axiom is always useAt
            val expr =
              q"""({case () => edu.cmu.cs.ls.keymaerax.btactics.UnifyUSCalculus.useAt(ProvableInfo($canonString))})""" // : (Unit => Any)
            val unif = unifier match {
              case "surjective" => Symbol("surjective")
              case "surjlinear" => Symbol("surlinear")
              case "full" => Symbol("full")
              case "linear" => Symbol("linear")
              case "surjlinearpretend" => Symbol("surlinearpretend")
              case s => c.abort(c.enclosingPosition, "Unknown unifier " + s)
            }
            val dispLvl = displayLevel match {
              case "internal" => Symbol("internal")
              case "browse" => Symbol("browse")
              case "menu" => Symbol("menu")
              case "all" => Symbol("all")
              case s => c.abort(c.enclosingPosition, "Unknown display level " + s)
            }
            val info =
              if (isCore) q"""CoreAxiomInfo(canonicalName = $canonString, display = ${convDI(display)(
                  c
                )}, codeName = $codeString, longDisplayName = $longDisplayName, unifier = $unif, displayLevel = $dispLvl, theKey = $key, theRecursor = $recursor, theExpr = $expr)"""
              else q"""DerivedAxiomInfo(canonicalName = $canonString, display = ${convDI(display)(
                  c
                )}, codeName = $codeString, longDisplayName = $longDisplayName, unifier = $unif, displayLevel = $dispLvl, theKey = $key, theRecursor = $recursor, theExpr = $expr)"""
            // Macro cannot introduce new statements or declarations, so introduce a library call which achieves our goal of registering
            // the axiom info to the global axiom info table
            val application = q"edu.cmu.cs.ls.keymaerax.btactics.macros.DerivationInfo.registerR($fullRhs, $info)"
            val lemmaType =
              if (isCore) { tq"edu.cmu.cs.ls.keymaerax.btactics.macros.CoreAxiomInfo" }
              else { tq"edu.cmu.cs.ls.keymaerax.btactics.macros.DerivedAxiomInfo" }
            c.Expr[Nothing](q"""$mods val $declName: $lemmaType = $application""")
          case q"$mods val $cName: $tpt = $functionName( ..$params )" =>
            c.abort(c.enclosingPosition, "Expected derivedAxiom with 3 parameters, got:" + params.length)

        }
      case t => c.abort(
          c.enclosingPosition,
          "Invalid annottee: Expected val declaration got: " + t.head + " of type: " + t.head.getClass(),
        )
    }
  }
}
