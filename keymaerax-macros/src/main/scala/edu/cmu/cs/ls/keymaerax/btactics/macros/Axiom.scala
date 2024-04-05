/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics.macros

import edu.cmu.cs.ls.keymaerax.btactics.macros.AnnotationCommon.{convDI, parseAIs, parsePos, parsePoses}

import scala.annotation.{compileTimeOnly, StaticAnnotation}
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
@compileTimeOnly("enable -Ymacro-annotations")
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
  // Magic incantation, see https://docs.scala-lang.org/overviews/macros/annotations.html
  def macroTransform(annottees: Any*): Any = macro AxiomMacro.impl
}

/** Helper class for easy annotation argument parsing. Must stay in sync with [[Axiom]]! */
case class AxiomArgs(
    names: Any,
    codeName: String = "",
    longDisplayName: String = "",
    conclusion: String = "",
    unifier: String = "full",
    displayLevel: String = "internal",
    inputs: String = "",
    key: String = "0",
    recursor: String = "",
)

object AxiomMacro {

  /** Functions that can be used with `@Axiom` and their corresponding min and max parameter counts. */
  private val ALLOWED_FUNCTIONS_AND_ARGUMENTS: Map[String, (Int, Int)] = Map(
    "coreAxiom" -> (1, 1),
    "derivedAxiom" -> (3, 4),
    "derivedAxiomFromFact" -> (3, 4),
    "derivedFormula" -> (3, 4),
    "derivedFact" -> (2, 3),
  )

  private val ALLOWED_FUNCTION_NAMES_STR: String = ALLOWED_FUNCTIONS_AND_ARGUMENTS.keys.toList.sorted.mkString(", ")

  def impl(c: whitebox.Context)(annottees: c.Expr[Any]*): c.Expr[Any] = {
    import c.universe._

    /*
     * Obtain annotation arguments
     */

    // While this is quite a bit slower than the previous code, it is also a lot simpler and more type safe.
    // https://stackoverflow.com/questions/32631372/getting-parameters-from-scala-macro-annotation
    // https://stackoverflow.com/questions/37891855/macro-annotation-with-default-arguments
    val args = c.prefix.tree match {
      case q"new $_(..$args)" =>
        c.eval(c.Expr[AxiomArgs](q"edu.cmu.cs.ls.keymaerax.btactics.macros.AxiomArgs(..$args)"))
      case q"new $_()" => c.eval(c.Expr[AxiomArgs](q"edu.cmu.cs.ls.keymaerax.btactics.macros.AxiomArgs()"))
      case _ => c.abort(c.enclosingPosition, "this should never happen")
    }

    /*
     * Deconstruct syntax tree and check for consistency
     */

    // Annotation must be applied to the val definition of an axiom.
    val valDef = annottees.map(_.tree).toList match {
      case List(valDef: ValDef) => valDef
      case t: Tree => c.abort(t.pos, "@Axiom must be applied to val definition")
    }

    // The val definition must be an invocation of one of the functions for defining derived axioms.
    // It may optionally have modifiers and type annotations.
    val (tMods, tDeclName: TermName, tFunctionName: Tree, tParams) = valDef match {
      case q"$mods val $declName: $_ = $functionName(..$params)" => (mods, declName, functionName, params)
      case _ => c.abort(valDef.pos, "@Axiom must be applied to val definition")
    }

    // Annotation can only be attached to known library functions for defining new axioms.
    val functionName = tFunctionName match {
      case id: Ident => id.name.decodedName.toString
      case t: Tree => c.abort(t.pos, s"@Axiom definition must use one of $ALLOWED_FUNCTION_NAMES_STR")
    }
    val (minParam, maxParam) = ALLOWED_FUNCTIONS_AND_ARGUMENTS.get(functionName) match {
      case Some(params) => params
      case None => c.abort(tFunctionName.pos, s"@Axiom definition must use one of $ALLOWED_FUNCTION_NAMES_STR")
    }
    if (tParams.length < minParam || tParams.length > maxParam) {
      c.abort(tFunctionName.pos, s"@Axiom requires function to have $minParam to $maxParam arguments")
    }
    val isCore = functionName == "coreAxiom"

    /*
     * Parse annotation arguments
     */

    val inputs: List[ArgInfo] = parseAIs(args.inputs)(c)
    val key = parsePos(args.key)(c)
    val recursor = parsePoses(args.recursor)(c)

    val simpleDisplay = args.names match {
      case (sl: String, sr: String) => SimpleDisplayInfo(sl, sr)
      case s: String => SimpleDisplayInfo(s, s)
      case _ => c.abort(c.enclosingPosition, "@Axiom names must be String or (String, String)")
    }

    val display: DisplayInfo = (args.conclusion, inputs) match {
      case ("", Nil) => simpleDisplay
      case ("", _) => c.abort(c.enclosingPosition, "@Axiom with inputs must have a conclusion")
      case (fml, Nil) => AxiomDisplayInfo.render(simpleDisplay, fml)
      case (fml, args) => InputAxiomDisplayInfo(simpleDisplay, fml, args)
    }

    /*
     * Compute different names
     */

    // If the codeName is not specified, it is taken from the declaration name.
    val codeName = if (args.codeName.nonEmpty) args.codeName else tDeclName.decodedName.toString
    if (codeName.contains('"')) c.abort(c.enclosingPosition, s"Code name $codeName must not contain escape characters")

    val longDisplayName =
      if (args.longDisplayName.nonEmpty) args.longDisplayName
      else if (display.name.nonEmpty) display.name
      else if (display.asciiName.nonEmpty) display.asciiName
      else codeName

    val storageName = codeName.toLowerCase

    val canonicalName = tParams.head.asInstanceOf[Literal].value.value.asInstanceOf[String]

    /*
     * Build AST
     */

    // The derived* functions allow an optional argument for the codeName, which we supply here.
    val fullParams = if (isCore) tParams else tParams.take(minParam) :+ q"Some($storageName)"
    val fullRhs = q"$tFunctionName( ..$fullParams)"

    // Tactic implementation of derived axiom is always useAt
    val expr = q"""
      ({ case () =>
        edu.cmu.cs.ls.keymaerax.btactics.UnifyUSCalculus.useAt(ProvableInfo($canonicalName))
      })
    """ // : (Unit => Any)

    val unifier = args.unifier match {
      case "surjective" => Symbol("surjective")
      case "surjlinear" => Symbol("surlinear")
      case "full" => Symbol("full")
      case "linear" => Symbol("linear")
      case "surjlinearpretend" => Symbol("surlinearpretend")
      case s => c.abort(c.enclosingPosition, "Unknown unifier " + s)
    }

    val displayLevel = args.displayLevel match {
      case "internal" => Symbol("internal")
      case "browse" => Symbol("browse")
      case "menu" => Symbol("menu")
      case "all" => Symbol("all")
      case s => c.abort(c.enclosingPosition, "Unknown display level " + s)
    }

    val (infoType, info) =
      if (isCore) (
        tq"edu.cmu.cs.ls.keymaerax.btactics.macros.CoreAxiomInfo",
        q"""CoreAxiomInfo(
          canonicalName = $canonicalName,
          display = ${convDI(display)(c)},
          codeName = $codeName,
          longDisplayName = $longDisplayName,
          unifier = $unifier,
          displayLevel = $displayLevel,
          theKey = $key,
          theRecursor = $recursor,
          theExpr = $expr,
        )""",
      )
      else (
        tq"edu.cmu.cs.ls.keymaerax.btactics.macros.DerivedAxiomInfo",
        q"""DerivedAxiomInfo(
          canonicalName = $canonicalName,
          display = ${convDI(display)(c)},
          codeName = $codeName,
          longDisplayName = $longDisplayName,
          unifier = $unifier,
          displayLevel = $displayLevel,
          theKey = $key,
          theRecursor = $recursor,
          theExpr = $expr,
        )""",
      )

    // Macro cannot introduce new statements or declarations, so introduce a library call which achieves our goal of
    // registering the axiom info to the global axiom info table.
    val result = q"""
      $tMods val $tDeclName: $infoType =
        edu.cmu.cs.ls.keymaerax.btactics.macros.DerivationInfo.registerR($fullRhs, $info)
    """

    c.Expr[Nothing](result)
  }
}
