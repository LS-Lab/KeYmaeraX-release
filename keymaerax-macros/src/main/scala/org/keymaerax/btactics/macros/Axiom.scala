/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics.macros

import org.keymaerax.btactics.macros.AnnotationCommon.{
  astForDisplayInfo,
  astForUnifier,
  parseAIs,
  parsePos,
  parsePoses,
  renderDisplayFormula,
}

import scala.annotation.{compileTimeOnly, StaticAnnotation}
import scala.language.experimental.macros
import scala.reflect.macros.whitebox

/**
 * Axiom Annotation for core axioms and derived axioms, which allows decentralized [[AxiomInfo]]. This annotation can
 * only be applied to val declarations whose right-hand-sides are applications of [[derivedAxiom]] or related functions,
 * see [[Ax]] for examples.
 *
 * @param name
 *   Unique identifier for this axiom. Used to invoke the axiom in tactics and for lemma storage. Must only contain the
 *   characters `a-zA-Z0-9_`. It is strongly recommended that this name is identical to the name of the annotated scala
 *   definition.
 * @param displayName
 *   Short name used for the axiom in the user interface. Defaults to [[name]].
 * @param displayNameAscii
 *   ASCII-only version of [[displayName]] that must be specified if [[displayName]] contains characters outside the
 *   printable ASCII range. Defaults to [[displayName]].
 * @param displayNameLong
 *   Descriptive long name used in some menus in the user interface. Should be a short, grammatical English phrase.
 *   Defaults to [[displayName]].
 * @param displayLevel
 *   Where to display an axiom/rule/tactic in the user interface. Defaults to [[DisplayLevelInternal]].
 * @param displayConclusion
 *   Formula string displayed for axioms as html with unicode in the user interface. For axioms with (non-position)
 *   inputs, the conclusion must mention each input. Sequent syntax is optionally supported: `A, B |- C, D`
 * @param unifier
 *   Which unifier to use. See also
 *   [[org.keymaerax.btactics.UnifyUSCalculus#matcherFor(org.keymaerax.btactics.macros.ProvableInfo)]]
 * @param inputs
 *   Display inputs for axiom-with-input as type declarations, e.g., "C:Formula" for cut. Arguments are separated with
 *   ;; and allowed fresh variables are given in square brackets, for example E[y,x,y']:Formula;; P[y]:Formula are the
 *   arguments to tactic dG. Supported types: Expression, Formula, Term, Variable, Number, String, Substitution, List[],
 *   Option[]
 * @param key
 *   The position of the subexpression in this formula that will be unified against when using this axiom. The notation
 *   is as in [[org.keymaerax.infrastruct.PosInExpr]] for
 *   [[org.keymaerax.btactics.UnifyUSCalculus.useAt]]/[[org.keymaerax.btactics.UnifyUSCalculus.useFor]].
 *   - Default key="0" is the left child.
 *   - Root key="" is the full formula.
 *   - key="1" is the right child.
 *   - key="0.1.1" is the right child of the right child of the left child.
 * @param recursor
 *   The ;-separated list of relative subpositions in the resulting formulas that will be chased away next. The notation
 *   is as in [[org.keymaerax.infrastruct.PosInExpr]] for [[org.keymaerax.btactics.UnifyUSCalculus.chase]]. The
 *   resulting subexpressions will be considered in the order of the ;-separated list.
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
    val name: String,
    val displayName: Option[String] = None,
    val displayNameAscii: Option[String] = None,
    val displayNameLong: Option[String] = None,
    val displayLevel: DisplayLevel = DisplayLevelInternal,
    val displayConclusion: String = "",
    val unifier: Unifier = UnifierFull,
    val inputs: String = "",
    val key: String = "0",
    val recursor: String = "",
) extends StaticAnnotation {
  // Magic incantation, see https://docs.scala-lang.org/overviews/macros/annotations.html
  def macroTransform(annottees: Any*): Any = macro AxiomMacro.impl
}

/** Helper class for easy annotation argument parsing. Must stay in sync with [[Axiom]]! */
case class AxiomArgs(
    name: String,
    displayName: Option[String] = None,
    displayNameAscii: Option[String] = None,
    displayNameLong: Option[String] = None,
    displayLevel: DisplayLevel = DisplayLevelInternal,
    displayConclusion: String = "",
    unifier: Unifier = UnifierFull,
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
      case q"new $_(..$args)" => c.eval(c.Expr[AxiomArgs](
          q"""{
            import org.keymaerax.btactics.macros.{
              DisplayLevel,
              DisplayLevelInternal,
              DisplayLevelBrowse,
              DisplayLevelMenu,
              DisplayLevelAll,
            };
            import org.keymaerax.btactics.macros.{
              Unifier,
              UnifierFull,
              UnifierLinear,
              UnifierSurjective,
              UnifierSurjectiveLinear,
              UnifierSurjectiveLinearPretend,
            };
            org.keymaerax.btactics.macros.AxiomArgs(..$args)
          }"""
        ))
      case _ => c.abort(c.enclosingPosition, "this should never happen")
    }

    /*
     * Deconstruct syntax tree and check for consistency
     */

    // Annotation must be applied to the val definition of an axiom.
    val valDef = annottees.map(_.tree).toList match {
      case List(valDef: ValDef) => valDef
      case _ => c.abort(c.enclosingPosition, "@Axiom must be applied to val definition")
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
     * Compute different names
     */

    val name = AnnotationCommon.getName(args.name)(c)
    val displayName = AnnotationCommon.getDisplayName(args.displayName, name)(c)
    val displayNameAscii = AnnotationCommon.getDisplayNameAscii(args.displayNameAscii, displayName)(c)
    val displayNameLong = AnnotationCommon.getDisplayNameLong(args.displayNameLong, displayName)(c)

    val storageName = name.toLowerCase
    val canonicalName = tParams.head.asInstanceOf[Literal].value.value.asInstanceOf[String]

    /*
     * Parse annotation arguments
     */

    val inputs: List[ArgInfo] = parseAIs(args.inputs)(c)
    val key = parsePos(args.key)(c)
    val recursor = parsePoses(args.recursor)(c)

    val display: DisplayInfo = (args.displayConclusion, inputs) match {
      case ("", Nil) => SimpleDisplayInfo(
          name = displayName,
          nameAscii = displayNameAscii,
          nameLong = displayNameLong,
          level = args.displayLevel,
        )

      case ("", _) => c.abort(c.enclosingPosition, "@Axiom with inputs must have a conclusion")

      case (fml, Nil) => AxiomDisplayInfo(
          name = displayName,
          nameAscii = displayNameAscii,
          nameLong = displayNameLong,
          level = args.displayLevel,
          formula = renderDisplayFormula(fml),
        )

      case (fml, input) => InputAxiomDisplayInfo(
          name = displayName,
          nameAscii = displayNameAscii,
          nameLong = displayNameLong,
          level = args.displayLevel,
          formula = fml,
          input = input,
        )
    }

    /*
     * Build AST
     */

    // The derived* functions allow an optional argument for the codeName, which we supply here.
    val fullParams = if (isCore) tParams else tParams.take(minParam) :+ q"Some($storageName)"
    val fullRhs = q"$tFunctionName( ..$fullParams)"

    // Tactic implementation of derived axiom is always useAt
    val expr = q"""
      ({ case () =>
        org.keymaerax.btactics.UnifyUSCalculus.useAt(ProvableInfo($canonicalName))
      })
    """ // : (Unit => Any)

    val (infoType, info) =
      if (isCore) (
        tq"org.keymaerax.btactics.macros.CoreAxiomInfo",
        q"""CoreAxiomInfo(
          canonicalName = $canonicalName,
          display = ${astForDisplayInfo(display)(c)},
          codeName = $name,
          unifier = ${astForUnifier(args.unifier)(c)},
          theKey = $key,
          theRecursor = $recursor,
          theExpr = $expr,
        )""",
      )
      else (
        tq"org.keymaerax.btactics.macros.DerivedAxiomInfo",
        q"""DerivedAxiomInfo(
          canonicalName = $canonicalName,
          display = ${astForDisplayInfo(display)(c)},
          codeName = $name,
          unifier = ${astForUnifier(args.unifier)(c)},
          theKey = $key,
          theRecursor = $recursor,
          theExpr = $expr,
        )""",
      )

    // Macro cannot introduce new statements or declarations, so introduce a library call which achieves our goal of
    // registering the axiom info to the global axiom info table.
    val result = q"""
      $tMods val $tDeclName: $infoType =
        org.keymaerax.btactics.macros.DerivationInfo.registerR($fullRhs, $info)
    """

    c.Expr[Nothing](result)
  }
}
