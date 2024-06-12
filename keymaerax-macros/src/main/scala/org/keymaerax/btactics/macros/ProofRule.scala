/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics.macros

import org.keymaerax.btactics.macros.AnnotationCommon.{astForDisplayInfo, astForUnifier, parsePos, parsePoses}

import scala.annotation.{compileTimeOnly, StaticAnnotation}
import scala.language.experimental.macros
import scala.reflect.macros.whitebox

/**
 * Annotation for core or derived axiomatic rules, which allows decentralized [[AxiomaticRuleInfo]]. This annotation can
 * only be applied to val declarations whose right-hand-sides are applications of [[derivedRule]] or related functions,
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
 * @param displayPremises
 *   String of premises when (if) the rule is displayed on the UI. Rules with premises must have conclusions. Premises
 *   are separated by `;;` and each premise is optionally a sequent. `P;; A, B |- C` specifies two premises, the latter
 *   of which is a sequent with two assumptions. An asterisk `*` indicates a rule that closes a branch.
 * @param displayConclusion
 *   Conclusion of rule displayed on UI. Sequent syntax is optionally supported: `A, B |- C, D`
 * @param unifier
 *   Which unifier to use. See also
 *   [[org.keymaerax.btactics.UnifyUSCalculus#matcherFor(org.keymaerax.btactics.macros.ProvableInfo)]]
 * @author
 *   Brandon Bohrer
 * @see
 *   [[TacticInfo]]
 */
@compileTimeOnly("enable -Ymacro-annotations")
class ProofRule(
    val name: String,
    val displayName: Option[String] = None,
    val displayNameAscii: Option[String] = None,
    val displayNameLong: Option[String] = None,
    val displayLevel: DisplayLevel = DisplayLevelInternal,
    val displayPremises: String = "",
    val displayConclusion: String = "",
    val unifier: Unifier = UnifierFull,
    val key: String = "",
    val recursor: String = "*",
) extends StaticAnnotation {
  // Magic incantation, see https://docs.scala-lang.org/overviews/macros/annotations.html
  def macroTransform(annottees: Any*): Any = macro ProofRuleMacro.impl
}

/** Helper class for easy annotation argument parsing. Must stay in sync with [[ProofRule]]! */
case class ProofRuleArgs(
    name: String,
    displayName: Option[String] = None,
    displayNameAscii: Option[String] = None,
    displayNameLong: Option[String] = None,
    displayLevel: DisplayLevel = DisplayLevelInternal,
    displayPremises: String = "",
    displayConclusion: String = "",
    unifier: Unifier = UnifierFull,
    key: String = "",
    recursor: String = "*",
)

object ProofRuleMacro {

  /** Functions that can be used with `@Axiom` and their corresponding min and max parameter counts. */
  private val ALLOWED_FUNCTIONS_AND_ARGUMENTS: Map[String, (Int, Int)] =
    Map("coreRule" -> (1, 1), "derivedRule" -> (2, 3), "derivedRuleSequent" -> (3, 4))

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
      case q"new $_(..$args)" => c.eval(c.Expr[ProofRuleArgs](
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
            org.keymaerax.btactics.macros.ProofRuleArgs(..$args)
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
      case _ => c.abort(c.enclosingPosition, "@ProofRule must be applied to val definition")
    }

    // The val definition must be an invocation of one of the functions for defining proof rules.
    // It may optionally have modifiers and type annotations.
    val (tMods, tDeclName: TermName, tFunctionName: Tree, tParams) = valDef match {
      case q"$mods val $declName: $_ = $functionName(..$params)" => (mods, declName, functionName, params)
      case _ => c.abort(valDef.pos, "@ProofRule must be applied to val definition")
    }

    // Annotation can only be attached to known library functions for defining new axioms.
    val functionName = tFunctionName match {
      case id: Ident => id.name.decodedName.toString
      case t: Tree => c.abort(t.pos, s"@ProofRule definition must use one of $ALLOWED_FUNCTION_NAMES_STR")
    }
    val (minParam, maxParam) = ALLOWED_FUNCTIONS_AND_ARGUMENTS.get(functionName) match {
      case Some(params) => params
      case None => c.abort(tFunctionName.pos, s"@ProofRule definition must use one of $ALLOWED_FUNCTION_NAMES_STR")
    }
    if (tParams.length < minParam || tParams.length > maxParam) {
      c.abort(tFunctionName.pos, s"@ProofRule requires function to have $minParam to $maxParam arguments")
    }
    val isCore = functionName == "coreRule"

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

    val premises = DisplaySequent.parseMany(args.displayPremises)
    val conclusionOpt = Some(args.displayConclusion).filter(_.nonEmpty).map(DisplaySequent.parse)
    val key = parsePos(args.key)(c)
    val recursor = parsePoses(args.recursor)(c)

    val display = (premises, conclusionOpt) match {
      case (Nil, None) => SimpleDisplayInfo(
          name = displayName,
          nameAscii = displayNameAscii,
          nameLong = displayNameLong,
          level = args.displayLevel,
        )

      case (prem, Some(conc)) => RuleDisplayInfo(
          name = displayName,
          nameAscii = displayNameAscii,
          nameLong = displayNameLong,
          level = args.displayLevel,
          conclusion = conc,
          premises = prem,
          inputGenerator = None,
        )

      case _ => c.abort(c.enclosingPosition, "@ProofRule with premises must have a conclusion")
    }

    /*
     * Build AST
     */

    // The derived* functions allow an optional argument for the codeName, which we supply here.
    val fullParams = if (isCore) tParams else tParams.take(minParam).:+(q"Some($storageName)")
    val fullRhs = q"$tFunctionName( ..$fullParams)"

    // Tactic implementation of derived rule is always useAt
    val expr = q"""
      ({ case () =>
        org.keymaerax.btactics.UnifyUSCalculus.useAt(ProvableInfo($canonicalName))
      })
    """ // : (Unit => Any)

    val (infoType, info) =
      if (isCore) (
        tq"org.keymaerax.btactics.macros.AxiomaticRuleInfo",
        q"""AxiomaticRuleInfo(
          canonicalName = $canonicalName,
          display = ${astForDisplayInfo(display)(c)},
          codeName = $name,
          unifier = ${astForUnifier(args.unifier)(c)},
          theExpr = $expr,
          theKey = $key,
          theRecursor = $recursor,
        )""",
      )
      else (
        tq"org.keymaerax.btactics.macros.DerivedRuleInfo",
        q"""DerivedRuleInfo(
          canonicalName = $canonicalName,
          display = ${astForDisplayInfo(display)(c)},
          codeName = $name,
          unifier = ${astForUnifier(args.unifier)(c)},
          theExpr = $expr,
          theKey = $key,
          theRecursor = $recursor,
        )""",
      )

    // Macro cannot introduce new statements or declarations, so introduce a library call which achieves our goal of
    // registering the proof rule info to the global proof rule info table.
    val result = q"""
      $tMods val $tDeclName: $infoType =
        org.keymaerax.btactics.macros.DerivationInfo.registerR($fullRhs, $info)
    """

    c.Expr[Nothing](result)
  }
}
