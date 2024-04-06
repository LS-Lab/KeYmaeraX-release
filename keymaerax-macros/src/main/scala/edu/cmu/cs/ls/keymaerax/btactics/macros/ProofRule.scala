/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics.macros

import edu.cmu.cs.ls.keymaerax.btactics.macros.AnnotationCommon.{
  convDI,
  parsePos,
  parsePoses,
  parseSequent,
  parseSequents,
}

import scala.annotation.{compileTimeOnly, StaticAnnotation}
import scala.language.experimental.macros
import scala.reflect.macros.whitebox

/**
 * Annotation for core or derived axiomatic rules, which allows decentralized [[AxiomaticRuleInfo]]. This annotation can
 * only be applied to val declarations whose right-hand-sides are applications of [[derivedRule]] or related functions,
 * see [[Ax]] for examples.
 *
 * @param names
 *   Display names to display in user interface. If two names are given, the first is Unicode and the second ASCII. If
 *   one ASCII name is given, it is also used as the Unicode name. Unicode names are useful for display to end users,
 *   ASCII names appear to be better-supported in error messages. Optional, defaults to codeName
 * @param codeName
 *   You almost never need to specify this argument (for proof rules, as opposed to tactics). Permanent unique code name
 *   used to invoke this axiom in tactics as a string and for Lemma storage. `codeName` will be inferred from the val
 *   that is annotated by this `@ProofRule` and is strongly recommended to be identical to it.
 * @param longDisplayName
 *   Descriptive name used in longer menus. Should be a short, grammatical English phrase. Optional, defaults to ASCII
 *   display name
 * @param premises
 *   String of premises when (if) the rule is displayed on the UI. Rules with premises must have conclusions. Premises
 *   are separated by `;;` and each premise is optionally a sequent. `P;; A, B |- C` specifies two premises, the latter
 *   of which is a sequent with two assumptions. An asterisk `*` indicates a rule that closes a branch.
 * @param conclusion
 *   Conclusion of rule displayed on UI. The name of each input is given in [[inputs]], which may be generated from the
 *   [[def]]. Sequent syntax is optionally supported: `A, B |- C, D`
 * @param displayLevel
 *   Where to show the axiom: "internal" (not on UI at all), "browse", "menu", "all" (on UI everywhere)
 * @author
 *   Brandon Bohrer
 * @see
 *   [[TacticInfo]]
 */
@compileTimeOnly("enable -Ymacro-annotations")
class ProofRule(
    val names: Any = false, /* false is a sigil value, user value should be string, strings, or displayinfo*/
    val codeName: String = "",
    val longDisplayName: String = "",
    val premises: String = "",
    val conclusion: String = "",
    val unifier: String = "full",
    val displayLevel: String = "internal",
    val key: String = "",
    val recursor: String = "*",
) extends StaticAnnotation {
  // Magic incantation, see https://docs.scala-lang.org/overviews/macros/annotations.html
  def macroTransform(annottees: Any*): Any = macro ProofRuleMacro.impl
}

/** Helper class for easy annotation argument parsing. Must stay in sync with [[ProofRule]]! */
case class ProofRuleArgs(
    names: Any = false,
    codeName: String = "",
    longDisplayName: String = "",
    premises: String = "",
    conclusion: String = "",
    unifier: String = "full",
    displayLevel: String = "internal",
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
      case q"new $_(..$args)" =>
        c.eval(c.Expr[ProofRuleArgs](q"edu.cmu.cs.ls.keymaerax.btactics.macros.ProofRuleArgs(..$args)"))
      case q"new $_()" => c.eval(c.Expr[ProofRuleArgs](q"edu.cmu.cs.ls.keymaerax.btactics.macros.ProofRuleArgs()"))
      case _ => c.abort(c.enclosingPosition, "this should never happen")
    }

    /*
     * Deconstruct syntax tree and check for consistency
     */

    // Annotation must be applied to the val definition of an axiom.
    val valDef = annottees.map(_.tree).toList match {
      case List(valDef: ValDef) => valDef
      case t: Tree => c.abort(t.pos, "@ProofRule must be applied to val definition")
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
     * Parse annotation arguments
     */

    val declName = tDeclName.decodedName.toString

    val premises = parseSequents(args.premises)(c)
    val conclusionOpt = if (args.conclusion.isEmpty) None else Some(parseSequent(args.conclusion)(c))
    val key = parsePos(args.key)(c)
    val recursor = parsePoses(args.recursor)(c)

    val simpleDisplay = args.names match {
      case (sl: String, sr: String) => SimpleDisplayInfo(sl, sr)
      case s: String => SimpleDisplayInfo(s, s)
      case false => SimpleDisplayInfo(declName, declName)
      case _ => c.abort(c.enclosingPosition, "@ProofRule names must be String or (String, String)")
    }

    val display = (simpleDisplay, premises, conclusionOpt) match {
      case (_, Nil, None) => simpleDisplay
      case (sd, p, Some(c)) => RuleDisplayInfo(sd, c, p, "")
      case _ => c.abort(c.enclosingPosition, "@ProofRule with premises must have a conclusion")
    }

    /*
     * Compute different names
     */

    // If the codeName is not specified, it is taken from the declaration name.
    val codeName = if (args.codeName.nonEmpty) args.codeName else declName

    val longDisplayName: String = if (args.longDisplayName.nonEmpty) args.longDisplayName else simpleDisplay.asciiName

    val storageName = codeName.toLowerCase

    val canonicalName = tParams.head.asInstanceOf[Literal].value.value.asInstanceOf[String]

    /*
     * Build AST
     */

    // The derived* functions allow an optional argument for the codeName, which we supply here.
    val fullParams = if (isCore) tParams else tParams.take(minParam).:+(q"Some($storageName)")
    val fullRhs = q"$tFunctionName( ..$fullParams)"

    // Tactic implementation of derived rule is always useAt
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
        tq"edu.cmu.cs.ls.keymaerax.btactics.macros.AxiomaticRuleInfo",
        q"""AxiomaticRuleInfo(
          canonicalName = $canonicalName,
          display = ${convDI(display)(c)},
          codeName = $codeName,
          longDisplayName = $longDisplayName,
          unifier = $unifier,
          theExpr = $expr,
          displayLevel = $displayLevel,
          theKey = $key,
          theRecursor = $recursor,
        )""",
      )
      else (
        tq"edu.cmu.cs.ls.keymaerax.btactics.macros.DerivedRuleInfo",
        q"""DerivedRuleInfo(
          canonicalName = $canonicalName,
          display = ${convDI(display)(c)},
          codeName = $codeName,
          longDisplayName = $longDisplayName,
          unifier = $unifier,
          theExpr = $expr,
          displayLevel = $displayLevel,
          theKey = $key,
          theRecursor = $recursor,
        )""",
      )

    // Macro cannot introduce new statements or declarations, so introduce a library call which achieves our goal of
    // registering the proof rule info to the global proof rule info table.
    val result = q"""
      $tMods val $tDeclName: $infoType =
        edu.cmu.cs.ls.keymaerax.btactics.macros.DerivationInfo.registerR($fullRhs, $info)
    """

    c.Expr[Nothing](result)
  }
}
