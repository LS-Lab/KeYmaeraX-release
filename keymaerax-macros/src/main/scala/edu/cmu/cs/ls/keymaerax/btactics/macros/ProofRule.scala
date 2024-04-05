/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics.macros

import edu.cmu.cs.ls.keymaerax.btactics.macros.AnnotationCommon._

import scala.annotation.StaticAnnotation
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
  // Annotation is implemented a macro; this is a necessary, reserved magic invocation which says DerivedAxiomAnnotation.impl is the macro body
  def macroTransform(annottees: Any*): Any = macro RuleImpl.apply
}

class RuleImpl(val c: whitebox.Context) {
  type ExprPos = List[Int]
  import c.universe._
  def apply(annottees: c.Expr[Any]*): c.Expr[Any] = {
    def getLiteral(t: Tree): String = {
      t match {
        case Literal(Constant(s: String)) => s
        case t => c.abort(c.enclosingPosition, "Expected string literal, got: " + t)
      }
    }
    val paramNames = List(
      "names",
      "codeName",
      "longDisplayName",
      "premises",
      "conclusion",
      "unifier",
      "displayLevel",
      "key",
      "recursor",
    )
    // Macro library does not allow directly passing arguments from annotation constructor to macro implementation.
    // Searching the prefix allows us to recover the arguments
    def paramify(
        tn: TermName,
        params: Seq[Tree],
    ): (String, String, DisplayInfo, String, ExprPos, List[ExprPos], String) = {
      val defaultMap: Map[String, c.universe.Tree] = Map(
        "names" -> Literal(Constant(false)),
        "unifier" -> Literal(Constant("full")),
        "codeName" -> Literal(Constant("")),
        "longDisplayName" -> Literal(Constant(false)),
        "premises" -> Literal(Constant("")),
        "conclusion" -> Literal(Constant("")),
        "displayLevel" -> Literal(Constant("internal")),
        "key" -> Literal(Constant("")),
        "recursor" -> Literal(Constant("*")),
      )
      val (_idx, _wereNamed, paramMap) = params.foldLeft((0, false, defaultMap))({ case (acc, x) =>
        foldParams(c, paramNames)(acc, x)
      })
      val (
        displayObject,
        premisesString,
        conclusionString,
        unifier,
        codeName,
        displayLevel,
        keyString,
        recursorString,
      ) = (
        paramMap("names"),
        getLiteral(paramMap("premises")),
        getLiteral(paramMap("conclusion")),
        getLiteral(paramMap("unifier")),
        getLiteral(paramMap("codeName")),
        getLiteral(paramMap("displayLevel")),
        getLiteral(paramMap("key")),
        getLiteral(paramMap("recursor")),
      )
      val key = parsePos(keyString)(c)
      val recursor = parsePoses(recursorString)(c)
      val simpleDisplay = displayObject match {
        case q"""(${Literal(Constant(sl: String))}, ${Literal(Constant(sr: String))})""" => SimpleDisplayInfo(sl, sr)
        case Literal(Constant(s: String)) => SimpleDisplayInfo(s, s)
        case Literal(Constant(false)) => {
          val s = tn.decodedName.toString
          SimpleDisplayInfo(s, s)
        }
        case di => c.abort(
            c.enclosingPosition,
            "@ProofRule expected names: String or names: (String, String) or names: SimpleDisplayInfo, got: " + di,
          )
      }
      val premises = parseSequents(premisesString)(c)
      val conclusionOpt = if (conclusionString == "") None else Some(parseSequent(conclusionString)(c))
      val displayInfo = (simpleDisplay, premises, conclusionOpt) match {
        case (_, Nil, None) => simpleDisplay
        case (sd, p, Some(c)) => RuleDisplayInfo(sd, c, p, "")
        case _ => c.abort(c.enclosingPosition, "Expected both premises and conclusion")
      }
      val longDisplayName = paramMap("longDisplayName") match {
        case Literal(Constant(s: String)) => s
        case Literal(Constant(false)) => { simpleDisplay.asciiName }
      }

      (codeName, longDisplayName, displayInfo, displayLevel, key, recursor, unifier)
    }
    def getParams(tn: TermName): (String, String, DisplayInfo, String, ExprPos, List[ExprPos], String) = {
      import c.universe._
      c.prefix.tree match {
        case q"new $annotation(..$params)" => paramify(tn, params)
        case q"new $annotation()" => paramify(tn, Nil)
        case e => c.abort(c.enclosingPosition, "Expected @ProofRule(args), got: " + e)
      }
    }
    // Annotation can only be attached to library functions for defining new axioms
    def correctName(c: whitebox.Context)(t: c.universe.Tree): Boolean = {
      import c.universe._
      t match {
        case id: Ident => {
          if (Set("coreRule", "derivedRule", "derivedRuleSequent").contains(id.name.decodedName.toString)) true
          else c.abort(
            c.enclosingPosition,
            "Expected function name coreRule, derivedRule or derivedRuleSequent, got: " + t + " of type " + t.getClass(),
          )
        }
        case t => c.abort(
            c.enclosingPosition,
            "Invalid annottee: Expected rule function, got: " + t + " of type " + t.getClass(),
          )
      }
    }
    // private[btactics] def derivedRule(name: String, fact: ProvableSig, codeNameOpt: Option[String]): Lemma = {
    // private[btactics] def derivedRule(name: String, derived: => Sequent, tactic: => BelleExpr, codeNameOpt: Option[String] = None): Lemma = {
    def paramCount(c: whitebox.Context)(t: c.universe.Tree): (Int, Int) = {
      import c.universe._
      t match {
        case id: Ident => {
          id.name.decodedName.toString match {
            case "coreRule" => (1, 1)
            case "derivedRule" => (2, 3)
            case "derivedRuleSequent" => (3, 4)
            case _ => c.abort(
                c.enclosingPosition,
                "Expected function name: one of {coreRule, derivedRule, derivedRuleSequent}, got: " + t + " of type " +
                  t.getClass(),
              )
          }
        }
        case t => c.abort(
            c.enclosingPosition,
            "Invalid annottee: Expected rule function, got: " + t + " of type " + t.getClass(),
          )
      }
    }
    import c.universe._
    annottees.map(_.tree).toList match {
      // Annottee must be a val declaration of an axiom
      case (valDecl: ValDef) :: Nil => valDecl match {
          // val declaration must be an invocation of one of the functions for defining derived axioms and optionally can
          // have modifiers and type annotations
          case q"$mods val ${declName: TermName}: $tpt = $functionName( ..$params )" =>
            if (!correctName(c)(functionName)) c.abort(
              c.enclosingPosition,
              "Invalid annottee: Expected val name = <ruleFunction>(x1, x2, ..), got: " + functionName + " of type " +
                functionName.getClass(),
            )
            val (minParam, maxParam) = paramCount(c)(functionName)
            val isCore = (minParam == maxParam)
            val (
              codeNameParam: String,
              longDisplayNameParam: String,
              display: DisplayInfo,
              displayLevel: String,
              key,
              recursor,
              unifier,
            ) = getParams(declName)
            if (params.length < minParam || params.length > maxParam) c.abort(
              c.enclosingPosition,
              s"Function $functionName had ${params.length} arguments, needs $minParam-$maxParam",
            )
            // codeName is usually supplied, but can be taken from the bound identifier of the declaration by default
            val codeName = if (codeNameParam.nonEmpty) TermName(codeNameParam) else declName
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
            val dispLvl = displayLevel match {
              case "internal" => Symbol("internal")
              case "browse" => Symbol("browse")
              case "menu" => Symbol("menu")
              case "all" => Symbol("all")
              case s => c.abort(c.enclosingPosition, "Unknown display level " + s)
            }
            val unif = unifier match {
              case "surjective" => Symbol("surjective")
              case "surjlinear" => Symbol("surlinear")
              case "full" => Symbol("full")
              case "linear" => Symbol("linear")
              case "surjlinearpretend" => Symbol("surlinearpretend")
              case s => c.abort(c.enclosingPosition, "Unknown unifier " + s)
            }
            val longDisplayName = Literal(Constant(longDisplayNameParam))
            val info =
              if (isCore) {
                q"""AxiomaticRuleInfo(canonicalName = $canonString, display = ${convDI(display)(
                    c
                  )}, codeName = $codeString, longDisplayName = $longDisplayName, unifier = $unif, theExpr = $expr, displayLevel = $dispLvl, theKey = $key, theRecursor = $recursor)"""
              } else {
                q"""DerivedRuleInfo(canonicalName = $canonString, display = ${convDI(display)(
                    c
                  )}, codeName = $codeString, longDisplayName = $longDisplayName, unifier = $unif, theExpr = $expr, displayLevel = $dispLvl, theKey = $key, theRecursor = $recursor)"""
              }
            // Macro cannot introduce new statements or declarations, so introduce a library call which achieves our goal of registering
            // the axiom info to the global axiom info table
            val application = q"edu.cmu.cs.ls.keymaerax.btactics.macros.DerivationInfo.registerR($fullRhs, $info)"
            val lemmaType =
              if (isCore) { tq"edu.cmu.cs.ls.keymaerax.btactics.macros.AxiomaticRuleInfo" }
              else { tq"edu.cmu.cs.ls.keymaerax.btactics.macros.DerivedRuleInfo" }
            val res = c.Expr[Nothing](q"""$mods val $declName: $lemmaType = $application""")
            res
          case q"$mods val $cName: $tpt = $functionName( ..$params )" =>
            c.abort(c.enclosingPosition, "Expected derivedRule with 2-3 parameters, got:" + params.length)

        }
      case t => c.abort(
          c.enclosingPosition,
          "Invalid annottee: Expected val declaration got: " + t.head + " of type: " + t.head.getClass(),
        )
    }
  }
}
