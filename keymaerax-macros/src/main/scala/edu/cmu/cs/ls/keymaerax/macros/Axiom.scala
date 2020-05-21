/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.macros

import edu.cmu.cs.ls.keymaerax.macros.Axiom.ExprPos

import scala.annotation.StaticAnnotation
import scala.collection.immutable.Nil
import scala.language.experimental.macros
import scala.reflect.macros.whitebox
import AnnotationCommon._


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
class Axiom(val names: Any,
            val codeName: String = "",
            val formula: String = "",
            val unifier: String = "full",
            val displayLevel: String = "internal",
            val inputs: String = "",
            val key: ExprPos = 0::Nil,
            val recursor: List[ExprPos] = Nil
                  ) extends StaticAnnotation {
  // Annotation is implemented a macro; this is a necessary, reserved magic invocation which says DerivedAxiomAnnotation.impl is the macro body
  def macroTransform(annottees: Any*): Any = macro Axiom.impl
}

object Axiom {

  // Would just use PosInExpr but can't pull in core
  type ExprPos = List[Int]
  def impl(c: whitebox.Context)(annottees: c.Expr[Any]*): c.Expr[Any] = {
    val u = c.universe
    val paramNames = List("names", "codeName", "formula", "unifier", "displayLevel", "inputs", "key", "recursor")
    // Macro library does not allow directly passing arguments from annotation constructor to macro implementation.
    // Searching the prefix allows us to recover the arguments
    def getParams(implicit c: whitebox.Context): (String, DisplayInfo, String, String, ExprPos, List[ExprPos]) = {
      // @TODO: What do ASTs look like when option arguments are omitted or passed by name?
      import c.universe._
      c.prefix.tree match {
        case q"new $annotation(..$params)" =>
          val defaultMap = Map(
            "codeName" -> Literal(Constant("")),
            "formula" -> Literal(Constant("")),
            "unifier" -> Literal(Constant("full")),
            "displayLevel" -> Literal(Constant("internal")),
            "key" -> q"""0::scala.collection.immutable.Nil""",
            "recursor" -> q"""scala.collection.immutable.Nil""",
            "inputs" -> Literal(Constant(""))
          )
          val (_idx, _wereNamed, paramMap) = params.foldLeft((0, false, defaultMap))({case (acc, x) => foldParams(c, paramNames)(acc, x)})
          val (displayObj, fml: String, inputString: String, codeName, unifier: String, displayLevel: String, key: ExprPos, recursor: List[ExprPos])
          = (c.eval[(Any, String, String, String, String, String, ExprPos, List[ExprPos])](c.Expr
            (q"""(${paramMap("names")}, ${paramMap("formula")}, ${paramMap("inputs")}, ${paramMap("codeName")}, ${paramMap("unifier")},
              ${paramMap("displayLevel")}, ${paramMap("key")}, ${paramMap("recursor")})""")))
          val inputs: List[ArgInfo] = parseAIs(inputString)(c)
          val simpleDisplay = displayObj match {
            case s: String => SimpleDisplayInfo(s, s)
            case (sl: String, sr: String) => SimpleDisplayInfo(sl, sr)
            case sdi: SimpleDisplayInfo => sdi
            case di => c.abort(c.enclosingPosition, "@Axiom expected names: String or names: (String, String) or names: SimpleDisplayInfo, got: " + di)
          }
          val displayInfo = (fml, inputs, Nil, None) match {
            case ("", Nil, Nil, None) => simpleDisplay
            case (fml, Nil, Nil, None) if fml != "" => AxiomDisplayInfo(simpleDisplay, fml)
            case (fml, args, Nil, None) if fml != "" => InputAxiomDisplayInfo(simpleDisplay, fml, args)
            //case ("", Nil, premises, Some(conclusion)) => RuleDisplayInfo(simpleDisplay, conclusion, premises)
            case _ => c.abort(c.enclosingPosition, "Unsupported argument combination for @Axiom: either specify premisses and conclusion, or formula optionally with inputs, not both")
          }
          (codeName, displayInfo, unifier, displayLevel, key, recursor)
        case e => c.abort(c.enclosingPosition, "Excepted @Axiom(args), got: " + e)
      }
    }
    val (codeNameParam: String, display: DisplayInfo, unifier: String, displayLevel: String, key, recursor) = getParams(c)
    // Annotation can only be attached to library functions for defining new axioms
    def correctName(c: whitebox.Context)(t: c.universe.Tree): Boolean = {
      import c.universe._
      t match {
        case id: Ident => {
          if (Set("coreAxiom", "derivedAxiom", "derivedFormula", "derivedAxiomFromFact", "derivedFact").contains(id.name.decodedName.toString)) true
          else c.abort(c.enclosingPosition, "Expected function name: one of {coreaxiom, derivedAxiom, derivedFormula, derivedAxiomFromFact, derivedFact}, got: " + t + " of type " + t.getClass())
        }
        case t => c.abort(c.enclosingPosition, "Invalid annottee: Expected axiom function, got: " + t + " of type " + t.getClass())
      }
    }
    def paramCount(c: whitebox.Context)(t: c.universe.Tree): (Int, Int) = {
      import c.universe._
      t match {
        case id: Ident => {
          id.name.decodedName.toString match {
            case "coreAxiom" => (1, 1)
            case "derivedAxiom" | "derivedAxiomFromFact" | "derivedFormula" => (3, 4)
            case "derivedFact" => (2, 3)
            case _ => c.abort(c.enclosingPosition, "Expected function name: one of {coreAxiom, derivedAxiom, derivedFormula, derivedAxiomFromFact, derivedFact}, got: " + t + " of type " + t.getClass())
          }
        }
        case t => c.abort(c.enclosingPosition, "Invalid annottee: Expected derivedAxiom string, got: " + t + " of type " + t.getClass())
      }
    }
    import c.universe._
    annottees map (_.tree) toList match {
      // Annottee must be a val declaration of an axiom
      case (valDecl: ValDef) :: Nil =>
        valDecl match {
          // val declaration must be an invocation of one of the functions for defining derived axioms and optionally can
          // have modifiers and type annotations
          case q"$mods val $declName: $tpt = $functionName( ..$params )" =>
            if (!correctName(c)(functionName))
              c.abort(c.enclosingPosition, "Invalid annottee: Expected val name = <derivedAxiomFunction>(x1, x2, x3), got: " + functionName + " of type " + functionName.getClass())
            val (minParam, maxParam) = paramCount(c)(functionName)
            val isCore = (minParam == maxParam)
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
            val fullParams = if(isCore) params else params.take(minParam).:+(q"Some($storageString)")
            val fullRhs = q"$functionName( ..$fullParams)"
            // Tactic implementation of derived axiom is always useAt
            val expr = q"""({case () => edu.cmu.cs.ls.keymaerax.btactics.HilbertCalculus.useAt($canonString)})""" // : (Unit => Any)
            val unif = unifier match {case "full" => 'full case "linear" => 'linear case s => c.abort(c.enclosingPosition, "Unknown unifier " + s)}
            val dispLvl = displayLevel match {case "internal" => 'internal case "browse" => 'browse case "menu" => 'menu case "all" => 'all
              case s => c.abort(c.enclosingPosition, "Unknown display level " + s)}
            val info =
              if(isCore)
                q"""CoreAxiomInfo(canonicalName = $canonString, display = ${convDI(display)(c)}, codeName = $codeString, unifier = $unif, displayLevel = $dispLvl, theKey = $key, theRecursor = $recursor, theExpr = $expr)"""
              else
                q"""DerivedAxiomInfo(canonicalName = $canonString, display = ${convDI(display)(c)}, codeName = $codeString, unifier = $unif, displayLevel = $dispLvl, theKey = $key, theRecursor = $recursor, theExpr = $expr)"""
            // Macro cannot introduce new statements or declarations, so introduce a library call which achieves our goal of registering
            // the axiom info to the global axiom info table
            val (application, lemmaType) =
              if(isCore) {
                (q"edu.cmu.cs.ls.keymaerax.macros.DerivationInfo.registerCore($fullRhs, $info)", tq"edu.cmu.cs.ls.keymaerax.macros.CoreAxiomInfo")
              }  else {
                (q"edu.cmu.cs.ls.keymaerax.macros.DerivationInfo.registerDerived($fullRhs, $info)", tq"edu.cmu.cs.ls.keymaerax.macros.DerivedAxiomInfo")
              }
            c.Expr[Nothing](q"""$mods val $declName: $lemmaType = $application""")
          case q"$mods val $cName: $tpt = $functionName( ..$params )" => c.abort(c.enclosingPosition, "Expected derivedAxiom with 3 parameters, got:" + params.length)

        }
      case t => c.abort(c.enclosingPosition, "Invalid annottee: Expected val declaration got: " + t.head + " of type: " + t.head.getClass())
    }
  }
}