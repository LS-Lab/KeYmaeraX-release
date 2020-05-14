/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.macros

import scala.annotation.StaticAnnotation
import scala.language.experimental.macros
import scala.reflect.macros.whitebox


/**
 *  Annotation for derived axioms, which allows decentralized AxiomInfo
 *  @param displayObj Should be a DisplayInfo and describes how the axiom is presented on the UI
 *  @param codeName used to invoke axiom in tactics
 *  @param linear is the axiom linear in the sense of a linear pattern
 *  @author Brandon Bohrer
 *  */
class DerivedAxiom(val displayObj: Any, val codeName: String = "", val linear: Boolean = false) extends StaticAnnotation {
  // Annotation is implemented a macro; this is a necessary, reserved magic invocation which says DerivedAxiomAnnotation.impl is the macro body
  def macroTransform(annottees: Any*): Any = macro DerivedAxiom.impl
}

object DerivedAxiom {
  def impl(c: whitebox.Context)(annottees: c.Expr[Any]*): c.Expr[Any] = {
    import c.universe._
    // Abstract syntax trees for string and string list literals
    def literal(s: String): Tree = Literal(Constant(s))
    def literals(ss: List[String]): Tree = q"""List(..${ss.map((s: String) => literal(s))})"""
    // Abstract syntax trees for all the display info data structures
    def convAIs(ais: List[ArgInfo]): Tree = {
      q"""new List(..${ais.map((ai:ArgInfo) => convAI(ai))})"""
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
    // Macro library does not allow directly passing arguments from annotation constructor to macro implementation.
    // Searching the prefix allows us to recover the arguments
    val codeNameParam: String = c.prefix.tree match {
      case q"new $annotation($display)" => ""
      case q"new $annotation($display, $codeName)" => c.eval[String](c.Expr(codeName))
      case q"new $annotation($display, $codeName, $linear)" => c.eval[String](c.Expr(codeName))
    }
    def display: DisplayInfo = {
      val displayObj: Any = c.prefix.tree match {
        case q"new $annotation($display)" => c.eval[Any](c.Expr(display))
        case q"new $annotation($display, $codeName)" => c.eval[Any](c.Expr(display))
        case q"new $annotation($display, $codeName, $linear)" => c.eval[Any](c.Expr(display))
      }
      // For convenience, the display argument can be a string, pair of strings which we cast to a DisplayInfo here.
      // Previous implementations accomplished this with implicits, but implicits mix poorly with macros.
      displayObj match {
        case s: String => SimpleDisplayInfo(s, s)
        case (sl: String, sr: String) => SimpleDisplayInfo(sl, sr)
        case di: DisplayInfo => di
        case di => c.abort(c.enclosingPosition, "@DerivedAxiomAnnotation expected DisplayInfo, got: " + di)
      }
    }
    // Annotation can only be attached to library functions for defining new axioms
    def correctName(t: Tree): Boolean = {
      t match {
        case id: Ident => {
          if (Set("derivedAxiom", "derivedFormula", "derivedAxiomFromFact").contains(id.name.decodedName.toString)) true
          else c.abort(c.enclosingPosition, "Expected function name: one of {derivedAxiom, derivedFormula, derivedAxiomFromFact}, got: " + t + " of type " + t.getClass())
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
          case q"$mods val $declName: $tpt = $functionName( ..$params )" if correctName(functionName) &&
            (params.length == 3  || params.length == 4) =>
              // codeName is usually supplied, but can be taken from the bound identifier of the declaration by default
              val codeName = if(codeNameParam.nonEmpty) TermName(codeNameParam) else declName
              // AST for literal strings for the names
              val codeString = Literal(Constant(codeName.decodedName.toString))
              val canonString = params(0)
              // derivedAxiom functions allow an optional argument for the codeName, which we supply here
              val fullParams = Seq(params(0), params(1), params(2), q"Some($codeString)")
              val fullRhs = q"$functionName( ..$fullParams)"
              // Tactic implementation of derived axiom is always useAt
              val expr = q"""({case () => edu.cmu.cs.ls.keymaerax.btactics.HilbertCalculus.useAt($canonString)})""" // : (Unit => Any)
              val info = q"""DerivedAxiomInfo(canonicalName = $canonString, codeName = $codeString, linear = false, theExpr = $expr, display = ${convDI(display)})"""
              // Macro cannot introduce new statements or declarations, so introduce a library call which achieves our goal of registering
              // the axiom info to the global axiom info table
              val application = q"edu.cmu.cs.ls.keymaerax.macros.DerivationInfo.register($fullRhs, $info)"
              val lemmaType = tq"edu.cmu.cs.ls.keymaerax.lemma.Lemma"
              c.Expr[Nothing](q"""$mods val $declName: $lemmaType = $application""")
          case q"$mods val $cName: $tpt = $functionName( ..$params )" => c.abort(c.enclosingPosition, "Expected derivedAxiom with 3 parameters, got:" + params.length)
          case t => c.abort(c.enclosingPosition, "Invalid annottee: Expected val name = <derivedAxiomFunction>(x1, x2, x3), got: " + t + " of type " + t.getClass())
        }
      case t => c.abort(c.enclosingPosition, "Invalid annottee: Expected val declaration got: " + t.head + " of type: " + t.head.getClass())
    }
  }
}