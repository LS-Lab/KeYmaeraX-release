package edu.cmu.cs.ls.keymaerax.macros

import scala.annotation.StaticAnnotation
import scala.language.experimental.macros
import scala.reflect.macros.whitebox

class IdentAnnotation extends StaticAnnotation {
  def macroTransform(annottees: Any*): Any = macro IdentAnnotation.impl
}

object IdentAnnotation {
  def impl(c: whitebox.Context)(annottees: c.Expr[Any]*): c.Expr[Any] =  annottees(0)
}

class DerivedAxiomAnnotation(val displayObj: Any, val codeName: String = "", val linear: Boolean = false) extends StaticAnnotation {
  def macroTransform(annottees: Any*): Any = macro DerivedAxiomAnnotation.impl
}


object DerivedAxiomAnnotation {

  // @TODO: Is this signature correct
  def impl(c: whitebox.Context)(annottees: c.Expr[Any]*): c.Expr[Any] = {
    import c.universe._
    def literal(s: String): Tree = Literal(Constant(s))
    def literals(ss: List[String]): Tree = q"""List(..${ss.map((s: String) => literal(s))})"""
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
      displayObj match {
        case s: String => SimpleDisplayInfo(s, s)
        case (sl: String, sr: String) => SimpleDisplayInfo(sl, sr)
        case di: DisplayInfo => di
        case di => c.abort(c.enclosingPosition, "@DerivedAxiomAnnotation expected DisplayInfo, got: " + di)
      }
    }
    def correctName(t: Tree): Boolean = {
      t match {
        case id: Ident => {
          if (Set("derivedAxiom", "derivedFormula", "derivedAxiomFromFact").contains(id.name.decodedName.toString)) true // , "derivedFact"
          else c.abort(c.enclosingPosition, "Expected function name: one of {derivedAxiom, derivedFormula, derivedAxiomFromFact}, got: " + t + " of type " + t.getClass())
        }
        case t => c.abort(c.enclosingPosition, "Invalid annottee: Expected derivedAxiom string, got: " + t + " of type " + t.getClass())
      }
    }
    annottees map (_.tree) toList match {
      case (valDecl: ValDef) :: Nil =>
        valDecl match {
          case q"$mods val $declName: $tpt = $functionName( ..$params )"if correctName(functionName) &&
            (params.length == 3  || params.length == 4) =>
                val codeName: TermName = if(codeNameParam.nonEmpty) TermName(codeNameParam) else declName
                val codeString = Literal(Constant(codeName.decodedName.toString))
                val canonString = params(0)
                val fullParams = Seq(params(0), params(1), params(2), q"Some($codeString)")
                val fullRhs = q"$functionName( ..$fullParams)"
                val expr = q"""({case () => edu.cmu.cs.ls.keymaerax.btactics.HilbertCalculus.useAt($canonString)})""" // : (Unit => Any)
                val info = q"""DerivedAxiomInfo(canonicalName = $canonString, codeName = $codeString, linear = false, theExpr = $expr, display = ${convDI(display)})"""
                val printInfo = q"""{println("Registering info: " + $info); $info}"""
                val application = q"edu.cmu.cs.ls.keymaerax.macros.DerivationInfo.register($fullRhs, $printInfo)"
                val lemmaType = tq"edu.cmu.cs.ls.keymaerax.lemma.Lemma"
                c.Expr[Nothing](q"""$mods val $declName: $lemmaType = $application""")
          case q"$mods val $cName: $tpt = $functionName( ..$params )" => c.abort(c.enclosingPosition, "Expected derivedAxiom with 3 parameters, got:" + params.length)
          case t => c.abort(c.enclosingPosition, "Invalid annottee: Expected val name = <derivedAxiomFunction>(x1, x2, x3), got: " + t + " of type " + t.getClass())
        }
      case t => c.abort(c.enclosingPosition, "Invalid annottee: Expected val declaration got: " + t.head + " of type: " + t.head.getClass())
    }
  }
}