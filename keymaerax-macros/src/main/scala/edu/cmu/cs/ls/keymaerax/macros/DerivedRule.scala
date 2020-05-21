package edu.cmu.cs.ls.keymaerax.macros

import scala.language.experimental.macros
import AnnotationCommon._
import scala.annotation.StaticAnnotation
import scala.collection.immutable.Nil
import scala.reflect.macros.whitebox

/**
 *  Annotation for derived axioms, which allows decentralized AxiomInfo
 *  @param names Display names
 *  @param codeName used to invoke axiom in tactics
 *  @param premises Premises displayed for rule
 *  @param conclusion Conclusion displayed for rule
 *  @param displayLevel Where to show the axiom: 'internal, 'browse, 'menu, 'all
 *  @author Brandon Bohrer
 *  */
class DerivedRule(val names: Any,
                  val codeName: String = "",
                  val premises: String = "",
                  val conclusion: String = "",
                  val displayLevel: String = "internal",
                  ) extends StaticAnnotation {
  // Annotation is implemented a macro; this is a necessary, reserved magic invocation which says DerivedAxiomAnnotation.impl is the macro body
  def macroTransform(annottees: Any*): Any = macro DerivedRule.impl
}

object DerivedRule {
  type ExprPos = List[Int]
  def impl(c: whitebox.Context)(annottees: c.Expr[Any]*): c.Expr[Any] = {
    val u = c.universe
    val paramNames = List("names", "codeName", "formula", "unifier", "displayLevel", "inputs", "key", "recursor")
    // Macro library does not allow directly passing arguments from annotation constructor to macro implementation.
    // Searching the prefix allows us to recover the arguments
    def getParams(implicit c: whitebox.Context): (String, DisplayInfo, String) = {
      // @TODO: What do ASTs look like when option arguments are omitted or passed by name?
      import c.universe._
      c.prefix.tree match {
        case q"new $annotation(..$params)" =>
          val defaultMap:Map[String, c.universe.Tree] = Map(
            "codeName" -> Literal(Constant("")),
            "premises" -> Literal(Constant("")),
            "conclusion" -> Literal(Constant("")),
            "displayLevel" -> Literal(Constant("internal"))
          )
          val (_idx, _wereNamed, paramMap) = params.foldLeft((0, false, defaultMap))({case (acc, x) => foldParams(c, paramNames)(acc, x)})
          val (displayObj, premisesString: String, conclusionString: String, codeName, displayLevel: String)
            = c.eval[(Any, String, String, String, String)](c.Expr
              (q"""(${paramMap("names")}, ${paramMap("premises")}, ${paramMap("conclusion")}, ${paramMap("codeName")}, ${paramMap("displayLevel")})"""))
          val premises = parseSequents(premisesString)
          val conclusionOpt = if(conclusionString == "") None else Some(parseSequent(conclusionString))
          val simpleDisplay = displayObj match {
            case s: String => SimpleDisplayInfo(s, s)
            case (sl: String, sr: String) => SimpleDisplayInfo(sl, sr)
            case sdi: SimpleDisplayInfo => sdi
            case di => c.abort(c.enclosingPosition, "@DerivedAxiomAnnotation expected names: String or names: (String, String) or names: SimpleDisplayInfo, got: " + di)
          }
          val displayInfo = (simpleDisplay, premises, conclusionOpt) match {
            case (sd, Nil, None) => simpleDisplay
            case (sd, p, Some(c)) => RuleDisplayInfo(sd, c, p)
            case _ => c.abort(c.enclosingPosition, "Expected both premises and conclusion")
          }
          (codeName, displayInfo, displayLevel)
        case e => c.abort(c.enclosingPosition, "Excepted @DerivedRule(args), got: " + e)
      }
    }
    val (codeNameParam: String, display: DisplayInfo, displayLevel: String) = getParams(c)
    // Annotation can only be attached to library functions for defining new axioms
    def correctName(c: whitebox.Context)(t: c.universe.Tree): Boolean = {
      import c.universe._
      t match {
        case id: Ident => {
          if (Set("derivedRule", "derivedRuleSequent").contains(id.name.decodedName.toString)) true
          else c.abort(c.enclosingPosition, "Expected function name derivedRule or derivedRuleSequent, got: " + t + " of type " + t.getClass())
        }
        case t => c.abort(c.enclosingPosition, "Invalid annottee: Expected derivedRule string, got: " + t + " of type " + t.getClass())
      }
    }
    // private[btactics] def derivedRule(name: String, fact: ProvableSig, codeNameOpt: Option[String]): Lemma = {
    // private[btactics] def derivedRule(name: String, derived: => Sequent, tactic: => BelleExpr, codeNameOpt: Option[String] = None): Lemma = {
    def paramCount(c: whitebox.Context)(t: c.universe.Tree): (Int, Int) = {
      import c.universe._
      t match {
        case id: Ident => {
          id.name.decodedName.toString match {
            case "derivedRule"  => (2, 3)
            case "derivedRuleSequent" => (3, 4)
            case _ => c.abort(c.enclosingPosition, "Expected function name: one of {derivedRule, derivedRuleSequent}, got: " + t + " of type " + t.getClass())
          }
        }
        case t => c.abort(c.enclosingPosition, "Invalid annottee: Expected derivedRule string, got: " + t + " of type " + t.getClass())
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
              c.abort(c.enclosingPosition, "Invalid annottee: Expected val name = <derivedRuleFunction>(x1, x2, ..), got: " + functionName + " of type " + functionName.getClass())
            val (minParam, maxParam) = paramCount(c)(functionName)
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
            val dispLvl = displayLevel match {case "internal" => 'internal case "browse" => 'browse case "menu" => 'menu case "all" => 'all
            case s => c.abort(c.enclosingPosition, "Unknown display level " + s)}
            //  DerivedRuleInfo(override val canonicalName:String, override val display: DisplayInfo, override val codeName: String, val theExpr: Unit => Any)
            val info = q"""DerivedRuleInfo(canonicalName = $canonString, display = ${convDI(display)(c)}, codeName = $codeString, displayLevel = $dispLvl, theExpr = $expr)"""
            // Macro cannot introduce new statements or declarations, so introduce a library call which achieves our goal of registering
            // the axiom info to the global axiom info table
            val application = q"edu.cmu.cs.ls.keymaerax.macros.DerivationInfo.registerDerivedRule($fullRhs, $info)"
            val lemmaType = tq"edu.cmu.cs.ls.keymaerax.macros.DerivedRuleInfo"
            c.Expr[Nothing](q"""$mods val $declName: $lemmaType = $application""")
          case q"$mods val $cName: $tpt = $functionName( ..$params )" => c.abort(c.enclosingPosition, "Expected derivedRule with 2-3 parameters, got:" + params.length)

        }
      case t => c.abort(c.enclosingPosition, "Invalid annottee: Expected val declaration got: " + t.head + " of type: " + t.head.getClass())
    }
  }
}
