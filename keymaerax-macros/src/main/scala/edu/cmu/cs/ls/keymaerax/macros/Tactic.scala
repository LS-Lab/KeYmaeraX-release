package edu.cmu.cs.ls.keymaerax.macros

import scala.annotation.StaticAnnotation
import scala.collection.immutable.Nil
import scala.language.experimental.macros
import scala.reflect.macros.whitebox
import AnnotationCommon._

class Tactic(val names: Any,
             val formula: String = "",
             val premises: String = "",
             val conclusion: String = "",
             val displayLevel: String = "internal",
             val needsTool: Boolean = false,
             val needsGenerator: Boolean = false,
             val revealInternalSteps: Boolean = false,
            // @TODO: Can probably be eliminated by scraping def
             val inputs:String = ""
           ) extends StaticAnnotation {
    // Annotation is implemented a macro; this is a necessary, reserved magic invocation which says DerivedAxiomAnnotation.impl is the macro body
    def macroTransform(annottees: Any*): Any = macro Tactic.impl
}

/*
case class PositionTacticInfo(override val codeName: String, override val display: DisplayInfo, override val theExpr: Unit => Any,needsTool: Boolean = false, override val needsGenerator: Boolean = false,override val revealInternalSteps: Boolean = false)
case class TwoPositionTacticInfo(override val codeName: String, override val display: DisplayInfo, override val theExpr: Unit => Any, needsTool: Boolean = false, override val needsGenerator: Boolean = false)
case class InputTacticInfo(override val codeName: String, override val display: DisplayInfo, override val inputs:List[ArgInfo], expr: Unit => TypedFunc[_, _], needsTool: Boolean = false, override val needsGenerator: Boolean = false, override val revealInternalSteps: Boolean = false)
case class InputPositionTacticInfo(override val codeName: String, override val display: DisplayInfo, override val inputs:List[ArgInfo], expr: Unit => TypedFunc[_,_], needsTool: Boolean = false,override val needsGenerator: Boolean = false, override val revealInternalSteps: Boolean = false)
case class InputTwoPositionTacticInfo(override val codeName: String, override val display: DisplayInfo, override val inputs:List[ArgInfo], expr: Unit => TypedFunc[_, _], needsTool: Boolean = false, override val needsGenerator: Boolean = false)
 */

private case class OnePos(posName: String, seqName: String)


object Tactic {
  // Would just use PosInExpr but can't pull in core
  def impl(c: whitebox.Context)(annottees: c.Expr[Any]*): c.Expr[Any] = {
    val u = c.universe
    val paramNames = List("names", "formula", "premises", "conclusion", "displayLevel", "needsTool", "needsGenerator", "revealInternalSteps", "inputs")
    // Macro library does not allow directly passing arguments from annotation constructor to macro implementation.
    // Searching the prefix allows us to recover the arguments
    def getParams(implicit c: whitebox.Context): (DisplayInfo, String, Boolean, Boolean, Boolean) = {
      // @TODO: What do ASTs look like when option arguments are omitted or passed by name?
      import c.universe._
      c.prefix.tree match {
        case q"new $annotation(..$params)" =>
          val defaultMap: Map[String, Tree] = Map(
            "formula" -> Literal(Constant("")),
            "premises" -> Literal(Constant("")),
            "conclusion" -> Literal(Constant("")),
            "displayLevel" -> Literal(Constant("internal")),
            "needsTool" -> Literal(Constant(false)),
            "needsGenerator" -> Literal(Constant(false)),
            "revealInternalSteps" -> Literal(Constant(false)),
            "inputs" -> Literal(Constant(""))
          )
          val (_idx, _wereNamed, paramMap) = params.foldLeft((0, false, defaultMap))({case (acc, x) => foldParams(c, paramNames)(acc, x)})
          val (displayObj, fml: String, premisesString: String, conclusionString: String, displayLevel: String, needsTool: Boolean, needsString: Boolean, revealInternalSteps: Boolean, inputString: String)
          = (c.eval[(Any, String, String, String, String, Boolean, Boolean, Boolean, String)](c.Expr
          (q"""(${paramMap("names")}, ${paramMap("formula")}, ${paramMap("premises")}, ${paramMap("conclusion")}, ${paramMap("displayLevel")},
               ${paramMap("needsTool")}, ${paramMap("needsGenerator")}, ${paramMap("revealInternalSteps")}, ${paramMap("inputs")})""")))
          val inputs: List[ArgInfo] = parseAIs(inputString)(c)
          val simpleDisplay = displayObj match {
            case s: String => SimpleDisplayInfo(s, s)
            case (sl: String, sr: String) => SimpleDisplayInfo(sl, sr)
            case sdi: SimpleDisplayInfo => sdi
            case di => c.abort(c.enclosingPosition, "@Axiom expected names: String or names: (String, String) or names: SimpleDisplayInfo, got: " + di)
          }
          val displayInfo = (fml, inputs, premisesString, conclusionString) match {
            case ("", Nil, "", "") => simpleDisplay
            case (fml, Nil, "", "") if fml != "" => AxiomDisplayInfo(simpleDisplay, fml)
            case (fml, args, "", "") if fml != "" => InputAxiomDisplayInfo(simpleDisplay, fml, args)
            case (fml, Nil, _, _) if fml != "" =>
              val (prem, conc) = (parseSequents(premisesString), parseSequent(conclusionString))
              RuleDisplayInfo(simpleDisplay, conc, prem)
            case _ => c.abort(c.enclosingPosition, "Unsupported argument combination for @Tactic: either specify premisses and conclusion, or formula, not both")
          }
          (displayInfo, displayLevel, needsTool, needsString, revealInternalSteps)
        case e => c.abort(c.enclosingPosition, "Excepted @Axiom(args), got: " + e)
      }
    }
    def isBelleExpr(c: whitebox.Context)(tRet: c.universe.Tree): Boolean = {
      import c.universe._
      tRet match {
        case tq"BelleExpr" => true
        case _ => false
      }
    }
    def getPositioning(c: whitebox.Context)(params: Seq[c.universe.Tree]): OnePos = {
      import c.universe._
      params.toList match {
        case (posDef: ValDef) :: (seqDef: ValDef) :: Nil  =>
          (posDef.tpt, seqDef.tpt) match {
            case (tq"Position", tq"Sequent") => OnePos(posDef.name.toString, seqDef.name.toString)
            case params => c.abort(c.enclosingPosition, "Bad params: " + params)
          }
        case params => c.abort(c.enclosingPosition, "Bad params: " + params.map(_.getClass).mkString(","))
      }
    }
    val (display, displayLevel, needsTool, needsGenerator, revealInternalSteps) = getParams(c)
    import c.universe._
    annottees map (_.tree) toList match {
      // Annottee must be a val declaration of an axiom
      case (defDecl: DefDef) :: Nil =>
        defDecl match {
          // val declaration must be an invocation of one of the functions for defining derived axioms and optionally can
          // have modifiers and type annotations
          case q"$mods def $codeName(..$params): $tRet = $rhs" =>
            if (!isBelleExpr(c)(tRet))
              c.abort(c.enclosingPosition, "Invalid annottee: Expected def <tactic>(...): BelleExpr = ..., got: " + tRet + " " + tRet.getClass)
            val positions = getPositioning(c)(params)
            if (codeName.toString.exists(c => c =='\"'))
              c.abort(c.enclosingPosition, "Identifier " + codeName + " must not contain escape characters")
            // AST for literal strings for the names
            val codeString = Literal(Constant(codeName.decodedName.toString))
            // derivedAxiom functions allow an optional argument for the codeName, which we supply here
            // Tactic implementation of derived axiom is always useAt
            val expr = q"""({case () => $rhs})""" // : (Unit => Any)
            val dispLvl = displayLevel match {case "internal" => 'internal case "browse" => 'browse case "menu" => 'menu case "all" => 'all
              case s => c.abort(c.enclosingPosition, "Unknown display level " + s)}
            val info = positions match {
              case OnePos(pos, seq) => q"""PositionTacticInfo(codeName = $codeName, display = ${convDI(display)(c)}, theExpr = $expr, needsTool = $needsTool, needsGenerator = $needsGenerator, revealInternalSteps = $revealInternalSteps)"""
            }
            // Macro cannot introduce new statements or declarations, so introduce a library call which achieves our goal of registering
            // the axiom info to the global axiom info table
            val (application, rhsType) =
            positions match  {
              case OnePos(pos, seq) => (q"edu.cmu.cs.ls.keymaerax.macros.DerivationInfo.registerPositionTactic($rhs, $info)", tq"edu.cmu.cs.ls.keymaerax.bellerophon.DependentPositionTactic")
            }
            c.Expr[Nothing](q"""$mods val $codeName: $rhsType = $application""")
          case q"$mods def $declName(..$inputs)(..$params): $tRet = $rhs" => ???
          case q"$mods val $cName: $tpt = $functionName( ..$params )" => c.abort(c.enclosingPosition, "Expected derivedAxiom with 3 parameters, got:" + params.length)

        }
      case t => c.abort(c.enclosingPosition, "Invalid annottee: Expected val declaration got: " + t.head + " of type: " + t.head.getClass())
    }
  }
}
