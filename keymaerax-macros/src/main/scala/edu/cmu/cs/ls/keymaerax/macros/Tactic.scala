package edu.cmu.cs.ls.keymaerax.macros

import scala.annotation.StaticAnnotation
import scala.collection.immutable.Nil
import scala.language.experimental.macros
import scala.reflect.macros.{Universe, whitebox}
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
    // Annotation is implemented a macro; this is a necessary, reserved magic invocation which says Tactic.impl is the macro body
    def macroTransform(annottees: Any*): Any = macro Tactic.impl
}

// Case class representing positional argument type annotations from tactic definition.
// @TODO: Additional constructors for multiple positions and zero positions
private case class OnePos[u <: Universe](posName: u#ValDef, seqName: u#ValDef)


object Tactic {
  // Would just use PosInExpr but can't pull in core
  def impl(c: whitebox.Context)(annottees: c.Expr[Any]*): c.Expr[Any] = {
    val u = c.universe
    val paramNames = List("names", "formula", "premises", "conclusion", "displayLevel", "needsTool", "needsGenerator", "revealInternalSteps", "inputs")
    // Macro library does not allow directly passing arguments from annotation constructor to macro implementation.
    // Searching the prefix allows us to recover the arguments
    def getParams(implicit c: whitebox.Context): (DisplayInfo, List[ArgInfo], String, Boolean, Boolean, Boolean) = {
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
          val (idx, _wereNamed, paramMap) = params.foldLeft((0, false, defaultMap))({case (acc, x) => foldParams(c, paramNames)(acc, x)})
          val (displayObj, fml: String, premisesString: String, conclusionString: String, displayLevel: String, needsTool: Boolean, needsString: Boolean, revealInternalSteps: Boolean, inputString: String)
          = (c.eval[(Any, String, String, String, String, Boolean, Boolean, Boolean, String)](c.Expr
          (q"""(${paramMap("names")}, ${paramMap("formula")}, ${paramMap("premises")}, ${paramMap("conclusion")}, ${paramMap("displayLevel")},
               ${paramMap("needsTool")}, ${paramMap("needsGenerator")}, ${paramMap("revealInternalSteps")}, ${paramMap("inputs")})""")))
          val inputs: List[ArgInfo] = parseAIs(inputString)(c)
          val simpleDisplay = displayObj match {
            case s: String => SimpleDisplayInfo(s, s)
            case (sl: String, sr: String) => SimpleDisplayInfo(sl, sr)
            case sdi: SimpleDisplayInfo => sdi
            case di => c.abort(c.enclosingPosition, "@Tactic expected names: String or names: (String, String) or names: SimpleDisplayInfo, got: " + di)
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
          (displayInfo, inputs, displayLevel, needsTool, needsString, revealInternalSteps)
        case e => c.abort(c.enclosingPosition, "Excepted @Tactic(args), got: " + e)
      }
    }
    // Return type of tactic definition should be BelleExpr
    def isBelleExpr(c: whitebox.Context)(tRet: c.universe.Tree): Boolean = {
      import c.universe._
      tRet match {
        case tq"BelleExpr" => true
        case _ => false
      }
    }
    // Scrape position argument info from declaration
    def getPositioning(c: whitebox.Context)(params: Seq[c.universe.Tree]): OnePos[c.universe.type] = {
      import c.universe._
      params.toList match {
        // ValDef is also used for argument specifications
        case (posDef: ValDef) :: (seqDef: ValDef) :: Nil  =>
          (posDef.tpt, seqDef.tpt) match {
            case (tq"Position", tq"Sequent") => OnePos(posDef, seqDef)
            case params => c.abort(c.enclosingPosition, "Bad params: " + params)
          }
        case params => c.abort(c.enclosingPosition, "Bad params: " + params.map(_.getClass).mkString(","))
      }
    }
    val (display, args, displayLevel, needsTool, needsGenerator, revealInternalSteps) = getParams(c)
    import c.universe._
    // Scala types corresponding to tactic inputs
    def typeName(ai: ArgInfo): String = {
      ai match {
        case _: FormulaArg => "Formula"
        case _: StringArg => "String"
        case _: NumberArg => "Number"
        case _: VariableArg => "Variable"
      }
    }
    // Type and term ASTs which wrap acc in position and/or input arguments as anonymous lambdas
    def argue(funName: String, acc: Tree, pos: OnePos[c.universe.type], args: List[ArgInfo]): (Tree, Tree) = {
      val funStr = Literal(Constant(funName))
      val base: (Tree, Tree) =
        pos match {
          case OnePos(pname, sname) =>
            // @TODO: Check whether TacticForNameFactory.by is fine or whether overloading caused an issue
            // byPosition is a wrapper for TacticForNameFactory.by
            val expr = q"""edu.cmu.cs.ls.keymaerax.btactics.DerivationInfoAugmentors.byPosition($funStr, (($pname, $sname) =>  $acc))"""
            val ty = tq"edu.cmu.cs.ls.keymaerax.bellerophon.DependentPositionTactic"
            (expr, ty)
        }
      args.foldRight[(Tree, Tree)](base)({case (arg, (acc, accTy)) =>
        val name = arg match {
          case a: VariableArg => a.name case a: FormulaArg => a.name case n: NumberArg => n.name
          case a: StringArg => a.name
        }
        val argTy = typeName(arg)
        val funTy = tq"""TypedFunc[$argTy, $accTy]"""
        val term = q"""(($name: $argTy) => $acc): $funTy"""
        (term, funTy)})
    }
    annottees map (_.tree) toList match {
      // Annottee must be a def declaration of an tactic
      case (defDecl: DefDef) :: Nil =>
        defDecl match {
          // def has parameters for positions and/or inputs, and may have a return type
          case q"$mods def $codeName(..$params): $tRet = $rhs" =>
            val underlyingCodeName = codeName.asInstanceOf[TermName].decodedName.toString
            if (!isBelleExpr(c)(tRet))
              c.abort(c.enclosingPosition, "Invalid annottee: Expected def <tactic>(...): BelleExpr = ..., got: " + tRet + " " + tRet.getClass)
            val positions = getPositioning(c)(params)
            if (codeName.toString.exists(c => c =='\"'))
              c.abort(c.enclosingPosition, "Identifier " + codeName + " must not contain escape characters")
            // AST for literal strings for the names
            val codeString = Literal(Constant(codeName.decodedName.toString))
            val (termTree, typeTree) = argue(underlyingCodeName, rhs, positions, args)
            val expr = q"""((_: Unit) => ($termTree))"""
            // @TODO: Add to info constructors
            val dispLvl = displayLevel match {case "internal" => 'internal case "browse" => 'browse case "menu" => 'menu case "all" => 'all
              case s => c.abort(c.enclosingPosition, "Unknown display level " + s)}
            val info = positions match {
              case OnePos(pos, seq) => q"""new edu.cmu.cs.ls.keymaerax.macros.PositionTacticInfo(codeName = $codeString, display = ${convDI(display)(c)}, theExpr = $expr, needsTool = $needsTool, needsGenerator = $needsGenerator, revealInternalSteps = $revealInternalSteps)"""
            }
            // Macro cannot introduce new statements or declarations, so introduce a library call which achieves our goal of registering
            // the tactic info to the global derivation info table
            val (application, rhsType) =
              positions match  {
                case OnePos(pos, seq) => (q"""edu.cmu.cs.ls.keymaerax.macros.DerivationInfo.registerPositionTactic($termTree, $info)""", tq"""(edu.cmu.cs.ls.keymaerax.bellerophon.DependentPositionTactic)""")
              }
            c.Expr[Nothing](q"""$mods val $codeName: $rhsType = $application """) // $rhsType //
          case q"$mods def $declName(..$inputs)(..$params): $tRet = $rhs" => ???
          case q"$mods val $cName: $tpt = $functionName( ..$params )" => c.abort(c.enclosingPosition, "Expected def of tactic, got:" + params.length)
        }
      case t => c.abort(c.enclosingPosition, "Invalid annottee: Expected val declaration got: " + t.head + " of type: " + t.head.getClass())
    }
  }
}
