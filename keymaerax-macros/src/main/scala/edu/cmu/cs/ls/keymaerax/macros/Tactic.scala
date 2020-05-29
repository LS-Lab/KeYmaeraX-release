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
    def macroTransform(annottees: Any*): Any = macro TacticImpl.apply
}

class TacticImpl(val c: whitebox.Context) {
  import c.universe._
  private trait PosArgs
  private case class OnePos(posName: ValDef, seqName: ValDef) extends PosArgs
  private case class TwoPos(provableName: ValDef, pos1Name: ValDef, pos2Name: ValDef) extends PosArgs
  private case class NoPos() extends PosArgs
  // Would just use PosInExpr but can't pull in core
  def apply(annottees: c.Expr[Any]*): c.Expr[Any] = {
    val paramNames = List("names", "formula", "premises", "conclusion", "displayLevel", "needsTool", "needsGenerator", "revealInternalSteps", "inputs")
    // Macro library does not allow directly passing arguments from annotation constructor to macro implementation.
    // Searching the prefix allows us to recover the arguments
    def getLiteral(t: Tree): String = {
      t match {
        case Literal(Constant(s: String)) => s
        case t => c.abort(c.enclosingPosition, "Expected string literal, got: " + t)
      }
    }
    def getBoolLiteral(t: Tree): Boolean = {
      t match {
        case Literal(Constant(s: Boolean)) => s
        case t => c.abort(c.enclosingPosition, "Expected string literal, got: " + t)
      }
    }
    def getParams: (DisplayInfo, List[ArgInfo], String, Boolean, Boolean, Boolean) = {
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
          val (fml, inputString,  displayLevel, premisesString, conclusionString, needsTool, needsGenerator, revealInternal) =
            (getLiteral(paramMap("formula")), getLiteral(paramMap("inputs")),
              getLiteral(paramMap("displayLevel")), getLiteral(paramMap("premises")), getLiteral(paramMap("conclusion")),
              getBoolLiteral(paramMap("needsTool")), getBoolLiteral(paramMap("needsGenerator")), getBoolLiteral(paramMap("revealInternalSteps")))
          val inputs: List[ArgInfo] = parseAIs(inputString)(c)
          val simpleDisplay = paramMap("names") match {
            case q"""(${Literal(Constant(sl: String))}, ${Literal(Constant(sr: String))})""" => SimpleDisplayInfo(sl, sr)
            case Literal(Constant(s: String)) => SimpleDisplayInfo(s, s)
            //case sdi: SimpleDisplayInfo => sdi
            case di => c.abort(c.enclosingPosition, "@Tactic expected names: String or names: (String, String) or names: SimpleDisplayInfo, got: " + di)
          }
          val displayInfo = (fml, inputs, premisesString, conclusionString) match {
            case ("", Nil, "", "") => simpleDisplay
            case (fml, Nil, "", "") if fml != "" => AxiomDisplayInfo(simpleDisplay, fml)
            case (fml, args, "", "") if fml != "" => InputAxiomDisplayInfo(simpleDisplay, fml, args)
            case (fml, args, _, _) if conclusionString != "" && premisesString != "" =>
              val (prem, conc) = (parseSequents(premisesString)(c), parseSequent(conclusionString)(c))
              RuleDisplayInfo(simpleDisplay, conc, prem)
            case _ => c.abort(c.enclosingPosition, "Unsupported argument combination for @Tactic: either specify premises and conclusion, or formula, not both")
          }
          (displayInfo, inputs, displayLevel, needsTool, needsGenerator, revealInternal)
        case e => c.abort(c.enclosingPosition, "Excepted @Tactic(args), got: " + e)
      }
    }
    // Return type of tactic definition should be BelleExpr
    def isBelleExpr(tRet: Tree): Boolean = {
      tRet match {
        case tq"BelleExpr" => true
        case _ => false
      }
    }
    // Scrape position argument info from declaration
    def getPositioning(params: Seq[Tree]): PosArgs = {
      params.toList match {
        // ValDef is also used for argument specifications
        case Nil => NoPos()
        case (posDef: ValDef) :: (seqDef: ValDef) :: Nil  =>
          (posDef.tpt, seqDef.tpt) match {
            case (tq"Position", tq"Sequent") => OnePos(posDef, seqDef)
            case params => c.abort(c.enclosingPosition, "Bad params: " + params)
          }
        case (provableDef: ValDef) :: (pos1Def: ValDef) :: (pos2Def: ValDef) :: Nil  =>
          (provableDef.tpt, pos1Def.tpt, pos2Def.tpt) match {
            case (tq"ProvableSig", tq"Position", tq"Position") => TwoPos(provableDef, pos1Def, pos2Def)
            case params => c.abort(c.enclosingPosition, "Bad params: " + params)
          }
        case params => c.abort(c.enclosingPosition, "Bad params: " + params.map(_.getClass).mkString(","))
      }
    }
    // Scrape argument info from declaration
    def getInput(param: c.universe.Tree): ArgInfo = {
      param match {
        case v: ValDef =>
          v.tpt match {
            case tq"""Formula""" => FormulaArg(v.name.decodedName.toString)
            case tq"""Expression""" => new ExpressionArg(v.name.decodedName.toString)
            case tq"""Term""" => new TermArg(v.name.decodedName.toString)
            case tq"""Number""" => NumberArg(v.name.decodedName.toString)
            case tq"""Variable""" => VariableArg(v.name.decodedName.toString)
            case tq"""String""" => StringArg(v.name.decodedName.toString)
            case tq"""Substitution""" => SubstitutionArg(v.name.decodedName.toString)
            case tq"""Option[$t]""" => new OptionArg(getInput(t))
            case tq"""List[$t]""" => new ListArg(v.name.decodedName.toString, getInput(t).name)
          }
      }
    }
    def getInputs(params: Seq[c.universe.Tree]): List[ArgInfo] = {
      params.toList.map(getInput)
    }
    val (display, _argInfoAnnotation, displayLevel, needsTool, needsGenerator, revealInternalSteps) = getParams
    // Scala types corresponding to tactic inputs
    // @TODO rename
    def typeName(ai: ArgInfo): Tree = {
      ai match {
        case _: FormulaArg => tq"edu.cmu.cs.ls.keymaerax.core.Formula"
        case _: StringArg => tq"String"
        case _: NumberArg => tq"edu.cmu.cs.ls.keymaerax.core.Number"
        case _: VariableArg => tq"edu.cmu.cs.ls.keymaerax.core.Variable"
        case _: TermArg => tq"edu.cmu.cs.ls.keymaerax.core.Term"
        case _: SubstitutionArg => tq"edu.cmu.cs.ls.keymaerax.core.Subst"
        case _: ExpressionArg => tq"edu.cmu.cs.ls.keymaerax.core.Expression"
      }
    }
    // Type and term ASTs which wrap acc in position and/or input arguments as anonymous lambdas
    def argue(funName: String, acc: Tree, pos: PosArgs, args: List[ArgInfo]): (Tree, Tree) = {
      val funStr = Literal(Constant(funName))
      val base: (Tree, Tree) =
        pos match {
          case NoPos() =>
            val expr = q"""new edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory ($funStr).by($funStr, $acc)"""
            val ty = tq"edu.cmu.cs.ls.keymaerax.bellerophon.DependentTactic"
            (expr, ty)
          case OnePos(pname, sname) =>
            // @TODO: Check whether TacticForNameFactory.by is fine or whether overloading caused an issue
            // byPosition is a wrapper for TacticForNameFactory.by
            val expr = q"""new edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory ($funStr).by(($pname, $sname) =>  $acc)"""
            val ty = tq"edu.cmu.cs.ls.keymaerax.bellerophon.DependentPositionTactic"
            (expr, ty)
          case TwoPos(provable, pos1, pos2) =>
            val expr = q"""new edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory ($funStr).by($funStr, (($provable, $pos1, $pos2) =>  $acc))"""
            val ty = tq"edu.cmu.cs.ls.keymaerax.bellerophon.DependentTwoPositionTactic"
            (expr, ty)
        }
      args.foldRight[(Tree, Tree)](base)({case (arg, (acc, accTy)) =>
        val name = arg match {
          case a: VariableArg => a.name case a: FormulaArg => a.name case n: NumberArg => n.name
          case a: StringArg => a.name case a: TermArg => a.name case a: SubstitutionArg => a.name
          case a: ExpressionArg => a.name
        }
        val argTy = typeName(arg)
        val funTy = tq"""edu.cmu.cs.ls.keymaerax.macros.TypedFunc[$argTy, $accTy]"""
        val vd = ValDef(Modifiers(), name, tq"""$argTy""", EmptyTree)
        if(vd.rhs.nonEmpty)
          c.abort(c.enclosingPosition, "Nonempty val")
        val term = q"""(($vd) => $acc): $funTy"""
        (term, funTy)})
    }
    def assemble(mods: Modifiers, codeName: TermName, inputs: List[ArgInfo], positions: PosArgs, rhs: Tree): c.Expr[Nothing] = {
      val underlyingCodeName = codeName.decodedName.toString
      if (codeName.toString.exists(c => c =='\"'))
        c.abort(c.enclosingPosition, "Identifier " + codeName + " must not contain escape characters")
      // AST for literal strings for the names
      val codeString = Literal(Constant(codeName.decodedName.toString))
      val (termTree, typeTree) = argue(underlyingCodeName, rhs, positions, inputs)
      val expr = q"""((_: Unit) => ($termTree))"""
      // @TODO: Add to info constructors
      val dispLvl = displayLevel match {case "internal" => 'internal case "browse" => 'browse case "menu" => 'menu case "all" => 'all
      case s => c.abort(c.enclosingPosition, "Unknown display level " + s)}
      val (info, rhsType) = (inputs, positions) match {
        case (Nil, _: NoPos) => (q"""new edu.cmu.cs.ls.keymaerax.macros.TacticInfo(codeName = $codeString, display = ${convDI(display)(c)}, theExpr = $expr, needsTool = $needsTool, needsGenerator = $needsGenerator, revealInternalSteps = $revealInternalSteps)""", tq"""edu.cmu.cs.ls.keymaerax.bellerophon.DependentTactic""")
        case (Nil, _: OnePos) => (q"""new edu.cmu.cs.ls.keymaerax.macros.PositionTacticInfo(codeName = $codeString, display = ${convDI(display)(c)}, theExpr = $expr, needsTool = $needsTool, needsGenerator = $needsGenerator, revealInternalSteps = $revealInternalSteps)""", tq"""edu.cmu.cs.ls.keymaerax.bellerophon.DependentPositionTactic""")
        case (Nil, _: TwoPos) => (q"""new edu.cmu.cs.ls.keymaerax.macros.TwoPositionTacticInfo(codeName = $codeString, display = ${convDI(display)(c)}, theExpr = $expr, needsTool = $needsTool, needsGenerator = $needsGenerator)""", tq"""edu.cmu.cs.ls.keymaerax.bellerophon.DependentTwoPositionTactic""")
        case (_, _: NoPos) => (q"""new edu.cmu.cs.ls.keymaerax.macros.InputTacticInfo(codeName = $codeString, display = ${convDI(display)(c)}, inputs = ${convAIs(inputs)(c)}, theExpr = $expr, needsTool = $needsTool, needsGenerator = $needsGenerator, revealInternalSteps = $revealInternalSteps)""", typeTree)
        case (_, _: OnePos) => (q"""new edu.cmu.cs.ls.keymaerax.macros.InputPositionTacticInfo(codeName = $codeString, display = ${convDI(display)(c)}, inputs = ${convAIs(inputs)(c)}, theExpr = $expr, needsTool = $needsTool, needsGenerator = $needsGenerator, revealInternalSteps = $revealInternalSteps)""", typeTree)
        case (_, _: TwoPos) => (q"""new edu.cmu.cs.ls.keymaerax.macros.InputTwoPositionTacticInfo(codeName = $codeString, display = ${convDI(display)(c)}, inputs = ${convAIs(inputs)(c)}, theExpr = $expr, needsTool = $needsTool, needsGenerator = $needsGenerator)""", typeTree)
      }
      // Macro cannot introduce new statements or declarations, so introduce a library call which achieves our goal of registering
      // the tactic info to the global derivation info table
      val application = q"""edu.cmu.cs.ls.keymaerax.macros.DerivationInfo.registerL($termTree, $info)"""
      c.Expr[Nothing](q"""$mods val $codeName: $rhsType = $application """)
    }
    annottees map (_.tree) toList match {
      // Annottee must be a def declaration of an tactic
      case (defDecl: DefDef) :: Nil =>
        defDecl match {
          // def has parameters for positions and/or inputs, and may have a return type
          case q"$mods def ${codeName: TermName}(..$inArgs)(..$params): $tRet = $rhs" =>
            if (!isBelleExpr(tRet))
              c.abort(c.enclosingPosition, "Invalid annottee: Expected def <tactic>(...): BelleExpr = ..., got: " + tRet + " " + tRet.getClass)
            val positions = getPositioning(params)
            val inputs = getInputs(inArgs)
            assemble(mods, codeName, inputs, positions, rhs)
          case q"$mods def ${codeName: TermName}(..$params): $tRet = $rhs" =>
            if (!isBelleExpr(tRet))
              c.abort(c.enclosingPosition, "Invalid annottee: Expected def <tactic>(...): BelleExpr = ..., got: " + tRet + " " + tRet.getClass)
            val positions = getPositioning(params)
            val inputs = positions match { case NoPos() => getInputs(params) case _ => Nil}
            assemble(mods, codeName, inputs, positions, rhs)
          case q"$mods val $cName: $tpt = $functionName( ..$params )" => c.abort(c.enclosingPosition, "Expected def of tactic, got:" + params.length)
        }
      case t => c.abort(c.enclosingPosition, "Invalid annottee: Expected val declaration got: " + t.head + " of type: " + t.head.getClass())
    }
  }
}