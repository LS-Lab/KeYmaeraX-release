package edu.cmu.cs.ls.keymaerax.macros

import scala.annotation.StaticAnnotation
import scala.collection.immutable.Nil
import scala.language.experimental.macros
import scala.reflect.macros.{Universe, blackbox}
import AnnotationCommon._

/**
* @param names Display names to render in the user interface.
* @param codeName You should avoid using this argument. Permanent unique code name used to invoke this axiom in tactics as a string and for Lemma storage.
*                 `codeName`` will be inferred from the val that is annotated by this `@Axiom` and is strongly recommended to be identical to it.
* @param inputs Display input information for non-positioning arguments, e.g., "C:Formula" for cut.
*               Arguments are separated with ;; and allowed fresh variables are given in square brackets, for example
*               E[y,x,y']:Formula;; P[y]:Formula are the arguments to tactic dG.
*               By default, this argument is inferred from the argument types and names of the annotated [[def]].
*               Use this argument when you want customized display on the UI or when there are allowedFresh variables.
 *              Supported types: Expression, Formula, Term, Variable, Number, String, Substitution, List[], Option[]
* @param premises String of premises when (if) the tactic is displayed like a rule on the UI.
*                 For tactics with (non-position) inputs, the premises or conclusion must mention each input.
*                 The name of each input is given in [[inputs]], which may be generated from the [[def]].
*                 Premises are separated by ;; and each premise is optionally a sequent.  "P;; A, B |- C" specifies two
*                 premises, the latter of which is a sequent with two assumptions. An asterisk "*" indicates a tactic that
*                 closes a branch.
* @param conclusion Conclusion of rule displayed on UI. Axiom-like tactics have a conclusion and no premises.
 *                  Tactics with premises must have conclusions.
*                   For tactics with (non-position) inputs, the premises or conclusion must mention each input.
*                   The name of each input is given in [[inputs]], which may be generated from the [[def]].
*                   Sequent syntax is optionally supported:   A, B |- C, D
* @param displayLevel Where to show the tactic: "internal" (not on UI at all), "browse", "menu", "all" (on UI everywhere)
* @param needsGenerator Does the tactic use invariant formula generators such as the @invariant annotation in .kyx files?
 *                       Used for a small number of tactics such as master.
* @param revealInternalSteps Does the Web UI allow stepping inside this tactic?
*/
class Tactic(val names: Any = false, /* false is a sigil value, user value should be string, strings, or displayinfo*/
             val codeName: String = "",
             val premises: String = "",
             val conclusion: String = "",
             val displayLevel: String = "internal",
             val needsGenerator: Boolean = false,
             val revealInternalSteps: Boolean = false,
             val inputs:String = ""
           ) extends StaticAnnotation {
    // Annotation is implemented a macro; this is a necessary, reserved magic invocation which says Tactic.impl is the macro body
    def macroTransform(annottees: Any*): Any = macro TacticImpl.apply
}

class TacticImpl(val c: blackbox.Context) {
  import c.universe._
  private trait PosArgs
  private case class AntePos(provableName: ValDef, posName: ValDef) extends PosArgs
  private case class SuccPos(provableName: ValDef, posName: ValDef) extends PosArgs
  /** Arguments are Position, (Position, Sequent), or (ProvableSig, Position). In the latter case, useProvable = true*/
  private case class OnePos(lname: ValDef, rname: Option[ValDef], useProvable: Boolean = false) extends PosArgs
  private case class TwoPos(provableName: ValDef, pos1Name: ValDef, pos2Name: ValDef) extends PosArgs
  private case class SequentArg(sequentName: ValDef) extends PosArgs
  private case class NoPos() extends PosArgs
  // Would just use PosInExpr but can't pull in core
  def apply(annottees: c.Expr[Any]*): c.Expr[Any] = {
    val paramNames = List("names", "codeName", "premises", "conclusion", "displayLevel", "needsGenerator", "revealInternalSteps", "inputs")
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
    def paramify(tn: TermName, params: Seq[Tree]): (String, DisplayInfo, List[ArgInfo], String, Boolean) = {
      val defaultMap: Map[String, Tree] = Map(
        "names"    -> Literal(Constant(false)),
        "codeName" -> Literal(Constant("")),
        "premises" -> Literal(Constant("")),
        "conclusion" -> Literal(Constant("")),
        "displayLevel" -> Literal(Constant("internal")),
        "revealInternalSteps" -> Literal(Constant(false)),
        "inputs" -> Literal(Constant(""))
      )
      val (idx, _wereNamed, paramMap) = params.foldLeft((0, false, defaultMap))({case (acc, x) => foldParams(c, paramNames)(acc, x)})
      val (inputString, displayLevel, premisesString, conclusionString, revealInternal) =
        (getLiteral(paramMap("inputs")), getLiteral(paramMap("displayLevel")), getLiteral(paramMap("premises")), getLiteral(paramMap("conclusion")),
           getBoolLiteral(paramMap("revealInternalSteps")))
      val inputs: List[ArgInfo] = parseAIs(inputString)(c)
      val codeName: String = paramMap("codeName") match {
        case Literal(Constant("")) => tn.decodedName.toString
        case Literal(Constant(s: String)) => s
        case t => c.abort(c.enclosingPosition, "Expected codeName to be a string literal, got: " + t)
      }
      val simpleDisplay = paramMap("names") match {
        case q"""(${Literal(Constant(sl: String))}, ${Literal(Constant(sr: String))})""" => SimpleDisplayInfo(sl, sr)
        case Literal(Constant(s: String)) => SimpleDisplayInfo(s, s)
        case Literal(Constant(false)) => {
          val s = codeName
          SimpleDisplayInfo(s, s)
        }
        //case sdi: SimpleDisplayInfo => sdi
        case di => c.abort(c.enclosingPosition, "@Tactic expected names: String or names: (String, String) or names: SimpleDisplayInfo, got: " + di)
      }
      val displayInfo = (inputs, premisesString, conclusionString) match {
        case (Nil, "", "") => simpleDisplay
        case (Nil, "", concl) if concl != "" => AxiomDisplayInfo(simpleDisplay, concl)
        case (ins, prem, concl) if concl != "" => InputAxiomDisplayInfo(simpleDisplay, concl, inputs)
        case (ins, prem, concl) if concl != "" && prem != "" =>
          val (prem, conc) = (parseSequents(premisesString)(c), parseSequent(conclusionString)(c))
          RuleDisplayInfo(simpleDisplay, conc, prem)
        case (_, "", "") => SimpleDisplayInfo(codeName, codeName)
        case _ => c.abort(c.enclosingPosition, "Unsupported argument combination for @Tactic: If premises or inputs are given, conclusion must be given")
      }
      (codeName, displayInfo, inputs, displayLevel, revealInternal)
    }
    def getParams (tn: TermName): (String, DisplayInfo, List[ArgInfo], String, Boolean) = {
        c.prefix.tree match {
        case q"new $annotation(..$params)" => paramify(tn, params)
        case q"new $annotation()" => paramify(tn, Nil)
        case e => c.abort(c.enclosingPosition, "Excepted @Tactic(args), got: " + e)
      }
    }
    // Return type of tactic definition
    def isTactic(tRet: Tree): Boolean = {
      tRet match {
        case tq"DependentTactic" | tq"DependentPositionTactic" | tq"InputPositionTactic"
             | tq"BuiltInLeftTactic" | tq"BuiltInRightTactic"
             | tq"CoreLeftTactic" | tq"CoreRightTactic"
             | tq"BuiltInTwoPositionTactic" | tq"InputTwoPositionTactic" | tq"InputTactic"
             | tq"DependentPositionWithAppliedInputTactic"
             | tq"AppliedBuiltInTwoPositionTactic"
             | tq"BelleExpr" => true
        case _ => false
      }
    }
    // Return type of tactic definition
    def isValTactic(tRet: Tree): Boolean = {
      tRet match {
        case tq"BelleExpr" | tq"InputTactic" => true
        case _ => false
      }
    }
    // Scrape position argument info from declaration
    def getPositioning(params: Seq[Tree]): PosArgs = {
      val supportedArgs = "Unit, Position, Sequent, (Position, Sequent), or (ProvableSig, Position, Position)"
      params.toList match {
        // ValDef is also used for argument specifications
        case Nil => NoPos()
        case (posDef: ValDef) :: Nil =>
          posDef.tpt match {
            case (tq"Position") => OnePos(posDef, None)
            case (tq"Sequent") => SequentArg(posDef)
            case params => c.abort(c.enclosingPosition, s"Positioning arguments must be $supportedArgs, got: $params")
          }
        case (ldef: ValDef) :: (rdef: ValDef) :: Nil  =>
          (ldef.tpt, rdef.tpt) match {
            case (tq"Position", tq"Sequent") => OnePos(ldef, Some(rdef))
            case (tq"ProvableSig", tq"Position") => OnePos(ldef, Some(rdef), useProvable = true)
            case (tq"ProvableSig", tq"AntePosition") => AntePos(ldef, rdef)
            case (tq"ProvableSig", tq"SuccPosition") => SuccPos(ldef, rdef)
            case params => c.abort(c.enclosingPosition, s"Positioning arguments must be $supportedArgs, got: $params")
          }
        case (provableDef: ValDef) :: (pos1Def: ValDef) :: (pos2Def: ValDef) :: Nil  =>
          (provableDef.tpt, pos1Def.tpt, pos2Def.tpt) match {
            case (tq"ProvableSig", tq"Position", tq"Position") => TwoPos(provableDef, pos1Def, pos2Def)
            case params => c.abort(c.enclosingPosition, s"Positioning arguments must be $supportedArgs, got: $params")
          }
        case params => c.abort(c.enclosingPosition, s"Positioning arguments must be $supportedArgs, got: ${params.map(_.getClass).mkString(",")}")
      }
    }
    // Scrape argument info from declaration
    def getInput(param: Tree): ArgInfo = {
      param match {
        case v: ValDef =>
          v.tpt match {
            case tq"""Generator[GenProduct]""" => GeneratorArg(v.name.decodedName.toString)
            case tq"""Formula""" => FormulaArg(v.name.decodedName.toString)
            case tq"""Expression""" => new ExpressionArg(v.name.decodedName.toString)
            case tq"""Term""" => new TermArg(v.name.decodedName.toString)
            case tq"""Number""" => NumberArg(v.name.decodedName.toString)
            case tq"""Variable""" => VariableArg(v.name.decodedName.toString)
            case tq"""String""" => StringArg(v.name.decodedName.toString)
            case tq"""PosInExpr""" => PosInExprArg(v.name.decodedName.toString)
            case tq"""Substitution""" => SubstitutionArg(v.name.decodedName.toString)
            case tq"""Option[$t]""" =>
              val vd = ValDef(v.mods, v.name, t, v.rhs)
              new OptionArg(getInput(vd))
            case tq"""List[$t]""" =>
              val vd = ValDef(v.mods, v.name, t, v.rhs)
              new ListArg(v.name.decodedName.toString, getInput(vd).name)
            case t => c.abort(c.enclosingPosition, "Expected supported input type in tactic definition, got unsupported type: " + t)
          }
      }
    }
    def getInputs(params: Seq[Tree]): (Option[ArgInfo], List[ArgInfo]) = {
      val infos = params.toList.map(getInput)
      val gen = infos.find((ai: ArgInfo) => ai match {case _: GeneratorArg => true case _ => false})
      if (infos.nonEmpty && infos.dropRight(1).contains((ai: ArgInfo) => ai match {case _: GeneratorArg => true case _ => false})) {
        c.abort(c.enclosingPosition, "Generator argument to tactic must appear after all expression arguments")
      }
      (gen, infos)
    }
    // Scala types corresponding to tactic inputs
    def typeName(ai: ArgInfo): Tree = {
      ai match {
        case _: GeneratorArg => tq"edu.cmu.cs.ls.keymaerax.btactics.Generator.Generator[edu.cmu.cs.ls.keymaerax.btactics.InvariantGenerator.GenProduct]"
        case _: FormulaArg => tq"edu.cmu.cs.ls.keymaerax.core.Formula"
        case _: StringArg => tq"String"
        case _: NumberArg => tq"edu.cmu.cs.ls.keymaerax.core.Number"
        case _: VariableArg => tq"edu.cmu.cs.ls.keymaerax.core.Variable"
        case _: TermArg => tq"edu.cmu.cs.ls.keymaerax.core.Term"
        case _: SubstitutionArg => tq"edu.cmu.cs.ls.keymaerax.core.Subst"
        case _: ExpressionArg => tq"edu.cmu.cs.ls.keymaerax.core.Expression"
        case _: PosInExprArg => tq"edu.cmu.cs.ls.keymaerax.infrastruct.PosInExpr"
        case OptionArg(ai) => tq"scala.Option[${typeName(ai)}]"
        case ListArg(name, elementSort, allowsFresh) =>
          c.abort(c.enclosingPosition, "List arguments in tactics not yet supported")
        case ai => c.abort(c.enclosingPosition, "Unimplemented case in @Tactic, could not convert argument spec: " + ai)
      }
    }
    // Type and term ASTs which wrap acc in position and/or input arguments as anonymous lambdas
    def argue(funName: String, acc: Tree, pos: PosArgs, args: List[ArgInfo], generatorOpt: Option[ArgInfo], isCoreAnon: Boolean): (Tree, Seq[ValDef], Seq[Tree], (Tree, Tree)) = {
      val funStr = Literal(Constant(funName))
      val argExpr = args match {
        case Nil => q"Nil"
        case _ => args.foldRight[Tree](q"Nil")({case (ai, acc) => q"${ai.name} :: $acc"})
      }
      val base: (Tree, Tree) =
        pos match {
          case NoPos() =>
              if(args.isEmpty)
                // @TODO: acc could be DEpendentTactic or BelleExpr
                (q"""new edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory ($funStr).by($acc)""", tq"edu.cmu.cs.ls.keymaerax.bellerophon.BelleExpr")
              else
                (q"""new edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory ($funStr).byWithInputs($argExpr, $acc)""", tq"edu.cmu.cs.ls.keymaerax.bellerophon.InputTactic")
          case SequentArg(sequentName) =>
            if(args.isEmpty) {
              (q"""new edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory ($funStr).by(($sequentName) => $acc)""", tq"edu.cmu.cs.ls.keymaerax.bellerophon.DependentTactic")
            } else {
              (q"""new edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory ($funStr).byWithInputs($argExpr, ($sequentName) => $acc)""", tq"edu.cmu.cs.ls.keymaerax.bellerophon.InputTactic")
            }
          case OnePos(pname, None, _) =>
            if(args.isEmpty)
              (q"""new edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory ($funStr).by(($pname) =>  $acc)""",tq"edu.cmu.cs.ls.keymaerax.bellerophon.DependentPositionTactic")
            else
              (q"""new edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory ($funStr).byWithInputs($argExpr, ($pname) =>  $acc)""", tq"edu.cmu.cs.ls.keymaerax.bellerophon.DependentPositionWithAppliedInputTactic")
          case OnePos(pname, Some(sname), provable) =>
              if(args.isEmpty)
                (q"""new edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory ($funStr).by(($pname, $sname) =>  $acc)""",tq"edu.cmu.cs.ls.keymaerax.bellerophon.DependentPositionTactic")
              else if (provable) {
                (q"""new edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory ($funStr).byWithInputsP($argExpr, ($pname, $sname) =>  $acc)""", tq"edu.cmu.cs.ls.keymaerax.bellerophon.DependentPositionWithAppliedInputTactic")
              } else
                (q"""new edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory ($funStr).byWithInputs($argExpr, ($pname, $sname) =>  $acc)""", tq"edu.cmu.cs.ls.keymaerax.bellerophon.DependentPositionWithAppliedInputTactic")
          case AntePos(sname, pname) =>
            if (args.isEmpty) {
              if (isCoreAnon) {
                (q"""new edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory ($funStr).coreby(($sname, $pname) =>  $acc)""", tq"edu.cmu.cs.ls.keymaerax.bellerophon.CoreLeftTactic")
              } else
                (q"""new edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory ($funStr).by(($sname, $pname) =>  $acc)""", tq"edu.cmu.cs.ls.keymaerax.bellerophon.BuiltInLeftTactic")
            }
            else {
              if (isCoreAnon) {
                (q"""new edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory ($funStr).corebyWithInputsL($argExpr, ($sname, $pname) =>  $acc)""",tq"edu.cmu.cs.ls.keymaerax.bellerophon.DependentPositionWithAppliedInputTactic")
              } else {
                (q"""new edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory ($funStr).corebyWithInputsL($argExpr, ($sname, $pname) =>  $acc)""",tq"edu.cmu.cs.ls.keymaerax.bellerophon.DependentPositionWithAppliedInputTactic")
              }
            }
          case SuccPos(sname, pname) =>
            if(args.isEmpty) {
              if (isCoreAnon)
                (q"""new edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory ($funStr).coreby(($sname, $pname) =>  $acc)""",tq"edu.cmu.cs.ls.keymaerax.bellerophon.CoreRightTactic")
              else
                (q"""new edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory ($funStr).by(($sname, $pname) =>  $acc)""",tq"edu.cmu.cs.ls.keymaerax.bellerophon.BuiltInRightTactic")
            } else {
              if (isCoreAnon) {
                (q"""new edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory ($funStr).corebywithInputsR($argExpr, ($sname, $pname) =>  $acc)""",tq"edu.cmu.cs.ls.keymaerax.bellerophon.DependentPositionWithAppliedInputTactic")
              } else {
                (q"""new edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory ($funStr).corebyWithInputsR($argExpr, ($sname, $pname) =>  $acc)""",tq"edu.cmu.cs.ls.keymaerax.bellerophon.DependentPositionWithAppliedInputTactic")
              }
            }
          case TwoPos(provable, pos1, pos2) =>
              if(args.isEmpty)
                (q"""new edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory ($funStr).by((($provable, $pos1, $pos2) =>  $acc))""", tq"edu.cmu.cs.ls.keymaerax.bellerophon.BuiltInTwoPositionTactic")
              else
                (q"""new edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory ($funStr).byWithInputs($argExpr, (($provable, $pos1, $pos2) =>  $acc))""", tq"edu.cmu.cs.ls.keymaerax.bellerophon.AppliedBuiltInTwoPositionTactic")
          case t => c.abort(c.enclosingPosition, s"Unsupported argument combination in @Tactic: $args; $pos")
      }
      def aiToVal(ai: ArgInfo): ValDef = {
        val name = ai.name
        val argTy = typeName(ai)
        ValDef(Modifiers(), name, tq"""$argTy""", EmptyTree)
      }
      val (curried, typeTree) = args.foldRight[(Tree, Tree)](base)({case (arg, (acc, accTy)) =>
        val argTy = typeName(arg)
        val funTy = tq"""edu.cmu.cs.ls.keymaerax.macros.TypedFunc[$argTy, $accTy]"""
        val vd = aiToVal(arg)
        if(vd.rhs.nonEmpty)
          c.abort(c.enclosingPosition, "Nonempty val")
        val term =
          q"""(($vd) => $acc): $funTy"""
        (term, funTy)})
      val argSeq: Seq[ValDef] = args.map(aiToVal)
      val argTySeq: Seq[Tree] = argSeq.map(_.tpt)
      (curried, argSeq, argTySeq, base)
    }
    def assemble(mods: Modifiers, declName: TermName, inArgs: Seq[Tree], positions: PosArgs, rhs: Tree, isDef: Boolean
                , isCoreAnon: Boolean): c.Expr[Any] = {
      val (codeName, display, _argInfoAnnotation, displayLevel, revealInternalSteps) = getParams(declName)
      val (generatorOpt, inputs) = getInputs(inArgs)
      val needsGenerator = generatorOpt.isDefined
      if (codeName.exists(c => c =='\"'))
        c.abort(c.enclosingPosition, "Identifier " + codeName + " must not contain escape characters")
      // AST for literal strings for the names
      val codeString = Literal(Constant(codeName))

      val (curriedTermTree, argSeq, argTySeq, (base, baseType)) = argue(codeName, rhs, positions, inputs, generatorOpt, isCoreAnon)

      val expr = q"""((_: Unit) => ($curriedTermTree))"""
      // @TODO: Add to info constructors
      val dispLvl = displayLevel match {case "internal" => 'internal case "browse" => 'browse case "menu" => 'menu case "all" => 'all
        case s => c.abort(c.enclosingPosition, "Unknown display level " + s)}
      val (info, rhsType) = (inputs, positions) match {
          // @TODO: BElleExpr or DependentTActic
        case (Nil, _: NoPos) => (q"""new edu.cmu.cs.ls.keymaerax.macros.TacticInfo(codeName = $codeString, display = ${convDI(display)(c)}, theExpr = $expr, needsGenerator = $needsGenerator, revealInternalSteps = $revealInternalSteps)""", tq"""edu.cmu.cs.ls.keymaerax.bellerophon.BelleExpr""")
        case (Nil, _: SequentArg) => (q"""new edu.cmu.cs.ls.keymaerax.macros.TacticInfo(codeName = $codeString, display = ${convDI(display)(c)}, theExpr = $expr, needsGenerator = $needsGenerator, revealInternalSteps = $revealInternalSteps)""", tq"""edu.cmu.cs.ls.keymaerax.bellerophon.DependentTactic""")
        case (Nil, _: OnePos) => (q"""new edu.cmu.cs.ls.keymaerax.macros.PositionTacticInfo(codeName = $codeString, display = ${convDI(display)(c)}, theExpr = $expr, needsGenerator = $needsGenerator, revealInternalSteps = $revealInternalSteps)""", tq"""edu.cmu.cs.ls.keymaerax.bellerophon.DependentPositionTactic""")
        case (Nil, _: AntePos) =>
          val r =
            if(isCoreAnon) tq"""edu.cmu.cs.ls.keymaerax.bellerophon.CoreLeftTactic"""
            else tq"""edu.cmu.cs.ls.keymaerax.bellerophon.BuiltInLeftTactic"""
          (q"""new edu.cmu.cs.ls.keymaerax.macros.PositionTacticInfo(codeName = $codeString, display = ${convDI(display)(c)}, theExpr = $expr, needsGenerator = $needsGenerator, revealInternalSteps = $revealInternalSteps)""", r)
        case (Nil, _: SuccPos) =>
          val r =
            if(isCoreAnon) tq"""edu.cmu.cs.ls.keymaerax.bellerophon.CoreRightTactic"""
            else  tq"""edu.cmu.cs.ls.keymaerax.bellerophon.BuiltInRightTactic"""
          (q"""new edu.cmu.cs.ls.keymaerax.macros.PositionTacticInfo(codeName = $codeString, display = ${convDI(display)(c)}, theExpr = $expr, needsGenerator = $needsGenerator, revealInternalSteps = $revealInternalSteps)""", r)
        case (Nil, _: TwoPos) => (q"""new edu.cmu.cs.ls.keymaerax.macros.TwoPositionTacticInfo(codeName = $codeString, display = ${convDI(display)(c)}, theExpr = $expr, needsGenerator = $needsGenerator)""", tq"""edu.cmu.cs.ls.keymaerax.bellerophon.BuiltInTwoPositionTactic""")
        case (_, _: NoPos) => (q"""new edu.cmu.cs.ls.keymaerax.macros.InputTacticInfo(codeName = $codeString, display = ${convDI(display)(c)}, inputs = ${convAIs(inputs)(c)}, theExpr = $expr,  needsGenerator = $needsGenerator, revealInternalSteps = $revealInternalSteps)""", tq"""edu.cmu.cs.ls.keymaerax.bellerophon.InputTactic""")
        case (_, _: SequentArg) => (q"""new edu.cmu.cs.ls.keymaerax.macros.TacticInfo(codeName = $codeString, display = ${convDI(display)(c)}, theExpr = $expr, needsGenerator = $needsGenerator, revealInternalSteps = $revealInternalSteps)""", tq"""edu.cmu.cs.ls.keymaerax.bellerophon.InputTactic""")
        case (_, _: OnePos) => (q"""new edu.cmu.cs.ls.keymaerax.macros.InputPositionTacticInfo(codeName = $codeString, display = ${convDI(display)(c)}, inputs = ${convAIs(inputs)(c)}, theExpr = $expr, needsGenerator = $needsGenerator, revealInternalSteps = $revealInternalSteps)""", tq"""edu.cmu.cs.ls.keymaerax.bellerophon.DependentPositionWithAppliedInputTactic""")
        case (_, _: AntePos) =>
          val r = tq"edu.cmu.cs.ls.keymaerax.bellerophon.DependentPositionWithAppliedInputTactic"
          (q"""new edu.cmu.cs.ls.keymaerax.macros.PositionTacticInfo(codeName = $codeString, display = ${convDI(display)(c)}, theExpr = $expr, needsGenerator = $needsGenerator, revealInternalSteps = $revealInternalSteps)""", r)
        case (_, _: SuccPos) =>
          val r = tq"edu.cmu.cs.ls.keymaerax.bellerophon.DependentPositionWithAppliedInputTactic"
          (q"""new edu.cmu.cs.ls.keymaerax.macros.PositionTacticInfo(codeName = $codeString, display = ${convDI(display)(c)}, theExpr = $expr, needsGenerator = $needsGenerator, revealInternalSteps = $revealInternalSteps)""", r)
        case (_, _: TwoPos) => (q"""new edu.cmu.cs.ls.keymaerax.macros.InputTwoPositionTacticInfo(codeName = $codeString, display = ${convDI(display)(c)}, inputs = ${convAIs(inputs)(c)}, theExpr = $expr, needsGenerator = $needsGenerator)""", tq"""edu.cmu.cs.ls.keymaerax.bellerophon.AppliedBuiltInTwoPositionTactic""")
        case (x, y) => c.abort(c.enclosingPosition, s"Unsupported argument combination in @Tactic: ($x, $y)")
      }
      // Macro cannot introduce new statements or declarations, so introduce a library call which achieves our goal of registering
      // the tactic info to the global derivation info table
        if(isDef) {
          val application = q"""edu.cmu.cs.ls.keymaerax.macros.DerivationInfo.registerL($base, $info)"""
          if (inputs.isEmpty) {
          //val tag: TypeTag[_] = tagify(annottees.head.actualType)
//            c.typecheck()
          c.Expr(q"""$mods def $declName: $baseType = $application""")
        }
        else {
          c.Expr(q"""$mods def $declName (..$argSeq): $baseType = $application""")
        }
      } else {
        val application = q"""edu.cmu.cs.ls.keymaerax.macros.DerivationInfo.registerL($base, $info)"""
        c.Expr(q"""$mods val $declName: $baseType = $application""")
      }
    }
    def coreAnon(s: String): Boolean = {
      s match {
        case "anon" => false
        case "inputanon" => false
        case "inputanonL" => false
        case "inputanonP" => false
        case "inputanonR" => false
        case "coreanon" => true
        case _ => c.abort(c.enclosingPosition, s"""Expected function "anon" on RHS, got: $s""")
      }
    }
    annottees map (_.tree) toList match {
      // Annottee must be a val or def declaration of an tactic
      case (defDecl: DefDef) :: Nil =>
        defDecl match {
          // def has parameters for positions and/or inputs, and may have a return type
          case q"$mods def ${codeName: TermName}(..$inArgs): $tRet = ${f: Ident}($theRhs)" =>
            theRhs match {
              case q"((..$params) => $rhs)" =>
                val isCoreAnon = coreAnon(f.toString)
                if (!isTactic(tRet))
                  c.abort(c.enclosingPosition, "Invalid annottee: Expected val <tactic>: <Tactic> = <anon> ((args) => rhs)..., got: " + tRet + " " + tRet.getClass)
                val positions = getPositioning(params)
                assemble(mods, codeName, inArgs, positions, rhs, isDef = true, isCoreAnon)
              //c.abort(c.enclosingPosition, "Expected anonymous function, got:" + t)
              case rhs =>
                val isCoreAnon = coreAnon(f.toString)
                if (!isValTactic(tRet))
                  c.abort(c.enclosingPosition, "Invalid annottee: Unexpected return type: " + tRet)
                assemble(mods, codeName, inArgs, NoPos(), rhs, isDef = true, isCoreAnon)
            }
          case rhs => c.abort(c.enclosingPosition, "@Tactic expects def <name> (args): <T> = anon(...), got: " + rhs)
        }
      case (valDecl: ValDef) :: Nil =>
        valDecl match {
          case q"$mods val ${declName: TermName}: $tRet = ${f: Ident}($theRhs)" =>
             theRhs match {
               case q"((..$params) => $rhs)" =>
                 val isCoreAnon = coreAnon(f.toString)
                 if (!isTactic(tRet))
                  c.abort(c.enclosingPosition, s"Invalid annottee: Return type $tRet is not one of the supported return types")
                val positions = getPositioning(params)
                assemble(mods, declName, Nil, positions, rhs, isDef = false, isCoreAnon)
               case rhs =>
                 val isCoreAnon = coreAnon(f.toString)
                 if (!isValTactic(tRet))
                   c.abort(c.enclosingPosition, "Invalid annottee: Unexpected return type: " + tRet)
                 assemble(mods, declName, Nil, NoPos(), rhs, isDef = false, isCoreAnon)
               }
          case q"$mods val $cName: $tpt = $functionName( ..$params )" => c.abort(c.enclosingPosition, "Expected function application anon(..) on right-hand side of val, got: " + valDecl)
          case rhs => c.abort(c.enclosingPosition, "@Tactic expects val <name> (args): <T> = f(...), got: " + rhs)
        }
      case t => c.abort(c.enclosingPosition, "Invalid annottee: Expected val or def declaration got: " + t.head + " of type: " + t.head.getClass())
    }
  }
}