package edu.cmu.cs.ls.keymaerax.macros

import scala.annotation.StaticAnnotation
import scala.collection.immutable.Nil
import scala.language.experimental.macros
import scala.reflect.macros.{Universe, blackbox}
import AnnotationCommon._

/**
  * Tactic Annotation for proof tactics, which allows decentralized [[TacticInfo]].
  * @param names Display names to render in the user interface.
  * @param codeName You should avoid using this argument. Permanent unique code name used to invoke this axiom in tactics as a string and for Lemma storage.
  *                 `codeName`` will be inferred from the val that is annotated by this `@Axiom` and is strongly recommended to be identical to it.
  * @param inputs Display input information for non-positioning arguments, e.g., "C:Formula" for cut.
  *               Arguments are separated with ;; and allowed fresh variables are given in square brackets, for example
  *               E[y,x,y']:Formula;; P[y]:Formula are the arguments to tactic dG.
  *               By default, this argument is inferred from the argument types and names of the annotated [[def]].
  *               Use this argument when you want customized display on the UI or when there are allowedFresh variables.
  *               Supported types: Expression, Formula, Term, Variable, Number, String, Substitution, List[], Option[]
  *               Type names are case-insensitive.
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
  * @see [[TacticInfo]]
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
  private trait AnonSort
  private case object CoreAnonSort extends AnonSort
  private case object SimpleAnonSort extends AnonSort
  private case object UnguardedAnonSort extends AnonSort

  private trait PosArgs
  private case class AnteSuccPos(anteName: ValDef, succName: ValDef) extends PosArgs
  private case class AntePos(provableName: Option[ValDef], posName: ValDef) extends PosArgs
  private case class SuccPos(provableName: Option[ValDef], posName: ValDef) extends PosArgs
  /** Arguments are Position, (Position, Sequent), or (ProvableSig, Position). In the latter case, useProvable = true*/
  private case class OnePos(lname: ValDef, rname: Option[ValDef], useProvable: Boolean = false) extends PosArgs
  private case class TwoPos(provableName: ValDef, pos1Name: ValDef, pos2Name: ValDef) extends PosArgs
  private case class SequentArg(sequentName: ValDef) extends PosArgs
  private case class NoPos(provableName: Option[ValDef]) extends PosArgs
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
    def paramify(tn: TermName, params: Seq[Tree]): (String, DisplayInfo, String, List[ArgInfo], Boolean) = {
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
        case (ins, "", concl) if concl != "" && ins.nonEmpty => InputAxiomDisplayInfo(simpleDisplay, concl, inputs)
        case (ins, prem, concl) if concl != "" && prem != "" =>
          val (prem, conc) = (parseSequents(premisesString)(c), parseSequent(conclusionString)(c))
          RuleDisplayInfo(simpleDisplay, conc, prem)
        //case (_::_, "", "") => SimpleDisplayInfo(codeName, codeName)
        case _ => c.abort(c.enclosingPosition, "Unsupported argument combination for @Tactic: If premises or inputs are given, conclusion must be given")
      }
      (codeName, displayInfo, displayLevel, inputs, revealInternal)
    }
    def getParams (tn: TermName): (String, DisplayInfo, String, List[ArgInfo], Boolean) = {
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
             | tq"BuiltInLeftTactic" | tq"BuiltInRightTactic" | tq"BuiltInTactic" | tq"BuiltInPositionTactic"
             | tq"CoreLeftTactic" | tq"CoreRightTactic"
             | tq"BuiltInTwoPositionTactic" | tq"InputTwoPositionTactic" | tq"InputTactic"
             | tq"DependentPositionWithAppliedInputTactic"
             | tq"AppliedBuiltInTwoPositionTactic"
             | tq"BelleExpr" => true
        case _ => false
      }
    }
    // Scrape position argument info from declaration
    def getPositioning(params: Seq[Tree]): PosArgs = {
      val supportedArgs = "Unit, Position, Sequent, (Position, Sequent), or (ProvableSig, Position, Position)"
      params.toList match {
        // ValDef is also used for argument specifications
        case Nil => NoPos(None)
        case (posDef: ValDef) :: Nil =>
          posDef.tpt match {
            case (tq"ProvableSig") => NoPos(Some(posDef))
            case (tq"Position") => OnePos(posDef, None)
            case (tq"Sequent") => SequentArg(posDef)
            case tq"AntePosition" => AntePos(None, posDef)
            case tq"SuccPosition" => SuccPos(None, posDef)
            case params => c.abort(c.enclosingPosition, s"Positioning arguments must be $supportedArgs, got: $params")
          }
        case (ldef: ValDef) :: (rdef: ValDef) :: Nil  =>
          (ldef.tpt, rdef.tpt) match {
            case (tq"Position", tq"Sequent") => OnePos(ldef, Some(rdef))
            case (tq"ProvableSig", tq"Position") => OnePos(ldef, Some(rdef), useProvable = true)
            case (tq"AntePosition", tq"SuccPosition") => AnteSuccPos(ldef, rdef)
            case (tq"ProvableSig", tq"AntePosition") => AntePos(Some(ldef), rdef)
            case (tq"ProvableSig", tq"SuccPosition") => SuccPos(Some(ldef), rdef)
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
              new ListArg(getInput(vd))
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
        case ListArg(ai: ArgInfo) => tq"scala.List[${typeName(ai)}]"
        case ai => c.abort(c.enclosingPosition, "Unimplemented case in @Tactic, could not convert argument spec: " + ai)
      }
    }

    def inferType(defaultType: Tree, args: List[ArgInfo], pos: PosArgs, anonSort: Option[AnonSort]): Tree = {
      // Only infer type if annotation is empty
      defaultType match {
        case tq"" =>
          (args, pos) match {
            case (Nil, _: NoPos | _: SequentArg) => tq"edu.cmu.cs.ls.keymaerax.bellerophon.DependentTactic"
            case (_ :: _, _: NoPos | _: SequentArg) => tq"edu.cmu.cs.ls.keymaerax.bellerophon.InputTactic"
            case (Nil, _: AntePos | _: OnePos | _: SuccPos) => tq"edu.cmu.cs.ls.keymaerax.bellerophon.DependentPositionTactic"
            case (_ :: _, _: OnePos | _: AntePos | _: SuccPos) =>
              tq"edu.cmu.cs.ls.keymaerax.bellerophon.DependentPositionWithAppliedInputTactic"
            case (Nil, _: TwoPos | _: AnteSuccPos) =>
              (tq"edu.cmu.cs.ls.keymaerax.bellerophon.BuiltInTwoPositionTactic")
            case (_ :: _, _: TwoPos | _: AnteSuccPos) =>
              (tq"edu.cmu.cs.ls.keymaerax.bellerophon.AppliedBuiltInTwoPositionTactic")
            case (Nil, AntePos(Some(sname), pname)) =>
              if (anonSort.contains(CoreAnonSort))
                (tq"edu.cmu.cs.ls.keymaerax.bellerophon.CoreLeftTactic")
              else
                (tq"edu.cmu.cs.ls.keymaerax.bellerophon.BuiltInLeftTactic")
            case (Nil, SuccPos(Some(sname), pname)) =>
              if (anonSort.contains(CoreAnonSort))
                (tq"edu.cmu.cs.ls.keymaerax.bellerophon.CoreRightTactic")
              else
                (tq"edu.cmu.cs.ls.keymaerax.bellerophon.BuiltInRightTactic")
            case (_ :: _, _: SuccPos | _: AntePos) =>
              c.abort(c.enclosingPosition, "Argument combination not yet supported")
            case t => c.abort(c.enclosingPosition, s"Unsupported argument combination in @Tactic: $args; $pos; $defaultType")
          }
        case _ => defaultType
      }
    }
    def arguePos(funStr: Literal, argExpr: Tree, args: List[ArgInfo], pos: PosArgs, acc: Tree, anonSort: Option[AnonSort]): Tree = {
      // [[isCoreAnon]] represents "which anon function" was on the RHS of the definition.
      // If this is empty, the @Tactic is a forward to another BelleExpr. [[forward]] has overloads for most (@TODO all)
      // tactic classes, so in each case we just call [[forward]]
      if (anonSort.isEmpty) {
        return q"""new edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory ($funStr).forward($acc)"""
      }
      (args, pos) match {
        case (Nil, NoPos(None)) =>
          if(anonSort.contains(UnguardedAnonSort)) {
            q"""new edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory ($funStr).bys($acc)"""
          } else {
            q"""new edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory ($funStr).by($acc)"""
          }
        case (Nil, NoPos(Some(arg))) =>
          q"""new edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory ($funStr).by(($arg) => $acc)"""
        case (Nil, SequentArg(sequentName)) =>
          q"""new edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory ($funStr).by(($sequentName) => $acc)"""
        case (Nil, OnePos(pname, None, _)) =>
          q"""new edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory ($funStr).by(($pname) =>  $acc)"""
        case (Nil, OnePos(pname, Some(sname), _)) =>
          q"""new edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory ($funStr).by(($pname, $sname) =>  $acc)"""
        case (_::_, NoPos(None)) =>
          q"""new edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory ($funStr).byWithInputs($argExpr, $acc)"""
        case (_::_, NoPos(Some(pname))) =>
          q"""new edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory ($funStr).byWithInputsP($argExpr, ($pname) => $acc)"""
        case (_::_, SequentArg(sequentName)) =>
          q"""new edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory ($funStr).byWithInputs($argExpr, ($sequentName) => $acc)"""
        case (_::_, OnePos(pname, None, _)) =>
          q"""new edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory ($funStr).byWithInputs($argExpr, ($pname) =>  $acc)"""
        case (_::_, OnePos(pname, Some(sname), false)) =>
          q"""new edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory ($funStr).byWithInputs($argExpr, ($pname, $sname) =>  $acc)"""
        case (_::_, OnePos(pname, Some(sname), true)) =>
          q"""new edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory ($funStr).byWithInputsP($argExpr, ($pname, $sname) =>  $acc)"""
        case (Nil, AntePos(None, pname)) =>
          q"""new edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory ($funStr).byL(($pname) =>  $acc)"""
        case (Nil, AntePos(Some(sname), pname)) =>
          if (anonSort.contains(CoreAnonSort))
            q"""new edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory ($funStr).coreby(($sname, $pname) =>  $acc)"""
          else
            q"""new edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory ($funStr).by(($sname, $pname) =>  $acc)"""
        case (_::_, AntePos(Some(sname), pname)) =>
          q"""new edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory ($funStr).corebyWithInputsL($argExpr, ($sname, $pname) =>  $acc)"""
        case (Nil, SuccPos(None, pname)) =>
          q"""new edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory ($funStr).byR(($pname) =>  $acc)"""
        case (Nil, SuccPos(Some(sname), pname)) =>
          if (anonSort.contains(CoreAnonSort))
            q"""new edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory ($funStr).coreby(($sname, $pname) =>  $acc)"""
          else
            q"""new edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory ($funStr).by(($sname, $pname) =>  $acc)"""
        case (_::_, SuccPos(Some(sname), pname)) =>
          q"""new edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory ($funStr).corebyWithInputsR($argExpr, ($sname, $pname) =>  $acc)"""
        case (Nil, AnteSuccPos(sname, pname)) =>
          q"""new edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory ($funStr).byLR(($sname, $pname) =>  $acc)"""
        case (Nil, TwoPos(provable, pos1, pos2)) =>
          q"""new edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory ($funStr).by((($provable, $pos1, $pos2) =>  $acc))"""
        case (_::_, TwoPos(provable, pos1, pos2)) =>
          q"""new edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory ($funStr).byWithInputs($argExpr, (($provable, $pos1, $pos2) =>  $acc))"""
        case (_::_, _: SuccPos | _: AntePos | _: AnteSuccPos) =>
          c.abort(c.enclosingPosition, "Argument combination not yet supported")
        case t => c.abort(c.enclosingPosition, s"Unsupported argument combination in @Tactic: $args; $pos; ")
      }
    }
    // Type and term ASTs which wrap acc in position and/or input arguments as anonymous lambdas
    def argue(funName: String, acc: Tree, pos: PosArgs, args: List[ArgInfo], generatorOpt: Option[ArgInfo], tRet: Tree, anonSort: Option[AnonSort]): (Tree, Seq[ValDef], Seq[Tree], (Tree, Tree)) = {
      val funStr = Literal(Constant(funName))
      val argExpr = args match {
        case Nil => q"Nil"
        case _ => args.foldRight[Tree](q"Nil")({case (ai, acc) => q"${Ident(TermName(ai.name))} :: $acc"})
      }
      // if no "anon" function present, then tactic is a simple forwarding expression like val e: BelleExpr = <tac>
      val baseType = inferType(tRet, args, pos, anonSort)
      val baseTerm = arguePos(funStr, argExpr, args, pos, acc, anonSort)
      val base = (baseTerm, baseType)
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
    def sdContains(sd: SequentDisplay, s: String): Boolean = {
      sd.ante.exists(n => n.contains(s)) || sd.succ.exists(n => n.contains(s))
    }
    // Error check: Web UI uses axiom/rule display to let user input arguments of tactic. This requires every argument
    // name to appear in the displayinfo.
    def missingInput(displayLevel: String, args: List[ArgInfo], display: DisplayInfo): Option[ArgInfo] = {
      // Input doesn't need to appear in displayinfo if UI can't show the tactic anyway
      if (displayLevel == "internal") None
      else {
        args.find((ai: ArgInfo) => {
          display match {
            case (_: AxiomDisplayInfo) | (_: SimpleDisplayInfo) => true
            case InputAxiomDisplayInfo(names, displayFormula, _input) => !displayFormula.contains(ai.name)
            case RuleDisplayInfo(sd, conc, prem) => !(sdContains(conc, ai.name) || prem.exists(sd => sdContains(sd, ai.name)))
          }
        })
      }
    }
    def assemble(mods: Modifiers, declName: TermName, inArgs: Seq[Tree], positions: PosArgs, rhs: Tree, tRet: Tree, isDef: Boolean
                 , anonSort: Option[AnonSort]): c.Expr[Any] = {
      val (codeName, display, displayLevel, parsedArgs, revealInternalSteps) = getParams(declName)
      val (generatorOpt, defArgs) = getInputs(inArgs)
      val displayInputs = if (parsedArgs.nonEmpty) parsedArgs else defArgs
      val needsGenerator = generatorOpt.isDefined
      if (codeName.exists(c => c =='\"'))
        c.abort(c.enclosingPosition, "Identifier " + codeName + " must not contain escape characters")
      // AST for literal strings for the names
      val codeString = Literal(Constant(codeName))
      val (curriedTermTree, argSeq, argTySeq, (base, baseType)) = argue(codeName, rhs, positions, defArgs, generatorOpt, tRet, anonSort)
      val expr = q"""((_: Unit) => ($curriedTermTree))"""
      val info = (displayInputs, positions) match {
        case (Nil, _: NoPos | _: SequentArg) => (q"""new edu.cmu.cs.ls.keymaerax.macros.TacticInfo(codeName = $codeString, display = ${convDI(display)(c)}, theExpr = $expr, displayLevel = ${convSymbol(displayLevel)(c)}, needsGenerator = $needsGenerator, revealInternalSteps = $revealInternalSteps)""")
        case (_ :: _, _: NoPos | _: SequentArg) => (q"""new edu.cmu.cs.ls.keymaerax.macros.InputTacticInfo(codeName = $codeString, display = ${convDI(display)(c)}, inputs = ${convAIs(displayInputs)(c)}, theExpr = $expr, displayLevel = ${convSymbol(displayLevel)(c)},  needsGenerator = $needsGenerator, revealInternalSteps = $revealInternalSteps)""")
        case (Nil, _: OnePos | _: AntePos | _: SuccPos) => (q"""new edu.cmu.cs.ls.keymaerax.macros.PositionTacticInfo(codeName = $codeString, display = ${convDI(display)(c)}, theExpr = $expr, displayLevel = ${convSymbol(displayLevel)(c)}, needsGenerator = $needsGenerator, revealInternalSteps = $revealInternalSteps)""")
        case (_ :: _, _: OnePos | _: AntePos | _: SuccPos) => (q"""new edu.cmu.cs.ls.keymaerax.macros.InputPositionTacticInfo(codeName = $codeString, display = ${convDI(display)(c)}, inputs = ${convAIs(displayInputs)(c)}, theExpr = $expr, displayLevel = ${convSymbol(displayLevel)(c)}, needsGenerator = $needsGenerator, revealInternalSteps = $revealInternalSteps)""")
        case (Nil, (_: AnteSuccPos | _: TwoPos)) => q"""new edu.cmu.cs.ls.keymaerax.macros.TwoPositionTacticInfo(codeName = $codeString, display = ${convDI(display)(c)}, theExpr = $expr, displayLevel = ${convSymbol(displayLevel)(c)}, needsGenerator = $needsGenerator)"""
        case (_ :: _, (_: AnteSuccPos | _: TwoPos)) => q"""new edu.cmu.cs.ls.keymaerax.macros.InputTwoPositionTacticInfo(codeName = $codeString, display = ${convDI(display)(c)}, theExpr = $expr, displayLevel = ${convSymbol(displayLevel)(c)}, needsGenerator = $needsGenerator)"""
        case (x, y) => c.abort(c.enclosingPosition, s"Unsupported argument combination in @Tactic: ($x, $y)")
      }
      missingInput(displayLevel, displayInputs, display).
        map(ai => c.abort(c.enclosingPosition, s"Tactic $declName must mention every input in DisplayInfo, but argument $ai is not mentioned in DisplayInfo $display"))
      // Macro cannot introduce new statements or declarations, so introduce a library call which achieves our goal of registering
      // the tactic info to the global derivation info table
      if(isDef) {
        val application = q"""edu.cmu.cs.ls.keymaerax.macros.DerivationInfo.registerL($base, $info)"""
        if (defArgs.isEmpty)
          c.Expr(q"""$mods def $declName: $baseType = $application""")
        else
        c.Expr(q"""$mods def $declName (..$argSeq): $baseType = $application""")
      } else {
        val application = q"""edu.cmu.cs.ls.keymaerax.macros.DerivationInfo.registerL($base, $info)"""
        c.Expr(q"""$mods val $declName: $baseType = $application""")
      }
    }
    def anonSort(s: String): Option[AnonSort] = {
      s match {
        case "anon"  | "anonL" | "anonR" | "anonLR" | "inputanon" | "inputanonL"| "inputanonP" | "inputanonR" | "inputanonP" => Some(SimpleAnonSort)
        case  "anons" => Some(UnguardedAnonSort)
        case "coreanon" => Some(CoreAnonSort)
        case _ => None
      }
    }
    def pickRhs(f: Ident, rhs: Tree, params: Option[Seq[Tree]] = None): Tree = {
      if (anonSort(f.toString).isDefined) {
        rhs
      } else {
        params match {
          case Some(params) => q"${f: Ident}((..$params) => $rhs)"
          case None => q"${f: Ident}($rhs)"
        }
      }
    }
    val (isDef, mods, codeName, inArgs, tRet, fOpt, params, rhs) =
      annottees map (_.tree) toList match {
        case q"$mds def ${codeName: TermName}(..$inArgs): $tRet = ${f: Ident}(((..$params) => $rhs))" :: Nil =>
          (true, mds, codeName, inArgs, tRet, Some(f), params, pickRhs(f, rhs, Some(params)))
        case q"$mds def ${codeName: TermName}(..$inArgs): $tRet = ${f: Ident}($rhs)" :: Nil =>
          (true, mds, codeName, inArgs, tRet, Some(f), Nil, pickRhs(f, rhs))
        case q"$mds def ${codeName: TermName}(..$inArgs): $tRet = $rhs" :: Nil =>
          (true, mds, codeName, inArgs, tRet, None, Nil, rhs)
        case q"$mds def ${codeName: TermName}: $tRet = ${f: Ident}(((..$params) => $rhs))" :: Nil =>
          (true, mds, codeName, Nil, tRet, Some(f), params, pickRhs(f, rhs, Some(params)))
        case q"$mds def ${codeName: TermName}: $tRet = ${f: Ident}($rhs)" :: Nil =>
          (true, mds, codeName, Nil, tRet, Some(f), Nil, pickRhs(f, rhs))
        case q"$mds def ${codeName: TermName}: $tRet = $rhs" :: Nil =>
          (true, mds, codeName, Nil, tRet, None, Nil, rhs)
        case q"$mds val ${codeName: TermName}: $tRet = ${f: Ident}((..$params) => $rhs)" :: Nil =>
          (false, mds, codeName, Nil, tRet, Some(f), params, pickRhs(f, rhs, Some(params)))
        case q"$mds val ${codeName: TermName}: $tRet = ${f: Ident}($rhs)" :: Nil=>
          (false, mds, codeName, Nil, tRet, Some(f), Nil, pickRhs(f, rhs))
        case q"$mds val ${codeName: TermName}: $tRet = $rhs" :: Nil =>
          (false, mds, codeName, Nil, tRet, None, Nil, rhs)
        case _ :: _ :: _ =>
          c.abort(c.enclosingPosition, "Expected one tactic definition, got multiple: " + annottees.map(show(_)))
        case _ =>
          c.abort(c.enclosingPosition, "Expected tactic definition, got: " + annottees.map(show(_)))
      }
    tRet match {
      case tq"" => c.abort(c.enclosingPosition, "@Tactic expects a return type annotation on tactics. Please annotate the return type, see MiscTactics.scala for supported types")
      case _ => if (!isTactic(tRet))
        c.abort(c.enclosingPosition, "Invalid annottee: Expected val(or def) <tactic>: <Tactic> = <anon> ((args) => rhs)..., got: " + tRet + " " + tRet.getClass + ", see MiscTactics.scala for supported types")
    }
    val isCoreAnon = fOpt match { case Some(f) => anonSort(f.toString) case None => None }
    val positions = getPositioning(params)
    val res = assemble(mods, codeName, inArgs, positions, rhs, tRet, isDef, isCoreAnon)
    // Print debug info when applied to any tactic in this set
    val debugTactics: Set[String] = Set()
    if(debugTactics.contains(codeName.decodedName.toString)) {
      println(s"DEBUG (${codeName}): \n$res\n")
    }
    res
  }
}