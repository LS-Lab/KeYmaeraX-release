/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics.macros

import edu.cmu.cs.ls.keymaerax.btactics.macros.AnnotationCommon.{
  astForArgInfo,
  astForDisplayInfo,
  parseAIs,
  renderDisplayFormula,
}

import scala.annotation.{compileTimeOnly, StaticAnnotation}
import scala.language.experimental.macros
import scala.reflect.macros.whitebox

/**
 * Tactic Annotation for proof tactics, which allows decentralized [[TacticInfo]].
 *
 * @param name
 *   Unique identifier for this axiom. Used to invoke the axiom in tactics and for lemma storage. Must only contain the
 *   characters `a-zA-Z0-9_`. It is strongly recommended that this name is identical to the name of the annotated scala
 *   definition. The exception is when you wish for your tactic to have different arguments in the parsed Bellerophon
 *   language than does your implementation. In this case it is conventional to write a declaration `val <tacticName>X =
 *   <tacticName>(...)` with [[name]] `<tacticName>` which converts arguments as needed.
 * @param displayName
 *   Short name used for the axiom in the user interface. Defaults to [[name]].
 * @param displayNameAscii
 *   ASCII-only version of [[displayName]] that must be specified if [[displayName]] contains characters outside the
 *   printable ASCII range. Defaults to [[displayName]].
 * @param displayNameLong
 *   Descriptive long name used in some menus in the user interface. Should be a short, grammatical English phrase.
 *   Defaults to [[displayName]].
 * @param displayLevel
 *   Where to display an axiom/rule/tactic in the user interface. Defaults to [[DisplayLevelInternal]].
 * @param inputs
 *   Display input information for non-positioning arguments, e.g., "C:Formula" for cut. Arguments are separated with ;;
 *   and optional square brackets []. In the default case, without brackets, the inputs of tactic must not introduce any
 *   new variables. The optional brackets contain a comma-separated list of variables, which are always allowed to
 *   appear in the input, even if that appearance is fresh. For example, the tactic dG has arguments E and P which are
 *   annotated `E[y,x,y']:Formula;; P[y]:Formula`. This means that y,x, and y' are always allowed to be mentioned in E
 *   and y is always allowed to be mentioned in P. Fresh variables are most often specified for tactics such as dG which
 *   introduce ghost variables that we wish to mention in an input. By default, this argument is inferred from the
 *   argument types and names of the annotated [[def]]. Use this argument when you want customized display on the UI or
 *   when there are allowedFresh variables. Supported types: Expression, Formula, Term, Variable, Number, String,
 *   Substitution, List[], Option[] Bellerophon does not have options or lists. As far as parsing a Bellerophon tactic
 *   script is concerned, an input specification of type Option[T] indicates an optional argument which has type T,
 *   while an input specification of type List[T] indicates a variadic function where arbitrarily many arguments may
 *   have type T. At most one List[T] argument should be used, and it should be the last argument. If optional arguments
 *   are used, they should appear after all required arguments. Optional arguments are resolved positionally without
 *   regard to type. Type names are case-insensitive.
 * @param displayPremises
 *   String of premises when (if) the tactic is displayed like a rule on the UI. For tactics with (non-position) inputs,
 *   the premises or conclusion must mention each input. The name of each input is given in [[inputs]], which may be
 *   generated from the [[def]]. Premises are separated by ;; and each premise is optionally a sequent. "P;; A, B |- C"
 *   specifies two premises, the latter of which is a sequent with two assumptions. An asterisk "*" indicates a tactic
 *   that closes a branch.
 * @param displayConclusion
 *   Conclusion of rule displayed on UI. Axiom-like tactics have a conclusion and no premises. Tactics with premises
 *   must have conclusions. For tactics with (non-position) inputs, the premises or conclusion must mention each input.
 *   The name of each input is given in [[inputs]], which may be generated from the [[def]]. Sequent syntax is
 *   optionally supported: A, B |- C, D
 * @param needsGenerator
 *   Does the tactic use invariant formula generators such as the @invariant annotation in .kyx files? Used for a small
 *   number of tactics such as master.
 * @param revealInternalSteps
 *   Does the Web UI allow stepping inside this tactic?
 * @see
 *   [[TacticInfo]]
 * @example
 *   {{{
 *   @Tactic(name = "diffCuts")
 *   def diffCuts(fmls: List[Formula]): BelleExpr = ...   /* Definition */
 *   diffCuts(List("acc > 0".asFormula)) /* Used in Scala */
 *   diffCuts({`acc > 0`}) /* Used in Bellerophon */
 *   diffCuts(List("acc > 0".asFormula, "v > 0".asFormula, "x > 0".asFormula)) /* Used in Scala */
 *   diffCuts({`acc > 0`}, {`v > 0`}, {`x > 0`}) /* Used in Bellerophon */
 *   }}}
 * @example
 *   {{{
 *   @Tactic(name = "cutFresh", inputs = "x:Variable;; p(x)[x]:Formula")
 *   def cutFresh(x: Variable, px: Formula): InputTactic = ...
 *   cutFresh("x".asVariable, "x^2 >= 0".asFormula)  /* Used in Scala */
 *   cutFresh({`x`}, {`x^2 >= 0`})  /* Used in Bellerophon */
 *   }}}
 * @example
 *   {{{
 *   /* Discharge x:=*, optionally instantiate x := f for [] on left or <> on right */
 *   @Tactic(name = "random", inputs = "f:Option[Term]")
 *   def random(maybeF: Option[Term]): DependentPositionWithAppliedPositionTactic = ...
 *   random(None)(1) & random(Some("x".asTerm"))   /* Scala */
 *   random(1) & random({`x`})   /* Bellerophon */
 *   }}}
 * @example
 *   {{{
 *   /* Invalid: multiple variadic argument lists. Don't do this. */
 *   @Tactic(name = "cutLAndOrR", inputs = "lcuts: List[Formula];; rcuts: List[Formula]")
 *   def cutLAndOrR(lcuts: List[Formula], rcuts: List[Formula]): BelleExpr =  ...
 *   }}}
 * @example
 *   {{{
 *   /* Invalid: optional arguments stuttered with required arguments. Don't do this. */
 *   @Tactic(name = "sandwich", inputs = "l: Option[Term];; x: Term;; r: Option[Term]")
 *   def sandwich(l: Option[Term], x: Term, r: Option[Term]): BelleExpr =  ...
 *   }}}
 */
@compileTimeOnly("enable -Ymacro-annotations")
class Tactic(
    val name: String,
    val displayName: Option[String] = None,
    val displayNameAscii: Option[String] = None,
    val displayNameLong: Option[String] = None,
    val displayLevel: DisplayLevel = DisplayLevelInternal,
    val displayPremises: String = "",
    val displayConclusion: String = "",
    val displayContextPremises: String = "",
    val displayContextConclusion: String = "",
    val needsGenerator: Boolean = false,
    val revealInternalSteps: Boolean = false,
    val inputs: String = "",
    val inputGenerator: Option[String] = None,
) extends StaticAnnotation {
  // Magic incantation, see https://docs.scala-lang.org/overviews/macros/annotations.html
  def macroTransform(annottees: Any*): Any = macro TacticMacro.impl
}

/** Helper class for easy annotation argument parsing. Must stay in sync with [[Tactic]]! */
case class TacticArgs(
    name: String,
    displayName: Option[String] = None,
    displayNameAscii: Option[String] = None,
    displayNameLong: Option[String] = None,
    displayLevel: DisplayLevel = DisplayLevelInternal,
    displayPremises: String = "",
    displayConclusion: String = "",
    displayContextPremises: String = "",
    displayContextConclusion: String = "",
    needsGenerator: Boolean = false,
    revealInternalSteps: Boolean = false,
    inputs: String = "",
    inputGenerator: Option[String] = None,
)

object TacticMacro {
  trait AnonSort
  case object CoreAnonSort extends AnonSort
  case object SimpleAnonSort extends AnonSort
  case object UnguardedAnonSort extends AnonSort

  val ANON_SORTS: Map[String, AnonSort] = Map(
    "anon" -> SimpleAnonSort,
    "anonL" -> SimpleAnonSort,
    "anonR" -> SimpleAnonSort,
    "anonLR" -> SimpleAnonSort,
    "inputanon" -> SimpleAnonSort,
    "inputanonL" -> SimpleAnonSort,
    "inputanonP" -> SimpleAnonSort,
    "inputanonR" -> SimpleAnonSort,
    "inputanonS" -> SimpleAnonSort,
    "anons" -> UnguardedAnonSort,
    "coreanon" -> CoreAnonSort,
  )

  val KNOWN_TACTIC_TYPES: List[String] = List(
    "DependentTactic",
    "DependentPositionTactic",
    "DependentTwoPositionTactic",
    "InputPositionTactic",
    "BuiltInLeftTactic",
    "BuiltInRightTactic",
    "BuiltInTactic",
    "BuiltInPositionTactic",
    "CoreLeftTactic",
    "CoreRightTactic",
    "BuiltInTwoPositionTactic",
    "InputTwoPositionTactic",
    "InputTactic",
    "StringInputTactic",
    "DependentPositionWithAppliedInputTactic",
    "AppliedBuiltInTwoPositionTactic",
    "BelleExpr",
  ).sorted

  val KNOWN_TACTIC_TYPES_WITH_INPUT: List[String] = List(
    "InputPositionTactic",
    "InputTwoPositionTactic",
    "InputTactic",
    "StringInputTactic",
    "DependentPositionWithAppliedInputTactic",
  ).sorted

  def impl(c: whitebox.Context)(annottees: c.Expr[Any]*): c.Expr[Any] = {
    import c.universe._

    /*
     * Obtain annotation arguments
     */

    // While this is quite a bit slower than the previous code, it is also a lot simpler and more type safe.
    // https://stackoverflow.com/questions/32631372/getting-parameters-from-scala-macro-annotation
    // https://stackoverflow.com/questions/37891855/macro-annotation-with-default-arguments
    val args = c.prefix.tree match {
      case q"new $_(..$args)" => c.eval(c.Expr[TacticArgs](
          q"""{
            import edu.cmu.cs.ls.keymaerax.btactics.macros.{
              DisplayLevel,
              DisplayLevelInternal,
              DisplayLevelBrowse,
              DisplayLevelMenu,
              DisplayLevelAll,
            };
            edu.cmu.cs.ls.keymaerax.btactics.macros.TacticArgs(..$args)
          }"""
        ))
      case _ => c.abort(c.enclosingPosition, "this should never happen")
    }

    /*
     * Deconstruct syntax tree
     */

    sealed trait Definition {
      val mods: Modifiers
      val declName: TermName
      val returnType: Tree
      val body: Tree
    }
    final case class DefinitionDefParams(
        mods: Modifiers,
        declName: TermName,
        params: Seq[Tree],
        returnType: Tree,
        body: Tree,
    ) extends Definition
    final case class DefinitionDef(mods: Modifiers, declName: TermName, returnType: Tree, body: Tree) extends Definition
    final case class DefinitionVal(mods: Modifiers, declName: TermName, returnType: Tree, body: Tree) extends Definition

    sealed trait Body {
      val rhs: Tree
    }
    final case class BodyFuncLambda(func: Ident, params: Seq[Tree], rhs: Tree) extends Body
    final case class BodyFunc(func: Ident, rhs: Tree) extends Body
    final case class BodyPlain(rhs: Tree) extends Body

    // Annotation must be applied to single annottee
    val annottee = annottees.map(_.tree) match {
      case List(annottee) => annottee
      case _ => c.abort(c.enclosingPosition, "@Tactic must be applied to tactic definition")
    }

    // Annottee must be one of three possible definition styles
    val definition = annottee match {
      case q"$mods def $declName(..$params): $returnType = $body" =>
        DefinitionDefParams(mods, declName, params, returnType, body)
      case q"$mods def $declName: $returnType = $body" => DefinitionDef(mods, declName, returnType, body)
      case q"$mods val $declName: $returnType = $body" => DefinitionVal(mods, declName, returnType, body)
      case _ => c.abort(c.enclosingPosition, "@Tactic must be applied to tactic definition")
    }

    // Body must be one of three possible definition styles
    val body = definition.body match {
      case q"${func: Ident}((..$params) => $rhs)" => BodyFuncLambda(func, params, rhs)
      case q"${func: Ident}($rhs)" => BodyFunc(func, rhs)
      case rhs => BodyPlain(rhs)
    }

    val returnType = definition.returnType match {
      case Ident(name) => name.decodedName.toString
      case t => c.abort(t.pos, "@Tactic expects a return type annotation")
    }
    if (!KNOWN_TACTIC_TYPES.contains(returnType)) {
      c.abort(definition.returnType.pos, s"@Tactic return type must be one of ${KNOWN_TACTIC_TYPES.mkString(", ")}")
    }

    val funcName = body match {
      case BodyFuncLambda(func, _, _) => Some(func.name.decodedName.toString)
      case BodyFunc(func, _) => Some(func.name.decodedName.toString)
      case BodyPlain(_) => None
    }
    val funcSort = funcName.flatMap(ANON_SORTS.get)

    /*
     * Compute different names
     */

    val name = AnnotationCommon.getName(args.name)(c)
    val displayName = AnnotationCommon.getDisplayName(args.displayName, name)(c)
    val displayNameAscii = AnnotationCommon.getDisplayNameAscii(args.displayNameAscii, displayName)(c)
    val displayNameLong = AnnotationCommon.getDisplayNameLong(args.displayNameLong, displayName)(c)

    /*
     * Parse annotation arguments
     */

    val inputs: List[ArgInfo] = parseAIs(args.inputs)(c)

    val display = (
      inputs,
      args.displayPremises,
      args.displayConclusion,
      args.displayContextPremises,
      args.displayContextConclusion,
    ) match {
      case (Nil, "", "", _, _) => SimpleDisplayInfo(
          name = displayName,
          nameAscii = displayNameAscii,
          nameLong = displayNameLong,
          level = args.displayLevel,
        )

      case (Nil, "", concl, _, _) if concl != "" =>
        AxiomDisplayInfo(
          name = displayName,
          nameAscii = displayNameAscii,
          nameLong = displayNameLong,
          level = args.displayLevel,
          formula = renderDisplayFormula(concl),
        )

      case (ins, "", concl, _, _) if concl != "" && ins.nonEmpty =>
        InputAxiomDisplayInfo(
          name = displayName,
          nameAscii = displayNameAscii,
          nameLong = displayNameLong,
          level = args.displayLevel,
          formula = concl,
          input = inputs,
        )

      case (_, prem, concl, "", "") if concl != "" && prem != "" =>
        val premises = DisplaySequent.parseMany(args.displayPremises)
        val conclusion = DisplaySequent.parse(args.displayConclusion)
        RuleDisplayInfo(
          name = displayName,
          nameAscii = displayNameAscii,
          nameLong = displayNameLong,
          level = args.displayLevel,
          conclusion = conclusion,
          premises = premises,
          inputGenerator = args.inputGenerator,
        )

      case (_, prem, concl, ctxPrem, ctxConcl) if concl != "" && prem != "" && ctxPrem != "" && ctxConcl != "" =>
        val premises = DisplaySequent.parseMany(args.displayPremises)
        val conclusion = DisplaySequent.parse(args.displayConclusion)
        val ctxPremises = DisplaySequent.parseMany(args.displayContextPremises)
        val ctxConclusion = DisplaySequent.parse(args.displayContextConclusion)
        TacticDisplayInfo(
          name = displayName,
          nameAscii = displayNameAscii,
          nameLong = displayNameLong,
          level = args.displayLevel,
          conclusion = conclusion,
          premises = premises,
          ctxConclusion = ctxConclusion,
          ctxPremises = ctxPremises,
          inputGenerator = args.inputGenerator,
        )

      case _ => c.abort(c.enclosingPosition, "@Tactic with premises or inputs must have a conclusion")
    }

    /*
     * Scrape position argument info from lambda declaration
     */

    trait PosArgs
    case class AnteSuccPos(anteName: ValDef, succName: ValDef) extends PosArgs
    case class AntePos(provableName: Option[ValDef], posName: ValDef) extends PosArgs
    case class SuccPos(provableName: Option[ValDef], posName: ValDef) extends PosArgs

    /**
     * Arguments are Position, (Position, Sequent), or (ProvableSig, Position). In the latter case, useProvable = true
     */
    case class OnePos(lname: ValDef, rname: Option[ValDef], useProvable: Boolean = false) extends PosArgs
    case class TwoPos(provableName: ValDef, pos1Name: ValDef, pos2Name: ValDef) extends PosArgs
    case class SequentArg(sequentName: ValDef) extends PosArgs
    case class NoPos(provableName: Option[ValDef]) extends PosArgs

    val positionArgs = {
      val params = body match {
        case body: BodyFuncLambda => body.params.toList
        case _ => Nil
      }

      val supportedArgs = "Unit, Position, Sequent, (Position, Sequent), or (ProvableSig, Position, Position)"

      params match {
        // ValDef is also used for argument specifications
        case Nil => NoPos(None)

        case (posDef: ValDef) :: Nil => posDef.tpt match {
            case tq"ProvableSig" => NoPos(Some(posDef))
            case tq"Position" => OnePos(posDef, None)
            case tq"Sequent" => SequentArg(posDef)
            case tq"AntePosition" => AntePos(None, posDef)
            case tq"SuccPosition" => SuccPos(None, posDef)
            case params => c.abort(c.enclosingPosition, s"Positioning arguments must be $supportedArgs, got: $params")
          }

        case (ldef: ValDef) :: (rdef: ValDef) :: Nil => (ldef.tpt, rdef.tpt) match {
            case (tq"Position", tq"Sequent") => OnePos(ldef, Some(rdef))
            case (tq"ProvableSig", tq"Position") => OnePos(ldef, Some(rdef), useProvable = true)
            case (tq"AntePosition", tq"SuccPosition") => AnteSuccPos(ldef, rdef)
            case (tq"ProvableSig", tq"AntePosition") => AntePos(Some(ldef), rdef)
            case (tq"ProvableSig", tq"SuccPosition") => SuccPos(Some(ldef), rdef)
            case params => c.abort(c.enclosingPosition, s"Positioning arguments must be $supportedArgs, got: $params")
          }

        case (provableDef: ValDef) :: (pos1Def: ValDef) :: (pos2Def: ValDef) :: Nil =>
          (provableDef.tpt, pos1Def.tpt, pos2Def.tpt) match {
            case (tq"ProvableSig", tq"Position", tq"Position") => TwoPos(provableDef, pos1Def, pos2Def)
            case params => c.abort(c.enclosingPosition, s"Positioning arguments must be $supportedArgs, got: $params")
          }

        case params => c.abort(
            c.enclosingPosition,
            s"Positioning arguments must be $supportedArgs, got: ${params.map(_.getClass).mkString(",")}",
          )
      }
    }

    /*
     * Scrape argument info from declaration
     */

    def getArgInfoForDefParam(param: Tree): ArgInfo = {
      val valDef = param.asInstanceOf[ValDef]
      val name = valDef.name.decodedName.toString
      valDef.tpt match {
        case tq"Generator[GenProduct]" => GeneratorArg(name)
        case tq"Formula" => FormulaArg(name)
        case tq"Expression" => ExpressionArg(name)
        case tq"Term" => TermArg(name)
        case tq"Number" => NumberArg(name)
        case tq"Variable" => VariableArg(name)
        case tq"String" => StringArg(name)
        case tq"PosInExpr" => PosInExprArg(name)
        case tq"SubstitutionPair" => SubstitutionArg(name)
        case tq"Option[${t: Tree}]" => OptionArg(getArgInfoForDefParam(ValDef(valDef.mods, valDef.name, t, valDef.rhs)))
        case tq"List[${t: Tree}]" => ListArg(getArgInfoForDefParam(ValDef(valDef.mods, valDef.name, t, valDef.rhs)))
        case t =>
          c.abort(c.enclosingPosition, "Expected supported input type in tactic definition, got unsupported type: " + t)
      }
    }

    val definitionArgs = definition match {
      case d: DefinitionDefParams => d.params.map(getArgInfoForDefParam).toList
      case _ => Nil
    }

    // Quick check that there are only args iff the return type is known to take inputs.
    // The return type is used to drive serialization. An incorrect return type would lead to incorrect serialization.
    if (definitionArgs.nonEmpty && !KNOWN_TACTIC_TYPES_WITH_INPUT.contains(returnType)) {
      c.abort(c.enclosingPosition, "@Tactic detected tactic with inputs but the return type is no input tactic type")
    }

    // Previously, the Tactic macro code tried to ensure that, if a GeneratorArg existed, it was the last argument.
    // However, this check was buggy and would allow GeneratorArgs in any position.
    // The commented-out code below is a fixed version of this check.
    // It is commented out because two tactics in TactixLibrary don't comply with this rule.
    // TODO Uncomment this code and fix the tactics
    // if (definitionArgs.dropRight(1).exists(_.isInstanceOf[GeneratorArg])) {
    //   c.abort(c.enclosingPosition, "Generator argument to tactic must appear after all expression arguments")
    // }
    val generatorDefArg = definitionArgs.find(_.isInstanceOf[GeneratorArg])

    /*
     * The rest
     */

    // Scala types corresponding to tactic inputs
    def typeName(ai: ArgInfo): Tree = {
      ai match {
        case _: GeneratorArg =>
          tq"edu.cmu.cs.ls.keymaerax.btactics.Generator.Generator[edu.cmu.cs.ls.keymaerax.btactics.InvariantGenerator.GenProduct]"
        case _: FormulaArg => tq"edu.cmu.cs.ls.keymaerax.core.Formula"
        case _: StringArg => tq"String"
        case _: NumberArg => tq"edu.cmu.cs.ls.keymaerax.core.Number"
        case _: VariableArg => tq"edu.cmu.cs.ls.keymaerax.core.Variable"
        case _: TermArg => tq"edu.cmu.cs.ls.keymaerax.core.Term"
        case _: SubstitutionArg => tq"edu.cmu.cs.ls.keymaerax.core.SubstitutionPair"
        case _: ExpressionArg => tq"edu.cmu.cs.ls.keymaerax.core.Expression"
        case _: PosInExprArg => tq"edu.cmu.cs.ls.keymaerax.infrastruct.PosInExpr"
        case OptionArg(ai) => tq"scala.Option[${typeName(ai)}]"
        case ListArg(ai) => tq"scala.List[${typeName(ai)}]"
        case ai => c.abort(c.enclosingPosition, "Unimplemented case in @Tactic, could not convert argument spec: " + ai)
      }
    }

    def getBaseTerm(): Tree = {
      // if no "anon" function present, then tactic is a simple forwarding expression like val e: BelleExpr = <tac>
      val hasInputs = definitionArgs.nonEmpty || KNOWN_TACTIC_TYPES_WITH_INPUT.contains(returnType)

      val definitionArgsExpr = definitionArgs
        .map(ai => Ident(TermName(ai.name)))
        .foldRight[Tree](q"Nil") { case (arg, acc) => q"$arg :: $acc" }

      val tFactory = q"new edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory($name)"

      /** The body, but if the function used is in [[ANON_SORTS]], the function is removed. */
      val tRhs = body match {
        case body if funcSort.isDefined => body.rhs
        case BodyFuncLambda(func, params, rhs) => q"$func((..$params) => $rhs)"
        case BodyFunc(func, rhs) => q"$func($rhs)"
        case BodyPlain(rhs) => rhs
      }

      // [[isCoreAnon]] represents "which anon function" was on the RHS of the definition.
      // If this is empty, the @Tactic is a forward to another BelleExpr. [[forward]] has overloads for most (@TODO all)
      // tactic classes, so in each case we just call [[forward]]
      if (funcSort.isEmpty) return q"$tFactory.forward($tRhs)"

      (hasInputs, positionArgs) match {
        case (false, NoPos(None)) if funcSort.contains(UnguardedAnonSort) => q"$tFactory.bys($tRhs)"
        case (false, NoPos(None)) => q"$tFactory.by($tRhs)"
        case (false, NoPos(Some(arg))) if funcSort.contains(UnguardedAnonSort) => q"$tFactory.bys(($arg) => $tRhs)"
        case (false, NoPos(Some(arg))) => q"$tFactory.by(($arg) => $tRhs)"
        case (false, SequentArg(sequentName)) => q"$tFactory.by(($sequentName) => $tRhs)"
        case (false, OnePos(pname, None, _)) => q"$tFactory.by(($pname) => $tRhs)"
        case (false, OnePos(pname, Some(sname), _)) => q"$tFactory.by(($pname, $sname) => $tRhs)"
        case (true, NoPos(None)) => q"$tFactory.byWithInputs($definitionArgsExpr, $tRhs)"
        case (true, NoPos(Some(pname))) if definitionArgs.nonEmpty && definitionArgs.head.isInstanceOf[StringArg] =>
          q"$tFactory.byWithInputsS($definitionArgsExpr, ($pname) => $tRhs)"
        case (true, NoPos(Some(pname))) => q"$tFactory.byWithInputsP($definitionArgsExpr, ($pname) => $tRhs)"
        case (true, SequentArg(sequentName)) => q"$tFactory.byWithInputs($definitionArgsExpr, ($sequentName) => $tRhs)"
        case (true, OnePos(pname, None, _)) => q"$tFactory.byWithInputs($definitionArgsExpr, ($pname) => $tRhs)"
        case (true, OnePos(pname, Some(sname), false)) =>
          q"$tFactory.byWithInputs($definitionArgsExpr, ($pname, $sname) => $tRhs)"
        case (true, OnePos(pname, Some(sname), true)) =>
          q"$tFactory.byWithInputsP($definitionArgsExpr, ($pname, $sname) => $tRhs)"
        case (false, AntePos(None, pname)) => q"$tFactory.byL(($pname) => $tRhs)"
        case (false, AntePos(Some(sname), pname)) =>
          if (funcSort.contains(CoreAnonSort)) q"$tFactory.coreby(($sname, $pname) => $tRhs)"
          else q"$tFactory.by(($sname, $pname) => $tRhs)"
        case (true, AntePos(Some(sname), pname)) =>
          q"$tFactory.corebyWithInputsL($definitionArgsExpr, ($sname, $pname) => $tRhs)"
        case (false, SuccPos(None, pname)) => q"$tFactory.byR(($pname) => $tRhs)"
        case (false, SuccPos(Some(sname), pname)) =>
          if (funcSort.contains(CoreAnonSort)) q"$tFactory.coreby(($sname, $pname) => $tRhs)"
          else q"$tFactory.by(($sname, $pname) => $tRhs)"
        case (true, SuccPos(Some(sname), pname)) =>
          q"$tFactory.corebyWithInputsR($definitionArgsExpr, ($sname, $pname) => $tRhs)"
        case (false, AnteSuccPos(sname, pname)) => q"$tFactory.byLR(($sname, $pname) => $tRhs)"
        case (false, TwoPos(provable, pos1, pos2)) => q"$tFactory.by((($provable, $pos1, $pos2) => $tRhs))"
        case (true, TwoPos(provable, pos1, pos2)) =>
          q"$tFactory.byWithInputs($definitionArgsExpr, (($provable, $pos1, $pos2) => $tRhs))"
        case (true, _: SuccPos | _: AntePos | _: AnteSuccPos) => c
            .abort(c.enclosingPosition, "Argument combination not yet supported")
        case _ =>
          c.abort(c.enclosingPosition, s"Unsupported argument combination in @Tactic: $definitionArgs; $positionArgs; ")
      }
    }

    val baseType = definition.returnType
    val baseTerm = getBaseTerm()

    def argInfoToValDef(info: ArgInfo): ValDef = ValDef(Modifiers(), TermName(info.name), typeName(info), EmptyTree)

    val (curriedTerm, _) = definitionArgs.foldRight[(Tree, Tree)]((baseTerm, baseType))({ case (arg, (acc, accTy)) =>
      val argTy = typeName(arg)
      val funTy = tq"""edu.cmu.cs.ls.keymaerax.btactics.macros.TypedFunc[$argTy, $accTy]"""
      val argDef = argInfoToValDef(arg)
      val term = q"""(($argDef) => $acc): $funTy"""
      (term, funTy)
    })

    val definitionArgsExprs: Seq[ValDef] = definitionArgs.map(argInfoToValDef)

    def sdContains(sd: DisplaySequent, s: String): Boolean = {
      sd.ante.exists(n => n.contains(s)) || sd.succ.exists(n => n.contains(s))
    }

    val displayInputs: List[ArgInfo] = if (inputs.nonEmpty) inputs else definitionArgs
    val needsGenerator = generatorDefArg.isDefined

    // Error check:
    // The web UI uses the axiom/rule display to let the user input arguments of a tactic.
    // This requires every argument name to appear in the display info.
    if (args.displayLevel != DisplayLevelInternal) {
      for (input <- displayInputs) {
        val name = input.name

        val shouldMentionInputButDoesnt = display match {
          case _: AxiomDisplayInfo | _: SimpleDisplayInfo => true
          case d: InputAxiomDisplayInfo => !d.formula.contains(name)
          case d: RuleDisplayInfo => !(sdContains(d.conclusion, name) || d.premises.exists(sd => sdContains(sd, name)))
        }

        if (shouldMentionInputButDoesnt) {
          c.abort(c.enclosingPosition, s"Tactic must mention every input in DisplayInfo, but $name is not mentioned")
        }
      }
    }

    val expr = q"((_: Unit) => ($curriedTerm))"

    val info = returnType match {
      case "DependentTactic" | "BuiltInTactic" | "BelleExpr" => q"""
        new edu.cmu.cs.ls.keymaerax.btactics.macros.PlainTacticInfo(
          codeName = $name,
          display = ${astForDisplayInfo(display)(c)},
          needsGenerator = $needsGenerator,
          revealInternalSteps = ${args.revealInternalSteps},
        )(theExpr = $expr)
      """

      case "InputTactic" | "StringInputTactic" => q"""
        new edu.cmu.cs.ls.keymaerax.btactics.macros.InputTacticInfo(
          codeName = $name,
          display = ${astForDisplayInfo(display)(c)},
          inputs = ${displayInputs.map(ai => astForArgInfo(ai)(c))},
          needsGenerator = $needsGenerator,
          revealInternalSteps = ${args.revealInternalSteps},
        )(theExpr = $expr)
      """

      case "DependentPositionTactic" | "BuiltInLeftTactic" | "BuiltInRightTactic" | "BuiltInPositionTactic" |
          "CoreLeftTactic" | "CoreRightTactic" => q"""
        new edu.cmu.cs.ls.keymaerax.btactics.macros.PositionTacticInfo(
          codeName = $name,
          display = ${astForDisplayInfo(display)(c)},
          needsGenerator = $needsGenerator,
          revealInternalSteps = ${args.revealInternalSteps},
        )(theExpr = $expr)
      """

      case "InputPositionTactic" | "DependentPositionWithAppliedInputTactic" => q"""
        new edu.cmu.cs.ls.keymaerax.btactics.macros.InputPositionTacticInfo(
          codeName = $name,
          display = ${astForDisplayInfo(display)(c)},
          inputs = ${displayInputs.map(ai => astForArgInfo(ai)(c))},
          needsGenerator = $needsGenerator,
          revealInternalSteps = ${args.revealInternalSteps},
        )(theExpr = $expr)
      """

      case "DependentTwoPositionTactic" | "InputTwoPositionTactic" | "BuiltInTwoPositionTactic" => q"""
        new edu.cmu.cs.ls.keymaerax.btactics.macros.TwoPositionTacticInfo(
          codeName = $name,
          display = ${astForDisplayInfo(display)(c)},
          needsGenerator = $needsGenerator,
        )(theExpr = $expr)
      """

      case "AppliedBuiltInTwoPositionTactic" => q"""
        new edu.cmu.cs.ls.keymaerax.btactics.macros.InputTwoPositionTacticInfo(
          codeName = $name,
          display = ${astForDisplayInfo(display)(c)},
          needsGenerator = $needsGenerator,
        )(theExpr = $expr)
      """

      case _ =>
        c.abort(definition.returnType.pos, s"@Tactic return type must be one of ${KNOWN_TACTIC_TYPES.mkString(", ")}")
    }

    // Add annotation for runtime reflection-based detection of tactics.
    val mods = Modifiers(
      definition.mods.flags,
      definition.mods.privateWithin,
      q"new edu.cmu.cs.ls.keymaerax.btactics.macros.InternalAnnotation()" :: definition.mods.annotations,
    )

    // Macro cannot introduce new statements or declarations, so introduce a library call which achieves our goal of
    // registering the tactic info to the global tactic info table.
    val result = definition match {
      case d: DefinitionDefParams => q"""
        $mods def ${d.declName}(..$definitionArgsExprs): ${d.returnType} =
          edu.cmu.cs.ls.keymaerax.btactics.macros.DerivationInfo.registerL($baseTerm, $info)
      """
      case d: DefinitionDef => q"""
        $mods def ${d.declName}: ${d.returnType} =
          edu.cmu.cs.ls.keymaerax.btactics.macros.DerivationInfo.registerL($baseTerm, $info)
      """
      case d: DefinitionVal => q"""
        $mods val ${d.declName}: ${d.returnType} =
          edu.cmu.cs.ls.keymaerax.btactics.macros.DerivationInfo.registerL($baseTerm, $info)
      """
    }

    c.Expr[Nothing](result)
  }
}
