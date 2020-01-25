/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.btactics.DerivationInfo.AxiomNotFoundException
import edu.cmu.cs.ls.keymaerax.btactics.InvariantGenerator.GenProduct
import edu.cmu.cs.ls.keymaerax.btactics.arithmetic.speculative.ArithmeticSpeculativeSimplification
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.btactics.components.ComponentSystem
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig

import scala.collection.immutable.HashMap
import scala.language.implicitConversions
import scala.reflect.runtime.universe.TypeTag
import scala.util.Try

/**
  * Since axioms are always referred to by their names (which are strings), we have the following problems:
  * 1) It's hard to keep everything up to date when a new axiom is added
  * 2) We don't get any static exhaustiveness checking when we case on an axiom
  *
  * AxiomInfo exists to help fix that. An AxiomInfo is just a collection of per-axiom information. The tests for
  * this object dynamically ensure it is exhaustive with respect to AxiomBase and DerivedAxioms. By adding a new
  * field to AxiomInfo you can ensure that all new axioms will have to have that field.
  * Created by bbohrer on 12/28/15.
  */

/** UI display information on how to show an axiom, rule, or tactic application */
sealed trait DisplayInfo {
  /** how to render an axiom/rule/tactic name in the UI */
  def name: String
  /** how to render an axiom/rule/tactic name in ASCII plain text */
  def asciiName: String
}
case class SimpleDisplayInfo(override val name: String, override val asciiName: String) extends DisplayInfo
case class RuleDisplayInfo(names: SimpleDisplayInfo, conclusion: SequentDisplay, premises:List[SequentDisplay]) extends DisplayInfo {
  override def name = names.name
  override def asciiName = names.asciiName
}
case class SequentDisplay(ante: List[String], succ: List[String], isClosed: Boolean = false)
case class AxiomDisplayInfo(names: SimpleDisplayInfo, displayFormula: String) extends DisplayInfo {
  override def name = names.name
  override def asciiName = names.asciiName
}
case class InputAxiomDisplayInfo(names: SimpleDisplayInfo, displayFormula: String, input: List[ArgInfo]) extends DisplayInfo {
  override def name = names.name
  override def asciiName = names.asciiName
}

/** Typed functions to circumvent type erasure of arguments and return types. */
abstract class TypedFunc[-A: TypeTag, +R: TypeTag] extends (A => R) {
  val retType: TypeTag[_] = scala.reflect.runtime.universe.typeTag[R]
  val argType: TypeTag[_] = scala.reflect.runtime.universe.typeTag[A]
}
/** Creates TypedFunc implicitly, e.g., by ((x: String) => x.length): TypedFunc[String, Int]  */
object TypedFunc {
  implicit def apply[A: TypeTag, R: TypeTag](f: A => R): TypedFunc[A, R] = f match {
    case tf: TypedFunc[A, R]  => tf
    case _ => new TypedFunc[A, R] { final def apply(arg: A): R = f(arg) }
  }
}

/**
  * Central list of all derivation steps (axioms, derived axioms, proof rules, tactics)
  * with meta information of relevant names and display names and visualizations for the user interface.
  */
object DerivationInfo {
  implicit def displayInfo(name: String): SimpleDisplayInfo = {SimpleDisplayInfo(name, name)}
  implicit def displayInfo(pair: (String, String)): SimpleDisplayInfo = SimpleDisplayInfo(pair._1, pair._2)
  implicit def sequentDisplay(succAcc:(List[String], List[String])): SequentDisplay = {
    SequentDisplay(succAcc._1, succAcc._2)
  }
  implicit def sequentDisplay(succAccClosed:(List[String], List[String], Boolean)): SequentDisplay = {
    SequentDisplay(succAccClosed._1, succAccClosed._2, succAccClosed._3)
  }

  case class AxiomNotFoundException(axiomName: String) extends ProverException("Axiom with said name not found: " + axiomName)

  //@todo
  private val needsCodeName = "TODOTHISAXIOMSTILLNEEDSACODENAME"
  /** Unsure whether linear matcher suffices so default to false */
  //@todo avoid the use of unsure
  private val unsure = false
  /** unsure because of variable renaming being separate from substitution */
  private val unren = false

  private def useAt(l:Lemma):DependentPositionTactic = HilbertCalculus.useAt(l)
  private val posnil = TacticFactory.anon((pos,seq) => TactixLibrary.nil)

  private def convert(rules: Map[String,ProvableSig]): List[DerivationInfo] =
  //@todo display info is rather impoverished
    rules.keys.map(name => AxiomaticRuleInfo(name, SimpleDisplayInfo(name, name), canonicalize(name))).toList
  private def canonicalize(name: String): String = name.filter(c => c.isLetterOrDigit)

  private lazy val modalityInfos: List[DerivationInfo] = List(
    // [a] modalities and <a> modalities
    new CoreAxiomInfo("<> diamond"
      , AxiomDisplayInfo(("<·>", "<.>"), "<span class=\"k4-axiom-key\">&not;[a]&not;P</span> ↔ &langle;a&rangle;P")
      , "diamond", true, {case () => HilbertCalculus.diamond}),
    PositionTacticInfo("diamondd"
      , AxiomDisplayInfo(("<·>d", "<.>d"), "<span class=\"k4-axiom-key\">&langle;a&rangle;P</span> ↔ &not;[a]&not;P")
      , {case () => HilbertCalculus.useAt("<> diamond", PosInExpr(1::Nil))}),
    new DerivedAxiomInfo("[] box"
      , AxiomDisplayInfo(("[·]", "[.]"), "<span class=\"k4-axiom-key\">&not;&langle;a&rangle;&not;P</span> ↔ &langle;a&rangle;P")
      , "box", true, {case () => HilbertCalculus.useAt(DerivedAxioms.boxAxiom)}),
    PositionTacticInfo("boxd"
      , AxiomDisplayInfo(("[·]d", "[.]d"), "<span class=\"k4-axiom-key\">[a]P</span> ↔ &not;&langle;a&rangle;&not;P")
      , {case () => HilbertCalculus.useAt(DerivedAxioms.boxAxiom, PosInExpr(1::Nil))}),
    new PositionTacticInfo("assignb"
      , AxiomDisplayInfo("[:=]", "<span class=\"k4-axiom-key\">[x:=e]p(x)</span>↔p(e)")
      , {case () => TactixLibrary.assignb}, revealInternalSteps = true),
    new CoreAxiomInfo("[:=] assign", "[:=]", "assignbAxiom", false, {case () => HilbertCalculus.useAt("[:=] assign")}),
    new CoreAxiomInfo("[:=] self assign", "[:=]", "selfassignb", unsure, {case () => HilbertCalculus.useAt("[:=] self assign")}),
    new CoreAxiomInfo("[:=] self assign y", "[:=]y", "selfassignby", unsure, {case () => HilbertCalculus.useAt("[:=] self assign")}),
    new DerivedAxiomInfo("<:=> assign", AxiomDisplayInfo("<:=>", "<span class=\"k4-axiom-key\">&langle;x:=e&rangle;p(x)</span>↔p(e)"), "assignd", false, {case () => HilbertCalculus.assignd}),
    new DerivedAxiomInfo("<:=> self assign", "<:=>", "selfassignd", unsure, {case () => HilbertCalculus.useAt("<:=> self assign")}),
    new DerivedAxiomInfo("<:=> assign equality", "<:=>", "assigndEquality", unsure, {case () => HilbertCalculus.useAt("<:=> assign equality")}),
    new DerivedAxiomInfo("<:=> assign equality all", "<:=>", "assigndEqualityAll", unsure, {case () => HilbertCalculus.useAt("<:=> assign equality all")}),
    new CoreAxiomInfo("[:=] assign equality", "[:=]=", "assignbeq", unsure, {case () => HilbertCalculus.useAt("[:=] assign equality")}),
    new CoreAxiomInfo("[:=] assign equality y", "[:=]=y", "assignbeqy", unsure, {case () => HilbertCalculus.useAt("[:=] assign equality y")}),
    new PositionTacticInfo("assignEquality", "[:=]=", {case () => DLBySubst.assignEquality}, revealInternalSteps = true),
    new DerivedAxiomInfo("[:=] assign exists", ("[:=]∃","[:=]exists"), "assignbexists", unsure, {case () => HilbertCalculus.useAt(DerivedAxioms.assignbImpliesExistsAxiom) }),
    new DerivedAxiomInfo("[:=] assign all", ("[:=]∀","[:=]all"), "assignball", unsure, {case () => HilbertCalculus.useAt(DerivedAxioms.forallImpliesAssignbAxiom) }),
    new DerivedAxiomInfo("[:=] assign equality exists", ("[:=]","[:=] assign exists"), "assignbequalityexists", unsure, {case () => HilbertCalculus.useAt(DerivedAxioms.assignbEquationalAxiom) }),
    new InputPositionTacticInfo("assignbExistsRule",
      RuleDisplayInfo(
        "[:=] assign exists",
        /* conclusion */ (List("&Gamma;"), List("∃t [x:=t;]P", "&Delta;")),
        /* premises */ List( (List("&Gamma;"), List("[t:=e;][x:=t;]P", "&Delta;")) )
      ),
      List(TermArg("e")),
      _ => ((e: Term) => DLBySubst.assignbExists(e)): TypedFunc[Term, BelleExpr]
    ),
    new CoreAxiomInfo("[':=] differential assign"
      , AxiomDisplayInfo(("[:=]","[:=]"), "<span class=\"k4-axiom-key\">[x′:=c]p(x′)</span>↔p(c)")
      , "Dassignb", false, {case () => HilbertCalculus.Dassignb}),
    new DerivedAxiomInfo("[':=] differential assign y"
      , AxiomDisplayInfo(("[y′:=]","[y':=]"), "<span class=\"k4-axiom-key\">[y′:=c]p(y′)</span>↔p(c)")
      , "Dassignby", false, {case () => useAt(DerivedAxioms.assignDAxiomby)}),
    new CoreAxiomInfo("[:*] assign nondet"
      , AxiomDisplayInfo("[:*]", "<span class=\"k4-axiom-key\">[x:=*]p(x)</span>↔∀x p(x)")
      , "randomb", unren, {case () => HilbertCalculus.randomb}),
    new CoreAxiomInfo("[?] test"
      , AxiomDisplayInfo("[?]", "<span class=\"k4-axiom-key\">[?Q]P</span>↔(Q→P)")
      , "testb", true, {case () => HilbertCalculus.testb}),
    new DerivedAxiomInfo("<?> test", "<?>", "testd", true, {case () => HilbertCalculus.testd}),
    new DerivedAxiomInfo("<?> combine", "<?> combine", "testdcombine", true, {case () => useAt(DerivedAxioms.combineTestdAxiom)}),
    new DerivedAxiomInfo("<?> invtest", "<?>i", "invtestd", true, {case () => useAt(DerivedAxioms.invTestdAxiom)}),
    new CoreAxiomInfo("[++] choice"
      , AxiomDisplayInfo(("[∪]", "[++]"), "<span class=\"k4-axiom-key\">[a∪b]P</span>↔[a]P∧[b]P"), "choiceb", true, {case () => HilbertCalculus.choiceb}),
    new DerivedAxiomInfo("<++> choice", ("<∪>", "<++>"), "choiced", true, {case () => HilbertCalculus.choiced}),
    new CoreAxiomInfo("[;] compose"
      , AxiomDisplayInfo("[;]", "<span class=\"k4-axiom-key\">[a;b]P</span>↔[a][b]P")
      , "composeb", true, {case () => HilbertCalculus.composeb}),
    new DerivedAxiomInfo("<;> compose", "<;>", "composed", true, {case () => HilbertCalculus.composed}),
    new CoreAxiomInfo("[*] iterate"
      , AxiomDisplayInfo("[*]", "<span class=\"k4-axiom-key\">[a*]P</span>↔P∧[a][a*]P")
      , "iterateb", true, {case () => HilbertCalculus.iterateb}),
    new DerivedAxiomInfo("<*> iterate", "<*>", "iterated", true, {case () => HilbertCalculus.iterated}),
    new CoreAxiomInfo("<d> dual"
      , AxiomDisplayInfo(("<d>", "<d>"), "<span class=\"k4-axiom-key\">&langle;a<sup>d</sup>&rangle;P</span>↔¬&langle;a&rangle;¬P"), "duald", true, {case () => HilbertCalculus.duald}),
    new DerivedAxiomInfo("[d] dual"
      , AxiomDisplayInfo(("[d]", "[d]"), "<span class=\"k4-axiom-key\">[a<sup>d</sup>]P</span>↔¬[a]¬P"), "dualb", true, {case () => HilbertCalculus.dualb}),
    new DerivedAxiomInfo("[d] dual direct"
      , AxiomDisplayInfo(("[d]", "[d]"), "<span class=\"k4-axiom-key\">[a<sup>d</sup>]P</span>↔&langle;a&rangle;P"), "dualDirectb", true, {case () => HilbertCalculus.useAt(DerivedAxioms.dualbDirectAxiom)}),
    new DerivedAxiomInfo("<d> dual direct"
      , AxiomDisplayInfo(("<d>", "<d>"), "<span class=\"k4-axiom-key\">&langle;a<sup>d</sup>&rangle;P</span>↔[a]P"), "dualDirectd", true, {case () => HilbertCalculus.useAt(DerivedAxioms.dualdDirectAxiom)}),
    new CoreAxiomInfo("K modal modus ponens", "K", "K", true, {case () => TactixLibrary.K}),
    //@note the tactic I has a codeName and belleExpr, but there's no tactic that simply applies the I axiom
    CoreAxiomInfo("I induction"
      , AxiomDisplayInfo(("I<sub>→</sub>", "Iimp"), "P∧[a*](P→[a]P)→<span class=\"k4-axiom-key\">[a*]P</span>"), "Iind", unsure, {case () => HilbertCalculus.useAt("I induction") }),
    new CoreAxiomInfo("VK vacuous"
      , AxiomDisplayInfo("VK", "(p→<span class=\"k4-axiom-key\">[a]p</span>)←[a]T")
      , "VK", unsure, {case () => HilbertCalculus.VK}),
    new DerivedAxiomInfo("V vacuous"
      , AxiomDisplayInfo("V", "p→<span class=\"k4-axiom-key\">[a]p</span>")
      , "V", unsure, {case () => HilbertCalculus.V}),
    new CoreAxiomInfo("[]T system"
      , AxiomDisplayInfo("[]T", "[a]true")
      , "boxTrue", true, {case () => HilbertCalculus.boxTrue})
  )

  private lazy val odeInfos: List[DerivationInfo] = List(
    new CoreAxiomInfo("DW base", "DWbase", "DWbase", true, {case () => HilbertCalculus.DW}),
    PositionTacticInfo("dW"
      , RuleDisplayInfo("Differential Weaken"
        , /* conclusion */ (List("&Gamma;"),List("[{x′=f(x) & Q}]p(x)","&Delta;"))
        , /* premises */ List((List("&Gamma;<sub>const</sub>", "Q"), List("p(x)", "&Delta;<sub>const</sub>"))))
      , {case () => DifferentialTactics.diffWeaken}, revealInternalSteps = true),
    PositionTacticInfo("dWplus"
      , RuleDisplayInfo("Assumption-Preserving Differential Weaken"
        , /* conclusion */ (List("&Gamma;"),List("[{x′=f(x) & Q}]p(x)","&Delta;"))
        , /* premises */ List((List("&Gamma;<sub>const</sub>", "Q"), List("p(x)", "&Delta;<sub>const</sub>"))))
      , {case () => DifferentialTactics.diffWeakenPlus}, revealInternalSteps = true),
    new DerivedAxiomInfo("DC differential cut"
      , InputAxiomDisplayInfo("DC","(<span class=\"k4-axiom-key\">[{x′=f(x)&Q}]P</span>↔[{x′=f(x)&Q∧R}]P)←[{x′=f(x)&Q}]R", List(FormulaArg("R")))
      , "DC", true, {case () => HilbertCalculus.useAt("DC differential cut")}),
    InputPositionTacticInfo("dC"
      , RuleDisplayInfo("Differential Cut"
        , /* conclusion */ (List("&Gamma;"),List("[{x′=f(x) & Q}]P","&Delta;"))
        , /* premises */ List((List("&Gamma;"), List("[{x′=f(x) & Q}]R", "&Delta;")),
          (List("&Gamma;"), List("[{x′=f(x) & (Q∧R)}]P","&Delta;"))))
      , List(FormulaArg("R")) //@todo should be ListArg -> before merge, we already had lists in concrete Bellerophon syntax
      , _ => ((fml: Formula) => TactixLibrary.dC(fml)): TypedFunc[Formula, BelleExpr], revealInternalSteps = true),
    InputPositionTacticInfo("dR"
      , RuleDisplayInfo("Differential Refine"
        , /* conclusion */ (List("&Gamma;"),List("[{x′=f(x) & Q}]P","&Delta;"))
        , /* premises */ List((List("&Gamma;"), List("[{x′=f(x) & Q}]R", "&Delta;")),
          (List("&Gamma;"), List("[{x′=f(x) & R}]P","&Delta;"))))
      , List(FormulaArg("R")) //@todo should be ListArg -> before merge, we already had lists in concrete Bellerophon syntax
      , _ => ((fml: Formula) => DifferentialTactics.diffRefine(fml)): TypedFunc[Formula, BelleExpr]),
    PositionTacticInfo("dCi"
      , RuleDisplayInfo("dCi"
        , /* conclusion */ (List("&Gamma;"),List("[{x′=f(x) & (Q∧R)}]P","&Delta;"))
        , /* premises */ List(
          (List("&Gamma;"), List("[{x′=f(x) & Q}]P", "&Delta;")),
          (List("&Gamma;"), List("R", "&Delta;"))))
      , _ => DifferentialTactics.inverseDiffCut),
    new CoreAxiomInfo("DMP differential modus ponens"
      , InputAxiomDisplayInfo("DMP","(<span class=\"k4-axiom-key\">[{x′=f(x)&Q}]P</span>←[{x′=f(x)&R}]P)←[{x′=f(x)&Q}](Q→R)", List(FormulaArg("R")))
      , "DMP", true, {case () => HilbertCalculus.useAt("DMP differential modus ponens")}),
    new DerivedAxiomInfo("DR differential refine"
      , InputAxiomDisplayInfo("DR","(<span class=\"k4-axiom-key\">[{x′=f(x)&Q}]P</span>←[{x′=f(x)&R}]P)←[{x′=f(x)&Q}]R", List(FormulaArg("R")))
      , "DR", true, {case () => HilbertCalculus.useAt("DR differential refine")}),
    new DerivedAxiomInfo("DR<> differential refine"
      , InputAxiomDisplayInfo("DRd","(<span class=\"k4-axiom-key\"><{x′=f(x)&Q}>P</span>←<{x′=f(x)&R}>P)←[{x′=f(x)&R}]Q", List(FormulaArg("R")))
      , "DRd", true, {case () => HilbertCalculus.useAt("DR<> differential refine")}),
    new CoreAxiomInfo("RI& closed real induction >=", "RI& >=", "RIclosedgeq", unsure,
      {case () => HilbertCalculus.useAt("RI& closed real induction >=")}),
    new CoreAxiomInfo("Cont continuous existence", "Cont", "Cont", unsure,
      {case () => HilbertCalculus.useAt("Cont continuous existence")}),
    new CoreAxiomInfo("Uniq uniqueness", "Uniq", "Uniq", unsure,
      {case () => HilbertCalculus.useAt("Uniq uniqueness")}),
    { val converter = (e: Expression) => e match {
        case n: Number => Left(n)
        case _ => Right("Expected a number but got " + e.prettyString)
      }
      InputPositionTacticInfo("autoApproximate",
        RuleDisplayInfo("Approximate",
          (List("&Gamma;"), List("[{X'=F & &Alpha;(n)}]", "&Delta;")),
          List( (List("&Gamma;"), List("[{X'=F}]", "&Delta;")) )
        ),
        List(ExpressionArg("n", Nil, converter)),
        _ => ((e: Expression) => converter(e) match {
          case Left(n: Number) => Approximator.autoApproximate(n)
          case Right(msg) => throw new IllegalArgumentException(msg)
        }) : TypedFunc[Number, BelleExpr]
      )
    },
    { val nConverter = (e: Expression) => e match {
        case n: Number => Left(n)
        case _ => Right("Expected a number but got " + e.prettyString)
      }
      val eConverter = (e: Expression) => e match {
        case v: Variable => Left(v)
        case _ => Right("Expected a variable but got " + e.prettyString)
      }
      InputPositionTacticInfo("expApproximate",
        RuleDisplayInfo("e'=e Approximation",
          (List("&Gamma;"), List("[{c1,e'=e,c2 & approximate(n)}]", "&Delta;")),
          List( (List("&Gamma;"), List("[{c1,e'=c,c2}]", "&Delta;")) )
        ),
        List(ExpressionArg("e", "e"::Nil), ExpressionArg("n", Nil, nConverter)),
        _ =>
          ((e: Expression) => (eConverter(e) match {
              case Left(v: Variable) => (n: Expression) => nConverter(n) match {
                case Left(n: Number) => Approximator.expApproximate(v, n)
                case Right(msg) => throw new IllegalArgumentException(msg)
              }
              case Right(msg) => throw new IllegalArgumentException(msg)
            }): TypedFunc[Expression, BelleExpr]
          ): TypedFunc[Expression, TypedFunc[Expression, BelleExpr]]
      )
    },
    {
      val nConverter = (e: Expression) => e match {
        case n: Number => Left(n)
        case _ => Right("Expected a number but got " + e.prettyString)
      }
      val vConverter = (e: Expression) => e match {
        case v: Variable => Left(v)
        case _ => Right("Expected a variable but got " + e.prettyString)
      }
      InputPositionTacticInfo("circularApproximate",
        RuleDisplayInfo("Circular Dynamics Approximation",
          (List("&Gamma;"), List("[{c1,s'=c,c2,c'=-s,c3 & approximate(n)}]", "&Delta;")),
          List((List("&Gamma;"), List("[{c1,e'=c,c2}]", "&Delta;")))
        ),
        List(ExpressionArg("s", "s" :: Nil, vConverter), ExpressionArg("c", "c" :: Nil, vConverter), ExpressionArg("n", Nil, nConverter)),
        _ =>
          ((s: Expression) => vConverter(s) match {
            case Left(sv: Variable) => ((c: Expression) => vConverter(c) match {
              case Left(cv: Variable) => ((n: Expression) => nConverter(n) match {
                case Left(nn: Number) => Approximator.circularApproximate(sv, cv, nn)
                case Right(msg) => throw new IllegalArgumentException(msg)
              }): TypedFunc[Expression, BelleExpr]
              case Right(msg) => throw new IllegalArgumentException(msg)
            }): TypedFunc[Expression, TypedFunc[Expression, BelleExpr]]
            case Right(msg) => throw new IllegalArgumentException(msg)
          }): TypedFunc[Expression, TypedFunc[Expression, TypedFunc[Expression, BelleExpr]]]
      )
    },
    {
      val converter = (e: Expression) => e match {
        case Equal(l: DifferentialSymbol, r) => Left(AtomicODE(l, r))
        case dp: DifferentialProgram => Left(dp)
        case _ => Right("Expected a differential program y′=f(y), but got " + e.prettyString)
      }
      InputPositionTacticInfo("dG",
        RuleDisplayInfo(
          "Differential Ghost",
          /* conclusion */ (List("&Gamma;"), List("[{x′=f(x) & Q}]P", "&Delta;")),
          /* premises */ List( (List("&Gamma;"), List("∃y [{x′=f(x),E & Q}]P", "&Delta;")) )
        ),
        List(ExpressionArg("E", "y"::"x"::"y'"::Nil, converter), FormulaArg("P", "y"::Nil)),
        _ =>
          ((f: Expression) =>
            ((p: Option[Formula]) => converter(f) match {
              case Left(dp: DifferentialProgram) => TactixLibrary.dG(dp, p)
              case Left(e) => throw new IllegalStateException("Expected a differential program, but expression converter produced " + e.prettyString)
              case Right(msg) => throw new IllegalArgumentException(msg)
            }) :  TypedFunc[Option[Formula], BelleExpr]
            ) : TypedFunc[Expression, TypedFunc[Option[Formula], BelleExpr]]
        ,
        revealInternalSteps = true
      )
    },
    PositionTacticInfo("dGi",
      RuleDisplayInfo(
        "Inverse Differential Ghost",
        /* conclusion */ (List("&Gamma;"), List("∃y [{x′=f(x),E & Q}]P", "&Delta;")),
        /* premises */ List( (List("&Gamma;"), List("[{x′=f(x) & Q}]P", "&Delta;")) )
      ),
      _ => DifferentialTactics.inverseDiffGhost
    ),
    InputPositionTacticInfo("dbx",
      RuleDisplayInfo(
        "Darboux (in)equalities",
        /* conclusion */ (List("p≳0"), List("[{x′=f(x) & Q}]p≳0")),
        /* premises */ List( (List("Q"), List("p' ≥ gp")) )
      ),
      List(OptionArg(TermArg("g"))),
      _ => {
        case Some(g: Term) => DifferentialTactics.dgDbx(g)
        case None => DifferentialTactics.dgDbxAuto
      }: TypedFunc[Option[Term], BelleExpr]
    ),
    PositionTacticInfo("diffUnpackEvolDomain",
      RuleDisplayInfo(
        "Unpack evolution domain",
        /* conclusion */ (List("&Gamma;"), List("[{x′=f(x) & Q}]P","&Delta;")),
        /* premises */ List( (List("&Gamma;","Q"), List("[{x′=f(x) & Q}]P","&Delta;")) )
      ),
      _ => DifferentialTactics.diffUnpackEvolutionDomainInitially
      , needsTool = false
    ),
    PositionTacticInfo("barrier",
      RuleDisplayInfo(
        "Strict Barrier Certificate",
        /* conclusion */ (List("p≳0"), List("[{x′=f(x) & Q}]p≳0")),
        /* premises */ List( (List("Q ∧ p=0"), List("p'>0")) )
      ),
      _ => DifferentialTactics.dgBarrier
      , needsTool = true
    ),
    PositionTacticInfo("dRI",
      RuleDisplayInfo(
        "(Conj.) Differential Radical Invariants",
        /* conclusion */ (List("p*=0"), List("[{x′=f(x) & Q}]p=0")),
        /* premises */ List( (List("Q"), List("p*=0")) )
      ),
      _ => ODEInvariance.dRI
      , needsTool = true
    ),
    new InputPositionTacticInfo("dGold",
      RuleDisplayInfo(
        "Differential Ghost",
        /* conclusion */ (List("&Gamma;"), List("[{x′=f(x) & Q}]P", "&Delta;")),
        /* premises */ List( (List("&Gamma;"), List("∃y [{x′=f(x),y′=a(x)*y+b(x) & Q}]P", "&Delta;")) )
      ),
      List(VariableArg("y", "y"::Nil), TermArg("a(x)"), TermArg("b(x)"), FormulaArg("P", "y"::Nil)),
      _ =>
        ((y: Variable) =>
          ((t1: Term) =>
            ((t2: Term) =>
              ((p: Option[Formula]) => TactixLibrary.dG(AtomicODE(DifferentialSymbol(y), Plus(Times(t1, y), t2)), p)
                ): TypedFunc[Option[Formula], BelleExpr]
              ): TypedFunc[Term, TypedFunc[Option[Formula], BelleExpr]]
            ): TypedFunc[Term, TypedFunc[Term, TypedFunc[Option[Formula], BelleExpr]]]
          ): TypedFunc[Variable, TypedFunc[Term, TypedFunc[Term, TypedFunc[Option[Formula], BelleExpr]]]]
    ),

    new CoreAxiomInfo("DE differential effect"
      , AxiomDisplayInfo("DE", "<span class=\"k4-axiom-key\">[{x′=f(x)&Q}]P</span>↔[x′=f(x)&Q][x′:=f(x)]P")
      , "DE", unsure, {case () => HilbertCalculus.DE}),
    new CoreAxiomInfo("DE differential effect (system)"
      , AxiomDisplayInfo("DE", "<span class=\"k4-axiom-key\">[{x′=F,c&Q}]P</span>↔[{c,x′=F&Q}][x′:=f(x)]P")
      , "DEs", unsure, {case () => HilbertCalculus.DE}),
    new CoreAxiomInfo("DE differential effect (system) y"
      , AxiomDisplayInfo("DEsysy", "<span class=\"k4-axiom-key\">[{y′=F,c&Q}]P</span>↔[{c,y′=F&Q}][y′:=f(x)]P")
      , "DEsysy", unsure, {case () => HilbertCalculus.useAt("DE differential effect (system) y")}),
    new CoreAxiomInfo("DI differential invariance"
      , AxiomDisplayInfo("DI", "(<span class=\"k4-axiom-key\">[{x′=f(x)&Q}]P</span>↔[?Q]P)←(Q→[{x′=f(x)&Q}](P)′)")
      , "DIequiv", true, {case () => HilbertCalculus.useAt("DI differential invariance")}),
    new DerivedAxiomInfo("DI differential invariant"
      , AxiomDisplayInfo("DI", "<span class=\"k4-axiom-key\">[{x′=f(x)&Q}]P</span>←(Q→P∧[{x′=f(x)&Q}](P)′)")
      , "DI", true, {case () => HilbertCalculus.DI}),
    new CoreAxiomInfo("DG differential ghost"
      , AxiomDisplayInfo("DG", "<span class=\"k4-axiom-key\">[{x′=f(x)&Q}]P</span>↔∃y [{x′=f(x),y′=a*y+b&Q}]P")
      , "DGa", unsure, {case () => HilbertCalculus.useAt("DG differential ghost")}),
    new CoreAxiomInfo("DG differential ghost constant"
      , AxiomDisplayInfo("DG", "<span class=\"k4-axiom-key\">[{x′=f(x)&Q}]P</span>↔∃y [{x′=f(x),y′=g()&Q}]P")
      , "DGC", unsure, {case () => HilbertCalculus.useAt("DG differential ghost constant")}),
    new CoreAxiomInfo("DG differential ghost constant all"
      , AxiomDisplayInfo("DGa", "<span class=\"k4-axiom-key\">[{x′=f(x)&Q}]P</span>↔∀y [{x′=f(x),y′=g()&Q}]P")
      , "DGCa", unsure, {case () => HilbertCalculus.useAt("DG differential ghost constant all")}),
    //@todo name: why inverse instead of universal?
    new CoreAxiomInfo("DG inverse differential ghost", "DG inverse differential ghost", "DGpp", unsure, {case () => HilbertCalculus.useAt("DG inverse differential ghost") }),
    new CoreAxiomInfo("DG inverse differential ghost implicational", "DG inverse differential ghost implicational", "DGi", unsure, {case () => HilbertCalculus.useAt("DG inverse differential ghost implicational") }),
    new CoreAxiomInfo(", commute", ",", "commaCommute", true, {case () => HilbertCalculus.useAt(", commute")}),
    new CoreAxiomInfo(", sort", ",", "commaSort", true, {case () => HilbertCalculus.useAt(", sort")}),
    new CoreAxiomInfo("DS& differential equation solution", "DS&", "DS", unren, {case () => HilbertCalculus.DS}),
    new CoreAxiomInfo("DIo open differential invariance >"
      , AxiomDisplayInfo("DIo >", "(<span class=\"k4-axiom-key\">[{x′=f(x)&Q}]g(x)>h(x)</span>↔[?Q]g(x)>h(x))←(Q→[{x′=f(x)&Q}](g(x)>h(x)→(g(x)>h(x))′))")
      , "DIogreater", true, {case () => HilbertCalculus.useAt("DIo open differential invariance >")}),
    new DerivedAxiomInfo("DIo open differential invariance <"
      , AxiomDisplayInfo("DIo <", "(<span class=\"k4-axiom-key\">[{x′=f(x)&Q}]g(x)<h(x)</span>↔[?Q]g(x)<h(x))←(Q→[{x′=f(x)&Q}](g(x)<h(x)→(g(x)<h(x))′))")
      , "DIoless", true, {case () => HilbertCalculus.useAt("DIo open differential invariance <")}),
    new CoreAxiomInfo("DV differential variant >="
      , AxiomDisplayInfo("DVgeq", "todo DVgeq")
      , "DVgeq", unsure, {case () => HilbertCalculus.useAt("DV differential variant >=")}),
    new DerivedAxiomInfo("DV differential variant <="
      , AxiomDisplayInfo("DVleq", "todo DVleq")
      , "DVleq", unsure, {case () => HilbertCalculus.useAt("DV differential variant <=")})
  )

  private lazy val differentialInfos: List[DerivationInfo] = List(
    new CoreAxiomInfo("c()' derive constant fn"
      , AxiomDisplayInfo(("c()'", "c()′"), "<span class=\"k4-axiom-key\">(c)′</span>=0")
      , "Dconst", true, {case () => HilbertCalculus.Derive.Dconst}),
    new CoreAxiomInfo("x' derive var"
      ,  AxiomDisplayInfo("x'", "<span class=\"k4-axiom-key\">(x)′</span>=x′")
      , "Dvar", true, {case () => HilbertCalculus.Derive.Dvar}),
    new DerivedAxiomInfo("x' derive variable"
      ,  AxiomDisplayInfo(("x′","x'"), "<span class=\"k4-axiom-key\">(x)′</span>=x′")
      , "DvariableAxiom", unsure, {case () => HilbertCalculus.useAt(DerivedAxioms.Dvariable)}),
    new DerivedAxiomInfo("x' derive var commuted"
      ,  AxiomDisplayInfo(("x′,C","x',C"), "x′=<span class=\"k4-axiom-key\">(x)′</span>")
      , "DvariableCommutedAxiom", true, {case () => HilbertCalculus.useAt(DerivedAxioms.DvariableCommuted)}),
    new PositionTacticInfo("Dvariable"
      ,  AxiomDisplayInfo(("x′","x'"), "<span class=\"k4-axiom-key\">(x)′</span>=x′")
      , {case () => DifferentialTactics.Dvariable}),
    new CoreAxiomInfo("+' derive sum"
      ,  AxiomDisplayInfo(("+′","+'"), "<span class=\"k4-axiom-key\">(f(x)+g(x))′</span>=f(x)′+g(x)′")
      , "Dplus", true, {case () => HilbertCalculus.Derive.Dplus}),
    new CoreAxiomInfo("-' derive neg"
      ,  AxiomDisplayInfo(("-′","-'"),"<span class=\"k4-axiom-key\">(-f(x))′</span>=-(f(x))′")
      , "Dneg", true, {case () => HilbertCalculus.Derive.Dneg}),
    new CoreAxiomInfo("-' derive minus"
      ,  AxiomDisplayInfo(("-′","-'"), "<span class=\"k4-axiom-key\">(f(x)-g(x))′</span>=f(x)′-g(x)′")
      , "Dminus", true, {case () => HilbertCalculus.Derive.Dminus}),
    new CoreAxiomInfo("*' derive product"
      ,  AxiomDisplayInfo(("·′","*'"), "<span class=\"k4-axiom-key\">(f(x)·g(x))′</span>=(f(x))′·g(x)+f(x)·(g(x))′")
      , "Dtimes", true, {case () => HilbertCalculus.Derive.Dtimes}),
    new CoreAxiomInfo("/' derive quotient"
      ,  AxiomDisplayInfo(("/′","/'"), "<span class=\"k4-axiom-key\">(f(g)/g(x))′</span>=(g(x)·(f(x))w-f(x)·(g(x))′)/g(x)^2")
      , "Dquotient", true, {case () => HilbertCalculus.Derive.Dquotient}),
    new CoreAxiomInfo("^' derive power"
      ,  AxiomDisplayInfo(("^′","^'"), "<span class=\"k4-axiom-key\">(f(g)^n)′</span>=n·f(g)^(n-1)·(f(g))′←n≠0")
      , "Dpower", true, {case () => HilbertCalculus.Derive.Dpower}),
    new CoreAxiomInfo("chain rule"
      ,  AxiomDisplayInfo(("∘′","o'"), "[y:=g(x)][y′:=1]((f(g(x)))′=(f(y))′·(g(x))′")
      , "Dcompose", unsure, {case () => TactixLibrary.Derive.Dcompose}),

    new CoreAxiomInfo("=' derive ="
      ,  AxiomDisplayInfo(("=′","='"),"<span class=\"k4-axiom-key\">(f(x)=g(x))′</span>↔f(x)′=g(x)′")
      , "Dequal", true, {case () => HilbertCalculus.Derive.Dequal}),
    new CoreAxiomInfo(">=' derive >="
      ,  AxiomDisplayInfo(("≥′",">='"), "<span class=\"k4-axiom-key\">(f(x)≥g(x))′</span>↔f(x)′≥g(x)′")
      , "Dgreaterequal", true, {case () => HilbertCalculus.Derive.Dgreaterequal}),
    new CoreAxiomInfo(">' derive >"
      ,  AxiomDisplayInfo((">′",">'"),"<span class=\"k4-axiom-key\">(f(x)>g(x))′</span>↔f(x)′≥g(x)′")
      , "Dgreater", true, {case () => HilbertCalculus.Derive.Dgreater}),
    new CoreAxiomInfo("<=' derive <="
      ,  AxiomDisplayInfo(("≤′","<='"), "<span class=\"k4-axiom-key\">(f(x)≤g(x))′</span>↔f(x)′≤g(x)′")
      , "Dlessequal", true, {case () => HilbertCalculus.Derive.Dlessequal}),
    new CoreAxiomInfo("<' derive <"
      ,  AxiomDisplayInfo(("<′","<'"),"<span class=\"k4-axiom-key\">(f(x)<g(m))′</span>↔f(x)′≤g(x)′")
      , "Dless", true, {case () => HilbertCalculus.Derive.Dless}),
    new CoreAxiomInfo("!=' derive !="
      ,  AxiomDisplayInfo(("≠′","!='"), "<span class=\"k4-axiom-key\">(f(x)≠g(x))′</span>↔f(x)′=g(x)′")
      , "Dnotequal", true, {case () => HilbertCalculus.Derive.Dnotequal}),
    new CoreAxiomInfo("&' derive and"
      ,  AxiomDisplayInfo(("∧′", "&'"),"<span class=\"k4-axiom-key\">(P&Q)′</span>↔P′∧Q′")
      , "Dand", true, {case () => HilbertCalculus.Derive.Dand}),
    new CoreAxiomInfo("|' derive or"
      ,  AxiomDisplayInfo(("∨′", "|'"), "<span class=\"k4-axiom-key\">(P|Q)′</span>↔P′∧Q′")
      , "Dor", true, {case () => HilbertCalculus.Derive.Dor}),
    new DerivedAxiomInfo("->' derive imply"
      ,  AxiomDisplayInfo(("→′","->'"), "<span class=\"k4-axiom-key\">(P→Q)′</span>↔(¬P∨Q)′")
      , "Dimply", true, {case () => HilbertCalculus.Derive.Dimply}),
    new CoreAxiomInfo("forall' derive forall"
      ,  AxiomDisplayInfo(("∀′","forall'"), "<span class=\"k4-axiom-key\">(∀x p(x))′</span>↔∀x (p(x))′")
      , "Dforall", true, {case () => HilbertCalculus.Derive.Dforall}),
    new CoreAxiomInfo("exists' derive exists"
      ,  AxiomDisplayInfo(("∃′","exists'"), "<span class=\"k4-axiom-key\">(∃x p(x))′</span>↔∀x (p(x))′")
      , "Dexists", true, {case () => HilbertCalculus.Derive.Dexists}),

    PositionTacticInfo("derive", "()'", {case () => HilbertCalculus.derive} , revealInternalSteps = false /* uninformative as forward proof */)
  )

  private lazy val foInfos: List[DerivationInfo] = List(
    new CoreAxiomInfo("all instantiate", ("∀inst","allInst"), "allInst", unsure, {case () => HilbertCalculus.useAt("all instantiate")}),
    new DerivedAxiomInfo("all distribute", ("∀→","all->"), "allDist", unsure, {case () => HilbertCalculus.allDist}),
    new CoreAxiomInfo("vacuous all quantifier", ("V∀","allV"), "allV", unsure, {case () => HilbertCalculus.allV}),
    new DerivedAxiomInfo("vacuous exists quantifier", ("V∃","existsV"), "existsV", unsure, {case () => HilbertCalculus.existsV}),
    new DerivedAxiomInfo("partial vacuous exists quantifier", ("pV∃","pexistsV"), "pexistsV", unsure, {case () => HilbertCalculus.useAt("partial vacuous exists quantifier")}),
    new CoreAxiomInfo("all dual", ("∀d","alld"), "alld", unsure, {case () => posnil}),
    new CoreAxiomInfo("all dual time", ("∀d","alldt"), "alldt", unsure, {case () => posnil}),
    new CoreAxiomInfo("all dual y", ("∀d","alldy"), "alldy", unsure, {case () => posnil}),
    new CoreAxiomInfo("all eliminate", ("∀e","alle"), "alle", unsure, {case () => posnil}),
    new CoreAxiomInfo("all eliminate y", ("∀y","ally"), "ally", unsure, {case () => posnil})
  )

  private lazy val miscInfos: List[DerivationInfo] = List(
    // more
    // Note: only used to implement Dskipd
    new CoreAxiomInfo("DX differential skip", "DX", "DX", true, {case () => throw new UnsupportedOperationException("DX differential skip is not available for general-purpose use") }),

    new CoreAxiomInfo("exists eliminate y", ("∃ey","existsey"), "existsey", unsure, {case () => HilbertCalculus.useAt("exists eliminate y")}),

    // compatibility axioms (derivable with Mathematica, but not with Z3)
    CoreAxiomInfo("dgZeroEquilibrium", "dgZeroEquilibrium", "dgZeroEquilibrium", unsure, _ => TactixLibrary.useAt("dgZeroEquilibrium"))
  )

  private lazy val derivedAxiomsInfos: List[DerivationInfo] = List(
    new DerivedAxiomInfo("exists eliminate", ("∃e","existse"), "existse", unsure, {case () => HilbertCalculus.existsE}),
    new DerivedAxiomInfo("[:=] assign update", "[:=]", "assignbup", unsure, {case () => HilbertCalculus.assignb}),
    new DerivedAxiomInfo("<:=> assign update", "<:=>", "assigndup", unsure, {case () => HilbertCalculus.assignd}),
    new DerivedAxiomInfo("<:*> assign nondet", "<:*>", "randomd", unren, {case () => HilbertCalculus.randomd}),
    new DerivedAxiomInfo("[:=] assign equational", "[:=]==", "assignbequational", unsure, {case () => HilbertCalculus.assignb}),
    /* @todo replace all the axioms with useAt(axiom) */
    new DerivedAxiomInfo("<':=> differential assign", ("<′:=>","<':=>"), "Dassignd", unsure, {case () => useAt(DerivedAxioms.assignDAxiom)}),
    new DerivedAxiomInfo("DS differential equation solution", "DS", "DSnodomain", true, {case () => useAt(DerivedAxioms.DSnodomain)}),
    new DerivedAxiomInfo("Dsol& differential equation solution", "DS&", "DSddomain", true, {case () => useAt(DerivedAxioms.DSddomain)}),
    new DerivedAxiomInfo("Dsol differential equation solution", "DS", "DSdnodomain", true, {case () => useAt(DerivedAxioms.DSdnodomain)}),
    new DerivedAxiomInfo("DG differential pre-ghost", "DG", "DGpreghost", unsure, {case () => useAt(DerivedAxioms.DGpreghost)}),
    new DerivedAxiomInfo("DW differential weakening"
      , AxiomDisplayInfo("DW","[x′=f(x)&Q]P↔[x′=f(x)&Q](Q→P)")
      , "DW", true, {case () => HilbertCalculus.DW}),
    new DerivedAxiomInfo("DW differential weakening and"
      , AxiomDisplayInfo("DW∧","[x′=f(x)&Q]P→[x′=f(x)&Q](Q∧P)")
      , "DWeakenAnd", unsure, {case () => HilbertCalculus.DW}),
    new DerivedAxiomInfo("DX diamond differential skip", "DX", "Dskipd", true, {case () => useAt(DerivedAxioms.Dskipd)}),
    new DerivedAxiomInfo("DGd diamond differential ghost", "DGd", "DGd", unsure, {case () => useAt(DerivedAxioms.DGddifferentialghost)}),
    new DerivedAxiomInfo("DGd diamond differential ghost constant", "DGCd", "DGCd", unsure, {case () => useAt(DerivedAxioms.DGCddifferentialghostconst)}),
    new DerivedAxiomInfo("DGd diamond differential ghost constant converse", "DGCdc", "DGCdc", unsure, {case () => useAt(DerivedAxioms.DGCddifferentialghostconstconv)}),
    new DerivedAxiomInfo("DGd diamond differential ghost constant exists", "DGCde", "DGCde", unsure, {case () => useAt(DerivedAxioms.DGCddifferentialghostconstexists)}),
    new DerivedAxiomInfo("DCd diamond differential cut", "DCd", "DCd", unsure, {case () => useAt(DerivedAxioms.DCddifferentialcut)}),
    new DerivedAxiomInfo("leave within closed <=", "leaveWithinClosed", "leaveWithinClosed", unsure, {case () => useAt(DerivedAxioms.leaveWithinClosed)}),
    new DerivedAxiomInfo("open invariant closure >", "openInvariantClosure", "openInvariantClosure", unsure, {case () => useAt(DerivedAxioms.openInvariantClosure)}),
    new DerivedAxiomInfo("DWd diamond differential weakening", "DWd", "DWd", unsure, {case () => useAt(DerivedAxioms.DWddifferentialweakening)}),
    new DerivedAxiomInfo("DWd2 diamond differential weakening", "DWd2", "DWd2", unsure, {case () => useAt(DerivedAxioms.DWd2differentialweakening)}),
    new DerivedAxiomInfo(",d commute", "commaCommuted", "commaCommuted", unsure, {case () => useAt(DerivedAxioms.commaCommuted)}),
    new DerivedAxiomInfo("DGd diamond inverse differential ghost implicational", "DGdi", "DGdi", unsure, {case () => useAt(DerivedAxioms.DGdinversedifferentialghostimplicational)}),
    new DerivedAxiomInfo("Uniq uniqueness 2", "Uniq2", "Uniq2", unsure, {case () => HilbertCalculus.useAt(DerivedAxioms.uniqueness2)}),
    new DerivedAxiomInfo("DBX>", "DBXgt", "DBXgt", unsure, {case () => useAt(DerivedAxioms.darbouxGt)}),
    new DerivedAxiomInfo("DBX> open", "DBXgtOpen", "DBXgtOpen", unsure, {case () => useAt(DerivedAxioms.darbouxOpenGt)}),
    //    new DerivedAxiomInfo("all eliminate", "alle", "allEliminate", {case () => useAt(DerivedAxioms.allEliminateAxiom)}),
    //@note derived axiom exists eliminate not yet proven -> use core axiom instead
    //    new DerivedAxiomInfo("exists eliminate", "existse", "existsEliminate", {case () => useAt(DerivedAxioms.existsEliminate)}),
    new DerivedAxiomInfo("\\exists& exists and", "∃∧", "existsAnd", unsure, {case () => useAt(DerivedAxioms.existsAndAxiom)}),
    new DerivedAxiomInfo("\\forall-> forall implies", "∀→", "forallImplies", unsure, {case () => useAt(DerivedAxioms.forallImpliesAxiom)}),
    new DerivedAxiomInfo("exists dual", ("∃d","existsd"), "existsDual", unsure, {case () => useAt(DerivedAxioms.existsDualAxiom)}),
    new DerivedAxiomInfo("' linear", ("l′","l'"), "Dlinear", true, {case () => useAt(DerivedAxioms.Dlinear)}),
    new DerivedAxiomInfo("' linear right", ("l′","l'"), "DlinearRight", true, {case () => useAt(DerivedAxioms.DlinearRight)}),
    new DerivedAxiomInfo("!& deMorgan"
      , AxiomDisplayInfo(("¬∧", "!&"), "<span class=\"k4-axiom-key\">¬(p∧q)</span>↔(¬p|¬q)")
      , "notAnd", true, {case () => useAt(DerivedAxioms.notAnd)}),
    new DerivedAxiomInfo("!| deMorgan"
      , AxiomDisplayInfo(("¬∨","!|"), "<span class=\"k4-axiom-key\">(¬(p|q))</span>↔(¬p∧¬q)")
      , "notOr", true, {case () => useAt(DerivedAxioms.notOr)}),
    new DerivedAxiomInfo("!-> deMorgan"
      , AxiomDisplayInfo(("¬→","!->"), "<span class=\"k4-axiom-key\">¬(p->q)</span>↔(p∧¬q)")
      , "notImply", true, {case () => useAt(DerivedAxioms.notImply)}),
    new DerivedAxiomInfo("!<-> deMorgan"
      , AxiomDisplayInfo(("¬↔", "!<->"), "<span class=\"k4-axiom-key\">¬(p↔q)</span>↔(p∧¬q)| (¬p∧q)")
      , "notEquiv", true, {case () => useAt(DerivedAxioms.notEquiv)}),
    new DerivedAxiomInfo("!all"
      , AxiomDisplayInfo(("¬∀", "!all"), "<span class=\"k4-axiom-key\">¬∀x (p(x)))</span>↔∃x (¬p(x))")
      , "notAll", true, {case () => useAt(DerivedAxioms.notAll)}),
    new DerivedAxiomInfo("!exists"
      , AxiomDisplayInfo(("¬∃","!exists"), "<span class=\"k4-axiom-key\">(¬∃x (p(x)))</span>↔∀x (¬p(x))")
      , "notExists", true, {case () => useAt(DerivedAxioms.notExists)}),
    new DerivedAxiomInfo("![]", ("¬[]","![]"), "notBox", true, {case () => useAt(DerivedAxioms.notBox)}),
    new DerivedAxiomInfo("!<>", ("¬<>","!<>"), "notDiamond", true, {case () => useAt(DerivedAxioms.notDiamond)}),
    new DerivedAxiomInfo("[] split"
      , AxiomDisplayInfo(("[]∧", "[]^"), "<span class=\"k4-axiom-key\">[a](P∧Q)</span>↔[a]P ∧ [a]Q")
      , "boxAnd", true, {case () => HilbertCalculus.boxAnd}),
    new DerivedAxiomInfo("[] conditional split"
      , AxiomDisplayInfo(("[]→∧", "[]->^"), "<span class=\"k4-axiom-key\">[a](P→Q∧R)</span> ↔ [a](P→Q) ∧ [a](P→R)")
      , "boxImpliesAnd", true, {case () => HilbertCalculus.boxImpliesAnd}),
    new DerivedAxiomInfo("<> split"
      , AxiomDisplayInfo(("<>∨","<>|"), "<span class=\"k4-axiom-key\">&langle;a&rangle;(P∨Q)</span>↔&langle;a&rangle;P ∨ &langle;a&rangle;Q")
      , "diamondOr", true, {case () => useAt(DerivedAxioms.diamondOr)}),
    new DerivedAxiomInfo("<> partial vacuous", ("pVd","pVd"), "pVd", unsure, {case () => HilbertCalculus.useAt("<> partial vacuous")}),
    //    new DerivedAxiomInfo("<> split left", "<>|<-", "diamondSplitLeft", {case () => useAt(DerivedAxioms.diamondSplitLeft)}),
    //    new DerivedAxiomInfo("[] split left", "[]&<-", "boxSplitLeft", {case () => useAt(DerivedAxioms.boxSplitLeft)}),
    //    new DerivedAxiomInfo("[] split right", "[]&->", "boxSplitRight", {case () => useAt(DerivedAxioms.boxSplitRight)}),
    new DerivedAxiomInfo("<*> approx", "<*> approx", "loopApproxd", unsure, {case () => useAt(DerivedAxioms.loopApproxd)}),
    new DerivedAxiomInfo("<*> stuck", "<*> stuck", "loopStuck", unsure, {case () => useAt(DerivedAxioms.loopStuck)}),
    new DerivedAxiomInfo("<a> stuck", "<a> stuck", "programStuck", unsure, {case () => useAt(DerivedAxioms.programStuck)}),
    new DerivedAxiomInfo("<'> stuck", ("<′> stuck","<'> stuck"), "odeStuck", unsure, {case () => useAt(DerivedAxioms.odeStuck)}),
    new DerivedAxiomInfo("all stutter", "all stutter", "allStutter", unsure, {case () => useAt(DerivedAxioms.forallStutter)}),
    new DerivedAxiomInfo("exists stutter", "exists stutter", "existsStutter", unsure, {case () => useAt(DerivedAxioms.existsStutter)}),
    new DerivedAxiomInfo("[] post weaken", "[]PW", "postWeaken", unsure, {case () => useAt(DerivedAxioms.postconditionWeaken)}),
    new DerivedAxiomInfo("<-> reflexive", ("↔R","<->R"), "equivReflexive", false, {case () => useAt(DerivedAxioms.equivReflexiveAxiom)}),
    new DerivedAxiomInfo("-> distributes over &", ("→∧", "->&"), "implyDistAnd", unsure, {case () => useAt(DerivedAxioms.implyDistAndAxiom)}),
    new DerivedAxiomInfo("-> distributes over <->", ("→↔","-><->"), "implyDistEquiv", unsure, {case () => useAt(DerivedAxioms.implyDistEquivAxiom)}),
    new DerivedAxiomInfo("-> weaken", ("→W","->W"), "implyWeaken", unsure, {case () => useAt(DerivedAxioms.implWeaken)}),
    new DerivedAxiomInfo("!! double negation"
      , AxiomDisplayInfo(("¬¬","!!"), "(¬¬p↔p")
      , "doubleNegation", true, {case () => useAt(DerivedAxioms.doubleNegationAxiom)}),
    new DerivedAxiomInfo(":= assign dual", ":=D", "assignDual", unsure, {case () => useAt(DerivedAxioms.assignDualAxiom)}),
    new DerivedAxiomInfo(":= assign dual 2", ":=D", "assignDual2", unsure, {case () => useAt(DerivedAxioms.assignDual2Axiom)}),
    new DerivedAxiomInfo("[:=] vacuous assign", "V[:=]", "vacuousAssignb", unsure, {case () => useAt(DerivedAxioms.vacuousAssignbAxiom)}),
    new DerivedAxiomInfo("<:=> vacuous assign", "V<:=>", "vacuousAssignd", unsure, {case () => useAt(DerivedAxioms.vacuousAssigndAxiom)}),
    new DerivedAxiomInfo("[*] approx", "[*] approx", "loopApproxb", unsure, {case () => useAt(DerivedAxioms.loopApproxb)}),
    new DerivedAxiomInfo("[*] merge", "[*] merge", "loopMergeb", unsure, {case () => useAt(DerivedAxioms.loopMergeb)}),
    new DerivedAxiomInfo("<*> merge", "<*> merge", "loopMerged", unsure, {case () => useAt(DerivedAxioms.loopMerged)}),
    new DerivedAxiomInfo("[**] iterate iterate", "[**]", "iterateiterateb", false, {case () => useAt(DerivedAxioms.iterateiterateb)}),
    new DerivedAxiomInfo("<**> iterate iterate", "<**>", "iterateiterated", false, {case () => useAt(DerivedAxioms.iterateiterated)}),
    new DerivedAxiomInfo("[*-] backiterate", "[*-]", "backiterateb", true, {case () => useAt(DerivedAxioms.backiterateb)}),
    new DerivedAxiomInfo("[*-] backiterate necessity", "[*-] backiterate necessity", "backiteratebnecc", unsure, {case () => useAt(DerivedAxioms.backiteratebnecc)}),
    new DerivedAxiomInfo("[*-] backiterate sufficiency", "[*-] backiterate sufficiency", "backiteratebsuff", unsure, {case () => useAt(DerivedAxioms.backiteratebsuff)}),
    new DerivedAxiomInfo("II induction", "II induction", "IIinduction", unsure, {case () => useAt(DerivedAxioms.iiinduction)}),
    new DerivedAxiomInfo("I"
      , AxiomDisplayInfo(("I", "I"), "<span class=\"k4-axiom-key\">[a*]P</span>↔P∧[a*](P→[a]P)"), "I", true, {case () => useAt(DerivedAxioms.Ieq)}),
    //@todo might have a better name
    new DerivedAxiomInfo("exists generalize", ("∃G","existsG"), "existsGeneralize", unsure, {case () => useAt(DerivedAxioms.existsGeneralize)}),
    new DerivedAxiomInfo("exists generalize y", ("∃Gy","existsGy"), "existsGeneralizey", unsure, {case () => useAt(DerivedAxioms.existsGeneralizey)}),
    new DerivedAxiomInfo("all substitute", ("∀S","allS"), "allSubstitute", unsure, {case () => useAt(DerivedAxioms.allSubstitute)}),
    new DerivedAxiomInfo("V[:*] vacuous assign nondet", "V[:*]", "vacuousBoxAssignNondet", unsure, {case () => useAt(DerivedAxioms.vacuousBoxAssignNondetAxiom)}),
    new DerivedAxiomInfo("V<:*> vacuous assign nondet", "V<:*>", "vacuousDiamondAssignNondet", unsure, {case () => useAt(DerivedAxioms.vacuousDiamondAssignNondetAxiom)}),
    new DerivedAxiomInfo("Domain Constraint Conjunction Reordering", ("{∧}C","{&}C"), "domainCommute", unsure, {case () => useAt(DerivedAxioms.domainCommute)}), //@todo shortname
    new DerivedAxiomInfo("& commute", ("∧C","&C"), "andCommute", true, {case () => useAt(DerivedAxioms.andCommute)}),
    new DerivedAxiomInfo("& reflexive", ("∧R","&R"), "andReflexive", false, {case () => useAt(DerivedAxioms.andReflexive)}),
    new DerivedAxiomInfo("& associative", ("∧A","&A"), "andAssoc", true, {case () => useAt(DerivedAxioms.andAssoc)}),
    new DerivedAxiomInfo("-> expand", ("→E","->E"), "implyExpand", true, {case () => useAt(DerivedAxioms.implyExpand)}),
    new DerivedAxiomInfo("-> tautology", ("→taut","->taut"), "implyTautology", false, {case () => useAt(DerivedAxioms.implyTautology)}),
    new DerivedAxiomInfo("\\forall->\\exists", ("∀→∃","all->exists"), "forallThenExists", unsure, {case () => useAt(DerivedAxioms.forallThenExistsAxiom)}),
    new DerivedAxiomInfo("->true"
      , AxiomDisplayInfo(("→⊤","->T"), "<span class=\"k4-axiom-key\">(p→⊤)</span>↔⊤")
      , "implyTrue", true, {case () => useAt(DerivedAxioms.impliesTrue)}),
    new DerivedAxiomInfo("true->"
      , AxiomDisplayInfo(("⊤→", "T->"), "<span class=\"k4-axiom-key\">(⊤→p)</span>↔p")
      , "trueImply", true, {case () => useAt(DerivedAxioms.trueImplies)}),
    new DerivedAxiomInfo("&true"
      , AxiomDisplayInfo(("∧⊤","&T"), "<span class=\"k4-axiom-key\">(p∧⊤)</span>↔p")
      , "andTrue", true, {case () => useAt(DerivedAxioms.andTrue)}),
    new DerivedAxiomInfo("&true inv", "&true inv", "andTrueInv", unsure, {case () => useAt(DerivedAxioms.invAndTrue)}),
    new DerivedAxiomInfo("true&"
      , AxiomDisplayInfo(("⊤∧","T&"), "<span class=\"k4-axiom-key\">(⊤∧p)</span>↔p")
      , "trueAnd", true, {case () => useAt(DerivedAxioms.trueAnd)}),
    new DerivedAxiomInfo("0*", "0*", "zeroTimes", true, {case () => useAt(DerivedAxioms.zeroTimes)}),
    new DerivedAxiomInfo("0+", "0+", "zeroPlus", true, {case () => useAt(DerivedAxioms.zeroPlus)}),
    new DerivedAxiomInfo("*0", "*0", "timesZero", true, {case () => useAt(DerivedAxioms.timesZero)}),
    new DerivedAxiomInfo("+0", "+0", "plusZero", true, {case () => useAt(DerivedAxioms.plusZero)}),
    new DerivedAxiomInfo("= reflexive", "=R", "equalReflexive", false, {case () => useAt(DerivedAxioms.equalReflex)}),
    new DerivedAxiomInfo(">= reflexive", ">=R", "greaterEqualReflexive", false, {case () => useAt(DerivedAxioms.greaterEqualReflex)}),
    new DerivedAxiomInfo("= commute", "=C", "equalCommute", true, {case () => useAt(DerivedAxioms.equalCommute)}),
    new DerivedAxiomInfo("<=", "<=", "lessEqual", true, {case () => useAt(DerivedAxioms.lessEqual)}),
    new DerivedAxiomInfo(">=", ">=", "greaterEqual", true, {case () => useAt(DerivedAxioms.greaterEqual)}),
    new DerivedAxiomInfo("! <"
      , AxiomDisplayInfo(("¬<","!<"), "<span class=\"k4-axiom-key\">¬(f<g)</span>↔(f≥g)")
      , "notLess", true, {case () => useAt(DerivedAxioms.notLess)}),
    new DerivedAxiomInfo("! >"
      , AxiomDisplayInfo(("¬>","!>"), "<span class=\"k4-axiom-key\">¬(f>g)</span>↔(f≤g)")
      , "notGreater", true, {case () => useAt(DerivedAxioms.notGreater)}),
    new DerivedAxiomInfo("! >=", ("¬≥","!>="), "notGreaterEqual", true, {case () => useAt(DerivedAxioms.notGreaterEqual)}),
    new DerivedAxiomInfo(">= flip", ">=F", "flipGreaterEqual", true, {case () => useAt(DerivedAxioms.flipGreaterEqual)}),
    new DerivedAxiomInfo("> flip", ">F", "flipGreater", true, {case () => useAt(DerivedAxioms.flipGreater)}),
    new DerivedAxiomInfo("<= flip", "<=F", "flipLessEqual", true, {case () => useAt(DerivedAxioms.flipLessEqual)}),
    new DerivedAxiomInfo("< flip", "<F", "flipLess", true, {case () => useAt(DerivedAxioms.flipLess)}),
    new DerivedAxiomInfo("<", "<", "less", true, {case () => useAt(DerivedAxioms.less)}),
    new DerivedAxiomInfo(">", ">", "greater", true, {case () => useAt(DerivedAxioms.greater)}),

    //    new DerivedAxiomInfo("!= elimination", ("≠", "!="), "notEqualElim", {case () => useAt(DerivedAxioms.notEqualElim)}),
    //    new DerivedAxiomInfo(">= elimination", ("≥", ">="), "greaterEqualElim", {case () => useAt(DerivedAxioms.greaterEqualElim)}),
    //    new DerivedAxiomInfo("> elimination", ">", "greaterElim", {case () => useAt(DerivedAxioms.greaterElim)}),
    new DerivedAxiomInfo("1>0", "1>0", "oneGreaterZero", true, {case () => useAt(DerivedAxioms.oneGreaterZero)}),
    new DerivedAxiomInfo("nonnegative squares", "^2>=0", "nonnegativeSquares", true, {case () => useAt(DerivedAxioms.nonnegativeSquares)}),
    new DerivedAxiomInfo(">2!=", ">2!=", "greaterImpliesNotEqual", unsure, {case () => useAt(DerivedAxioms.greaterImpliesNotEqual)}),
    new DerivedAxiomInfo("> monotone", ">mon", "greaterMonotone", unsure, {case () => useAt(DerivedAxioms.greaterMonotone)}),

    new DerivedAxiomInfo("abs", "abs", "abs", unsure, {case () => useAt(DerivedAxioms.absDef)}),
    new DerivedAxiomInfo("min", "min", "min", unsure, {case () => useAt(DerivedAxioms.minDef)}),
    new DerivedAxiomInfo("max", "max", "max", unsure, {case () => useAt(DerivedAxioms.maxDef)}),
    new DerivedAxiomInfo("& recursor", "& recursor", "andRecursor", true, {case () => useAt(DerivedAxioms.andRecursor)}),
    new DerivedAxiomInfo("| recursor", "| recursor", "orRecursor", true, {case () => useAt(DerivedAxioms.orRecursor)}),
    new DerivedAxiomInfo("<= both", "<= both", "intervalLEBoth", unsure, {case () => useAt(DerivedAxioms.intervalLEBoth)}),
    new DerivedAxiomInfo("< both", "< both", "intervalLBoth", unsure, {case () => useAt(DerivedAxioms.intervalLBoth)}),
    new DerivedAxiomInfo("neg<= up", "neg<=", "intervalUpNeg", unsure, {case () => useAt(DerivedAxioms.intervalUpNeg)}),
    new DerivedAxiomInfo("abs<= up", "abs<=", "intervalUpAbs", unsure, {case () => useAt(DerivedAxioms.intervalUpAbs)}),
    new DerivedAxiomInfo("max<= up", "max<=", "intervalUpMax", unsure, {case () => useAt(DerivedAxioms.intervalUpMax)}),
    new DerivedAxiomInfo("min<= up", "min<=", "intervalUpMin", unsure, {case () => useAt(DerivedAxioms.intervalUpMin)}),
    new DerivedAxiomInfo("+<= up", "+<=", "intervalUpPlus", unsure, {case () => useAt(DerivedAxioms.intervalUpPlus)}),
    new DerivedAxiomInfo("-<= up", "-<=", "intervalUpMinus", unsure, {case () => useAt(DerivedAxioms.intervalUpMinus)}),
    new DerivedAxiomInfo("*<= up", "*<=", "intervalUpTimes", unsure, {case () => useAt(DerivedAxioms.intervalUpTimes)}),
    new DerivedAxiomInfo("1Div<= up", "1/<=", "intervalUp1Divide", unsure, {case () => useAt(DerivedAxioms.intervalUp1Divide)}),
    //    new DerivedAxiomInfo("Div<= up", "/<=", "intervalUpDivide", {case () => useAt(DerivedAxioms.intervalUpDivide)}),
    new DerivedAxiomInfo("pow<= up", "pow<=", "intervalUpPower", unsure, {case () => useAt(DerivedAxioms.intervalUpPower)}),
    new DerivedAxiomInfo("<=neg down", "<=neg", "intervalDownNeg", unsure, {case () => useAt(DerivedAxioms.intervalDownNeg)}),
    new DerivedAxiomInfo("<=abs down", "<=abs", "intervalDownAbs", unsure, {case () => useAt(DerivedAxioms.intervalDownAbs)}),
    new DerivedAxiomInfo("<=max down", "<=max", "intervalDownMax", unsure, {case () => useAt(DerivedAxioms.intervalDownMax)}),
    new DerivedAxiomInfo("<=min down", "<=min", "intervalDownMin", unsure, {case () => useAt(DerivedAxioms.intervalDownMin)}),
    new DerivedAxiomInfo("<=+ down", "<=+", "intervalDownPlus", unsure, {case () => useAt(DerivedAxioms.intervalDownPlus)}),
    new DerivedAxiomInfo("<=- down", "<=-", "intervalDownMinus", unsure, {case () => useAt(DerivedAxioms.intervalDownMinus)}),
    new DerivedAxiomInfo("<=* down", "<=*", "intervalDownTimes", unsure, {case () => useAt(DerivedAxioms.intervalDownTimes)}),
    new DerivedAxiomInfo("<=1Div down", "<=1/", "intervalDown1Divide", unsure, {case () => useAt(DerivedAxioms.intervalDown1Divide)}),
    //    new DerivedAxiomInfo("<=Div down", "<=/", "intervalDownDivide", {case () => useAt(DerivedAxioms.intervalDownDivide)}),
    new DerivedAxiomInfo("<=pow down", "<=pow", "intervalDownPower", unsure, {case () => useAt(DerivedAxioms.intervalDownPower)}),
    new DerivedAxiomInfo("! !="
      , AxiomDisplayInfo(("¬≠","!!="), "<span class=\"k4-axiom-key\">(¬(f≠g)</span>↔(f=g))")
      , "notNotEqual", true, {case () => useAt(DerivedAxioms.notNotEqual)}),
    new DerivedAxiomInfo("! ="
      , AxiomDisplayInfo(("¬ =","! ="), "<span class=\"k4-axiom-key\">(¬(f=g))</span>↔(f≠g)")
      , "notEqual", true, {case () => useAt(DerivedAxioms.notEqual)}),
    new DerivedAxiomInfo("! <="
      , AxiomDisplayInfo(("¬≤","!<="), "<span class=\"k4-axiom-key\">(¬(f≤g)</span>↔(f>g)")
      , "notLessEqual", true, {case () => useAt(DerivedAxioms.notLessEqual)}),
    new DerivedAxiomInfo("* associative", "*A", "timesAssociative", true, {case () => useAt(DerivedAxioms.timesAssociative)}),
    new DerivedAxiomInfo("* commute", "*C", "timesCommute", true, {case () => useAt(DerivedAxioms.timesCommutative)}),
    new DerivedAxiomInfo("* inverse", "*i", "timesInverse", false, {case () => useAt(DerivedAxioms.timesInverse)}),
    new DerivedAxiomInfo("* closed", "*c", "timesClosed", unsure, {case () => useAt(DerivedAxioms.timesClosed)}),
    new DerivedAxiomInfo("* identity", "*I", "timesIdentity", unsure, {case () => useAt(DerivedAxioms.timesIdentity)}),
    new DerivedAxiomInfo("+ associative", "+A", "plusAssociative", true, {case () => useAt(DerivedAxioms.plusAssociative)}),
    new DerivedAxiomInfo("+ commute", "+C", "plusCommute", true, {case () => useAt(DerivedAxioms.plusCommutative)}),
    new DerivedAxiomInfo("+ inverse", "+i", "plusInverse", false, {case () => useAt(DerivedAxioms.plusInverse)}),
    new DerivedAxiomInfo("+ closed", "+c", "plusClosed", unsure, {case () => useAt(DerivedAxioms.plusClosed)}),
    new DerivedAxiomInfo("positivity", "Pos", "positivity", unsure, {case () => useAt(DerivedAxioms.positivity)}),
    new DerivedAxiomInfo("distributive", "*+", "distributive", unsure, {case () => useAt(DerivedAxioms.distributive)}),
    new DerivedAxiomInfo("[]~><> propagation", "[]~><>", "boxDiamondPropagation", unsure, {case () => useAt(DerivedAxioms.boxDiamondPropagation)}),
    new DerivedAxiomInfo("[]~><> subst propagation", "[]~><> subst", "boxDiamondSubstPropagation", unsure, {case () => useAt(DerivedAxioms.boxDiamondSubstPropagation)}),
    new DerivedAxiomInfo("-> self", ("→self","-> self"), "implySelf", unsure, {case () => useAt(DerivedAxioms.implySelf)}),
    new DerivedAxiomInfo("-> converse", ("→conv","-> conv"), "converseImply", unsure, {case () => useAt(DerivedAxioms.converseImply)}),
    new DerivedAxiomInfo("<-> true", ("↔true","<-> true"), "equivTrue", true, {case () => useAt(DerivedAxioms.equivTrue)}),
    new DerivedAxiomInfo("Kd diamond modus ponens", "Kd", "Kd", unsure, {case () => useAt(DerivedAxioms.KdAxiom)}),
    new DerivedAxiomInfo("Kd2 diamond modus ponens", "Kd2", "Kd2", unsure, {case () => useAt(DerivedAxioms.Kd2Axiom)}),
    //@todo internal only
    //    new DerivedAxiomInfo("K1", "K1", "K1", {case () => useAt(DerivedAxioms.K1)}),
    //    new DerivedAxiomInfo("K2", "K2", "K2", {case () => useAt(DerivedAxioms.K2)}),
    new DerivedAxiomInfo("PC1", "PC1", "PC1", false, {case () => useAt(DerivedAxioms.PC1)}),
    new DerivedAxiomInfo("PC2", "PC2", "PC2", false, {case () => useAt(DerivedAxioms.PC2)}),
    new DerivedAxiomInfo("PC3", "PC3", "PC3", false, {case () => useAt(DerivedAxioms.PC3)}),
    new DerivedAxiomInfo("PC9", "PC9", "PC9", false, {case () => useAt(DerivedAxioms.PC9)}),
    new DerivedAxiomInfo("PC10", "PC10", "PC10", false, {case () => useAt(DerivedAxioms.PC10)}),
    new DerivedAxiomInfo("K modal modus ponens &", "K&", "Kand", unsure, {case () => useAt(DerivedAxioms.Kand)}),
    new DerivedAxiomInfo("&->", "&->", "andImplies", unsure, {case () => useAt(DerivedAxioms.andImplies)}),

    // metric axioms
    new DerivedAxiomInfo("= expand", "equalExpand", "equalExpand", unsure, {case () => useAt(DerivedAxioms.equalExpand)}),
    new DerivedAxiomInfo("!= expand", "notEqualExpand", "notEqualExpand", unsure, {case () => useAt(DerivedAxioms.notEqualExpand)}),
    new DerivedAxiomInfo("<= to <", "leApprox", "leApprox", true, {case () => useAt(DerivedAxioms.le2l)}),
    new DerivedAxiomInfo("metric <=", "metricLe", "metricLe", unsure, {case () => useAt(DerivedAxioms.metricLessEqual)}),
    new DerivedAxiomInfo("metric <", "metricLt", "metricLt", unsure, {case () => useAt(DerivedAxioms.metricLess)}),
    new DerivedAxiomInfo("metric <= & <=", "metricAndLe", "metricAndLe", unsure, {case () => useAt(DerivedAxioms.metricAndLe)}),
    new DerivedAxiomInfo("metric < & <", "metricAndLt", "metricAndLt", unsure, {case () => useAt(DerivedAxioms.metricAndLt)}),
    new DerivedAxiomInfo("metric <= | <=", "metricOrLe", "metricOrLe", unsure, {case () => useAt(DerivedAxioms.metricOrLe)}),
    new DerivedAxiomInfo("metric < | <", "metricOrLt", "metricOrLt", unsure, {case () => useAt(DerivedAxioms.metricOrLt)}),

    //Extra SimplifierV3 axioms
    new DerivedAxiomInfo("* identity neg", "timesIdentityNeg", "timesIdentityNeg", unsure, {case () => useAt(DerivedAxioms.timesIdentityNeg)}),
    new DerivedAxiomInfo("-0", "minusZero", "minusZero", true, {case () => useAt(DerivedAxioms.minusZero)}),
    new DerivedAxiomInfo("0-", "zeroMinus", "zeroMinus", true, {case () => useAt(DerivedAxioms.zeroMinus)}),
    new DerivedAxiomInfo(">0 -> !=0" ,"gtzImpNez" , "gtzImpNez"  ,unsure, {case () => useAt(DerivedAxioms.gtzImpNez)}),
    new DerivedAxiomInfo("<0 -> !=0" ,"ltzImpNez" , "ltzImpNez"  ,unsure, {case () => useAt(DerivedAxioms.ltzImpNez)}),
    new DerivedAxiomInfo("!=0 -> 0/F","zeroDivNez", "zeroDivNez" ,unsure, {case () => useAt(DerivedAxioms.zeroDivNez)}),
    new DerivedAxiomInfo("F^0","powZero", "powZero" ,unsure, {case () => useAt(DerivedAxioms.powZero)}),
    new DerivedAxiomInfo("F^1","powOne"    , "powOne"     ,unsure, {case () => useAt(DerivedAxioms.powOne)}),
    new DerivedAxiomInfo("< irrefl", "lessNotRefl", "lessNotRefl", false, {case () => useAt(DerivedAxioms.lessNotRefl)}),
    new DerivedAxiomInfo("> irrefl", "greaterNotRefl", "greaterNotRefl", false, {case () => useAt(DerivedAxioms.greaterNotRefl)}),
    new DerivedAxiomInfo("!= irrefl", "notEqualNotRefl", "notEqualNotRefl", false, {case () => useAt(DerivedAxioms.notEqualNotRefl)}),
    new DerivedAxiomInfo("= refl", "equalRefl", "equalRefl", false, {case () => useAt(DerivedAxioms.equalRefl)}),
    new DerivedAxiomInfo("<= refl", "lessEqualRefl", "lessEqualRefl", false, {case () => useAt(DerivedAxioms.lessEqualRefl)}),
    new DerivedAxiomInfo(">= refl", "greaterEqualRefl", "greaterEqualRefl", false, {case () => useAt(DerivedAxioms.greaterEqualRefl)}),
    new DerivedAxiomInfo("= sym", "equalSym", "equalSym", unsure, {case () => useAt(DerivedAxioms.equalSym)}),
    new DerivedAxiomInfo("!= sym", "notEqualSym", "notEqualSym", unsure, {case () => useAt(DerivedAxioms.notEqualSym)}),
    new DerivedAxiomInfo("> antisym", "greaterNotSym", "greaterNotSym", unsure, {case () => useAt(DerivedAxioms.greaterNotSym)}),
    new DerivedAxiomInfo("< antisym", "lessNotSym", "lessNotSym", unsure, {case () => useAt(DerivedAxioms.lessNotSym)}),
    new DerivedAxiomInfo("const congruence", "CCE", "constCongruence", false, {case () => HilbertCalculus.useAt(DerivedAxioms.constCongruence)}),
    new DerivedAxiomInfo("const formula congruence", "CCQ", "constFormulaCongruence", false, {case () => HilbertCalculus.useAt(DerivedAxioms.constFormulaCongruence)})
  )

  private lazy val sequentCalculusInfos: List[DerivationInfo] = List(
    new PositionTacticInfo("notL"
      , RuleDisplayInfo(("¬L", "!L"), (List("¬P", "&Gamma;"),List("&Delta;")), List((List("&Gamma;"),List("&Delta;","P"))))
      , {case () => SequentCalculus.notL}),
    new PositionTacticInfo("notR"
      , RuleDisplayInfo(("¬R", "!R"), (List("&Gamma;"),List("¬P","&Delta;")), List((List("&Gamma;","P"),List("&Delta;"))))
      , {case () => SequentCalculus.notR}),
    new PositionTacticInfo("andR"
      , RuleDisplayInfo(("∧R", "^R"), (List("&Gamma;"),List("P∧Q","&Delta;")),
        List((List("&Gamma;"),List("P", "&Delta;")),
          (List("&Gamma;"), List("Q", "&Delta;"))))
      , {case () => SequentCalculus.andR}),
    new PositionTacticInfo("andL"
      , RuleDisplayInfo(("∧L", "^L"), (List("P∧Q", "&Gamma;"),List("&Delta;")), List((List("&Gamma;","P","Q"),List("&Delta;"))))
      , {case () => SequentCalculus.andL}),
    new PositionTacticInfo("orL"
      , RuleDisplayInfo(("∨L", "|L"), (List("P∨Q", "&Gamma;"),List("&Delta;")),
        List((List("&Gamma;", "P"),List("&Delta;")),
          (List("&Gamma;", "Q"),List("&Delta;"))))
      , {case () => SequentCalculus.orL}),
    new PositionTacticInfo("orR"
      , RuleDisplayInfo(("∨R", "|R"), (List("&Gamma;"),List("P∨Q","&Delta;")), List((List("&Gamma;"),List("P","Q","&Delta;"))))
      , {case () => SequentCalculus.orR}),
    new PositionTacticInfo("implyR"
      , RuleDisplayInfo(("→R", "->R"), (List("&Gamma;"),List("P→Q", "&Delta;")), List((List("&Gamma;","P"),List("Q","&Delta;"))))
      , {case () => SequentCalculus.implyR}),
    new TwoPositionTacticInfo("implyRi", "implyRi", _ => SequentCalculus.implyRi()),
    new PositionTacticInfo("implyL"
      , RuleDisplayInfo(("→L", "->L"), (List("P→Q","&Gamma;"),List("&Delta;")),
        List((List("&Gamma;","P"),List("&Delta;")),
          (List("&Gamma;"),List("Q","&Delta;"))))
      , {case () => SequentCalculus.implyL}),
    new PositionTacticInfo("equivL"
      , RuleDisplayInfo(("↔L", "<->L"), (List("P↔Q","&Gamma;"),List("&Delta;")),
        List((List("&Gamma;","P∧Q"),List("&Delta;")),
          (List("&Gamma;","¬P∧¬Q"),List("&Delta;"))
        ))
      , {case () => SequentCalculus.equivL}),
    new PositionTacticInfo("equivR"
      , RuleDisplayInfo(("↔R", "<->R"), (List("&Gamma;"),List("P↔Q","&Delta;")),
        List((List("&Gamma;","P","Q"),List("&Delta;")),
          (List("&Gamma;","¬P","¬Q"),List("&Delta;"))))
      , {case () => SequentCalculus.equivR}),
    new InputPositionTacticInfo("allL"
      , RuleDisplayInfo(("∀L", "allL"), (List("&Gamma;","∀x P(x)"), List("&Delta;")),
        List((List("&Gamma;", "P(θ)"),List("&Delta;"))))
      , List(TermArg("θ", "θ"::Nil))
      , _ => ((t:Term) => SequentCalculus.allL(t)): TypedFunc[Term, BelleExpr]),
    new PositionTacticInfo("allR"
      , RuleDisplayInfo(("∀R", "allR"), (List("&Gamma;"), List("∀x P(x)", "&Delta;")),
        List((List("&Gamma;"),List("P(x)","&Delta;"))))
      , {case () => SequentCalculus.allR}),
    new PositionTacticInfo("existsL"
      , RuleDisplayInfo(("∃L", "existsL"), (List("&Gamma;","∃x P(x)"),List("&Delta;")),
        List((List("&Gamma;","P(x)"),List("&Delta;"))))
      , {case () => SequentCalculus.existsL}),
    new PositionTacticInfo("G"
      , RuleDisplayInfo("G", (List("&Gamma;"), List("[a]P", "&Delta;")), List((List(),List("P"))))
      , {case () => HilbertCalculus.G}),
    new PositionTacticInfo("GV"
      , RuleDisplayInfo("G&ouml;del Vacuous", (List("&Gamma;"), List("[a]P", "&Delta;"))
        , List((List("&Gamma;<sub>const</sub>"), List("P", "&Delta;<sub>const</sub>"))))
      , {case () => TactixLibrary.abstractionb}, revealInternalSteps = true),
    new InputPositionTacticInfo("existsR"
      , RuleDisplayInfo(("∃R", "existsR"), (List("&Gamma;"), List("∃x P(x)", "&Delta;")),
        List((List("&Gamma;"),List("P(θ)", "&Delta;"))))
      , List(TermArg("θ", "θ"::Nil))
      , _ => ((t:Term) => SequentCalculus.existsR(t)): TypedFunc[Term, BelleExpr]),

    new PositionTacticInfo("commuteEquivL", ("↔CL", "<->CL"), {case () => SequentCalculus.commuteEquivL}),
    new PositionTacticInfo("commuteEquivR", ("↔CR", "<->CR"), {case () => SequentCalculus.commuteEquivR}),
    new PositionTacticInfo("equivifyR", ("→↔","-><->"), {case () => SequentCalculus.equivifyR}),
    new PositionTacticInfo("hideL"
      , RuleDisplayInfo("WL", (List("&Gamma;", "P"),List("&Delta;"))
        , List((List("&Gamma;"),List("&Delta;")))),
      {case () => SequentCalculus.hideL}),
    new PositionTacticInfo("hideR"
      , RuleDisplayInfo("WR", (List("&Gamma;"),List("P", "&Delta;"))
        , List((List("&Gamma;"),List("&Delta;")))),
      {case () => SequentCalculus.hideR}),
    new TacticInfo("smartHide", "smartHide", {case () => ArithmeticSimplification.smartHide}),
    new PositionTacticInfo("cohideL", "W", {case () => SequentCalculus.cohideL}),
    new PositionTacticInfo("cohideR", "W", {case () => SequentCalculus.cohideR}),
    new TacticInfo("closeFalse"
      , RuleDisplayInfo(("⊥L", "falseL"), (List("⊥","&Gamma;"),List("&Delta;")), List())
      , {case () => TactixLibrary.closeF}),
    new TacticInfo("closeTrue"
      , RuleDisplayInfo(("⊤R","trueR"), (List("&Gamma;"), List("⊤","&Delta;")),List())
      ,{case () => TactixLibrary.closeT}),
    new PositionTacticInfo("skolemizeR", "skolem", {case () => ProofRuleTactics.skolemizeR}),
    new PositionTacticInfo("cohide", "W", {case () => SequentCalculus.cohide}),
    new PositionTacticInfo("hide", "W", {case () => SequentCalculus.hide}),
    new PositionTacticInfo("allL2R", "L=R all", {case () => TactixLibrary.exhaustiveEqL2R}),
    new PositionTacticInfo("atomAllL2R", "L=R all atoms", {case () => EqualityTactics.atomExhaustiveEqL2R}),
    new PositionTacticInfo("allR2L", "R=L all", {case () => TactixLibrary.exhaustiveEqR2L}),
    new PositionTacticInfo("minmax", "min/max", {case () => EqualityTactics.minmax}),
    new PositionTacticInfo("absExp", "absExp", {case () => EqualityTactics.abs}),
    new PositionTacticInfo("toSingleFormula", "toFormula", {case () => PropositionalTactics.toSingleFormula}),

    PositionTacticInfo("CMon"
      , RuleDisplayInfo("CMon", (List(), List("C{o}→C{k}")), List((List(), List("o→k"))))
      , {case () => TactixLibrary.CMon}
    ),
    InputTacticInfo("CMonCongruence"
      , SimpleDisplayInfo("CMonCongruence","CMonCongruence")
      ,List(StringArg("inEqPos")), _ => ((inEqPos: String) => TactixLibrary.CMon(PosInExpr.parse(inEqPos))): TypedFunc[String, BelleExpr]),
    InputTacticInfo("CECongruence"
      , SimpleDisplayInfo("CECongruence","CECongruence")
      ,List(StringArg("inEqPos")), _ => ((inEqPos: String) => TactixLibrary.CE(PosInExpr.parse(inEqPos))): TypedFunc[String, BelleExpr]),

    // proof management tactics
    InputTacticInfo("debug"
      , SimpleDisplayInfo("Debug","debug")
      ,List(StringArg("msg")), _ => ((msg: String) => DebuggingTactics.debug(msg)): TypedFunc[String, BelleExpr]),
    InputTacticInfo("done"
      , SimpleDisplayInfo("Done","done")
      ,List(StringArg("msg"),StringArg("lemmaName")), _ =>
        ((msg: Option[String]) =>
          ((lemmaName: Option[String]) =>
            DebuggingTactics.done(msg.getOrElse(""), lemmaName)): TypedFunc[Option[String], BelleExpr]): TypedFunc[Option[String], _]
    ),
    InputTacticInfo("pending"
      , SimpleDisplayInfo("pending", "pending")
      ,List(StringArg("tactic")), _ =>
        ((tactic: String) => DebuggingTactics.pending(tactic)): TypedFunc[String, BelleExpr]
    ),
    InputTacticInfo("label"
      , SimpleDisplayInfo("label","label")
      ,List(StringArg("label")), _ => ((l: String) => TactixLibrary.label(BelleLabel.toPrettyString(BelleLabel.fromString(l)))): TypedFunc[String, BelleExpr]),

    // Proof rule two-position tactics
    new TwoPositionTacticInfo("coHide2", "W", {case () => SequentCalculus.cohide2}),
    new TwoPositionTacticInfo("equivRewriting", RuleDisplayInfo("equivRewriting", (List("&Gamma;", "∀X p(X) <-> q(X)"), List("p(Z)", "&Delta;")), List((List("&Gamma;", "∀X p(X) <-> q(X)"), List("q(Z)", "&Delta;")))), {case () => PropositionalTactics.equivRewriting}),
    new TwoPositionTacticInfo("instantiatedEquivRewriting", "instantiatedEquivRewriting", {case () => PropositionalTactics.instantiatedEquivRewriting}),
    //    new TwoPositionTacticInfo("exchangeL", "X", {case () => ProofRuleTactics.exchangeL}),
    //    new TwoPositionTacticInfo("exchangeR", "X", {case () => ProofRuleTactics.exchangeR}),
    new TacticInfo("closeTransitive", RuleDisplayInfo("closeTransitive", (List("a>=b", "b >= c", "c >= z"), List("a >= z")), Nil), {case () => Transitivity.closeTransitive}),
    //@note deprecated use id instead
    new TacticInfo("closeId",
      RuleDisplayInfo("Close by identity", (List("&Gamma;", "P"), List("P", "&Delta;")), Nil),
      {case () => TactixLibrary.closeId}),
    new TacticInfo("id",
      RuleDisplayInfo("Close by identity", (List("&Gamma;", "P"), List("P", "&Delta;")), Nil),
      {case () => TactixLibrary.closeId}),
    PositionTacticInfo("idWith",
      RuleDisplayInfo("Close by identity", (List("&Gamma;", "P"), List("P", "&Delta;")), Nil),
      {case () => TactixLibrary.closeIdWith}),
    new TacticInfo("close",
      RuleDisplayInfo("Close by ⊥/⊤", (List("&Gamma;", "P", "⊥"), List("⊤", "P", "&Delta;")), Nil),
      {case () => TactixLibrary.close}),
    new TwoPositionTacticInfo("L2R",
      RuleDisplayInfo("Apply equality",
        /*conclusion*/ (List("&Gamma;", "x=y", "P(x)"), List("Q(x)", "&Delta;")),
        /*premise*/    List((List("&Gamma;", "x=y", "P(y)"), List("Q(y)", "&Delta;")))),
      {case () => (pos: AntePosition) => TactixLibrary.eqL2R(pos)}),
    //      {case () => ProofRuleTactics.trivialCloser}), //@todo This is a 4.1b3 merge conflict. I'm not sure what the correct behavior is.

    // Proof rule input tactics
    new InputTacticInfo("cut"
      , RuleDisplayInfo(("cut","cut")
        ,(List("&Gamma;"), List("&Delta;"))
        ,List(
          (List("&Gamma;"),List("&Delta;","P")),
          (List("&Gamma;", "P"), List("&Delta;"))))
      ,List(FormulaArg("P")), _ => ((fml:Formula) => ProofRuleTactics.cut(fml)): TypedFunc[Formula, BelleExpr]),
    new InputTacticInfo("abbrv"
      , RuleDisplayInfo(("Abbreviate","abbrv")
        ,(List("&Gamma;"), List("&Delta;"))
        ,List(
          (List("&Gamma;", "freshVar=theta"),List("&Delta;"))))
      ,List(TermArg("theta"),VariableArg("freshVar", "freshVar"::Nil)), _ => ((t:Term) => ((v: Option[Variable]) => EqualityTactics.abbrv(t, v)): TypedFunc[Option[Variable], BelleExpr]): TypedFunc[Term, _]),
    // Proof rule input position tactics
    new InputPositionTacticInfo("cutL", "cutL", List(FormulaArg("cutFormula")),
      _ => ((fml:Formula) => TactixLibrary.cutL(fml)): TypedFunc[Formula, BelleExpr]),
    new InputPositionTacticInfo("cutR", "cutR", List(FormulaArg("cutFormula")),
      _ => ((fml:Formula) => TactixLibrary.cutR(fml)): TypedFunc[Formula, BelleExpr]),
    new InputPositionTacticInfo("cutLR", "cutLR", List(FormulaArg("cutFormula")),
      _ => ((fml:Formula) => TactixLibrary.cutLR(fml)): TypedFunc[Formula, BelleExpr]),
    new InputPositionTacticInfo("loop",
      RuleDisplayInfo("Induction",(List("&Gamma;"), List("[a*]P", "&Delta;")),
        List(
          (List("&Gamma;"),List("J", "&Delta;")),
          (List("J"),List("[a]J")),
          (List("J"),List("P"))))
      , List(FormulaArg("J")), _ => ((fml: Formula) => TactixLibrary.loop(fml)): TypedFunc[Formula, BelleExpr]
      , revealInternalSteps = true),
    new PositionTacticInfo("loopAuto", "loopAuto",
      {case () => (gen:Generator.Generator[GenProduct]) => TactixLibrary.loop(gen)}, needsGenerator = true),
    new InputPositionTacticInfo("throughout",
      RuleDisplayInfo("Loop Throughout",(List("&Gamma;"), List("[{a;{b;c};d}*]P", "&Delta;")),
        List(
          (List("&Gamma;"),List("j(x)", "&Delta;")),
          (List("j(x)"),List("[a]j(x)")),
          (List("j(x)"),List("[b;c]j(x)")),
          (List("j(x)"),List("[d]j(x)")),
          (List("j(x)"),List("P"))))
      , List(FormulaArg("j(x)")), _ => ((fml: Formula) => TactixLibrary.throughout(fml)): TypedFunc[Formula, BelleExpr]),
    new InputPositionTacticInfo("con",
      RuleDisplayInfo("Loop Convergence",(List("&Gamma;"), List("&lt;a*&gt;P", "&Delta;")),
        List(
          (List("&Gamma;"),List("∃x. j(x)", "&Delta;")),
          (List("x ≤ 0", "j(x)"),List("P")),
          (List("x > 0", "j(x)"),List("&lt;a&gt;j(x-1)"))))
      , List(VariableArg("x", allowsFresh = "x" :: Nil), FormulaArg("j(x)", allowsFresh = "x" :: Nil)), _ =>
        ((x: Variable) =>
          ((fml: Formula) => DLBySubst.con(x, fml)): TypedFunc[Formula, BelleExpr]): TypedFunc[Variable, _]),

    new PositionTacticInfo("loopauto", RuleDisplayInfo("loopauto",(List("&Gamma;"), List("[a*]P", "&Delta;")),
      List()), {case () => (gen: Generator.Generator[GenProduct]) => TactixLibrary.loopauto(gen)}, needsGenerator = true),

    new InputPositionTacticInfo("MR",
      RuleDisplayInfo("Monotonicity",(List("&Gamma;"), List("[a]P", "&Delta;")),
        List(
          (List("&Gamma;"),List("[a]Q", "&Delta;")),
          (List("Q"),List("P"))))
      , List(FormulaArg("Q")), _ => ((fml:Formula) => TactixLibrary.generalize(fml)): TypedFunc[Formula, BelleExpr], revealInternalSteps = true),
    InputPositionTacticInfo("transform",
      RuleDisplayInfo("trafo",
        //@todo suggests formulas, but also works with terms
        /* conclusion */ (List("&Gamma;"), List("P", "&Delta;")),
        /* premises */ List((List("&Gamma;"),List("Q", "&Delta;")))),
      List(ExpressionArg("Q")),
      _ => ((expr:Expression) => TactixLibrary.transform(expr)): TypedFunc[Expression, BelleExpr]),
    new InputPositionTacticInfo("edit", "edit", List(ExpressionArg("to")),
      _ => ((expr:Expression) => TactixLibrary.edit(expr)): TypedFunc[Expression, BelleExpr]),
    new TacticInfo("expandAll", "expandAll", _ => EqualityTactics.expandAll, revealInternalSteps = true),
    new InputPositionTacticInfo("boundRename"
      , RuleDisplayInfo(("BR", "BR"), (List("&Gamma;"), List("∀x P(x)","&Delta;")),
        List((List("&Gamma;"),List("∀y P(y)","&Delta;"))))
      , List(VariableArg("x"),VariableArg("y"))
      , _ => ((x:Variable) => ((y:Variable) => TactixLibrary.boundRename(x,y)): TypedFunc[Variable, BelleExpr]): TypedFunc[Variable, TypedFunc[Variable, BelleExpr]]),
    InputTacticInfo("uniformRename"
      , RuleDisplayInfo(("UR", "UR"), (List("P(x)"), List("Q(x)")),
        List((List("P(y)"),List("Q(y)"))))
      , List(VariableArg("x"),VariableArg("y"))
      , _ => ((x:Variable) => ((y:Variable) => TactixLibrary.uniformRename(x,y)): TypedFunc[Variable, BelleExpr]): TypedFunc[Variable, TypedFunc[Variable, BelleExpr]]),
    new InputPositionTacticInfo("stutter"
      , RuleDisplayInfo(("[:=]", "[:=]"), (List("&Gamma;"), List("P","&Delta;"))
        , List((List("&Gamma;"),List("[x:=x]P","&Delta;")))), List(VariableArg("x"))
      , _ => ((x:Variable) => DLBySubst.stutter(x)): TypedFunc[Variable, BelleExpr]),

    //
    new TacticInfo("nil", "nil", {case () => Idioms.nil}),

    new InputPositionTacticInfo(
      "transformEquality",
      "transformEquality",
      FormulaArg("equality") :: Nil,
      _ => ((f:Formula) => ArithmeticSimplification.transformEquality(f)): TypedFunc[Formula, BelleExpr]),

    new InputPositionTacticInfo(
      "discreteGhost",
      RuleDisplayInfo(("iG", "iG"), (List("&Gamma;"),List("P","&Delta;")),
        List((List("&Gamma;"), List("[gv:=gt;]P","&Delta;")))),
      TermArg("gt") :: VariableArg("gv", "gv"::Nil) :: Nil,
      _ => ((t:Term) => ((v: Option[Variable]) => DLBySubst.discreteGhost(t, v)): TypedFunc[Option[Variable], BelleExpr]): TypedFunc[Term, _]),

    /*new TacticInfo("monb", "Box Monotonicity", {case () => TactixLibrary.monb}),
    new TacticInfo("monb2", "Box Monotonicity 2", {case () => DLBySubst.monb2}),
    //@todo unify axiomatic rule and derived rules mond / mondtodo
    new TacticInfo("mond", "Diamond Monotonicity", {case () => TactixLibrary.mond}),*/

    // TactixLibrary tactics
    PositionTacticInfo("step", "step", {case () => TactixLibrary.step}),
    PositionTacticInfo("stepAt", "stepAt", {case () => HilbertCalculus.stepAt}),
    PositionTacticInfo("normalize", "normalize", {case () => TactixLibrary.normalize}, revealInternalSteps = true),
    PositionTacticInfo("unfold", "unfold", {case () => TactixLibrary.unfoldProgramNormalize}, revealInternalSteps = true),
    PositionTacticInfo("prop", "prop", {case () => TactixLibrary.prop}, revealInternalSteps = true),
    PositionTacticInfo("propAuto", "propAuto", {case () => TactixLibrary.propAuto}, revealInternalSteps = true),
    PositionTacticInfo("chase", "chase", {case () => TactixLibrary.chase}),
    PositionTacticInfo("chaseAt", "chaseAt", {case () => TactixLibrary.chaseAt()(
      TactixLibrary.andL, TactixLibrary.implyR, TactixLibrary.orR, TactixLibrary.allR, TacticIndex.allLStutter,
      TactixLibrary.existsL, TacticIndex.existsRStutter,
      ProofRuleTactics.closeTrue, ProofRuleTactics.closeFalse
    )}),
    PositionTacticInfo("simplify", "simplify", {case () => SimplifierV3.simpTac()}, needsTool = true),
    // Technically in InputPositionTactic(Generator[Formula, {case () => ???}), but the generator is optional
    new TacticInfo("master", "master", {case () => (gen:Generator.Generator[GenProduct]) => TactixLibrary.master(gen)}, needsGenerator = true, revealInternalSteps = true),
    new TacticInfo("explore", "explore", {case () => (gen:Generator.Generator[GenProduct]) => gen match {
      case cgen: ConfigurableGenerator[GenProduct] => TactixLibrary.explore(cgen)
      case _ => ??? // extract annotated invariants into a configurable generator
    } }, needsGenerator = true, revealInternalSteps = true),
    new TacticInfo("auto", "auto", {case () => TactixLibrary.auto}, needsGenerator = true, revealInternalSteps = true),
    InputTacticInfo("useSolver"
      , "useSolver"
      , List(StringArg("tool"))
      , _ => ((tool: String) => ToolTactics.switchSolver(tool)): TypedFunc[String, BelleExpr]),
    InputTacticInfo("QE", "QE",
      List(OptionArg(StringArg("tool")), OptionArg(TermArg("timeout"))),
      _ => { case Some(toolName: String) => {
        case (Some(Number(timeout))) => TactixLibrary.QE(Nil, Some(toolName), Some(timeout.toInt))
        // interpret optional toolName as timeout
        case _ if Try(Integer.parseInt(toolName)).isSuccess => TactixLibrary.QE(Nil, None, Some(Integer.parseInt(toolName)))
        case _ =>  TactixLibrary.QE(Nil, Some(toolName)) }: TypedFunc[Option[Term], BelleExpr]
      case _ => {
        case Some(Number(timeout)) => TactixLibrary.QE(Nil, None, Some(timeout.toInt))
        case _ => TactixLibrary.QE }: TypedFunc[Option[Term], BelleExpr]
      }: TypedFunc[Option[String], _], needsTool = true, revealInternalSteps = true),
    new TacticInfo("rcf", "RCF",  {case () => TactixLibrary.RCF}, needsTool = true),
    //new TacticInfo("MathematicaQE", "MathematicaQE", {case () => TactixLibrary.QE}, needsTool = true),
    new TacticInfo("pQE", "pQE",  {case () => TactixLibrary.partialQE}, needsTool = true),
    new TacticInfo("smartQE", "smartQE",  {case () => ArithmeticSpeculativeSimplification.speculativeQE}, needsTool = true),
    new TacticInfo("fullSimplify", "fullSimplify",  {case () => SimplifierV3.fullSimpTac()}, needsTool = true),
    //@todo universal closure may come with list of named symbols
    new PositionTacticInfo("universalClosure", SimpleDisplayInfo("∀Cl", "allClosure"), {case () => FOQuantifierTactics.universalClosure}),

    InputPositionTacticInfo("useAt"
      , "useAt"
      , List(StringArg("axiom"), StringArg("key"))
      , _ => ((axiomName: String) => {
        case None => TactixLibrary.useAt(axiomName) //@note serializes as codeName
        case Some(k: String) =>
          val key = PosInExpr(k.split("\\.").map(Integer.parseInt).toList)
          val defaultKey = AxiomIndex.axiomIndex(axiomName)._1
          if (key != defaultKey) {
            //@note serializes as useAt({`axiomName`},{`k`})
            "useAt" byWithInputs (axiomName::k::Nil, (pos: Position, seq: Sequent) => {
              val axiom = ProvableInfo(axiomName)
              TactixLibrary.useAt(axiom.provable, key)(pos)
            })
          } else TactixLibrary.useAt(axiomName) //@note serializes as codeName
      }: TypedFunc[Option[String], BelleExpr]): TypedFunc[String, _]),

    InputTacticInfo("useLemma"
      , "useLemma"
      , List(StringArg("lemma"), StringArg("tactic"))
      , _ => ((lemmaName: String) => ((tactic: Option[String]) =>
        TactixLibrary.useLemma(lemmaName, tactic.map(_.asTactic))): TypedFunc[Option[String], BelleExpr]): TypedFunc[String, _]),

    InputTacticInfo("byUS"
      , RuleDisplayInfo(("US", "byUS"), (List(),List("S(P)")),
        List((List(), List("P"))))
      , List(StringArg("P"), FormulaArg("S"))
      , _ => ((axiomName: String) => ({
        case None => TactixLibrary.byUS(axiomName)
        case Some(substFml: Formula) =>
          val subst = RenUSubst(FormulaTools.conjuncts(substFml).map({
            case Equal(l, r) => (l, r)
            case Equiv(l, r) => (l, r)
            case s => throw new IllegalArgumentException("Expected substitution of the shape t=s or p<->q, but got " + s.prettyString)
          }))
          TactixLibrary.byUS(axiomName, (_: UnificationMatch.Subst) => subst)
      }): TypedFunc[Option[Formula], BelleExpr]): TypedFunc[String, _]),
    InputTacticInfo("US"
      , RuleDisplayInfo(("US", "US"), (List(),List("S(P)")),
        List((List(), List("P"))))
      , List(SubstitutionArg("S"))
      , _ => ((subst: USubst) => TactixLibrary.uniformSubstitute(subst)): TypedFunc[USubst, BelleExpr]),

    InputPositionTacticInfo("useLemmaAt"
      , "useLemmaAt"
      , List(StringArg("lemma"), StringArg("key"))
      , _ => ((lemmaName: String) => ((key: Option[String]) =>
        TactixLibrary.useLemmaAt(lemmaName, key.map(k => PosInExpr(k.split("\\.").map(Integer.parseInt).toList)))): TypedFunc[Option[String], BelleExpr]): TypedFunc[String, _]),

    InputPositionTacticInfo("cutAt"
      , RuleDisplayInfo("cutAt",
        /* conclusion */ (List("&Gamma;"), List("C{c}", "&Delta;")),
        /* premises */   List((List("&Gamma;"),List("C{repl}", "&Delta;")),
          (List("&Gamma;"),List("&Delta;", "C{repl}→C{c}"))))
      , List(FormulaArg("repl"))
      , _ => ((fml: Formula) => TactixLibrary.cutAt(fml)): TypedFunc[Formula, BelleExpr]),

    InputPositionTacticInfo("proveComponentSystem"
      , RuleDisplayInfo("proveComponentSystem",
        /* conclusion */ (List("&Gamma;"), List("""t=t0 & Om & A1 & A2
                                                  |->
                                                  |[{ {mem1;mem2};
                                                  |   {ctrl1;ctrl2};
                                                  |   to:=t;
                                                  |   {t'=1,plant1,plant2};
                                                  |   {in1open;in2open};
                                                  |   {cp1;cp2;con};
                                                  | }*]((G1&P1) & (G2&P2))""".stripMargin, "&Delta;")),
        /* premises */   List(
          (List(),List("C1 Base: Om & A1 -> I1")),
          (List(),List("C1 Use:  Om & I1 -> G1 & P1")),
          (List(),List("C1 Step: Om & I1 -> [mem1; ctrl1; t0=t; {t'=1,plant1}; in1; cp1;]I1")),
          (List(),List("C2 Base: Om & A2 -> I2")),
          (List(),List("C2 Use:  Om & I2 -> G2 & P2")),
          (List(),List("C2 Step: Om & I2 -> [mem2; ctrl2; t0=t; {t'=1,plant2}; in2; cp2;]I2")),
          (List(),List("Compatibility: Om & Z -> [xin:=xo;](Pout(xo) -> Pin(xin))")),
          (List(),List("Com Safety:   [xin:=xo;]Z")),
          (List(),List("Com Liveness: <xin:=xo;>true"))
        )
      )
      ,
      List(
        StringArg("System Name"),
        StringArg("C1 Base: Om & A1 -> I1"), StringArg("C1 Use:  Om & I1 -> G1 & P1"), StringArg("C1 Step: Om & I1 -> [mem1; ctrl1; t0=t; {t'=1,plant1}; in1; cp1;]I1"),
        StringArg("C2 Base: Om & A2 -> I2"), StringArg("C2 Use:  Om & I2 -> G2 & P2"), StringArg("C2 Step: Om & I2 -> [mem2; ctrl2; t0=t; {t'=1,plant2}; in2; cp2;]I2"),
        StringArg("Compatibility: Om & Z -> [xin:=xo;](Pout(xo) -> Pin(xin))"), StringArg("Com Safety:   [xin:=xo;]Z"), StringArg("Com Liveness: <xin:=xo;>true")
      )
      , _ => (
        (systemName: String) =>
          ((c1base: String) => ((c1use: String) => ((c1step: String) => ((c2base: String) => ((c2use: String) =>
            ((c2step: String) => ((compat: String) => ((comSafe: String) => ((comLive: String) =>
              ComponentSystem.proveSystem(systemName, c1base, c1use, c1step, c2base, c2use, c2step, compat, comSafe, comLive)):
              TypedFunc[String, BelleExpr]): TypedFunc[String, _]): TypedFunc[String, _]):
              TypedFunc[String, _]): TypedFunc[String, _]): TypedFunc[String, _]): TypedFunc[String, _]): TypedFunc[String, _]): TypedFunc[String, _]
        ): TypedFunc[String, _]
    ),

    // Differential tactics
    new PositionTacticInfo("splitWeakInequality", "splitWeakInequality", {case () => DifferentialTactics.splitWeakInequality}, needsTool = true),
    new PositionTacticInfo("ODE",
      "Auto",
      {case () => TactixLibrary.ODE}, needsTool = true, revealInternalSteps = true),
    new PositionTacticInfo("odeInvC",
      "odeInvC",
      {case () => TactixLibrary.odeInvariantComplete}, needsTool = true),
    new PositionTacticInfo("dgZeroMonomial",
      "dgZeroMonomial",
      {case () => DifferentialTactics.dgZeroMonomial}, needsTool = true),
    new PositionTacticInfo("dgZeroPolynomial",
      "dgZeroPolynomial",
      {case () => DifferentialTactics.dgZeroPolynomial}, needsTool = true),
    new PositionTacticInfo("dI",
      RuleDisplayInfo("Differential Invariant",
        (List("&Gamma;"),List("[{x′ = f(x) & Q}]P","&Delta;")),
        /* premises */ List((List("&Gamma;", "Q"), List("P", "&Delta;"), true /*@todo auto for now, but shouldn't be once we can stop in the middle of dI*/),
          (List("Q"), List("[x′:=f(x)](P)′"), true /*@todo auto for now, but shouldn't be once we can stop in the middle of dI*/))),
      {case () => DifferentialTactics.diffInd(auto = 'cex)}, revealInternalSteps = true),
    new InputPositionTacticInfo("diffInvariant"
      , RuleDisplayInfo("Differential Cut + Differential Invariant"
        , (List("&Gamma;"),List("[{x′ = f(x) & Q}]P","&Delta;"))
        , /* premises */ List((List("&Gamma;"), List("[{x′ = f(x) & Q}]R", "&Delta;"), true),
          (List("&Gamma;"), List("[{x′ = f(x) & (Q∧R)}]P","&Delta;"))))
      , List(FormulaArg("R")) //@todo should be ListArg, before merge we already had concrete Bellerophon syntax for lists
      , _ => ((fml:Formula) => TactixLibrary.diffInvariant(fml)): TypedFunc[Formula, BelleExpr], revealInternalSteps = true),
    new PositionTacticInfo("solve",
      RuleDisplayInfo("Solution",
        (List("&Gamma;"),List("[{x′ = f(x) & q(x)}]p(x)","&Delta;")),
        List((List("&Gamma;"), List("∀t≥0 ( (∀0≤s≤t q(sol(s))) → [x:=sol(t)]p(x) )")))),
      {case () => TactixLibrary.solve}, needsTool = true, revealInternalSteps = true),
    new PositionTacticInfo("solveEnd",
      RuleDisplayInfo("Solution",
        (List("&Gamma;"),List("[{x′ = f(x) & q(x)}]p(x)","&Delta;")),
        List((List("&Gamma;"), List("∀t≥0 ( q(sol(t)) → [x:=sol(t)]p(x) )")))),
      {case () => TactixLibrary.solveEnd}, needsTool = true, revealInternalSteps = true),
    new PositionTacticInfo("DGauto",
      "DGauto",
      {case () => TactixLibrary.DGauto}, needsTool = true),

    // DLBySubst
    //new InputPositionTacticInfo("I", "I", List(FormulaArg("invariant")), {case () => (fml:Formula) => TactixLibrary.loop(fml)}),

    new PositionTacticInfo("decomposeController","decomposeController",{case () => {HybridProgramTactics.decomposeController}}),

    // Derived axiomatic rules
    new DerivedRuleInfo("all generalization"
      , RuleDisplayInfo(SimpleDisplayInfo("all gen", "allgen"), SequentDisplay(Nil, "\\forall x P"::Nil), SequentDisplay(Nil, "P"::Nil)::Nil)
      , "allGeneralize", {case () => HilbertCalculus.useAt(DerivedAxioms.allGeneralize)}),
    new DerivedRuleInfo("[] monotone"
      , RuleDisplayInfo(SimpleDisplayInfo("[] monotone", "[]monotone"), SequentDisplay("[a;]P"::Nil, "[a;]Q"::Nil), SequentDisplay("P"::Nil, "Q"::Nil)::Nil)
      , "monb", {case () => HilbertCalculus.useAt(DerivedAxioms.boxMonotone)}),
    new DerivedRuleInfo("[] monotone 2"
      , RuleDisplayInfo(SimpleDisplayInfo("[] monotone 2", "[]monotone 2"), SequentDisplay("[a;]Q"::Nil, "[a;]P"::Nil), SequentDisplay("Q"::Nil, "P"::Nil)::Nil)
      , "monb2", {case () => HilbertCalculus.useAt(DerivedAxioms.boxMonotone2)}),
    new DerivedRuleInfo("Goedel"
      , RuleDisplayInfo(SimpleDisplayInfo("G", "G"), SequentDisplay(Nil, "[a;]P"::Nil), SequentDisplay(Nil, "P"::Nil)::Nil)
      , "Goedel", {case () => HilbertCalculus.useAt(DerivedAxioms.Goedel)}),
    new DerivedRuleInfo("CT term congruence"
      , RuleDisplayInfo(SimpleDisplayInfo("CT term congruence", "CTtermCongruence"), SequentDisplay(Nil, "ctx_(f_(||)) = ctx_(g_(||))"::Nil), SequentDisplay(Nil, "f_(||) = g_(||)"::Nil)::Nil)
      , "CTtermCongruence", {case () => HilbertCalculus.useAt(DerivedAxioms.CTtermCongruence)}),
    new DerivedRuleInfo("con convergence flat"
      , RuleDisplayInfo(SimpleDisplayInfo("con flat", "conflat"), SequentDisplay("J"::Nil, "<a*>P"::Nil), SequentDisplay("\\exists v (v<=0&J)"::Nil, "P"::Nil)::SequentDisplay("v > 0"::"J"::Nil ,"<a>J(v-1)"::Nil)::Nil)
      , "conflat", {case () => HilbertCalculus.useAt(DerivedAxioms.convergenceFlat)}),

    // numerical bound tactics
    new TacticInfo("intervalArithmetic", "intervalArithmetic",  {case () => IntervalArithmeticV2.intervalArithmetic}, needsTool = true),
    InputTacticInfo("intervalCutTerms",
      RuleDisplayInfo(("Interval Arithmetic Cut","intervalCutTerms"),
        (List("&Gamma;"),List("&Delta;")),
        /* premises */ List((List("&Gamma;"), List("a <= trm", "trm <= b"), true),
          (List("&Gamma;", "a <= trm", "trm <= b"), List("&Delta;"), false)))
      ,List(TermArg("trm")), _ => ((t:Term) => IntervalArithmeticV2.intervalCutTerms(t)): TypedFunc[Term, BelleExpr]),
    PositionTacticInfo("intervalCut"
      , RuleDisplayInfo(("Interval Arithmetic Cut", "intervalCut"),
        (List("&Gamma;"),List("&Delta;")),
        List((List("&Gamma;"), List("a <= trm", "trm <= b"), true), (List("&Gamma;", "a <= trm", "trm <= b"), List("&Delta;"), false))
      )
      , {case () => IntervalArithmeticV2.intervalCut}),
    new PositionTacticInfo("dCClosure", "dCClosure", {case () => DifferentialTactics.dCClosure(true)}, needsTool = true),

    // assertions and messages
    InputTacticInfo("print"
      , SimpleDisplayInfo("Print","print")
      ,List(StringArg("msg")), _ => ((msg: String) => DebuggingTactics.printIndexed(msg)): TypedFunc[String, BelleExpr]),
    InputPositionTacticInfo("assert"
      , SimpleDisplayInfo("Assert","assert")
      , List(ExpressionArg("expected"), StringArg("msg"))
      , _ => ((expr: Expression) => ((msg: String) => DebuggingTactics.assertE(expr, msg)): TypedFunc[String, BelleExpr]): TypedFunc[Expression, TypedFunc[String, BelleExpr]]
    )
  )

  /**
    * Central registry for axiom, derived axiom, proof rule, and tactic meta-information.
    * Transferred into subsequent maps etc for efficiency reasons.
    */
  val allInfo: List[DerivationInfo] = (convert(ProvableSig.rules) ++ modalityInfos ++ odeInfos ++
    differentialInfos ++ foInfos ++ miscInfos ++ derivedAxiomsInfos ++ sequentCalculusInfos) ensures (
    consistentInfo _, "meta-information on AxiomInfo is consistent with actual (derived) axioms etc.")

  private def consistentInfo(list: List[DerivationInfo]): Boolean = {
    val canonicals = list.map(_.canonicalName)
    val codeNames = list.map(_.codeName).filter(_ != needsCodeName)
    val storedNames = list.filter(_.isInstanceOf[StorableInfo]).map(_.asInstanceOf[StorableInfo].storedName)
    list.forall({
        case ax: CoreAxiomInfo => ProvableSig.axiom.contains(ax.canonicalName) ensures(r=>r, "core axiom correctly marked as CoreAxiomInfo: " + ax.canonicalName)
        case _: DerivedAxiomInfo => true //@todo can't ask DerivedAxioms.derivedAxiom yet since still initializing, besides that'd be circular
        case _ => true
      }
    ) &&
      (canonicals.length==canonicals.distinct.length ensures(r=>r, "unique canonical names: " + (canonicals diff canonicals.distinct))) &&
      (codeNames.length==codeNames.distinct.length ensures(r=>r, "unique code names / identifiers: " + (codeNames diff codeNames.distinct))) &&
      //@note to avoid file storage issues on some OSes, lowercase versions of code names used in files are expected to be unique.
      (storedNames.length==storedNames.distinct.length ensures(r=>r, "unique stored names / identifiers across all derived axioms: " + (storedNames diff storedNames.distinct)))
  }

  /** code name mapped to derivation information */
  private val byCodeName: Map[String, DerivationInfo] =
  /* @todo Decide on a naming convention. Until then, making everything case insensitive */
    allInfo.foldLeft(HashMap.empty[String,DerivationInfo]){case (acc, info) =>
        acc + ((info.codeName, info))
    }

  /** canonical name mapped to derivation information */
  private val byCanonicalName: Map[String, DerivationInfo] =
    allInfo.foldLeft(HashMap.empty[String,DerivationInfo]){case (acc, info) =>
      acc + ((info.canonicalName, info))
    }

  /** Retrieve meta-information on an inference by the given canonical name `axiomName` */
  def apply(axiomName: String): DerivationInfo = byCanonicalName.getOrElse(axiomName,
    ofBuiltinName(axiomName).getOrElse(throw AxiomNotFoundException(axiomName)))

  /** Throw an AssertionError if id does not conform to the rules for code names. */
  def assertValidIdentifier(id: String): Unit = { assert(id.forall(_.isLetterOrDigit), "valid code name: " + id)}

  /** Retrieve meta-information on an inference by the given code name `codeName` */
  def ofCodeName(codeName:String): DerivationInfo = {
    assert(byCodeName != null, "byCodeName should not be null.")
    assert(codeName != null, "codeName should not be null.")

    byCodeName.getOrElse(codeName, ofBuiltinName(codeName).getOrElse(
      throw new IllegalArgumentException("No such DerivationInfo of identifier " + codeName)
    ))
  }

  /** Retrieve meta-information on a builtin tactic expression by the given `name`. */
  def ofBuiltinName(name: String): Option[DerivationInfo] = {
    val expandPattern = "(expand(?!All).*)|(expandAllDefs)".r
    name match {
      case expandPattern(_*) => Some(new BuiltinInfo(name, SimpleDisplayInfo(name, name)))
      case _ => None
    }
  }

  /** Locate the derivation info for said tactic */
  def locate(t: BelleExpr): Option[DerivationInfo] = t match {
    case n: NamedBelleExpr => try { Some(ofCodeName(n.name)) } catch { case _: Exception => None }
    case AppliedPositionTactic(n, _) => locate(n)
    case AppliedBuiltinTwoPositionTactic(n, _, _) => locate(n)
    //@todo probably more cases
    case _ => None
  }

  def hasCodeName(codeName: String): Boolean = byCodeName.keySet.contains(codeName)
}

object AxiomInfo {
  /** Retrieve meta-information on an axiom by the given canonical name `axiomName` */
  def apply(axiomName: String): AxiomInfo =
    DerivationInfo(axiomName) match {
      case info:AxiomInfo => info
      case info => throw new Exception("Derivation \"" + info.canonicalName + "\" is not an axiom")
  }

  /** Retrieve meta-information on an axiom by the given code name `codeName` */
  def ofCodeName(codeName: String): AxiomInfo =
    DerivationInfo.ofCodeName(codeName) match {
      case info:AxiomInfo => info
      case info => throw new Exception("Derivation \"" + info.canonicalName + "\" is not an axiom")
    }

  val allInfo:List[AxiomInfo] =  DerivationInfo.allInfo.filter(_.isInstanceOf[AxiomInfo]).map(_.asInstanceOf[AxiomInfo])
}

object TacticInfo {
  def apply(tacticName: String): TacticInfo =
    DerivationInfo(tacticName) match {
      case info:TacticInfo => info
      case info => throw new Exception("Derivation \"" + info.canonicalName + "\" is not a tactic")
    }
}

sealed trait ArgInfo {
  /** Argument sort. */
  val sort: String
  /** Argument name. */
  val name: String
  /** A list of allowed fresh symbols. */
  val allowsFresh: List[String]
  /** Converts an expression into the required format of the tactic (default: no-op). Returns either the converted
    * expression or an error message. */
  def convert(e: Expression): Either[Expression, String] = Left(e)
}
case class FormulaArg (override val name: String, override val allowsFresh: List[String] = Nil) extends ArgInfo {
  val sort = "formula"
}
case class VariableArg (override val name: String, override val allowsFresh: List[String] = Nil) extends ArgInfo {
  val sort = "variable"
}
case class ExpressionArg (override val name: String, override val allowsFresh: List[String] = Nil,
                          converter: Expression => Either[Expression, String] = e => Left(e)) extends ArgInfo {
  val sort = "expression"
  override def convert(e: Expression): Either[Expression, String] = converter(e)
}
case class TermArg (override val name: String, override val allowsFresh: List[String] = Nil) extends ArgInfo {
  val sort = "term"
}
case class StringArg (override val name: String, override val allowsFresh: List[String] = Nil) extends ArgInfo {
  val sort = "string"
}
case class SubstitutionArg (override val name: String, override val allowsFresh: List[String] = Nil) extends ArgInfo {
  val sort = "subst"
}
case class OptionArg(arg: ArgInfo) extends ArgInfo {
  val name: String = arg.name
  val sort: String = "option[" + arg.sort + "]"
  val allowsFresh: List[String] = arg.allowsFresh
}
@deprecated("Until lists are actually added to the concrete syntax of Bellerophon.", "4.2b1")
case class ListArg (override val name: String, elementSort: String, override val allowsFresh: List[String] = Nil) extends ArgInfo {
  val sort = "list"
}

/** Central meta-information on a derivation step, which is an axiom, derived axiom, proof rule, or tactic.
  * Provides information such as unique canonical names, internal code names, display information, etc.
  * @see [[CoreAxiomInfo]]
  * @see [[DerivedAxiomInfo]]
  * @see [[AxiomaticRuleInfo]]
  * @see [[DerivedRuleInfo]]
  * @see [[TacticInfo]]
  */
sealed trait DerivationInfo {
  /** Canonical name unique across all derivations (axioms or tactics). For axioms or axiomatic rules this is as declared in
    * [[AxiomBase]], for derived axioms or derived axiomatic rules as in [[DerivedAxioms]],
    * and for [[BelleExpr]] tactics it is identical to their codeName.
    * Canonical names can and will contain spaces and special chars. */
  val canonicalName: String
  /** How to display this inference step in a UI */
  val display: DisplayInfo
  /** The unique alphanumeric identifier for this inference step, cannot contain spaces. */
  val codeName: String
  /** Specification of inputs (other than positions) to the derivation, along with names to use when displaying in the UI. */
  val inputs: List[ArgInfo] = Nil
  /** Bellerophon tactic implementing the derivation. For non-input tactics this is simply a BelleExpr. For input tactics
    * it is (curried) function which accepts the inputs and produces a BelleExpr. */
  def belleExpr: Any
  //@todo add formattedName/unicodeName: String
  /** Number of positional arguments to the derivation. Can be 0, 1 or 2. */
  val numPositionArgs: Int = 0
  /** Whether the derivation expects the caller to provide it with a way to generate invariants */
  val needsGenerator: Boolean = false
  /** Whether the derivation makes internal steps that are useful for users to see. */
  val revealInternalSteps: Boolean = false
  override def toString: String = "DerivationInfo(" + canonicalName + "," + codeName + ")"
}

/** Meta-Information for a (derived) axiom or (derived) axiomatic rule
  * @see [[AxiomInfo]]
  * @see [[AxiomaticRuleInfo]]
  * @see [[DerivedRuleInfo]] */
trait ProvableInfo extends DerivationInfo {
  /** The Provable representing this (derived) axiom or (derived) axiomatic rule */
  val provable: ProvableSig
  /** `true` indicates that the key of this axiom/axiomatic proof rule can be matched linearly [[LinearMatcher]].
    * For completeness, this linearity declaration must be consistent with the default key from [[AxiomIndex.axiomFor()]].
    * @see [[LinearMatcher]] */
  val linear: Boolean
}

/** Storable items (e.g., as lemmas) */
trait StorableInfo extends DerivationInfo {
  val storedName: String = codeName.toLowerCase
}

object ProvableInfo {
  /** Retrieve meta-information on a (derived) axiom or (derived) axiomatic rule by the given canonical name `name` */
  def locate(name: String): Option[ProvableInfo] =
    DerivationInfo(name) match {
      case info: ProvableInfo => Some(info)
      case _ => None
    }
  /** Retrieve meta-information on a (derived) axiom or (derived) axiomatic rule by the given canonical name `name` */
  def apply(name: String): ProvableInfo =
    DerivationInfo(name) match {
      case info: ProvableInfo => info
      case info => throw new Exception("Derivation \"" + info.canonicalName + "\" is not an axiom or axiomatic rule, whether derived or not.")
    }

  /** True if ProvableInfo with `storedName` exists, false otherwise. */
  def existsStoredName(storedName: String): Boolean =
    DerivationInfo.allInfo.exists({case si: StorableInfo => si.storedName == storedName case _ => false})

  /** Retrieve meta-information on an inference by the given stored name `storedName` */
  def ofStoredName(storedName: String): ProvableInfo = {
    DerivationInfo.allInfo.find({case si: StorableInfo => si.storedName == storedName case _ => false}) match {
      case Some(info: ProvableInfo) => info
      case Some(info) => throw new Exception("Derivation \"" + info.canonicalName + "\" is not an axiom or axiomatic rule, whether derived or not.")
      case _ => throw new Exception("Derivation \"" + storedName + "\" is not a derived axiom or rule.")
    }
  }

  val allInfo:List[ProvableInfo] =  DerivationInfo.allInfo.filter(_.isInstanceOf[ProvableInfo]).map(_.asInstanceOf[ProvableInfo])
}


/** Meta-Information for an axiom or derived axiom
  * @see [[edu.cmu.cs.ls.keymaerax.btactics.AxiomIndex]] */
trait AxiomInfo extends ProvableInfo {
  /** The valid formula that this axiom represents */
  def formula: Formula
}

/** Meta-Information for an axiom from the prover core
  * @see [[AxiomBase]]
  * @see [[DerivedAxiomInfo]]
  */
case class CoreAxiomInfo(override val canonicalName:String, override val display: DisplayInfo, override val codeName: String, override val linear: Boolean, expr: Unit => DependentPositionTactic)
  extends AxiomInfo {
  DerivationInfo.assertValidIdentifier(codeName)
  import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory
  def belleExpr = codeName by ((pos:Position, seq:Sequent) => expr ()(pos))
  override val formula:Formula = {
    ProvableSig.axiom.get(canonicalName) match {
      case Some(fml) => fml
      case None => throw new AxiomNotFoundException("No formula for core axiom " + canonicalName)
    }
  }
  override lazy val provable:ProvableSig = ProvableSig.axioms(canonicalName)
  override val numPositionArgs = 1
}

object CoreAxiomInfo {
  /** Retrieve meta-information on a core axiom by the given canonical name `axiomName` */
  def apply(axiomName: String): CoreAxiomInfo =
  DerivationInfo(axiomName) match {
    case info:CoreAxiomInfo => info
    case info => throw new Exception("Derivation \"" + info.canonicalName + "\" is not a core axiom")
  }

  /** Retrieve meta-information on a core axiom by the given code name `codeName` */
  def ofCodeName(codeName: String): CoreAxiomInfo =
  DerivationInfo.ofCodeName(codeName) match {
    case info:CoreAxiomInfo => info
    case info => throw new Exception("Derivation \"" + info.canonicalName + "\" is not an axiom")
  }

  val allInfo:List[CoreAxiomInfo] =  DerivationInfo.allInfo.filter(_.isInstanceOf[CoreAxiomInfo]).map(_.asInstanceOf[CoreAxiomInfo])
}

/** Information for a derived axiom proved from the core
  * @see [[DerivedAxioms]]
  * @see [[CoreAxiomInfo]] */
case class DerivedAxiomInfo(override val canonicalName: String, override val display: DisplayInfo, override val codeName: String, override val linear: Boolean, expr: Unit => DependentPositionTactic)
  extends AxiomInfo with StorableInfo {
  DerivationInfo.assertValidIdentifier(codeName)
  import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory
  def belleExpr: BelleExpr = codeName by ((pos: Position, _: Sequent) => expr()(pos))
  override lazy val formula: Formula =
    DerivedAxioms.derivedAxiomOrRule(canonicalName).conclusion.succ.head
//  {
//    DerivedAxioms.derivedAxiomMap.get(canonicalName) match {
//      case Some(fml) => fml._1
//      case None => throw new AxiomNotFoundException("No formula for axiom " + canonicalName)
//    }
//  }
  override lazy val provable:ProvableSig = DerivedAxioms.derivedAxiomOrRule(canonicalName)
  override val numPositionArgs = 1
}

object DerivedAxiomInfo {
  /** Retrieve meta-information on an axiom by the given canonical name `axiomName` */
  def locate(axiomName: String): Option[DerivedAxiomInfo] =
    DerivationInfo(axiomName) match {
      case info: DerivedAxiomInfo => Some(info)
      case _ => None
    }
  /** Retrieve meta-information on an axiom by the given canonical name `axiomName` */
  def apply(axiomName: String): DerivedAxiomInfo =
    DerivationInfo(axiomName) match {
      case info: DerivedAxiomInfo => info
      case info => throw new Exception("Derivation \"" + info.canonicalName + "\" is not a derived axiom")
    }

  val allInfo:List[DerivedAxiomInfo] =  DerivationInfo.allInfo.filter(_.isInstanceOf[DerivedAxiomInfo]).map(_.asInstanceOf[DerivedAxiomInfo])
}

// tactics

/** Meta-information on builtin tactic expressions (expand etc.). */
class BuiltinInfo(override val codeName: String, override val display: DisplayInfo,
                 override val needsGenerator: Boolean = false, override val revealInternalSteps: Boolean = false)
  extends DerivationInfo {
  def belleExpr: BelleExpr = BelleParser(codeName)
  val canonicalName: String = codeName
}

/** Meta-information on a tactic performing a proof step (or more) */
class TacticInfo(override val codeName: String, override val display: DisplayInfo, expr: Unit => Any, needsTool: Boolean = false,
                 override val needsGenerator: Boolean = false, override val revealInternalSteps: Boolean = false)
  extends DerivationInfo {
  DerivationInfo.assertValidIdentifier(codeName)
  def belleExpr = expr()
  val canonicalName = codeName
}

case class PositionTacticInfo(override val codeName: String, override val display: DisplayInfo, expr: Unit => Any,
                              needsTool: Boolean = false, override val needsGenerator: Boolean = false,
                              override val revealInternalSteps: Boolean = false)
  extends TacticInfo(codeName, display, expr, needsTool, needsGenerator, revealInternalSteps) {
  override val numPositionArgs = 1
}

case class TwoPositionTacticInfo(override val codeName: String, override val display: DisplayInfo, expr: Unit => Any, needsTool: Boolean = false, override val needsGenerator: Boolean = false)
  extends TacticInfo(codeName, display, expr, needsTool, needsGenerator) {
  override val numPositionArgs = 2
}

case class InputTacticInfo(override val codeName: String, override val display: DisplayInfo, override val inputs:List[ArgInfo], expr: Unit => TypedFunc[_, _], needsTool: Boolean = false,
                           override val needsGenerator: Boolean = false, override val revealInternalSteps: Boolean = false)
  extends TacticInfo(codeName, display, expr, needsTool, needsGenerator, revealInternalSteps)

case class InputPositionTacticInfo(override val codeName: String, override val display: DisplayInfo,
                                   override val inputs:List[ArgInfo], expr: Unit => TypedFunc[_,_], needsTool: Boolean = false,
                                   override val needsGenerator: Boolean = false, override val revealInternalSteps: Boolean = false)
  extends TacticInfo(codeName, display, expr, needsTool, needsGenerator, revealInternalSteps) {
  override val numPositionArgs = 1
}

case class InputTwoPositionTacticInfo(override val codeName: String, override val display: DisplayInfo, override val inputs:List[ArgInfo], expr: Unit => TypedFunc[_, _], needsTool: Boolean = false, override val needsGenerator: Boolean = false)
  extends TacticInfo(codeName, display, expr, needsTool, needsGenerator) {
  override val numPositionArgs = 2
}

/** Information for an axiomatic rule
  * @see [[AxiomBase]]
  * @see [[DerivedRuleInfo]] */
case class AxiomaticRuleInfo(override val canonicalName:String, override val display: DisplayInfo, override val codeName: String)
  extends ProvableInfo {
  // lazy to avoid circular initializer call
  lazy val expr = TactixLibrary.by(provable, codeName)
  DerivationInfo.assertValidIdentifier(codeName)
  def belleExpr = expr
  lazy val provable: ProvableSig = ProvableSig.rules(canonicalName)
  override val numPositionArgs = 0
  //@note Presently, only nonlinear shapes in core axiomatic rules in [[edu.cmu.cs.ls.keymaerax.core.AxiomBase.loadAxiomaticRules]]
  override val linear: Boolean = false
}


/** Information for a derived rule proved from the core
  * @see [[AxiomaticRuleInfo]] */
case class DerivedRuleInfo(override val canonicalName:String, override val display: DisplayInfo, override val codeName: String, expr: Unit => Any)
  extends ProvableInfo with StorableInfo {
  DerivationInfo.assertValidIdentifier(codeName)
  def belleExpr = expr()
  lazy val provable: ProvableSig = DerivedAxioms.derivedAxiomOrRule(canonicalName)
  override val numPositionArgs = 0
  //@note Presently, mostly nonlinear shapes in derived axiomatic rules
  override val linear: Boolean = false
}

object DerivedRuleInfo {
  /** Retrieve meta-information on a rule by the given canonical name `ruleName` */
  def locate(ruleName: String): Option[DerivedRuleInfo] =
    DerivationInfo(ruleName) match {
      case info: DerivedRuleInfo => Some(info)
      case _ => None
    }
  /** Retrieve meta-information on a rule by the given canonical name `ruleName` */
  def apply(ruleName: String): DerivedRuleInfo =
    DerivationInfo(ruleName) match {
      case info: DerivedRuleInfo => info
      case info => throw new Exception("Derivation \"" + info.canonicalName + "\" is not a derived rule")
    }

  val allInfo:List[DerivedRuleInfo] =  DerivationInfo.allInfo.filter(_.isInstanceOf[DerivedRuleInfo]).map(_.asInstanceOf[DerivedRuleInfo])
}
