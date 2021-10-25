/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.btactics

import java.lang.reflect.Method

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.btactics.macros._
import edu.cmu.cs.ls.keymaerax.btactics.InvariantGenerator.GenProduct
import edu.cmu.cs.ls.keymaerax.btactics.arithmetic.speculative.ArithmeticSpeculativeSimplification
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.btactics.components.ComponentSystem
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct._
import edu.cmu.cs.ls.keymaerax.lemma.Lemma
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig

import scala.collection.immutable.HashMap
import scala.language.implicitConversions
import DerivationInfoAugmentors._
import edu.cmu.cs.ls.keymaerax.{Logging, btactics}

import scala.collection.mutable
import scala.reflect.macros
import scala.reflect.runtime.universe.TypeTag
import scala.reflect.runtime.{universe => ru}
import scala.util.Try

/**
  * Table of metadeta for all axioms, rules, and tactics in the prover.
  * This table is now dynamically generated during startup by reflecting data generated in @Tactic and related macros.
  * The old hard-coded table is no longer used, it is left here temporarily as a comment, as a courtesy for anyone who
  * might debug the new initialization code.
  * @TODO delete commented-out table after further testing
  * @see [[DerivationInfoRegistry.init]]
  *
  * Created by bbohrer on 12/28/15.
  */




////////////////////////////////////////////////////////////
// Central registry of all derivation steps
////////////////////////////////////////////////////////////



/**
  * Central list of all derivation steps (axioms, derived axioms, proof rules, tactics)
  * with meta information of relevant names and display names and visualizations for the user interface.
  */
object DerivationInfoRegistry extends Logging {
  import scala.language.implicitConversions
  //implicit def DerivationInfoToDerivationInfoConverter(s: DerivationInfo): DerivationInfoConverter = new DerivationInfoConverter(s)

  def convert(arg: ArgInfo, exprs: List[Expression]): Either[Any, String]  = {
    (arg, exprs) match {
      case (_: NumberArg, (v: Number) :: Nil) => Left(v)
      case (_: NumberArg, v :: Nil) => Right("Expected a number but got " + v.prettyString)
      case (_: VariableArg, (v: Variable) :: Nil) => Left(v)
      case (_: VariableArg, v :: Nil) => Right("Expected a variable but got " + v.prettyString)
      case (_: TermArg, (t: Term) :: Nil) => Left(t)
      case (_: TermArg, t :: Nil) => Right("Expected a term but got " + t.prettyString)
      case (_: FormulaArg, (f: Formula) :: Nil) => Left(f)
      case (_: FormulaArg, f :: Nil) => Right("Expected a formula but got " + f.prettyString)
      case (_: ExpressionArg, (e: Expression) :: Nil) => Left(e)
      case (_: ExpressionArg, e :: Nil) => Right("Expected an expression but got " + e.prettyString)
      case (ListArg(ai: ArgInfo), fmls) if fmls.forall(_.kind == FormulaKind) =>
        val res = fmls.map(e => convert(ai, List(e)))
        res.find({case _: Left[Any, String] => false case _: Right[Any, String] => true}) match {
          case Some(Right(err)) => Right(err)
          case None => Left(res.map({case Left(v) => v}))
        }
      case _ => Right("Expected: " + arg.sort + ", found: " + exprs.map(_.kind).mkString(",") + " " + exprs.map(_.prettyString).mkString(","))
    }
  }

  private val needsCodeName = "THISAXIOMSTILLNEEDSACODENAME"
  /** Unsure whether linear matcher suffices so default to false */
  private val unsure = 'full
  /** unsure because of variable renaming being separate from substitution */
  private val unren = 'full

  /** Check that the names of the given list of DerivationInfo are declared consistently. */
  private def consistentInfo(list: List[DerivationInfo]): Boolean = {
    val canonicals = list.map(_.canonicalName)
    val codeNames = list.map(_.codeName).filter(_ != needsCodeName)
    val storedNames = list.filter(_.isInstanceOf[StorableInfo]).map(_.asInstanceOf[StorableInfo].storedName)
    list.forall({
      case ax: CoreAxiomInfo => ProvableSig.axiom.contains(ax.canonicalName) ensures(r=>r, "core axiom correctly marked as CoreAxiomInfo: " + ax.canonicalName)
      case _: DerivedAxiomInfo => true //@todo can't ask Ax.derivedAxiom yet since still initializing, besides that'd be circular
      case _ => true
    }
    ) &&
      (canonicals.length==canonicals.distinct.length ensures(r=>r, "unique canonical names: " + (canonicals diff canonicals.distinct))) &&
      (codeNames.length==codeNames.distinct.length ensures(r=>r, "unique code names / identifiers: " + (codeNames diff codeNames.distinct))) &&
      //@note to avoid file storage issues on some OSes, lowercase versions of code names used in files are expected to be unique.
      (storedNames.length==storedNames.distinct.length ensures(r=>r, "unique stored names / identifiers across all derived axioms: " + (storedNames diff storedNames.distinct)))
  }

  /** Locate the derivation info for said tactic */
  def locate(t: BelleExpr): Option[DerivationInfo] = t match {
    case n: NamedBelleExpr => try { Some(DerivationInfo.ofCodeName(n.name)) } catch { case _: Exception => None }
    case AppliedPositionTactic(n, _) => locate(n)
    case AppliedBuiltinTwoPositionTactic(n, _, _) => locate(n)
    //@todo probably more cases
    case _ => None
  }



  private def useAt(pi: ProvableInfo): DependentPositionTactic = HilbertCalculus.useAt(pi)
  private def useAt(l: Lemma): DependentPositionTactic = HilbertCalculus.useAt(l)
  private val posnil = TacticFactory.anon((pos,seq) => TactixLibrary.nil)

  ////////////////////////////////////////////////////////
  // Structure registry [[allInfo]] as modalities, ODEs, differentials, quantifiers, misc, derived axioms, sequent rules.
  ////////////////////////////////////////////////////////

  //<editor-fold desc="modalities">

  /** Modality cases of [[allInfo]] */
  private[this] val modalityInfos: List[DerivationInfo] = List(/*
    // [a] modalities and <a> modalities
    PositionTacticInfo("diamondd" //@Tactic-fied
      , AxiomDisplayInfo(("<·>d", "<.>d"), "<span class=\"k4-axiom-key\">&langle;a&rangle;P</span> ↔ &not;[a]&not;P")
      , {case () => HilbertCalculus.useAt(Ax.diamond, PosInExpr(1::Nil))}),
    PositionTacticInfo("boxd" //@Tactic-fied
      , AxiomDisplayInfo(("[·]d", "[.]d"), "<span class=\"k4-axiom-key\">[a]P</span> ↔ &not;&langle;a&rangle;&not;P")
      , {case () => HilbertCalculus.useAt(Ax.box, PosInExpr(1::Nil))}),
    new PositionTacticInfo("assignb" //@Tactic-fied
      , AxiomDisplayInfo("[:=]", "<span class=\"k4-axiom-key\">[x:=e]p(x)</span>↔p(e)")
      , {case () => TactixLibrary.assignb}, revealInternalSteps = true),
    new PositionTacticInfo("assignd", AxiomDisplayInfo("<:=>", "<span class=\"k4-axiom-key\">&langle;x:=e&rangle;p(x)</span>↔p(e)"), {case () => HilbertCalculus.assignd}), //@Tactic-fied
    new PositionTacticInfo("assignEquality", "[:=]=", {case () => DLBySubst.assignEquality}, revealInternalSteps = true), //@Tactic-fied
    new InputPositionTacticInfo("assignbExistsRule", //@Tactic-fied
      RuleDisplayInfo(
        "[:=] assign exists",
        /* conclusion */ (List("&Gamma;"), List("∃t [x:=t;]P", "&Delta;")),
        /* premises */ List( (List("&Gamma;"), List("[t:=e;][x:=t;]P", "&Delta;")) )
      ),
      List(new TermArg("e")),
      _ => ((e: Term) => DLBySubst.assignbExists(e)): TypedFunc[Term, BelleExpr]
    ),
  */)
  //</editor-fold>

  //<editor-fold desc="ODEs">
  /** Differential equation cases of [[allInfo]] */
  private[this] lazy val odeInfos: List[DerivationInfo] = List(/*
    /*new CoreAxiomInfo("DW base", "DWbase", "DWbase", 'linear, {case () => HilbertCalculus.DW}),*/
    PositionTacticInfo("dW" // @Tactic-fied
      , RuleDisplayInfo("Differential Weaken"
        , /* conclusion */ (List("&Gamma;"),List("[{x′=f(x) & Q}]p(x)","&Delta;"))
        , /* premises */ List((List("&Gamma;<sub>const</sub>", "Q"), List("p(x)", "&Delta;<sub>const</sub>"))))
      , {case () => DifferentialTactics.diffWeaken}, revealInternalSteps = true),
    PositionTacticInfo("dWplus" // @Tactic-fied
      , RuleDisplayInfo("Assumption-Preserving Differential Weaken"
        , /* conclusion */ (List("&Gamma;"),List("[{x′=f(x) & Q}]p(x)","&Delta;"))
        , /* premises */ List((List("&Gamma;<sub>const</sub>", "Q"), List("p(x)", "&Delta;<sub>const</sub>"))))
      , {case () => DifferentialTactics.diffWeakenPlus}, revealInternalSteps = true),
    InputPositionTacticInfo("dC" // @Tactic-fied
      , RuleDisplayInfo("Differential Cut"
        , /* conclusion */ (List("&Gamma;"),List("[{x′=f(x) & Q}]P","&Delta;"))
        , /* premises */ List((List("&Gamma;"), List("[{x′=f(x) & Q}]R", "&Delta;")),
          (List("&Gamma;"), List("[{x′=f(x) & (Q∧R)}]P","&Delta;"))))
      , List(FormulaArg("R"))
      , _ => ((fml: Formula) => TactixLibrary.dC(fml)): TypedFunc[Formula, BelleExpr], revealInternalSteps = true),
    InputPositionTacticInfo("dR" // @Tactic-fied
      , RuleDisplayInfo("Differential Refine"
        , /* conclusion */ (List("&Gamma;"),List("[{x′=f(x) & Q}]P","&Delta;"))
        , /* premises */ List((List("&Gamma;"), List("[{x′=f(x) & Q}]R", "&Delta;")),
          (List("&Gamma;"), List("[{x′=f(x) & R}]P","&Delta;"))))
      , List(FormulaArg("R"))
      , _ => ((fml: Formula) => DifferentialTactics.diffRefine(fml)): TypedFunc[Formula, BelleExpr]),
    PositionTacticInfo("dCi" // @Tactic-fied
      , RuleDisplayInfo("dCi"
        , /* conclusion */ (List("&Gamma;"),List("[{x′=f(x) & (Q∧R)}]P","&Delta;"))
        , /* premises */ List(
          (List("&Gamma;"), List("[{x′=f(x) & Q}]P", "&Delta;")),
          (List("&Gamma;"), List("R", "&Delta;"))))
      , _ => DifferentialTactics.inverseDiffCut),
    {
      val converter = (e: Expression) => e match {
        case n: Number => Left(n)
        case _ => Right("Expected a number but got " + e.prettyString)
      }
      InputPositionTacticInfo("autoApproximate", // @Tactic-fied
        RuleDisplayInfo("Approximate",
          (List("&Gamma;"), List("[{X'=F & &Alpha;(n)}]", "&Delta;")),
          List( (List("&Gamma;"), List("[{X'=F}]", "&Delta;")) )
        ),
        List(new ExpressionArg("n", Nil)),
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
      InputPositionTacticInfo("expApproximate", // @Tactic-fied
        RuleDisplayInfo("e'=e Approximation",
          (List("&Gamma;"), List("[{c1,e'=e,c2 & approximate(n)}]", "&Delta;")),
          List( (List("&Gamma;"), List("[{c1,e'=c,c2}]", "&Delta;")) )
        ),
        List(new ExpressionArg("e", "e"::Nil), new ExpressionArg("n", Nil)),
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
      InputPositionTacticInfo("circularApproximate", // @Tactic-fied
        RuleDisplayInfo("Circular Dynamics Approximation",
          (List("&Gamma;"), List("[{c1,s'=c,c2,c'=-s,c3 & approximate(n)}]", "&Delta;")),
          List((List("&Gamma;"), List("[{c1,e'=c,c2}]", "&Delta;")))
        ),
        List(new ExpressionArg("s", "s" :: Nil), new ExpressionArg("c", "c" :: Nil), new ExpressionArg("n", Nil)),
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
      // @Tactic-ified
      InputPositionTacticInfo("dG",
        RuleDisplayInfo(
          "Differential Ghost",
          /* conclusion */ (List("&Gamma;"), List("[{x′=f(x) & Q}]P", "&Delta;")),
          /* premises */ List( (List("&Gamma;"), List("∃y [{x′=f(x),E & Q}]P", "&Delta;")) )
        ),
        List(new ExpressionArg("E", "y"::"x"::"y'"::Nil), FormulaArg("P", "y"::Nil)),
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
    PositionTacticInfo("dGi", // @Tactic-fied
      RuleDisplayInfo(
        "Inverse Differential Ghost",
        /* conclusion */ (List("&Gamma;"), List("∃y [{x′=f(x),E & Q}]P", "&Delta;")),
        /* premises */ List( (List("&Gamma;"), List("[{x′=f(x) & Q}]P", "&Delta;")) )
      ),
      _ => DifferentialTactics.inverseDiffGhost
    ),
    InputPositionTacticInfo("dbx", // @Tactic-fied
      RuleDisplayInfo(
        "Darboux (in)equalities",
        /* conclusion */ (List("p≳0"), List("[{x′=f(x) & Q}]p≳0")),
        /* premises */ List( (List("Q"), List("p' ≥ gp")) )
      ),
      List(OptionArg(new TermArg("g"))),
      _ => {
        case Some(g: Term) => DifferentialTactics.dgDbx(g)
        case None => DifferentialTactics.dgDbxAuto
      }: TypedFunc[Option[Term], BelleExpr]
    ),
    PositionTacticInfo("diffUnpackEvolDomain", //@Tactic-fied
      RuleDisplayInfo(
        "Unpack evolution domain",
        /* conclusion */ (List("&Gamma;"), List("[{x′=f(x) & Q}]P","&Delta;")),
        /* premises */ List( (List("&Gamma;","Q"), List("[{x′=f(x) & Q}]P","&Delta;")) )
      ),
      _ => DifferentialTactics.diffUnpackEvolutionDomainInitially
    ),
    PositionTacticInfo("barrier", //@Tactic-fied
      RuleDisplayInfo(
        "Strict Barrier Certificate",
        /* conclusion */ (List("p≳0"), List("[{x′=f(x) & Q}]p≳0")),
        /* premises */ List( (List("Q ∧ p=0"), List("p'>0")) )
      ),
      _ => DifferentialTactics.dgBarrier
    ),
    PositionTacticInfo("dRI", //@Tactic-fied
      RuleDisplayInfo(
        "(Conj.) Differential Radical Invariants",
        /* conclusion */ (List("p*=0"), List("[{x′=f(x) & Q}]p=0")),
        /* premises */ List( (List("Q"), List("p*=0")) )
      ),
      _ => ODEInvariance.dRI
    ),
    // @Tactic-ified
    new InputPositionTacticInfo("dGold",
      RuleDisplayInfo(
        "Differential Ghost",
        /* conclusion */ (List("&Gamma;"), List("[{x′=f(x) & Q}]P", "&Delta;")),
        /* premises */ List( (List("&Gamma;"), List("∃y [{x′=f(x),y′=a(x)*y+b(x) & Q}]P", "&Delta;")) )
      ),
      List(VariableArg("y", "y"::Nil), new TermArg("a(x)"), new TermArg("b(x)"), FormulaArg("P", "y"::Nil)),
      _ =>
        ((y: Variable) =>
          ((t1: Term) =>
            ((t2: Term) =>
              ((p: Option[Formula]) => TactixLibrary.dG(AtomicODE(DifferentialSymbol(y), Plus(Times(t1, y), t2)), p)
                ): TypedFunc[Option[Formula], BelleExpr]
              ): TypedFunc[Term, TypedFunc[Option[Formula], BelleExpr]]
            ): TypedFunc[Term, TypedFunc[Term, TypedFunc[Option[Formula], BelleExpr]]]
          ): TypedFunc[Variable, TypedFunc[Term, TypedFunc[Term, TypedFunc[Option[Formula], BelleExpr]]]]
    )*/
  )
  //</editor-fold>

  //<editor-fold desc="Differentials">
  /** Differential cases of [[allInfo]] */
  private[this] lazy val differentialInfos: List[DerivationInfo] = List(/*
    new PositionTacticInfo("Dvariable" //@Tactic-fied
      ,  AxiomDisplayInfo(("x′","x'"), "<span class=\"k4-axiom-key\">(x)′</span>=x′")
      , {case () => DifferentialTactics.Dvariable}),

    //@Tactic-fied
    new PositionTacticInfo("derive", "()'", {case () => HilbertCalculus.derive} , revealInternalSteps = false /* uninformative as forward proof */)*/
  )
  //</editor-fold>

  //<editor-fold desc="First-order quantifiers">
  /** First-order logic quantifier cases of [[allInfo]] */
  private[this] lazy val foInfos: List[DerivationInfo] = List()

  /** Miscellaneous cases of [[allInfo]] that don't really fit anywhere else.   */
  private[this] lazy val miscInfos: List[DerivationInfo] = List(
    // more
    // Note: only used to implement Dskipd
    //new CoreAxiomInfo("DX differential skip", "DX", "DX", 'linear, {case () => throw new UnsupportedOperationException("DX differential skip is not available for general-purpose use") })
  )

  /** Derived axiom cases of [[allInfo]] but [[DerivedAxiomInfo]] can also be filed elsewhere. */
  private[this] lazy val derivedAxiomsInfos: List[DerivedAxiomInfo] = List()
  //</editor-fold>

  //<editor-fold desc="Sequent Calculus">
  /** Sequent calculus cases of [[allInfo]] */
  private[this] lazy val sequentCalculusInfos: List[DerivationInfo] = List(/*
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
        List((List("&Gamma;"),List("&Delta;","P")),
          (List("Q","&Gamma;"),List("&Delta;"))))
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
    new InputPositionTacticInfo("allL" //@Tactic-fied
      , RuleDisplayInfo(("∀L", "allL"), (List("&Gamma;","∀x P(x)"), List("&Delta;")),
        List((List("&Gamma;", "P(θ)"),List("&Delta;"))))
      , List(new TermArg("θ", "θ"::Nil))
      , _ => ((t:Term) => SequentCalculus.allL(t)): TypedFunc[Term, BelleExpr]),
    new PositionTacticInfo("allR"  //@Tactic-fied
      , RuleDisplayInfo(("∀R", "allR"), (List("&Gamma;"), List("∀x P(x)", "&Delta;")),
        List((List("&Gamma;"),List("P(x)","&Delta;"))))
      , {case () => SequentCalculus.allR}),
    new PositionTacticInfo("existsL" //@Tactic-fied
      , RuleDisplayInfo(("∃L", "existsL"), (List("&Gamma;","∃x P(x)"),List("&Delta;")),
        List((List("&Gamma;","P(x)"),List("&Delta;"))))
      , {case () => SequentCalculus.existsL}),
    new PositionTacticInfo("G"
      , RuleDisplayInfo("G", (List("&Gamma;"), List("[a]P", "&Delta;")), List((List(),List("P"))))
      , {case () => HilbertCalculus.G}),
    new PositionTacticInfo("GV" //@Tactic-fied DLBySubst.scala
      , RuleDisplayInfo("G&ouml;del Vacuous", (List("&Gamma;"), List("[a]P", "&Delta;"))
        , List((List("&Gamma;<sub>const</sub>"), List("P", "&Delta;<sub>const</sub>"))))
      , {case () => TactixLibrary.abstractionb}, revealInternalSteps = true),
    new InputPositionTacticInfo("existsR" //@Tactic-fied
      , RuleDisplayInfo(("∃R", "existsR"), (List("&Gamma;"), List("∃x P(x)", "&Delta;")),
        List((List("&Gamma;"),List("P(θ)", "&Delta;"))))
      , List(new TermArg("θ", "θ"::Nil))
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
    new TacticInfo("smartHide", "smartHide", {case () => ArithmeticSimplification.smartHide}), //@Tactic-fied but broken
    new PositionTacticInfo("cohideL", "W", {case () => SequentCalculus.cohideL}), //@Tactic-fied
    new PositionTacticInfo("cohideR", "W", {case () => SequentCalculus.cohideR}), //@Tactic-fied
    new TacticInfo("closeFalse"  //@Tactic-fied
      , RuleDisplayInfo(("⊥L", "falseL"), (List("⊥","&Gamma;"),List("&Delta;")), List())
      , {case () => TactixLibrary.closeF}),
    new TacticInfo("closeTrue"  //@Tactic-fied
      , RuleDisplayInfo(("⊤R","trueR"), (List("&Gamma;"), List("⊤","&Delta;")),List())
      ,{case () => TactixLibrary.closeT}),
    new PositionTacticInfo("skolemizeR", "skolem", {case () => ProofRuleTactics.skolemizeR}), //@Tactic-fied
    new PositionTacticInfo("cohide", "W", {case () => SequentCalculus.cohide}), //@Tactic-fied
    new PositionTacticInfo("hide", "W", {case () => SequentCalculus.hide}), //@Tactic-fied
    new PositionTacticInfo("allL2R", "L=R all", {case () => TactixLibrary.exhaustiveEqL2R}), //@Tactic-fied
    new PositionTacticInfo("atomAllL2R", "L=R all atoms", {case () => EqualityTactics.atomExhaustiveEqL2R}), //@Tactic-fied
    new PositionTacticInfo("allR2L", "R=L all", {case () => TactixLibrary.exhaustiveEqR2L}), //@Tactic-fied
    new PositionTacticInfo("minmax", "min/max", {case () => EqualityTactics.minmax}), //@Tactic-fied
    new PositionTacticInfo("absExp", "absExp", {case () => EqualityTactics.abs}), //@Tactic-fied
    new PositionTacticInfo("toSingleFormula", "toFormula", {case () => PropositionalTactics.toSingleFormula}),  //@Tactic-fied

    PositionTacticInfo("CMon" //@Tactic-fied
      , RuleDisplayInfo("CMon", (List(), List("C{o}→C{k}")), List((List(), List("o→k"))))
      , {case () => TactixLibrary.CMon}
    ),
    InputTacticInfo("CMonCongruence" //@Tactic-fied
      , SimpleDisplayInfo("CMonCongruence","CMonCongruence")
      ,List(StringArg("inEqPos")), _ => ((inEqPos: String) => TactixLibrary.CMon(PosInExpr.parse(inEqPos))): TypedFunc[String, BelleExpr]),
    InputTacticInfo("CECongruence" //@Tactic-fied
      , SimpleDisplayInfo("CECongruence","CECongruence")
      ,List(StringArg("inEqPos")), _ => ((inEqPos: String) => TactixLibrary.CE(PosInExpr.parse(inEqPos))): TypedFunc[String, BelleExpr]),

    // proof management tactics
    //@Tactic-ified
    InputTacticInfo("debug"
      , SimpleDisplayInfo("Debug","debug")
      ,List(StringArg("msg")), _ => ((msg: String) => DebuggingTactics.debug(msg)): TypedFunc[String, BelleExpr]),
    //@Tactic-ified
    InputTacticInfo("done"
      , SimpleDisplayInfo("Done","done")
      ,List(StringArg("msg"),StringArg("lemmaName")), _ =>
        ((msg: Option[String]) =>
          ((lemmaName: Option[String]) =>
            DebuggingTactics.done(msg.getOrElse(""), lemmaName)): TypedFunc[Option[String], BelleExpr]): TypedFunc[Option[String], _]
    ),
    //@Tactic-ified
    InputTacticInfo("pending"
      , SimpleDisplayInfo("pending", "pending")
      ,List(StringArg("tactic")), _ =>
        ((tactic: String) => DebuggingTactics.pending(tactic)): TypedFunc[String, BelleExpr]
    ),
    InputTacticInfo("label" // @Tactic-ified
      , SimpleDisplayInfo("label","label")
      ,List(StringArg("label")), _ => ((l: String) => TactixLibrary.label(BelleLabel.toPrettyString(BelleLabel.fromString(l)))): TypedFunc[String, BelleExpr]),

    // Proof rule two-position tactics
    new TwoPositionTacticInfo("coHide2", "W", {case () => SequentCalculus.cohide2}),
    // @Tactic-ified
    new TwoPositionTacticInfo("equivRewriting", RuleDisplayInfo("equivRewriting", (List("&Gamma;", "∀X p(X) <-> q(X)"), List("p(Z)", "&Delta;")), List((List("&Gamma;", "∀X p(X) <-> q(X)"), List("q(Z)", "&Delta;")))), {case () => PropositionalTactics.equivRewriting}),
    // @Tactic-ifed
    new TwoPositionTacticInfo("instantiatedEquivRewriting", "instantiatedEquivRewriting", {case () => PropositionalTactics.instantiatedEquivRewriting}),
    //    new TwoPositionTacticInfo("exchangeL", "X", {case () => ProofRuleTactics.exchangeL}),
    //    new TwoPositionTacticInfo("exchangeR", "X", {case () => ProofRuleTactics.exchangeR}),
    // @Tactic-ified
    new TacticInfo("closeTransitive", RuleDisplayInfo("closeTransitive", (List("a>=b", "b >= c", "c >= z"), List("a >= z")), Nil), {case () => Transitivity.closeTransitive}),
    //@note deprecated use id instead
    new TacticInfo("id",
      RuleDisplayInfo("Close by identity", (List("&Gamma;", "P"), List("P", "&Delta;")), Nil),
      {case () => TactixLibrary.id}), //@Tactic-fied
    PositionTacticInfo("idWith", // @Tactic-ified
      RuleDisplayInfo("Close by identity", (List("&Gamma;", "P"), List("P", "&Delta;")), Nil),
      {case () => TactixLibrary.closeIdWith}),
    new TacticInfo("close", // @Tactic-ified
      RuleDisplayInfo("Close by ⊥/⊤", (List("&Gamma;", "P", "⊥"), List("⊤", "P", "&Delta;")), Nil),
      {case () => TactixLibrary.close}),
    //@Tactic-ified
    new TwoPositionTacticInfo("L2R",
      RuleDisplayInfo("Apply equality",
        /*conclusion*/ (List("&Gamma;", "x=y", "P(x)"), List("Q(x)", "&Delta;")),
        /*premise*/    List((List("&Gamma;", "x=y", "P(y)"), List("Q(y)", "&Delta;")))),
      {case () => (pos: AntePosition) => TactixLibrary.eqL2R(pos)}),

    // Proof rule input tactics
    new InputTacticInfo("cut" // @Tactic-ified
      , RuleDisplayInfo(("cut","cut")
        ,(List("&Gamma;"), List("&Delta;"))
        ,List(
          (List("&Gamma;"),List("&Delta;","P")),
          (List("&Gamma;", "P"), List("&Delta;"))))
      ,List(FormulaArg("P")), _ => ((fml:Formula) => SequentCalculus.cut(fml)): TypedFunc[Formula, BelleExpr]),
    new InputTacticInfo("abbrv" //@Tactic-fied TactixLibrary.abbrvAll
      , RuleDisplayInfo(("Abbreviate","abbrv")
        ,(List("&Gamma;"), List("&Delta;"))
        ,List(
          (List("&Gamma;", "freshVar=theta"),List("&Delta;"))))
      ,List(new TermArg("theta"),VariableArg("freshVar", "freshVar"::Nil)), _ => ((t:Term) => ((v: Option[Variable]) => EqualityTactics.abbrv(t, v)): TypedFunc[Option[Variable], BelleExpr]): TypedFunc[Term, _]),
    // Proof rule input position tactics
    new InputPositionTacticInfo("cutL", "cutL", List(FormulaArg("cutFormula")), // @Tactic-ified
      _ => ((fml:Formula) => TactixLibrary.cutL(fml)): TypedFunc[Formula, BelleExpr]),
    new InputPositionTacticInfo("cutR", "cutR", List(FormulaArg("cutFormula")), // @Tactic-ified
      _ => ((fml:Formula) => TactixLibrary.cutR(fml)): TypedFunc[Formula, BelleExpr]),
    new InputPositionTacticInfo("cutLR", "cutLR", List(FormulaArg("cutFormula")), // @Tactic-ified
      _ => ((fml:Formula) => TactixLibrary.cutLR(fml)): TypedFunc[Formula, BelleExpr]),
    new InputPositionTacticInfo("loop", // @Tactic-ified
      RuleDisplayInfo("Induction",(List("&Gamma;"), List("[a*]P", "&Delta;")),
        List(
          (List("&Gamma;"),List("J", "&Delta;")),
          (List("J"),List("[a]J")),
          (List("J"),List("P"))))
      , List(FormulaArg("J")), _ => ((fml: Formula) => TactixLibrary.loop(fml)): TypedFunc[Formula, BelleExpr]
      , revealInternalSteps = true),
    // Duplicate?  @Tactic-ified
    //new PositionTacticInfo("loopAuto", "loopAuto",
    //{case () => (gen:Generator.Generator[GenProduct]) => TactixLibrary.loop(gen)}, needsGenerator = true),
    new InputPositionTacticInfo("throughout", //@Tactic-fied
      RuleDisplayInfo("Loop Throughout",(List("&Gamma;"), List("[{a;{b;c};d}*]P", "&Delta;")),
        List(
          (List("&Gamma;"),List("j(x)", "&Delta;")),
          (List("j(x)"),List("[a]j(x)")),
          (List("j(x)"),List("[b;c]j(x)")),
          (List("j(x)"),List("[d]j(x)")),
          (List("j(x)"),List("P"))))
      , List(FormulaArg("j(x)")), _ => ((fml: Formula) => TactixLibrary.throughout(fml)): TypedFunc[Formula, BelleExpr]),
    new InputPositionTacticInfo("con", //@Tactic-fied
      RuleDisplayInfo("Loop Convergence",(List("&Gamma;"), List("&lt;a*&gt;P", "&Delta;")),
        List(
          (List("&Gamma;"),List("∃x. j(x)", "&Delta;")),
          (List("x ≤ 0", "j(x)"),List("P")),
          (List("x > 0", "j(x)"),List("&lt;a&gt;j(x-1)"))))
      , List(VariableArg("x", allowsFresh = "x" :: Nil), FormulaArg("j(x)", allowsFresh = "x" :: Nil)), _ =>
        ((x: Variable) =>
          ((fml: Formula) => DLBySubst.con(x, fml)): TypedFunc[Formula, BelleExpr]): TypedFunc[Variable, _]),
    // @Tactic-ified
    new PositionTacticInfo("loopauto", RuleDisplayInfo("loopauto",(List("&Gamma;"), List("[a*]P", "&Delta;")),
      List()), {case () => (gen: Generator.Generator[GenProduct]) => TactixLibrary.loopauto(gen)}, needsGenerator = true),
    new InputPositionTacticInfo("MR", // @Tactic-ified
      RuleDisplayInfo("Monotonicity",(List("&Gamma;"), List("[a]P", "&Delta;")),
        List(
          (List("&Gamma;"),List("[a]Q", "&Delta;")),
          (List("Q"),List("P"))))
      , List(FormulaArg("Q")), _ => ((fml:Formula) => TactixLibrary.generalize(fml)): TypedFunc[Formula, BelleExpr], revealInternalSteps = true),
    // @Tactic-ified
    InputPositionTacticInfo("transform",
      RuleDisplayInfo("trafo",
        //@todo suggests formulas, but also works with terms
        /* conclusion */ (List("&Gamma;"), List("P", "&Delta;")),
        /* premises */ List((List("&Gamma;"),List("Q", "&Delta;")))),
      List(new ExpressionArg("Q")),
      _ => ((expr:Expression) => TactixLibrary.transform(expr)): TypedFunc[Expression, BelleExpr]),
    // @Tactic-ified
    new InputPositionTacticInfo("edit", "edit", List(new ExpressionArg("to")),
      _ => ((expr:Expression) => TactixLibrary.edit(expr)): TypedFunc[Expression, BelleExpr]),
    new TacticInfo("expandAll", "expandAll", _ => EqualityTactics.expandAll, revealInternalSteps = true), //@Tactic-fied
    new InputPositionTacticInfo("boundRename" // @Tactic-ified in ProofRuleTactics
      , RuleDisplayInfo(("BR", "BR"), (List("&Gamma;"), List("∀x P(x)","&Delta;")),
        List((List("&Gamma;"),List("∀y P(y)","&Delta;"))))
      , List(VariableArg("x"),VariableArg("y"))
      , _ => ((x:Variable) => ((y:Variable) => TactixLibrary.boundRename(x,y)): TypedFunc[Variable, BelleExpr]): TypedFunc[Variable, TypedFunc[Variable, BelleExpr]]),
    InputTacticInfo("uniformRename" // @Tactic-ified in ProofRuleTactics
      , RuleDisplayInfo(("UR", "UR"), (List("P(x)"), List("Q(x)")),
        List((List("P(y)"),List("Q(y)"))))
      , List(VariableArg("x"),VariableArg("y"))
      , _ => ((x:Variable) => ((y:Variable) => TactixLibrary.uniformRename(x,y)): TypedFunc[Variable, BelleExpr]): TypedFunc[Variable, TypedFunc[Variable, BelleExpr]]),
    new InputPositionTacticInfo("stutter" //@Tactic-fied
      , RuleDisplayInfo(("[:=]", "[:=]"), (List("&Gamma;"), List("P","&Delta;"))
        , List((List("&Gamma;"),List("[x:=x]P","&Delta;")))), List(VariableArg("x"))
      , _ => ((x:Variable) => DLBySubst.stutter(x)): TypedFunc[Variable, BelleExpr]),

    new TacticInfo("nil", "nil", {case () => Idioms.nil}),  //@Tactic-fied

    new InputPositionTacticInfo( // @Tactic-fied
      "transformEquality",
      "transformEquality",
      FormulaArg("equality") :: Nil,
      _ => ((f:Formula) => ArithmeticSimplification.transformEquality(f)): TypedFunc[Formula, BelleExpr]),

    new InputPositionTacticInfo(  //@Tactic-fied
      "discreteGhost",
      RuleDisplayInfo(("iG", "iG"), (List("&Gamma;"),List("P","&Delta;")),
        List((List("&Gamma;"), List("[gv:=gt;]P","&Delta;")))),
      new TermArg("gt") :: VariableArg("gv", "gv"::Nil) :: Nil,
      _ => ((t:Term) => ((v: Option[Variable]) => DLBySubst.discreteGhost(t, v)): TypedFunc[Option[Variable], BelleExpr]): TypedFunc[Term, _]),

    /*new TacticInfo("monb", "Box Monotonicity", {case () => TactixLibrary.monb}),
    new TacticInfo("monb2", "Box Monotonicity 2", {case () => DLBySubst.monb2}),
    //@todo unify axiomatic rule and derived rules mond / mondtodo
    new TacticInfo("mond", "Diamond Monotonicity", {case () => TactixLibrary.mond}),*/

    // TactixLibrary tactics
    PositionTacticInfo("step", "step", {case () => TactixLibrary.step}),
    PositionTacticInfo("stepAt", "stepAt", {case () => HilbertCalculus.stepAt}),
    // @Tactic-ified
    PositionTacticInfo("normalize", "normalize", {case () => TactixLibrary.normalize}, revealInternalSteps = true),
    PositionTacticInfo("unfold", "unfold", {case () => TactixLibrary.unfoldProgramNormalize}, revealInternalSteps = true),  //@Tactic-fied
    PositionTacticInfo("prop", "prop", {case () => TactixLibrary.prop}, revealInternalSteps = true),  //@Tactic-fied
    PositionTacticInfo("propAuto", "propAuto", {case () => TactixLibrary.propAuto}, revealInternalSteps = true),  //@Tactic-fied
    PositionTacticInfo("chase", "chase", {case () => TactixLibrary.chase}),  //@Tactic-fied
    // @Tactic-ified
    PositionTacticInfo("chaseAt", "chaseAt", {case () => TactixLibrary.chaseAt()(
      TactixLibrary.andL, TactixLibrary.implyR, TactixLibrary.orR, TactixLibrary.allR, TacticIndex.allLStutter,
      TactixLibrary.existsL, TacticIndex.existsRStutter,
      ProofRuleTactics.closeTrue, ProofRuleTactics.closeFalse
    )}),
    PositionTacticInfo("simplify", "simplify", {case () => SimplifierV3.simpTac()}), //@Tactic-fied
    // Technically in InputPositionTactic(Generator[Formula, {case () => ???}), but the generator is optional
    // @TODO: Simplify codeName
    // @Tactic-ified
    new TacticInfo("master", "master", {case () => (gen:Generator.Generator[GenProduct]) => TactixLibrary.master(gen)}, needsGenerator = true, revealInternalSteps = true),
    // @Tactic-ified
    new TacticInfo("explore", "explore", {case () => (gen:Generator.Generator[GenProduct]) => gen match {
      case cgen: ConfigurableGenerator[GenProduct] => TactixLibrary.explore(cgen)
      case _ => ??? // extract annotated invariants into a configurable generator
    } }, needsGenerator = true, revealInternalSteps = true),
    new TacticInfo("auto", "auto", {case () => TactixLibrary.auto}, needsGenerator = true, revealInternalSteps = true),  //@Tactic-fied
    // @Tactic-ified
    InputTacticInfo("useSolver"
      , "useSolver"
      , List(StringArg("tool"))
      , _ => ((tool: String) => ToolTactics.switchSolver(tool)): TypedFunc[String, BelleExpr]),
    // @Tactic-ified
    InputTacticInfo("QE", "QE",
      List(OptionArg(StringArg("tool")), OptionArg(new TermArg("timeout"))),
      _ => { case Some(toolName: String) => {
        case (Some(Number(timeout))) => TactixLibrary.QE(Nil, Some(toolName), Some(timeout.toInt))
        // interpret optional toolName as timeout
        case _ if Try(Integer.parseInt(toolName)).isSuccess => TactixLibrary.QE(Nil, None, Some(Integer.parseInt(toolName)))
        case _ =>  TactixLibrary.QE(Nil, Some(toolName)) }: TypedFunc[Option[Term], BelleExpr]
      case _ => {
        case Some(Number(timeout)) => TactixLibrary.QE(Nil, None, Some(timeout.toInt))
        case _ => TactixLibrary.QE }: TypedFunc[Option[Term], BelleExpr]
      }: TypedFunc[Option[String], _], revealInternalSteps = true),
    new TacticInfo("rcf", "RCF",  {case () => TactixLibrary.RCF}), //@Tactic-fied
    //new TacticInfo("MathematicaQE", "MathematicaQE", {case () => TactixLibrary.QE}),
    new TacticInfo("pQE", "pQE",  {case () => TactixLibrary.partialQE}), //@Tactic-fied
    new TacticInfo("smartQE", "smartQE",  {case () => ArithmeticSpeculativeSimplification.speculativeQE}), //@Tactic-fied
    new TacticInfo("fullSimplify", "fullSimplify",  {case () => SimplifierV3.fullSimpTac()}),  //@Tactic-fied
    //@todo universal closure may come with list of named symbols
    new PositionTacticInfo("universalClosure", SimpleDisplayInfo("∀Cl", "allClosure"), {case () => FOQuantifierTactics.universalClosure}), //@Tactic-fied
    // @Tactic-ified
    InputPositionTacticInfo("useAt"
      , "useAt"
      , List(StringArg("axiom"), StringArg("key"))
      , _ => ((axiomName: String) => {
        case None => TactixLibrary.useAt(AxiomInfo(axiomName)) //@note serializes as codeName
        case Some(k: String) =>
          val key = PosInExpr(k.split("\\.").map(Integer.parseInt).toList)
          val defaultKey = AxiomInfo(axiomName).key
          if (key != defaultKey) {
            //@note serializes as useAt({`axiomName`},{`k`})
            "useAt" byWithInputs (axiomName::k::Nil, (pos: Position, seq: Sequent) => {
              val axiom = ProvableInfo(axiomName)
              TactixLibrary.useAt(axiom.provable, key)(pos)
            })
          } else TactixLibrary.useAt(AxiomInfo(axiomName)) //@note serializes as codeName
      }: TypedFunc[Option[String], BelleExpr]): TypedFunc[String, _]),

    // @Tactic-ified
    InputTacticInfo("useLemma"
      , "useLemma"
      , List(StringArg("lemma"), StringArg("tactic"))
      , _ => ((lemmaName: String) => ((tactic: Option[String]) =>
        TactixLibrary.useLemma(lemmaName, tactic.map(_.asTactic))): TypedFunc[Option[String], BelleExpr]): TypedFunc[String, _]),

    // @Tactic-ified
    InputTacticInfo("byUS"
      , RuleDisplayInfo(("US", "byUS"), (List(),List("S(P)")),
        List((List(), List("P"))))
      , List(StringArg("P"), FormulaArg("S"))
      , _ => ((axiomName: String) => ({
        case None => TactixLibrary.byUS(AxiomInfo(axiomName), us=>us)
        case Some(substFml: Formula) =>
          val subst = RenUSubst(FormulaTools.conjuncts(substFml).map({
            case Equal(l, r) => (l, r)
            case Equiv(l, r) => (l, r)
            case s => throw new IllegalArgumentException("Expected substitution of the shape t=s or p<->q, but got " + s.prettyString)
          }))
          TactixLibrary.byUS(AxiomInfo(axiomName), (_: UnificationMatch.Subst) => subst)
      }): TypedFunc[Option[Formula], BelleExpr]): TypedFunc[String, _]),
    // @Tactic-ified
    InputTacticInfo("US"
      , RuleDisplayInfo(("US", "US"), (List(),List("S(P)")),
        List((List(), List("P"))))
      , List(SubstitutionArg("S"))
      , _ => ((subst: USubst) => TactixLibrary.uniformSubstitute(subst)): TypedFunc[USubst, BelleExpr]),

    // @Tactic-ified
    InputPositionTacticInfo("useLemmaAt"
      , "useLemmaAt"
      , List(StringArg("lemma"), StringArg("key"))
      , _ => ((lemmaName: String) => ((key: Option[String]) =>
        TactixLibrary.useLemmaAt(lemmaName, key.map(k => PosInExpr(k.split("\\.").map(Integer.parseInt).toList)))): TypedFunc[Option[String], BelleExpr]): TypedFunc[String, _]),

    InputPositionTacticInfo("cutAt" // @Tactic-ified
      , RuleDisplayInfo("cutAt",
        /* conclusion */ (List("&Gamma;"), List("C{c}", "&Delta;")),
        /* premises */   List((List("&Gamma;"),List("C{repl}", "&Delta;")),
          (List("&Gamma;"),List("&Delta;", "C{repl}→C{c}"))))
      , List(FormulaArg("repl"))
      , _ => ((fml: Formula) => TactixLibrary.cutAt(fml)): TypedFunc[Formula, BelleExpr]),
    // @Tactic-ified
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
    new PositionTacticInfo("splitWeakInequality", "splitWeakInequality", {case () => DifferentialTactics.splitWeakInequality}), //@Tactic-fied
    // @Tactic-ified
    new PositionTacticInfo("ODE",
      "Auto",
      {case () => TactixLibrary.ODE}, revealInternalSteps = true),
    // @Tactic-ified
    new PositionTacticInfo("odeInvC",
      "odeInvC",
      {case () => TactixLibrary.odeInvariantComplete}),
    // Not @Tactic-fied because deprecated.
    // new PositionTacticInfo("dgZeroMonomial",
    //  "dgZeroMonomial",
    //  {case () => DifferentialTactics.dgZeroMonomial}),
    // Not @Tactic-fied because deprecated.
    // new PositionTacticInfo("dgZeroPolynomial",
    //  "dgZeroPolynomial",
    //  {case () => DifferentialTactics.dgZeroPolynomial}),
    new PositionTacticInfo("dI", //@Tactic-fied
      RuleDisplayInfo("Differential Invariant",
        (List("&Gamma;"),List("[{x′ = f(x) & Q}]P","&Delta;")),
        /* premises */ List((List("&Gamma;", "Q"), List("P", "&Delta;"), true /*@todo auto for now, but shouldn't be once we can stop in the middle of dI*/),
          (List("Q"), List("[x′:=f(x)](P)′"), true /*@todo auto for now, but shouldn't be once we can stop in the middle of dI*/))),
      {case () => DifferentialTactics.diffInd(auto = 'cex)}, revealInternalSteps = true),
    new InputPositionTacticInfo("diffInvariant"  //@Tactic-fied
      , RuleDisplayInfo("Differential Cut + Differential Invariant"
        , (List("&Gamma;"),List("[{x′ = f(x) & Q}]P","&Delta;"))
        , /* premises */ List((List("&Gamma;"), List("[{x′ = f(x) & Q}]R", "&Delta;"), true),
          (List("&Gamma;"), List("[{x′ = f(x) & (Q∧R)}]P","&Delta;"))))
      , List(FormulaArg("R")) //@todo should be ListArg, before merge we already had concrete Bellerophon syntax for lists
      , _ => ((fml:Formula) => TactixLibrary.diffInvariant(fml)): TypedFunc[Formula, BelleExpr], revealInternalSteps = true),
    new PositionTacticInfo("solve", // @Tactic-ified
      RuleDisplayInfo("Solution",
        (List("&Gamma;"),List("[{x′ = f(x) & q(x)}]p(x)","&Delta;")),
        List((List("&Gamma;"), List("∀t≥0 ( (∀0≤s≤t q(sol(s))) → [x:=sol(t)]p(x) )")))),
      {case () => TactixLibrary.solve}, revealInternalSteps = true),
    new PositionTacticInfo("solveEnd", // @Tactic-ified
      RuleDisplayInfo("Solution",
        (List("&Gamma;"),List("[{x′ = f(x) & q(x)}]p(x)","&Delta;")),
        List((List("&Gamma;"), List("∀t≥0 ( q(sol(t)) → [x:=sol(t)]p(x) )")))),
      {case () => TactixLibrary.solveEnd}, revealInternalSteps = true),
    new PositionTacticInfo("DGauto",  //@Tactic-fied
      "DGauto",
      {case () => TactixLibrary.DGauto}),

    // DLBySubst
    //new InputPositionTacticInfo("I", "I", List(FormulaArg("invariant")), {case () => (fml:Formula) => TactixLibrary.loop(fml)}),

    new PositionTacticInfo("decomposeController","decomposeController",{case () => {HybridProgramTactics.decomposeController}}), // @Tactic-ified

    // numerical bound tactics
    // @Tactic-ified
    new TacticInfo("intervalArithmetic", "intervalArithmetic",  {case () => IntervalArithmeticV2.intervalArithmetic}),
    InputTacticInfo("intervalCutTerms", // @Tactic-ified (@TODO cutTerm vs cutTerms, which one is needed?)
      RuleDisplayInfo(("Interval Arithmetic Cut","intervalCutTerms"),
        (List("&Gamma;"),List("&Delta;")),
        /* premises */ List((List("&Gamma;"), List("a <= trm", "trm <= b"), true),
          (List("&Gamma;", "a <= trm", "trm <= b"), List("&Delta;"), false)))
      ,List(new TermArg("trm")), _ => ((t:Term) => IntervalArithmeticV2.intervalCutTerms(scala.collection.immutable.Seq(t))): TypedFunc[Term, BelleExpr]),
    PositionTacticInfo("intervalCut" // @Tactic-ified
      , RuleDisplayInfo(("Interval Arithmetic Cut", "intervalCut"),
        (List("&Gamma;"),List("&Delta;")),
        List((List("&Gamma;"), List("a <= trm", "trm <= b"), true), (List("&Gamma;", "a <= trm", "trm <= b"), List("&Delta;"), false))
      )
      , {case () => IntervalArithmeticV2.intervalCut}),
    new PositionTacticInfo("dCClosure", "dCClosure", {case () => DifferentialTactics.dCClosure(true)}), //@Tactic-fied

    // assertions and messages
    // @Tactic-ified
    InputTacticInfo("print"
      , SimpleDisplayInfo("Print","print")
      ,List(StringArg("msg")), _ => ((msg: String) => DebuggingTactics.printIndexed(msg)): TypedFunc[String, BelleExpr]),
    // @Tactic-ified
    InputPositionTacticInfo("assert"
      , SimpleDisplayInfo("Assert","assert")
      , List(new ExpressionArg("expected"), StringArg("msg"))
      , _ => ((expr: Expression) => ((msg: String) => DebuggingTactics.assertE(expr, msg)): TypedFunc[String, BelleExpr]): TypedFunc[Expression, TypedFunc[String, BelleExpr]]
    )*/
  )
  //</editor-fold>

  ////////////////////////////////////////////////////////
  // Assemble above derivation infos in [[allInfo]] registry
  ////////////////////////////////////////////////////////

  /** We need to force the right-hand side of every tactic definition to evaluate, which requires passing in arguments
    * to every "def" of a tactic. Subtly, it's ok for these arguments to be dummies, because we're not actually
    * interpreting the tactic on a Provable, just creating a BelleExpr without interpreting that BelleExpr */
  private def instantiateArg(ai: String): Any = {
    ai match {
      case "Number" | "Term" | "Expression" => Number(0)
      case "String" => ""
      case "Variable" => Variable("x")
      case "Formula" => True
      case "Generator" => FixedGenerator(Nil)
      case "SubstitutionPair"  =>  SubstitutionPair(Nothing, Nothing)
      case "PosInExpr" => PosInExpr()
      case "Option" => None
      case "List" => Nil
    }
  }

  /* Apply a reflected method with well-typed dummy arguments (for its side effects)*/
  private def applyMirror(m: ru.MethodMirror, argSyms: List[ru.Symbol]): Unit = {
    val args = argSyms.map((theSymbol: ru.Symbol) => theSymbol.info.typeConstructor.toString.split('.').last)
    args match {
      // If [[m]] is a tactic, determine and instantiate correct argument types
      case Nil => m()
      case _ =>
        val arguments = args.map(instantiateArg)
        m(arguments:_*)
    }
  }


  /* Initialize TacticInfo for all @Tactic annotations in given class [[cl]]*/
  private def initClass(cl: Class[_], tpe: ru.Type): Unit = {
    // @TODO: Reduce code duplication
    /* Collect fields and methods of class */
    val fields  = cl.getDeclaredFields.filter(f => classOf[BelleExpr].isAssignableFrom(f.getType))
    val methods = cl.getDeclaredMethods.filter(f => classOf[BelleExpr].isAssignableFrom(f.getReturnType))
    val mirror = ru.runtimeMirror(getClass.getClassLoader)
    // access the singleton object
    val moduleMirror = mirror.reflectModule(tpe.termSymbol.asModule)
    val im = mirror.reflect(moduleMirror.instance)

    /*  @Tactic and friends disappear during compilation, but they replace themselves with @InternalAnnotation
     *  which we use here to identify annotated fields, which must be executed in order to initialize TacticInfos*/
    //@note lazy vals have a "hidden" getter method that does the initialization
    val keptFields = fields.filter(fn => { tpe.member(ru.TermName(fn.getName)).alternatives.flatMap(_.annotations).exists(_.tree.tpe.typeSymbol.toString == "InternalAnnotation")})
    val fieldFields = keptFields.map(fn => (fn, tpe.member(ru.TermName(fn.getName)).asMethod.getter.asMethod))
    val methodFields: mutable.ArraySeq[(String, ru.MethodSymbol)] = methods.flatMap(fn => {
      val mem = tpe.member(ru.TermName(fn.getName))
      /* Overoaded values are considered terms (not methods), and have a list of alternatives, which might be annotated.
      * In this case, we are only interested in the alternative that was actually annotated, not the whole method*/
      if (mem.isTerm && mem.asTerm.isOverloaded) {
        mem.asTerm.alternatives.filter(_.annotations.exists(_.tree.tpe.typeSymbol.name.toString == "InternalAnnotation"))
          .map(c => (fn.getName, c.asMethod))
      } else if (mem.annotations.exists(_.tree.tpe.typeSymbol.name.toString == "InternalAnnotation")){
        mutable.ArraySeq((fn.getName, mem.asMethod))
      } else {
        mutable.ArraySeq()
      }})
    val fieldMirrors = fieldFields.map({case (x, y) => (x, im.reflectMethod(y))})
    val methodMirrors = methodFields.map({case (x, y) => (x, im.reflectMethod(y))})
    val failures = mutable.Buffer.empty[(String,Throwable)]
    methodMirrors.indices.foreach(idx => {
      try {
        val (fn, fm) = methodMirrors(idx)
        /* Type signature of function needed in order to generate well-typed arguments */
        val argSyms = fm.symbol.typeSignature.paramLists.headOption.getOrElse(Nil)
        // NB: allInfo gets updated automatically when touching each field/method
        applyMirror(fm, argSyms)
      } catch {
        case e: Throwable =>
          failures += (methodFields(idx)._1 -> e)
          logger.warn("WARNING: Failed to initialize @Tactic.", e)
      }
    })
    if (failures.nonEmpty)
      throw new Exception(s"WARNING: Encountered ${failures} method failures when trying to initialize @Tactic in ${cl.getName}. Unable to initialize:\n" + failures.map(_._1).mkString("\n"), failures.head._2)
    fieldMirrors.indices.foreach(idx => {
      try {
        val (fn, fm) = fieldMirrors(idx)
        val argSyms = tpe.member(ru.TermName(fn.getName)).asMethod.typeSignature.paramLists.headOption.getOrElse(Nil)
        applyMirror(fm, argSyms)
      } catch {
        case e: Throwable =>
          failures += (keptFields(idx).getName -> e)
          logger.warn("WARNING: Failed to initialize @Tactic.", e)
      }
    })
    if (failures.nonEmpty)
      throw new Exception(s"WARNING: Encountered ${failures} field failures when trying to initialize @Tactic in ${cl.getName}. Unable to initialize:\n" + failures.map(_._1).mkString("\n"), failures.head._2)
  }

  /* Has the global DerivationInfo list been initialized? */
  def isInit: Boolean = DerivationInfo._allInfo.nonEmpty
  /* Initialize global DerivationInfo list. This is surprisingly tricky because DerivationInfo is attached to tactic
  * (and axiom and rule) definitions, which are scattered throughout the prover. Here we maintain a global list of files
  * that can contain @Tactic definitions. Those classes are reflected and all annotated definitions are evaluated.
  * Having been modified by the @Tactic macro, those definitions all contain a function call which adds their TacticInfo
  * object to the global list. While this process does not require evaluating tactics in full, it does require loading
  * a number of classes, which triggers their static initializers and thus requires some attention to initialization order.
  *
  * Sanity checks ensure a runtime error is raised if @Tactic is used outside the allowed classes.
  * */
  def init(initLibrary: Boolean = true): Unit = {
    /* Initialization is relatively slow, so only initialize once*/
    if(isInit) return
    // Remember that initialization is in progress,
    DerivationInfo._initStatus = DerivationInfo.InitInProgress
    if(!initLibrary) // Advanced use - user takes over in-progress initialization
      return
    // Initialize derived axioms and rules, which automatically initializes their AxiomInfo and RuleInfo too
    Ax.prepopulateDerivedLemmaDatabase()
    /* Global list of library files which are permitted to use @Tactic. When adding new files to the tactics library,
    * it should suffice to update this list. */
    val objects: List[(Class[_], ru.Type)] = List(
      (Approximator.getClass, ru.typeOf[Approximator.type]),
      (ArithmeticSimplification.getClass, ru.typeOf[ArithmeticSimplification.type]),
      (ArithmeticSpeculativeSimplification.getClass, ru.typeOf[ArithmeticSpeculativeSimplification.type]),
      (ComponentSystem.getClass, ru.typeOf[ComponentSystem.type]),
      (DebuggingTactics.getClass, ru.typeOf[DebuggingTactics.type]),
      (Derive.getClass, ru.typeOf[Derive.type]),
      (DifferentialEquationCalculus.getClass, ru.typeOf[btactics.DifferentialEquationCalculus.type]),
      (DifferentialTactics.getClass, ru.typeOf[DifferentialTactics.type]),
      (DLBySubst.getClass, ru.typeOf[DLBySubst.type]),
      (EqualityTactics.getClass, ru.typeOf[EqualityTactics.type]),
      (FOQuantifierTactics.getClass, ru.typeOf[FOQuantifierTactics.type]),
      (HilbertCalculus.getClass, ru.typeOf[HilbertCalculus.type]),
      (HybridProgramTactics.getClass, ru.typeOf[HybridProgramTactics.type]),
      (IntervalArithmeticV2.getClass, ru.typeOf[IntervalArithmeticV2.type]),
      (ODEInvariance.getClass, ru.typeOf[ODEInvariance.type]),
      (ODELiveness.getClass, ru.typeOf[ODELiveness.type]),
      (PropositionalTactics.getClass, ru.typeOf[PropositionalTactics.type]),
      (ProofRuleTactics.getClass, ru.typeOf[ProofRuleTactics.type]),
      (SequentCalculus.getClass, ru.typeOf[SequentCalculus.type]),
      (SimplifierV3.getClass, ru.typeOf[SimplifierV3.type]),
      (TactixLibrary.getClass, ru.typeOf[TactixLibrary.type]),
      (ToolTactics.getClass, ru.typeOf[ToolTactics.type]),
      (Transitivity.getClass, ru.typeOf[Transitivity.type]),
      (UnifyUSCalculus.getClass, ru.typeOf[UnifyUSCalculus.type]),
      (ModelPlex.getClass, ru.typeOf[ModelPlex.type]),
      (SwitchedSystems.getClass, ru.typeOf[SwitchedSystems.type])
    )
    objects.foreach({case (cl, ct) => initClass(cl, ct)})
    /* Check that the list of annotated tactics we processed matches the list of named BelleExprs which have been
     * constructed so far. This can catch some named tactics that were never annotated, or catch some annotated files
     * that were forgotten in our list of files.
    */
    // NB: This check used to be an assertion in NamedTactic, but that doesn't work if a tactic is mentioned before registration.
    // Instead, check the names after everything is initialized.
    var overimplemented: Set[String] = Set()
    DerivationInfo._seenNames.foreach((n:String) => {
      if (n != "Error" && !DerivationInfo.hasCodeName(n) && !n.startsWith("_"))
        overimplemented = overimplemented + n
    })
    assert(overimplemented.isEmpty, s"@Tactic init failed: NamedBelleExpr(s) named ${overimplemented.toList.mkString(", ")} but this name does not appear in DerivationInfo's list of codeNames.")
    var unimplemented: Set[String] = Set()
    DerivationInfo._allInfo.foreach({case (name, di: DerivationInfo) => {
      if(!DerivationInfo._seenNames.contains(di.codeName)) {
        di match {
          // Axioms and rules are not tracked
          case _: CoreAxiomInfo | _: AxiomaticRuleInfo | _: DerivedAxiomInfo => ()
          case _ => unimplemented = unimplemented.+(di.codeName)
        }
      }
    }})
    assert(unimplemented.isEmpty, s"@Tactic init failed: Following DerivationInfo never implemented as @Tactic: " + unimplemented.toList.mkString(", "))
    DerivationInfo._initStatus = DerivationInfo.InitComplete
  }

  ////////////////////////////////////////////////////////
  // End of derivation infos in [[allInfo]] registry
  ////////////////////////////////////////////////////////

}


