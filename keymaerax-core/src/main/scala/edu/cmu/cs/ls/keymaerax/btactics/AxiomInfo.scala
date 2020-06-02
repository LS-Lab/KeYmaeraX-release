/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.macros._
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
import scala.reflect.macros
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




////////////////////////////////////////////////////////////
// Central registry of all derivation steps
////////////////////////////////////////////////////////////



/**
  * Central list of all derivation steps (axioms, derived axioms, proof rules, tactics)
  * with meta information of relevant names and display names and visualizations for the user interface.
  */
object DerivationInfoRegistry {
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
      // @TODO: Generalize
      case (ListArg(n, "formula", a), fmls) if fmls.forall(_.kind == FormulaKind) =>
        val res = fmls.map(e => convert(FormulaArg(n, a), List(e)))
        res.find({case _: Left[Any, String] => false case _: Right[Any, String] => true}) match {
          case Some(Right(err)) => Right(err)
          case None => Left(res.map({case Left(v) => v}))
        }
      case _ => Right("Expected: " + arg.sort + ", found: " + exprs.map(_.kind).mkString(",") + " " + exprs.map(_.prettyString).mkString(","))
    }
  }

  //@todo
  private val needsCodeName = "TODOTHISAXIOMSTILLNEEDSACODENAME"
  /** Unsure whether linear matcher suffices so default to false */
  //@todo avoid the use of unsure
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
      case _: DerivedAxiomInfo => true //@todo can't ask DerivedAxioms.derivedAxiom yet since still initializing, besides that'd be circular
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

  /** Alphanumeric letter or digit parts of a name, skipping all other characters or spaces. */
  private def canonicalize(name: String): String = name.filter(c => c.isLetterOrDigit)

  /** Convert axiomatic proof rules to derivation infos. */
  private def convertAxiomaticRules(rules: Map[String,ProvableSig]): List[AxiomaticRuleInfo] =
  //@todo display info is rather impoverished
    rules.keys.map(name =>
      AxiomaticRuleInfo(name, SimpleDisplayInfo(name, name), canonicalize(name),
      {case () => TactixLibrary.by(ProvableSig.rules(name), name)})).toList

  ////////////////////////////////////////////////////////
  // Structure registry [[allInfo]] as modalities, ODEs, differentials, quantifiers, misc, derived axioms, sequent rules.
  ////////////////////////////////////////////////////////

  //<editor-fold desc="modalities">

  /** Modality cases of [[allInfo]] */
  private[this] val modalityInfos: List[DerivationInfo] = List(
    // [a] modalities and <a> modalities
    PositionTacticInfo("diamondd"
      , AxiomDisplayInfo(("<·>d", "<.>d"), "<span class=\"k4-axiom-key\">&langle;a&rangle;P</span> ↔ &not;[a]&not;P")
      , {case () => HilbertCalculus.useAt(Ax.diamond, PosInExpr(1::Nil))}),
    PositionTacticInfo("boxd"
      , AxiomDisplayInfo(("[·]d", "[.]d"), "<span class=\"k4-axiom-key\">[a]P</span> ↔ &not;&langle;a&rangle;&not;P")
      , {case () => HilbertCalculus.useAt(Ax.box, PosInExpr(1::Nil))}),
    new PositionTacticInfo("assignb"
      , AxiomDisplayInfo("[:=]", "<span class=\"k4-axiom-key\">[x:=e]p(x)</span>↔p(e)")
      , {case () => TactixLibrary.assignb}, revealInternalSteps = true),
    new PositionTacticInfo("assignd", AxiomDisplayInfo("<:=>", "<span class=\"k4-axiom-key\">&langle;x:=e&rangle;p(x)</span>↔p(e)"), {case () => HilbertCalculus.assignd}),
    new PositionTacticInfo("assignEquality", "[:=]=", {case () => DLBySubst.assignEquality}, revealInternalSteps = true),
    new InputPositionTacticInfo("assignbExistsRule",
      RuleDisplayInfo(
        "[:=] assign exists",
        /* conclusion */ (List("&Gamma;"), List("∃t [x:=t;]P", "&Delta;")),
        /* premises */ List( (List("&Gamma;"), List("[t:=e;][x:=t;]P", "&Delta;")) )
      ),
      List(new TermArg("e")),
      _ => ((e: Term) => DLBySubst.assignbExists(e)): TypedFunc[Term, BelleExpr]
    ),
  )
  //</editor-fold>

  //<editor-fold desc="ODEs">
  /** Differential equation cases of [[allInfo]] */
  private[this] lazy val odeInfos: List[DerivationInfo] = List(
    /*new CoreAxiomInfo("DW base", "DWbase", "DWbase", 'linear, {case () => HilbertCalculus.DW}),*/
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
    {
      // @TODO: Is converter necessary?
      val converter = (e: Expression) => e match {
        case n: Number => Left(n)
        case _ => Right("Expected a number but got " + e.prettyString)
      }
      InputPositionTacticInfo("autoApproximate",
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
      InputPositionTacticInfo("expApproximate",
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
      InputPositionTacticInfo("circularApproximate",
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
      List(OptionArg(new TermArg("g"))),
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
    )
  )
  //</editor-fold>

  //<editor-fold desc="Differentials">
  /** Differential cases of [[allInfo]] */
  private[this] lazy val differentialInfos: List[DerivationInfo] = List(
    new PositionTacticInfo("Dvariable"
      ,  AxiomDisplayInfo(("x′","x'"), "<span class=\"k4-axiom-key\">(x)′</span>=x′")
      , {case () => DifferentialTactics.Dvariable}),
    PositionTacticInfo("derive", "()'", {case () => HilbertCalculus.derive} , revealInternalSteps = false /* uninformative as forward proof */)
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
  private[this] lazy val sequentCalculusInfos: List[DerivationInfo] = List(
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
    new InputPositionTacticInfo("allL"
      , RuleDisplayInfo(("∀L", "allL"), (List("&Gamma;","∀x P(x)"), List("&Delta;")),
        List((List("&Gamma;", "P(θ)"),List("&Delta;"))))
      , List(new TermArg("θ", "θ"::Nil))
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
      ,List(new TermArg("theta"),VariableArg("freshVar", "freshVar"::Nil)), _ => ((t:Term) => ((v: Option[Variable]) => EqualityTactics.abbrv(t, v)): TypedFunc[Option[Variable], BelleExpr]): TypedFunc[Term, _]),
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
      List(new ExpressionArg("Q")),
      _ => ((expr:Expression) => TactixLibrary.transform(expr)): TypedFunc[Expression, BelleExpr]),
    new InputPositionTacticInfo("edit", "edit", List(new ExpressionArg("to")),
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
      new TermArg("gt") :: VariableArg("gv", "gv"::Nil) :: Nil,
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
      List(OptionArg(StringArg("tool")), OptionArg(new TermArg("timeout"))),
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
        case None => TactixLibrary.byUS(AxiomInfo(axiomName), us=>us)
        case Some(substFml: Formula) =>
          val subst = RenUSubst(FormulaTools.conjuncts(substFml).map({
            case Equal(l, r) => (l, r)
            case Equiv(l, r) => (l, r)
            case s => throw new IllegalArgumentException("Expected substitution of the shape t=s or p<->q, but got " + s.prettyString)
          }))
          //@todo
          TactixLibrary.byUS(AxiomInfo(axiomName), (_: UnificationMatch.Subst) => subst)
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
      , "allGeneralize", {case () => HilbertCalculus.useAt(Ax.allGeneralize)}),
    new DerivedRuleInfo("[] monotone"
      , RuleDisplayInfo(SimpleDisplayInfo("[] monotone", "[]monotone"), SequentDisplay("[a;]P"::Nil, "[a;]Q"::Nil), SequentDisplay("P"::Nil, "Q"::Nil)::Nil)
      , "monb", {case () => HilbertCalculus.useAt(Ax.monb)}),
    new DerivedRuleInfo("[] monotone 2"
      , RuleDisplayInfo(SimpleDisplayInfo("[] monotone 2", "[]monotone 2"), SequentDisplay("[a;]Q"::Nil, "[a;]P"::Nil), SequentDisplay("Q"::Nil, "P"::Nil)::Nil)
      , "monb2", {case () => HilbertCalculus.useAt(Ax.monb2)}),
    new DerivedRuleInfo("Goedel"
      , RuleDisplayInfo(SimpleDisplayInfo("G", "G"), SequentDisplay(Nil, "[a;]P"::Nil), SequentDisplay(Nil, "P"::Nil)::Nil)
      , "Goedel", {case () => HilbertCalculus.useAt(Ax.Goedel)}),
    new DerivedRuleInfo("CT term congruence"
      , RuleDisplayInfo(SimpleDisplayInfo("CT term congruence", "CTtermCongruence"), SequentDisplay(Nil, "ctx_(f_(||)) = ctx_(g_(||))"::Nil), SequentDisplay(Nil, "f_(||) = g_(||)"::Nil)::Nil)
      , "CTtermCongruence", {case () => HilbertCalculus.useAt(Ax.CTtermCongruence)}),
    new DerivedRuleInfo("con convergence flat"
      , RuleDisplayInfo(SimpleDisplayInfo("con flat", "conflat"), SequentDisplay("J"::Nil, "<a*>P"::Nil), SequentDisplay("\\exists v (v<=0&J)"::Nil, "P"::Nil)::SequentDisplay("v > 0"::"J"::Nil ,"<a>J(v-1)"::Nil)::Nil)
      , "conflat", {case () => HilbertCalculus.useAt(Ax.conflat)}),

    // numerical bound tactics
    new TacticInfo("intervalArithmetic", "intervalArithmetic",  {case () => IntervalArithmeticV2.intervalArithmetic}, needsTool = true),
    InputTacticInfo("intervalCutTerms",
      RuleDisplayInfo(("Interval Arithmetic Cut","intervalCutTerms"),
        (List("&Gamma;"),List("&Delta;")),
        /* premises */ List((List("&Gamma;"), List("a <= trm", "trm <= b"), true),
          (List("&Gamma;", "a <= trm", "trm <= b"), List("&Delta;"), false)))
      ,List(new TermArg("trm")), _ => ((t:Term) => IntervalArithmeticV2.intervalCutTerms(t)): TypedFunc[Term, BelleExpr]),
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
      , List(new ExpressionArg("expected"), StringArg("msg"))
      , _ => ((expr: Expression) => ((msg: String) => DebuggingTactics.assertE(expr, msg)): TypedFunc[String, BelleExpr]): TypedFunc[Expression, TypedFunc[String, BelleExpr]]
    )
  )
  //</editor-fold>

  ////////////////////////////////////////////////////////
  // Assemble above derivation infos in [[allInfo]] registry
  ////////////////////////////////////////////////////////

  /**
    * Central registry for axiom, derived axiom, proof rule, and tactic meta-information.
    * Transferred into subsequent maps etc for efficiency reasons.
    */
  var allInfo: List[DerivationInfo] = (convertAxiomaticRules(ProvableSig.rules) ++ modalityInfos ++ odeInfos ++
    differentialInfos ++ foInfos ++ miscInfos ++ derivedAxiomsInfos ++ sequentCalculusInfos) ensures (
    consistentInfo _, "meta-information on AxiomInfo is consistent with actual (derived) axioms etc.")

  def init: Unit = {
    if(DerivationInfo._allInfo.isEmpty)
      DerivationInfo._allInfo = DerivationInfo._allInfo ++ allInfo
  }

  ////////////////////////////////////////////////////////
  // End of derivation infos in [[allInfo]] registry
  ////////////////////////////////////////////////////////

}


