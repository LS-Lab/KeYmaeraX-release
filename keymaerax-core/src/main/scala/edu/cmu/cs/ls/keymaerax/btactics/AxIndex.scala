/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.Logging
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.PosInExpr
import edu.cmu.cs.ls.keymaerax.btactics.macros.{AxiomInfo, AxiomaticRuleInfo, CoreAxiomInfo, DerivationInfo, DerivedAxiomInfo, ProvableInfo}
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig

/**
  * Central Axiom Indexing data structures for canonical proof strategies, including
  * [[UnifyUSCalculus.chase]], [[UnifyUSCalculus.chaseFor()]]  and [[TactixLibrary.step]] and [[TactixLibrary.stepAt]].
  *
  * @note Could be generated automatically, yet better in a precomputation fashion, not on the fly.
  * @author Andre Platzer
  * @see Andre Platzer. [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 59(2), pp. 219-266, 2017.
  * @see [[edu.cmu.cs.ls.keymaerax.core.AxiomBase]]
  * @see [[edu.cmu.cs.ls.keymaerax.btactics.macros.AxiomInfo]]
  * @see [[edu.cmu.cs.ls.keymaerax.btactics.UnifyUSCalculus.chase()]]
  * @see [[edu.cmu.cs.ls.keymaerax.btactics.UnifyUSCalculus.chaseFor()]]
  * @see [[TactixLibrary.step]]
  * @see [[TactixLibrary.sequentStepIndex]]
 */
object AxIndex extends (Expression => List[DerivationInfo]) with Logging {

  /**
    * TODO: PURELY EXPERIMENTAL HACK. DO NOT MERGE.
    *
    * Map of (implicit) functions to the relevant differential axiom for their definition
    */
  val implFuncDiffs: scala.collection.mutable.Map[Function, List[(ProvableSig,PosInExpr, List[PosInExpr])]] =
    scala.collection.mutable.Map.empty

  /** lookup canonical axioms or tactics for an expression (index) */
  def apply(expr: Expression): List[DerivationInfo] = axiomsFor(expr)

  /**
    * AxiomIndex (key,recursor) where the key identifies the subformula used for matching and the recursors lists resulting siblings for subsequent chase.
    */
  type AxiomIndex = (PosInExpr, List[PosInExpr])

  import edu.cmu.cs.ls.keymaerax.btactics.macros.DerivationInfoAugmentors._
  /**
    * Return (derived) axiom index with key for matching and list of recursors on other sibling, i.e., for chasing after useAt/useFor.
    *
    * @see [[edu.cmu.cs.ls.keymaerax.btactics.UnifyUSCalculus.chase()]]
    * @see [[edu.cmu.cs.ls.keymaerax.btactics.UnifyUSCalculus.chaseFor()]]
    * @see [[AxiomInfo.theKey]]
    * @see [[AxiomInfo.theRecursor]]
    * @see [[edu.cmu.cs.ls.keymaerax.btactics.macros.Axiom]]
    * @todo copy documentation from chase
    */
  def axiomIndex(axiom: ProvableInfo): AxiomIndex = axiom match {
    case axiom: AxiomInfo => (axiom.key, axiom.recursor)
      //@todo improve if AxiomaticRuleInfo had recursor info we could keep chasing
    case _: AxiomaticRuleInfo => (PosInExpr.HereP, Nil)
  }


  /** Give the first canonical (derived) axiom or tactic that simplifies the expression `expr`.
    * @see [[axiomsFor()]] */
  def axiomFor(expr: Expression): Option[ProvableInfo] = axiomsFor(expr).headOption

  /** Return ordered list of all canonical (derived) axioms or tactics that simplify the expression `expr`.
    * @see [[axiomFor()]] */
  def axiomsFor(expr: Expression): List[ProvableInfo] = expr match{
    case term: Term => term match {
      case Differential(t) => t match {
        case _: Variable => Ax.DvarAxiom :: Ax.equalReflexive :: Nil // skip when Dvar fails in context with bound x'; recover after chase with DvariableTactic follow up
        case _: Number => Ax.Dconst :: Nil
        // optimizations
        case t: Term if StaticSemantics.freeVars(t).isEmpty => Ax.Dconst :: Nil
        case _: Neg => Ax.Dneg :: Nil
        case _: Plus => Ax.Dplus :: Nil
        case _: Minus => Ax.Dminus :: Nil
        // optimizations
        case Times(num, _) if StaticSemantics.freeVars(num).isEmpty => Ax.Dlinear :: Nil
        case Times(_, num) if StaticSemantics.freeVars(num).isEmpty => Ax.DlinearRight :: Nil
        case _: Times => Ax.Dtimes :: Nil
        case _: Divide => Ax.Dquotient :: Nil
        case _: Power => Ax.Dpower :: Nil
        case FuncOf(_, Nothing) => Ax.Dconst :: Nil
        case FuncOf(f,_) if f.interp.isDefined => ImplicitAx.getDiffAx(f).toList
        case _ => Nil
      }

      case Plus(Number(n), _) if n == 0 => Ax.zeroPlus :: Nil
      case Plus(_, Number(n)) if n == 0 => Ax.plusZero :: Nil
      case Times(Number(n), _) if n == 0 => Ax.zeroTimes :: Nil
      case Times(_, Number(n)) if n == 0 => Ax.timesZero :: Nil

      case _ => Nil
    }

    case formula: Formula => formula match {
      case DifferentialFormula(f) => f match {
        case _: And => Ax.Dand :: Nil
        case _: Or => Ax.Dor :: Nil
        case _: Imply => Ax.Dimply :: Nil
        case _: Equal => Ax.Dequal :: Nil
        case _: NotEqual => Ax.Dnotequal :: Nil
        case _: Greater => Ax.Dgreater :: Nil
        case _: GreaterEqual => Ax.Dgreaterequal :: Nil
        case _: Less => Ax.Dless :: Nil
        case _: LessEqual => Ax.Dlessequal :: Nil
        case _: Forall => Ax.Dforall :: Nil
        case _: Exists => Ax.Dexists :: Nil
        case _ => Nil
      }

      case Box(a, post) => a match {
        case _: Compose => Ax.composeb :: Nil
        case _: Choice => Ax.choiceb:: Nil
        //@todo "[:=] assign equality" does not automatically do the fresh renaming of "assignbTactic", which is not available forward, though.
        case Assign(_: BaseVariable, _) => Ax.assignbAxiom :: Ax.assignbeq :: Ax.assignbup :: Nil
        case Assign(_: DifferentialSymbol, _) => Ax.Dassignb :: Nil
        case _: AssignAny => Ax.randomb :: Nil
        case _: Test => Ax.testb :: Nil
        //@note Neither "loop" nor "[*] iterate" are automatic if invariant generator wrong and infinite unfolding useless.
//        case _: Loop => "loop" :: "[*] iterate" :: Nil
        //@note This misses the case where differential formulas are not top-level, but strategically that's okay. Also strategically, DW can wait until after DE.
        case ODESystem(ode, _) if post.isInstanceOf[DifferentialFormula] => ode match {
          case _: AtomicODE => Ax.DE :: Nil
          case _: DifferentialProduct => Ax.DEs :: Nil
          case _ => Nil
        }
        //@todo The following is a global search list unlike the others
        //@todo "diffSolve" should go first since the right thing to do for stepAt if solvable.
        case ODESystem(_, _) => Nil
          //@todo IDE type problem Ax.DWbase :: odeList
//        case ODESystem(ode, constraint) =>
//          /*@todo strategic "diffInvariant" would be better than diffInd since it does diffCut already ::*/
//          val tactics: List[String] = "diffSolve" :: "diffInd" :: Nil
//          if (constraint == True)
//            tactics ++ odeList
//          else
//            (tactics :+ "DW differential weakening") ++ odeList
        case _: Dual => Ax.dualDirectb :: Nil
        case _ => Nil
      }

      case Diamond(a, _) => a match {
        case _: Compose => Ax.composed :: Nil
        case _: Choice => Ax.choiced :: Nil
          //@todo optimizable the last two seem redundant
        case Assign(_: BaseVariable, _) => Ax.assigndAxiom :: Ax.assigndEqualityAll :: Ax.assigndEqualityAxiom :: Nil
        case Assign(_: DifferentialSymbol, _) => Ax.Dassignd :: Nil
        case _: AssignAny => Ax.randomd :: Nil
        case _: Test => Ax.testd :: Nil
        case _: Loop => Ax.iterated :: Nil
        case _: ODESystem => logger.warn("AxiomIndex for <ODE> still missing. Use tactic ODE"); Nil
        case _: Dual => Ax.dualDirectd :: Nil
        case _ => Nil
      }

      // push negations in
      case Not(f) => f match {
        case _: Not => Ax.doubleNegation :: Nil
        case _: And => Ax.notAnd :: Nil
        case _: Or => Ax.notOr :: Nil
        case _: Imply => Ax.notImply :: Nil
        case _: Equiv => Ax.notEquiv :: Nil
        case Box(_, Not(_)) => Ax.diamond :: Nil
        case _: Box => Ax.notBox :: Nil
        case Diamond(_, Not(_)) => Ax.box :: Nil
        case _: Diamond => Ax.notDiamond :: Nil
        case _: Forall => Ax.notAll :: Nil
        case _: Exists => Ax.notExists :: Nil
        case _: Equal => Ax.notEqual :: Nil
        case _: NotEqual => Ax.notNotEqual:: Nil
        case _: Less => Ax.notLess :: Nil
        case _: LessEqual => Ax.notLessEqual :: Nil
        case _: Greater => Ax.notGreater:: Nil
        case _: GreaterEqual => Ax.notGreaterEqual:: Nil
        case _ => Nil
      }

      case And(True, _) => Ax.trueAnd :: Nil
      case And(_, True) => Ax.andTrue :: Nil
      case And(False, _) => Ax.falseAnd :: Nil
      case And(_, False) => Ax.andFalse :: Nil
      case Imply(True, _) => Ax.trueImply :: Nil
      case Imply(_, True) => Ax.implyTrue :: Nil
        //@todo Or(True,_) as well as Or(False,_) should be added

      case _ => Nil
    }
    case _ => Nil
  }

  /** Descend into formulas and terms with stuttering. */
  def verboseAxiomsFor(expr: Expression): List[ProvableInfo] = axiomsFor(expr) match {
    case Nil => expr match {
      // chase inside formulas
      case Not(_) => Ax.notStutter :: Nil
      case And(_, _) => Ax.andStutter :: Nil
      case Or(_, _) => Ax.orStutter :: Nil
      case Imply(_, _) => Ax.implyStutter :: Nil
      case Equiv(_, _) => Ax.equivStutter :: Nil
      case Exists(_, _) => Ax.existsStutter :: Nil
      case Forall(_, _) => Ax.allStutter :: Nil
      //@todo chase into terms?
      case _ => Nil
    }
    case l => l
  }

  //@todo optimizable add "ODE" or replace others with "ODE"
  private val odeList: List[DerivationInfo] = Ax.DI ::
    //@note keeping the length of this list >=3 has the beneficial although weird side-effect that chase stops at box ODEs.
    // using the following axioms needs input so won't actually work but see above note.
    Ax.DC :: Ax.DGa ::
    Nil

}
