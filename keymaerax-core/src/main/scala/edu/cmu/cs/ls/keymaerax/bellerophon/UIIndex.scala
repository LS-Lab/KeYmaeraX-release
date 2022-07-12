/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.btactics.ImplicitAx
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.infrastruct.ExpressionTraversal.{ExpressionTraversalFunction, StopTraversal}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct._
import edu.cmu.cs.ls.keymaerax.btactics.macros.{DerivationInfo, OptionArg}
import org.slf4j.LoggerFactory

import scala.annotation.tailrec

/**
  * User-Interface Axiom/Tactic Index: Indexing data structure for all canonically applicable (derived) axioms/rules/tactics in User-Interface.
  * @author aplatzer
  * @see [[edu.cmu.cs.ls.keymaerax.btactics.AxIndex]]
  */
object UIIndex {
  private val logger = LoggerFactory.getLogger(UIIndex.getClass)

  /** Give the canonical (derived) axiom name or tactic names that simplifies the expression expr, optionally
    * considering that this expression occurs at the indicated position pos in the given sequent.
    * Disregard tactics that require input. */
  def theStepAt(expr: Expression, pos: Option[Position], sequent: Option[Sequent], substs: List[SubstitutionPair]): Option[DerivationInfo] = expr match {
    case Box(Loop(_), _) => None //@note: [*] iterate caused user confusion, so avoid left-click step on loops
    case Diamond(Loop(_), _) => None //@note: analogous to [*] iterate
    case _ => allStepsAt(expr, pos, sequent, substs).find(_.inputs.forall(_.isInstanceOf[OptionArg]))
  }

  /** Give the canonical (derived) axiom name or tactic names that apply at positions `pos1` and `pos2` in `sequent`.
    * Disregard tactics that require input. */
  def theStepAt(pos1: Position, pos2: Position, sequent: Sequent): Option[DerivationInfo] =
    allTwoPosSteps(pos1, pos2, sequent).find(_.inputs.forall(_.isInstanceOf[OptionArg]))

  /** Return ordered list of all canonical (derived) axiom names or tactic names that simplifies the expression expr, optionally considering that this expression occurs at the indicated position pos in the given sequent. */
  def allStepsAt(expr: Expression, pos: Option[Position], sequent: Option[Sequent],
                 substs: List[SubstitutionPair]): List[DerivationInfo] = autoPad(pos, sequent, {
    val isTop = pos.nonEmpty && pos.get.isTopLevel
    //@note the truth-value of isAnte/isSucc is nonsense if !isTop ....
    val isAnte = pos.nonEmpty && pos.get.isAnte
    val isSucc = pos.nonEmpty && pos.get.isSucc

    val alwaysApplicable = "chaseAt" :: Nil
    logger.debug("allStepsAt(" + expr + ") at " + pos + " which " + (if (isTop) "is top" else "is not top") + " and " + (if (isAnte) "is ante" else "is succ"))
    expr match {
      case Differential(t) =>
        val tactics =
          t match {
            case _: Variable => "DvariableTactic" :: alwaysApplicable
            case _: Number => "c()' derive constant fn" :: alwaysApplicable
            // optimizations
            case t: Term if StaticSemantics.freeVars(t).isEmpty => "c()' derive constant fn" :: alwaysApplicable
            case _: Neg => "-' derive neg" :: alwaysApplicable
            case _: Plus => "+' derive sum" :: alwaysApplicable
            case _: Minus => "-' derive minus" :: alwaysApplicable
            // optimizations
            case Times(num, _) if StaticSemantics.freeVars(num).isEmpty => "' linear" :: alwaysApplicable
            case Times(_, num) if StaticSemantics.freeVars(num).isEmpty => "' linear right" :: alwaysApplicable
            case _: Times => "*' derive product" :: alwaysApplicable
            case _: Divide => "/' derive quotient" :: alwaysApplicable
            case _: Power => "^' derive power" :: alwaysApplicable
            case FuncOf(_, Nothing) => "c()' derive constant fn" :: alwaysApplicable
            case FuncOf(f, _) if f.interpreted => {
              ImplicitAx.getDiffAx(f) match {
                case None => alwaysApplicable
                case Some(pf) => pf.canonicalName :: alwaysApplicable
              }
            }
            case _ => alwaysApplicable
          }
        "derive" :: tactics

      case DifferentialFormula(f) =>
        val tactics =
          f match {
            case _: Equal => "=' derive =" :: alwaysApplicable
            case _: NotEqual => "!=' derive !=" :: alwaysApplicable
            case _: Greater => ">' derive >" :: alwaysApplicable
            case _: GreaterEqual => ">=' derive >=" :: alwaysApplicable
            case _: Less => "<' derive <" :: alwaysApplicable
            case _: LessEqual => "<=' derive <=" :: alwaysApplicable
            case _: And => "&' derive and" :: alwaysApplicable
            case _: Or => "|' derive or" :: alwaysApplicable
            case _: Imply => "->' derive imply" :: alwaysApplicable
            case _: Forall => "forall' derive forall" :: alwaysApplicable
            case _: Exists => "exists' derive exists" :: alwaysApplicable
            case _ => alwaysApplicable
          }
        "derive" :: tactics
      case Box(a, True) if FormulaTools.dualFree(a) => "boxTrue" :: Nil

      case Box(a, post) =>
        val maybeSplit = post match {
          case _: And => "[] split" :: Nil
          case _ => Nil
        }
        def containsPrime(fml: Formula): Boolean = {
          var foundPrime = false
          ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
            override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = e match {
              case _: DifferentialFormula => foundPrime = true; Left(Some(ExpressionTraversal.stop))
              case _ => Left(None)
            }

            override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = e match {
              case _: DifferentialSymbol => foundPrime = true; Left(Some(ExpressionTraversal.stop))
              case _ => Left(None)
            }
          }, fml)
          foundPrime
        }
        val rules = maybeSplit ++  (if (isAnte) Nil else "GV" :: "MR" :: "chaseAt" :: Nil)
        a match {
          case Assign(_: DifferentialSymbol,_) => "[':=] differential assign" :: rules
          case Assign(_: BaseVariable, _) => "assignb" :: rules
          case _: AssignAny => "[:*] assign nondet" :: rules
          case _: Test => "[?] test" :: rules
          case _: Compose => "[;] compose" :: rules
          case _: Choice => "[++] choice" :: rules
          case _: Dual => "[d] dual direct" :: "[d] dual" :: Nil
          case _: Loop =>
            if (isTop && isSucc) "loop" +: (maybeSplit ++ ("[*] iterate" :: "GV" :: Nil))
            else maybeSplit ++ ("[*] iterate" :: Nil)
          //@note intermediate steps in dI
          case ODESystem(ode, _) if !post.isInstanceOf[Modal] && containsPrime(post) => ode match {
            case _: AtomicODE => "DE differential effect" :: "dW" :: "dC" :: (maybeSplit :+ "GV" :+ "MR")
            case _: DifferentialProduct => "DE differential effect (system)" :: "dW" :: "dC" :: (maybeSplit :+ "GV" :+ "MR")
            case _ => maybeSplit :+ "GV" :+ "MR"
          }
          case ODESystem(_, _) =>
            if (pos.forall(_.isSucc)) {
              if (pos.forall(_.isTopLevel)) ("ODE" :: "solve" :: "dC" :: "dIRule" ::  "dW" :: "dG" :: Nil) ++ (maybeSplit :+ "GV" :+ "MR")
              else ("solve" :: "dC" :: "dIRule" :: "dW" :: "dG" :: Nil) ++ (maybeSplit :+ "GV" :+ "MR")
            }
            else ("solve" :: "dC" :: Nil) ++ (maybeSplit :+ "GV" :+ "MR")
          case ProgramConst(name, _) if substs.exists({ case SubstitutionPair(ProgramConst(wn, _), _) => wn == name case _ => false }) =>
            s"""expand("$name")""" :: rules
          case SystemConst(name, _) if substs.exists({ case SubstitutionPair(SystemConst(wn, _), _) => wn == name case _ => false }) =>
            s"""expand("$name")""" :: rules
          case _ => rules
        }

      case Diamond(a, post) => 
        val maybeSplit = post match {case _ : Or => "<> split" :: Nil case _ => Nil }
        val rules = maybeSplit ++ alwaysApplicable
        a match {
          case Assign(_: DifferentialSymbol, _) => "<':=> differential assign" :: rules
          case Assign(_: BaseVariable, _) => "assignd" :: rules
          case _: AssignAny => "<:*> assign nondet" :: rules
          case _: Test => "<?> test" :: rules
          case _: Compose => "<;> compose" :: rules
          case _: Choice => "<++> choice" :: rules
          case _: Dual => "<d> dual direct" :: "<d> dual" :: rules
          case _: Loop => if (isTop) {
            if (isSucc)
              "con" +: maybeSplit :+ "<*> iterate"
            else
              "fp" +: maybeSplit :+ "<*> iterate"
          } else
            "<*> iterate" +: maybeSplit
          case ODESystem(_, _) =>
            if (pos.forall(_.isSucc)) {
              if (pos.forall(_.isTopLevel)) ("dV" :: "solve" :: "kDomainDiamond" :: "dDR" :: "compatCut":: "gEx" :: Nil)
              else ("solve" :: "compatCut" :: Nil) //todo
            } else ("solve" :: "compatCut" :: Nil) //todo
          case ProgramConst(name, _) if substs.exists({ case SubstitutionPair(ProgramConst(wn, _), _) => wn == name case _ => false }) =>
            s"""expand("$name")""" :: rules
          case _ => rules
        }

      case Not(f) =>
        val alwaysApplicableAtNot =
          if (isTop && isAnte) "notL" :: alwaysApplicable
          else if (isTop && !isAnte) "notR" :: alwaysApplicable
          else alwaysApplicable
        f match {
          case Box(_, Not(_)) => "<> diamond" :: alwaysApplicableAtNot
          case _: Box => "![]" :: alwaysApplicableAtNot
          case Diamond(_, Not(_)) => "[] box" :: alwaysApplicableAtNot
          case _: Diamond => "!<>" :: alwaysApplicableAtNot
          case _: Forall => "!all" :: alwaysApplicableAtNot
          case _: Exists => "!exists" :: alwaysApplicableAtNot
          case _: Equal => "! =" :: alwaysApplicableAtNot
          case _: NotEqual => "! !=" :: alwaysApplicableAtNot
          case _: Less => "! <" :: alwaysApplicableAtNot
          case _: LessEqual => "! <=" :: alwaysApplicableAtNot
          case _: Greater => "! >" :: alwaysApplicableAtNot
          case _: GreaterEqual => "! >=" :: alwaysApplicableAtNot
          case _: Not => "!! double negation" :: alwaysApplicableAtNot
          case _: And => "!& deMorgan" :: alwaysApplicableAtNot
          case _: Or => "!| deMorgan" :: alwaysApplicableAtNot
          case _: Imply => "!-> deMorgan" :: alwaysApplicableAtNot
          case _: Equiv => "!<-> deMorgan" :: alwaysApplicableAtNot
          case _ => alwaysApplicableAtNot
        }

      case _ =>
        // Check for axioms vs. rules separately because sometimes we might want to apply these axioms when we don't
        // have positions available (which we need to check rule applicability
        val axioms =
          expr match {
            case And(True, _) => "true&" :: Nil
            case And(_, True) => "&true" :: Nil
            case Imply(True, _) => "true->" :: Nil
            case Imply(_, True) => "->true" :: Nil
              //@todo add true|, false&, and similar as new DerivedAxioms
            case _ => Nil
          }
        if (!isTop) axioms
        else {
          // Check for expansions
          val sig = StaticSemantics.signature(expr)
          sig.toList.flatMap( s => s match {
            case fn: Function if substs.exists({
              case SubstitutionPair(FuncOf(wfn, _), _) => wfn == fn
              case SubstitutionPair(PredOf(wfn, _), _) => wfn == fn
              case _ => false }) =>
              Some(s"""expand("${fn.prettyString}")""")
            //case (PredOf(fn, _)) if substs.exists({ case SubstitutionPair(PredOf(wfn, _), _) => wfn == fn case _ => false }) =>
            //  Some(s"""expand("${fn.prettyString}")""")
            case _ => None
          }
          ) ++
          ((expr, isAnte) match {
            case (True, false) => "closeTrue" :: alwaysApplicable
            case (False, true) => "closeFalse" :: alwaysApplicable
            case (_: Not, true) => "notL" :: alwaysApplicable
            case (_: Not, false) => "notR" :: alwaysApplicable
            case (_: And, true) => axioms ++ ("andL" :: alwaysApplicable)
            case (_: And, false) => axioms ++ ("andR" :: alwaysApplicable)
            case (_: Or, true) => "orL" :: alwaysApplicable
            case (_: Or, false) => "orR" :: alwaysApplicable
            case (_: Imply, true) => axioms ++ ("implyL" :: alwaysApplicable)
            case (_: Imply, false) => axioms ++ ("implyR" :: alwaysApplicable)
            case (_: Equiv, true) => "equivL" :: alwaysApplicable
            case (_: Equiv, false) => "equivR" :: alwaysApplicable
            case (_: Forall, true) => "allL" :: "allLkeep" :: "allLmon" :: alwaysApplicable
            case (_: Forall, false) => "allR" :: alwaysApplicable
            case (_: Exists, true) => "existsL" :: alwaysApplicable
            case (_: Exists, false) => "existsR" :: "existsRmon" :: alwaysApplicable
            case (_: Equal, true) => "allL2R" :: "allR2L" :: "= commute" :: "alphaRenAllBy" :: alwaysApplicable
            // Suggest diffUnfolding for atomic comparisons if there is an interpreted function
            case (f:ComparisonFormula,false) =>
              if(StaticSemantics.signature(f).exists( e => e match {
                case ee: Function => ee.interpreted
              })) "diffUnfold" :: alwaysApplicable
              else alwaysApplicable
            case _ => alwaysApplicable
          })
        }
    }
  }).map(DerivationInfo(_))

  def allTwoPosSteps(pos1: Position, pos2: Position, sequent: Sequent): List[DerivationInfo] = {
    val expr1 = sequent.sub(pos1)
    val expr2 = sequent.sub(pos2)
    ((pos1, pos2, expr1, expr2) match {
      case (p1: AntePosition, p2: SuccPosition, Some(e1), Some(e2)) if p1.isTopLevel &&  p2.isTopLevel && e1 == e2 => "closeId" :: Nil
      case (p1: AntePosition, p2: SuccPosition, Some(e1), Some(e2)) if p1.isTopLevel && !p2.isTopLevel && e1 == e2 => /*@todo "knownR" ::*/ Nil
      case (_, _, Some(Equal(_, _)), _) => "L2R" :: Nil
      case (_: AntePosition, _, Some(fa: Forall), Some(_:Formula)) if bodyIsEquiv(fa) => "equivRewriting" :: Nil
      case (_: AntePosition, _, Some(_: Equiv), Some(_: Formula)) => "instantiatedEquivRewriting" :: Nil //@note for applying function definitions.
      case (_, _: AntePosition, Some(_: Term), Some(_: Forall)) => /*@todo "all instantiate pos" ::*/ Nil
      case (_, _: SuccPosition, Some(_: Term), Some(_: Exists)) => /*@todo "exists instantiate pos" ::*/ Nil
      case _ => Nil
      //@todo more drag-and-drop support
    }).map(DerivationInfo(_))
  }

  @tailrec
  private def bodyIsEquiv(x: Forall): Boolean = x.child match {
    case Forall(_, child:Forall) => bodyIsEquiv(child)
    case Equiv(_,_) => true
    case _ => false
  }

  def comfortOf(stepName: String): Option[DerivationInfo] = stepName match {
    //case "diffCut" => Some("diffInvariant")
    //case "diffInd" => Some("autoDiffInd")
    //case "diffSolve" => Some("autoDiffSolve")
    case _ => None
  }

  private def autoPad(pos: Option[Position], sequent: Option[Sequent], axioms: List[String]): List[String] = {
    //@note don't augment with hide since UI has a special button for it already.
    //@note don't augment with cutL+cutR since too cluttered.
    //    if (!axioms.isEmpty && pos.isDefined && pos.get.isTopLevel)
    //      axioms ++ (if (pos.get.isAnte) "hideL" :: /*"cutL" ::*/ Nil else "hideR" :: /*"cutR" ::*/ Nil)
    //    else
    logger.debug("allStepsAt=" + axioms)
    axioms
  }
}
