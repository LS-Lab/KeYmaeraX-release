package edu.cmu.cs.ls.keymaera.tactics

import edu.cmu.cs.ls.keymaera.core.ExpressionTraversal.{TraverseToPosition, StopTraversal, ExpressionTraversalFunction}
import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.BranchLabels._
import edu.cmu.cs.ls.keymaera.tactics.EqualityRewritingImpl.equivRewriting
import edu.cmu.cs.ls.keymaera.tactics.FormulaConverter._
import edu.cmu.cs.ls.keymaera.tactics.PropositionalTacticsImpl._
import edu.cmu.cs.ls.keymaera.tactics.SearchTacticsImpl.{locateAnte, locateSucc, lastAnte, lastSucc, onBranch}
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.debugT
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.TacticHelper.getFormula
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.TacticHelper.getTerm
import AxiomaticRuleTactics.{boxCongruenceT,equivalenceCongruenceT,boxMonotoneT,diamondMonotoneT}
import ContextTactics.{cutInContext,cutImplyInContext}
import edu.cmu.cs.ls.keymaera.tactics.Tactics._

object AxiomTactic {
  /**
   * Axiom lookup imports an axiom into the antecedent.
   */
  def axiomT(id: String): Tactic = Axiom.axioms.get(id) match {
    case Some(_) => new Tactics.ApplyRule(Axiom(id)) {
      override def applicable(node: ProofNode): Boolean = true
    }
    case _ => throw new IllegalArgumentException("Unknown axiom " + id)
  }

  /**
   * Creates a new tactic that uses equivalence congruence or equation congruence or monotone to uncover an axiom inside
   * a context.
   * @param axiomName The name of the axiom.
   * @param axiomInstance The axiom instance that should be used in context (an equivalence or equality).
   * @param baseT The base tactic to show the axiom instance once uncovered.
   * @return The new tactic.
   */
  def uncoverAxiomT(axiomName: String,
                    axiomInstance: Formula => Formula,
                    baseT: Formula => PositionTactic): PositionTactic = new PositionTactic(axiomName) {
    override def applies(s: Sequent, p: Position): Boolean = axiomInstance(getFormula(s, p)) match {
      case Equiv(lhs, rhs) => getFormula(s, p) == lhs || getFormula(s, p) == rhs
      case Imply(lhs, rhs) => getFormula(s, p) == lhs || getFormula(s, p) == rhs
      case _ => false
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] =
        axiomInstance(getFormula(node.sequent, p)) match {
          case inst@Equiv(f, g) =>
            Some(cutInContext(inst, p) & onBranch(
              (cutShowLbl, lastSucc(cohideT) & equivalenceCongruenceT(p.inExpr) & lastSucc(baseT(getFormula(node.sequent, p)))),
              (cutUseLbl, equivRewriting(AntePosition(node.sequent.ante.length), p.topLevel))
            ))
          case inst@Imply(f, g) if p.isAnte =>
            Some(cutImplyInContext(inst, p) & onBranch(
              (cutShowLbl, lastSucc(cohideT) & lastSucc(ImplyRightT) & (boxMonotoneT | diamondMonotoneT | NilT) &
                assertT(1, 1) & lastAnte(assertPT(f, "Unexpected formula in ante")) & lastSucc(assertPT(g, "Unexpected formula in succ")) &
                cutT(Some(inst)) & onBranch(
                (cutShowLbl, lastSucc(cohideT) & lastSucc(baseT(getFormula(node.sequent, p)))),
                (cutUseLbl, lastAnte(ImplyLeftT) & AxiomCloseT)
              )),
              (cutUseLbl, lastAnte(ImplyLeftT) &&(
                AxiomCloseT,
                (assertPT(node.sequent(p), "hiding original instance") & hideT)(p.topLevel)))
            ))
          case inst@Imply(f, g) if !p.isAnte =>
            Some(cutImplyInContext(inst, p) & onBranch(
              (cutShowLbl, lastSucc(cohideT) & lastSucc(ImplyRightT) & (boxMonotoneT | diamondMonotoneT | NilT) &
                assertT(1, 1) & lastAnte(assertPT(f, "Unexpected formula in ante")) & lastSucc(assertPT(g, "Unexpected formula in succ")) &
                cutT(Some(inst)) & onBranch(
                (cutShowLbl, lastSucc(cohideT) & lastSucc(baseT(getFormula(node.sequent, p)))),
                (cutUseLbl, lastAnte(ImplyLeftT) & AxiomCloseT)
              )),
              (cutUseLbl, lastAnte(ImplyLeftT) &&(
                (assertPT(node.sequent(p), "hiding original instance") & hideT)(p.topLevel),
                AxiomCloseT)
                )
            ))
          case Equals(sort, lhs, rhs) => ???
        }
    }
  }

  def uncoverConditionalAxiomT(axiomName: String,
                               axiomInstance: Formula => Formula,
                               condT: Formula => PositionTactic,
                               baseT: Formula => PositionTactic): PositionTactic = new PositionTactic(axiomName) {
    // TODO generalize to non-toplevel positions
    override def applies(s: Sequent, p: Position): Boolean = p.isTopLevel && (axiomInstance(getFormula(s, p)) match {
        case Imply(_, Equiv (lhs, rhs)) => getFormula(s, p) == lhs || getFormula(s, p) == rhs
        case _ => false
    })

    override def apply(p: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = axiomInstance(getFormula(node.sequent, p)) match {
        case inst@Imply(cond, equiv@Equiv(lhs, rhs)) =>
          Some(cutT(Some(equiv))/*cutEquivInContext(equiv, p)*/ & onBranch(
            (cutShowLbl, hideT(p.topLevel) & /* only works because top-level */ cutT(Some(cond)) & onBranch(
              (cutShowLbl, /* hide second-to-last */ hideT(SuccPosition(node.sequent.succ.length - 1)) &
                lastSucc(condT(getFormula(node.sequent, p)))),
              (cutUseLbl, cutT(Some(inst)) & onBranch(
                (cutShowLbl, lastSucc(cohideT) & lastSucc(baseT(getFormula(node.sequent, p)))),
                (cutUseLbl, lastAnte(ImplyLeftT) & AxiomCloseT)
              ))
              )),
            (cutUseLbl, equivRewriting(AntePosition(node.sequent.ante.length), p.topLevel) & LabelBranch(cutUseLbl))
          ))
      }
    }
  }

  def uncoverConditionalTermAxiomT(axiomName: String,
                                   axiomInstance: Term => Formula,
                                   condT: Term => PositionTactic,
                                   baseT: Term => PositionTactic): PositionTactic = new PositionTactic(axiomName) {
    override def applies(s: Sequent, p: Position): Boolean = axiomInstance(getTerm(s, p)) match {
      case Imply(_, Equiv (lhs, rhs)) => s(p) == lhs || s(p) == rhs
      case _ => false
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = axiomInstance(getTerm(node.sequent, p)) match {
        case inst@Imply(cond, equiv@Equiv(lhs, rhs)) =>
          Some(cutT(Some(equiv))/*cutEquivInContext(equiv, p)*/ & onBranch(
            (cutShowLbl, hideT(p.topLevel) & /* only works because top-level */ cutT(Some(cond)) & onBranch(
              (cutShowLbl, /* hide second-to-last */ hideT(SuccPosition(node.sequent.succ.length - 1)) &
                lastSucc(condT(getTerm(node.sequent, p)))),
              (cutUseLbl, cutT(Some(inst)) & onBranch(
                (cutShowLbl, lastSucc(cohideT) & lastSucc(baseT(getTerm(node.sequent, p)))),
                (cutUseLbl, lastAnte(ImplyLeftT) & AxiomCloseT)
              ))
            )),
            (cutUseLbl, equivRewriting(AntePosition(node.sequent.ante.length), p.topLevel) & LabelBranch(cutUseLbl))
          ))
      }
    }
  }

  /**
   * Creates a new tactic to show an axiom by lookup.
   * @param axiomName The name of the axiom.
   * @param subst A function fml => subst to create the substitution from the current axiom form fml (an equivalence or equality).
   * @param alpha A function fml => alpha to create tactic for alpha renaming after substitution from the current axiom form fml.
   * @param axiomInstance A function (fml, axiom) => axiomInstance to generate the axiom instance from the axiom
   *                      form as in the axiom file and the current form fml as in the sequent.
   * @return The new tactic.
   */
  def axiomLookupBaseT(axiomName: String,
                       subst: Formula => List[SubstitutionPair],
                       alpha: Formula => PositionTactic,
                       axiomInstance: (Formula, Formula) => Formula): PositionTactic = new PositionTactic(axiomName) {
    override def applies(s: Sequent, p: Position): Boolean = getFormula(s, p) match {
      case Equiv(_, _) => true
      case Imply(_, _) => true
      case _ => false
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(name) {
      val axiom = Axiom.axioms.get(axiomName) match {
        case Some(ax) => ax
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        val fml = getFormula(node.sequent, p)
        Some(
          uniformSubstT(subst(fml), Map(fml -> axiomInstance(fml, axiom))) &
            assertT(0, 1) & lastSucc(assertPT(axiomInstance(fml, axiom), "Unexpected uniform substitution result")) &
            lastSucc(alpha(fml)) & AxiomTactic.axiomT(axiomName) &
            assertT(1, 1) & lastAnte(assertPT(axiom, "Unexpected axiom form in antecedent")) &
            lastSucc(assertPT(axiom, "Unexpected axiom form in succedent")) & AxiomCloseT
        )
      }
    }
  }
}
// axiom wrapper shell
// TODO: Use findPosInExpr to find a position that matches the left side of the axiom and cut in the resulting instance
// we start with just using findPos to get a top level position

/**
 * Base class for axiom tactics.
 * @param name The name of the tactic.
 * @param axiomName The name of the axiom.
 */
@deprecated("Use uncoverAxiomT, uncoverConditionalAxiomT and axiomLookupBaseT instead", since="")
abstract class AxiomTactic(name: String, axiomName: String) extends PositionTactic(name) {
  //@todo a java.lang.ExceptionInInitializerError is thrown
  require(Axiom.axioms != null, "the list of axioms should be defined.")
  require(Axiom.axioms.keySet.contains(axiomName), "The requested axiom should be in the set of axioms.") //@todo remove before production.
  val axiom = Axiom.axioms.get(axiomName)
  def applies(f: Formula): Boolean
  override def applies(s: Sequent, p: Position): Boolean = axiom.isDefined && applies(getFormula(s, p))

  /**
   * This methods constructs the axiom before the renaming, axiom instance, substitution to be performed and a tactic
   * that performs the renaming.
   *
   * An axiom tactic performs the following steps (Hilbert style):
   * 1. Guess axiom
   * 2. Rename bound variables to match the instance we want
   * 3. Perform Uniform substitution to instantiate the axiom
   *
   * Axioms usually have the form ax = OP(a, b). The constructed instance either has the form OP(f, g) or OP(g, f).
   * Here, f is an input to this function and g is derived from the axiom to be used. The output of this function
   * should be 4 things:
   * 1. The form of the axiom before apply the tactic provided in 4
   * 2. The instance of the axiom eventually to be used in the proof
   * 3. The substitution to turn 2 into 1
   * 4. A tactic to turn the result of 3 into the actual axiom (and/or the other way around)
   *
   * In the long run all this should be computed by unification.
   *
   * @param f the formula that should be rewritten using the axiom
   * @param ax the axiom to be used
   * @param pos the position to which this rule is applied to
   * @return (Axiom before executing the given position tactic;
   *         the instance of the axiom,
   *         the uniform substitution that transforms the first into the second axiom (Hilbert style);
   *         an optional position tactic that transforms the actual axiom into the first argument;
   *         an optional position tactic that transforms the first
   *         argument into the actual axiom (usually alpha renaming)).
   * @see #constructInstanceAndSubst(Formula)
   */
  def constructInstanceAndSubst(f: Formula, ax: Formula, pos: Position): Option[(Formula, Formula, List[SubstitutionPair],
      Option[PositionTactic], Option[PositionTactic])] =
    constructInstanceAndSubst(f, ax)

  def constructInstanceAndSubst(f: Formula, ax: Formula): Option[(Formula, Formula, List[SubstitutionPair],
      Option[PositionTactic], Option[PositionTactic])] = {
    constructInstanceAndSubst(f) match {
      case Some((instance, subst)) => Some((ax, instance, subst, None, None))
      case None => None
    }
  }

  /**
   * This is a simpler form of the constructInstanceAndSubst method. It just gets the formula to be rewritten
   * and has to construct the axiom instance and the substitution to transform the axiom into its instance.
   *
   * This method will be called by the default implementation of constructInstanceAndSubst(f: Formula, a: Formula).
   *
   * @param f The formula to be rewritten using an axiom
   * @return (The axiom instance to be constructed and used for rewriting;
   *          Substitution to transform the axiom into its instance)
   * @see #constructInstanceAndSubst(Formula,Formula)
   */
  def constructInstanceAndSubst(f: Formula): Option[(Formula, List[SubstitutionPair])] = ???

  //@TODO Add contract that applies()=>\result fine
  override def apply(pos: Position): Tactic = new ConstructionTactic(this.name) {
    override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)

    override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
      import EqualityRewritingImpl.equivRewriting
      import AxiomTactic.axiomT
      axiom match {
        case Some(ax) =>
          constructInstanceAndSubst(getFormula(node.sequent, pos), ax, pos) match {
            case Some((modAx, axiomInstance, subst, anteTac, succTac)) =>
              val axiomInstPos = AntePosition(node.sequent.ante.length)
              val axiomApplyTactic = assertPT(axiomInstance)(axiomInstPos) & (axiomInstance match {
                //@TODO Prefer simpler sequent proof rule for <->left rather than congruence rewriting if the position to use it on is on top-level of sequent
                //@TODO If Pos.isAnte the following position management seems wrong since unstable.
                case Equiv(_, _) => equivRewriting(axiomInstPos, pos) & LabelBranch(axiomUseLbl)
                case Imply(_, _) if pos.isAnte  && pos.inExpr == HereP => modusPonensT(pos, axiomInstPos)
                case Imply(_, _) if !pos.isAnte && pos.inExpr == HereP => ImplyLeftT(axiomInstPos) & ((assertPT(node.sequent(pos),"hiding original instance")&hideT)(pos) & LabelBranch(axiomUseLbl), AxiomCloseT(axiomInstPos.topLevel, pos) | LabelBranch(axiomShowLbl))
                case _ => ???
              })
              // // hide in reverse order since hiding changes positions
              // val hideAllAnte = for(i <- node.sequent.ante.length - 1 to 0 by -1) yield hideT(AntePosition(i))
              // // this will hide all the formulas in the current succedent (the only remaining one will be the one we cut in)
              // val hideAllSuccButLast = for(i <- node.sequent.succ.length - 1 to 0 by -1) yield hideT(SuccPosition(i))
              // val hideAllAnteAllSuccButLast = (hideAllAnte ++ hideAllSuccButLast).reduce(seqT)
              //@TODO Insert contract tactic after hiding all which checks that exactly the intended axiom formula remains and nothing else.
              //@TODO Introduce a reusable tactic that hides all formulas except the ones given as argument and is followed up by a contract ensuring that exactly those formuals remain.
              val anteCont = anteTac match {
                // SuccPosition(0) is the only position remaining in axiom proof
                case Some(tactic) => assertT(1, 1) & tactic(AntePosition(0))
                case None => NilT
              }
              val succCont = succTac match {
                // SuccPosition(0) is the only position remaining in axiom proof
                case Some(tactic) => assertT(0, 1) & tactic(SuccPosition(0))
                case None => NilT
              }
              val axiomPos = SuccPosition(node.sequent.succ.length)
              println("Axiom instance " + axiomInstance)
              val axiomInstanceTactic = (assertPT(axiomInstance) & cohideT)(axiomPos) & (assertT(0,1) &
                assertT(axiomInstance, SuccPosition(0)) & uniformSubstT(subst, Map(axiomInstance -> modAx)) &
                assertT(0, 1) & succCont & axiomT(axiomName) & assertT(1, 1) & anteCont &
                  (AxiomCloseT | TacticLibrary.debugT(s"${getClass.getCanonicalName}: axiom close expected") & stopT))
              Some(cutT(Some(axiomInstance)) & onBranch((cutUseLbl, axiomApplyTactic), (cutShowLbl, axiomInstanceTactic)))
            case None =>
              assert(applicable(node), "tactic signalled applicability, but returned None")
              None
          }
        case None => None
      }
    }
  }

}

/**
 * Base class for tactics that want to use some knowledge in context. Derived classes have to close the
 * "knowledge subclass continue" branch (e.g., by axiom lookup or propositional tactics).
 * @param name The name of the tactic.
 */
abstract class ContextualizeKnowledgeTactic(name: String) extends PositionTactic(name) {
  def applies(f: Formula): Boolean
  override def applies(s: Sequent, p: Position): Boolean =
    !p.isTopLevel && inContextOfModality(s, parentPosition(p)) && applies(getFormula(s, p))

  def parentPosition(p: Position) =
    if (p.isAnte) AntePosition(p.index, PosInExpr(p.inExpr.pos.init))
    else SuccPosition(p.index, PosInExpr(p.inExpr.pos.init))

  def inContextOfModality(s: Sequent, p: Position): Boolean = getFormula(s, p) match {
    case BoxModality(_, _) => true
    case _ => !p.isTopLevel && inContextOfModality(s, parentPosition(p))
  }

  /**
   * This method constructs the desired result before the renaming.
   *
   * @param f the formula that should be rewritten
   * @return Desired result before executing the renaming
   */
  def constructInstanceAndSubst(f: Formula): Option[(Formula, Option[Tactic])]

  //@TODO Add contract that applies()=>\result fine
  override def apply(pos: Position): Tactic = new ConstructionTactic(this.name) {
    override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)

    override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
      import TacticLibrary.cutT
      import scala.language.postfixOps
      constructInstanceAndSubst(getFormula(node.sequent, pos)) match {
        case Some((desiredResult, renameTactic)) =>
          val f = getFormula(node.sequent, pos)
          def fToPhi(phi: Formula) = new ExpressionTraversalFunction {
            override def preF(pos: PosInExpr, frm: Formula): Either[Option[StopTraversal], Formula] =
              if (frm == f) Right(phi) else Left(None)
          }
          def traverse(phi: Formula) = ExpressionTraversal.traverse(TraverseToPosition(pos.inExpr, fToPhi(phi)),
            getFormula(node.sequent, pos.topLevel)) match {
            case Some(frm) => frm
            case None => throw new IllegalArgumentException("Unable to replace formula")
          }
          val desiredResultInContext = traverse(desiredResult)
          val fInContext = getFormula(node.sequent, pos.topLevel)
          val congruenceAxiomInstance = Equiv(fInContext, desiredResultInContext)
          val axiomInstance = Equiv(f, desiredResult)

          val axiomInstPos = AntePosition(node.sequent.ante.length)

          val axiomApplyTactic = assertPT(congruenceAxiomInstance)(axiomInstPos) &
            EquivLeftT(axiomInstPos) & onBranch(
            (equivLeftLbl, AndLeftT(axiomInstPos) & AxiomCloseT),
            (equivRightLbl, hideT(pos.topLevel) & AndLeftT(axiomInstPos) & hideT(axiomInstPos) & NotLeftT(axiomInstPos))
            )

          val cont = renameTactic match {
            case Some(t) => assertT(0, 1) & t
            case None => NilT
          }

          val axiomPos = SuccPosition(node.sequent.succ.length)

          val axiomInstanceTactic =
            (assertPT(congruenceAxiomInstance, s"$getClass A.1") & cohideT)(axiomPos) & assertT(0,1) &
              (boxCongruenceT*) & assertT(0,1) & cutT(Some(axiomInstance)) & onBranch(
              (cutUseLbl, assertPT(axiomInstance, s"$getClass A.2")(AntePosition(0)) & (
                ((AxiomCloseT | locateAnte(Propositional) | locateSucc(Propositional))*) |
                debugT(s"$getClass: axiom close failed unexpectedly") & stopT)),
              (cutShowLbl, hideT(SuccPosition(0)) & cont & LabelBranch(BranchLabels.knowledgeSubclassContinue))
            )

          Some(cutT(Some(congruenceAxiomInstance)) & onBranch((cutUseLbl, axiomApplyTactic), (cutShowLbl, axiomInstanceTactic)))
        case None =>
          assert(applicable(node), "tactic signalled applicability, but returned None")
          None
      }
    }
  }

}

/**
 * Base class for derivative axiom in context tactics.
 * @param name The name of the tactic.
 * @param axiomName The name of the axiom.
 */
abstract class DerivativeAxiomInContextTactic(name: String, axiomName: String)
    extends ContextualizeKnowledgeTactic(name) {
  require(Axiom.axioms != null, "the list of axioms should be defined.")
  require(Axiom.axioms.keySet.contains(axiomName), "The requested axiom should be in the set of axioms.")
  override def applies(s: Sequent, p: Position) = Axiom.axioms.get(axiomName).isDefined && super.applies(s, p)

  override def constructInstanceAndSubst(f: Formula) = constructInstanceAndSubst(f, Axiom.axioms.get(axiomName).get)

  def constructInstanceAndSubst(f: Formula, axiom: Formula): Option[(Formula, Option[Tactic])] = None

  override def apply(pos: Position): Tactic = super.apply(pos) & new ConstructionTactic(this.name) {
    import scala.language.postfixOps

    override def applicable(node: ProofNode): Boolean = node.sequent(pos) match {
      case Equiv(_, _) => true
      case _ => false
    }

    override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
      import AxiomTactic.axiomT
      Some(onBranch("knowledge subclass continue", assertT(0, 1) & axiomT(axiomName) & assertT(1, 1) &
        (AxiomCloseT | TacticLibrary.debugT("Should never happen") & stopT)))
    }
  }
}

/**
 * Base class for propositional equivalences in context tactics.
 * @param name The name of the tactic.
 */
abstract class PropositionalInContextTactic(name: String)
    extends ContextualizeKnowledgeTactic(name) {
  override def applies(s: Sequent, p: Position): Boolean = {
    try {
      applies(getFormula(s, p))
    }
    catch {
      case _ => ???
    }
  }

  override def apply(pos: Position): Tactic = super.apply(pos) &
    onBranch("knowledge subclass continue", TacticLibrary.debugT("Running propositional.") & TacticLibrary.propositional)
}

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// End term axiom tactics.
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
