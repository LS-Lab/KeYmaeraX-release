/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.tactics

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tactics.AxiomTactic._
import edu.cmu.cs.ls.keymaerax.tactics.BranchLabels._
import edu.cmu.cs.ls.keymaerax.tactics.ExpressionTraversal.ExpressionTraversalFunction
import edu.cmu.cs.ls.keymaerax.tactics.FOQuantifierTacticsImpl._
import edu.cmu.cs.ls.keymaerax.tactics.SearchTacticsImpl._
import edu.cmu.cs.ls.keymaerax.tactics.SyntacticDerivationInContext.ApplicableAtFormula
import edu.cmu.cs.ls.keymaerax.tactics.TacticLibrary.AxiomCloseT
import edu.cmu.cs.ls.keymaerax.tactics.TacticLibrary.TacticHelper._
import edu.cmu.cs.ls.keymaerax.tactics.TacticLibrary.skolemizeT
import edu.cmu.cs.ls.keymaerax.tactics.Tactics._
import edu.cmu.cs.ls.keymaerax.tools.Tool
import TacticLibrary._
import edu.cmu.cs.ls.keymaerax.tactics.PropositionalTacticsImpl.{InverseImplyRightT, kModalModusPonensT}
import edu.cmu.cs.ls.keymaerax.tactics.AxiomaticRuleTactics.boxMonotoneT

import scala.collection.immutable.List

/**
 * Solves simple ODEs.
 * @author Nathan Fulton
 */
object LogicalODESolver {
  def debugger(s : String) = debugT("[Logical ODE Solver] " + s)

  def solveT : PositionTactic = new PositionTactic("Solve ODE") {
    override def applies(s: Sequent, p: Position): Boolean = true //@todo

    val loggingPrefix = "[LODESolver Top Level] "

    /**
     * Solves a differential equation and returns something like \forall t ...
     * @todo Introduces a time variable and symbolic = initial conditions for primed variables, if they are not already present.
     * @note I think this is no longer true: renameAndDropImpl still produces an open goal that needs to be closed, maybe with monotonicity?
     */
    override def apply(p: Position): Tactic =
      LogicalODESolver.setupTimeVarT(p) ~ //may fail b/c time might already exist.
      (cutInSolnsT(p) *) &
      verboseDebugT(s"$loggingPrefix Finished Cutting In Solutions") &
      cutTimeLB(p) &
      verboseDebugT(s"$loggingPrefix Finished cutting in time") &
      ODETactics.diffWeakenAxiomT(p) & //the axiom, not the proof rule.
      verboseDebugT(s"$loggingPrefix Finished diff weaken axiom") &
      renameAndDropImpl(p) &
      verboseDebugT(s"$loggingPrefix Finished renameAndDropImpl step") &
      (successiveInverseCut(p) *) &
      verboseDebugT(s"$loggingPrefix Finished successive inverse diff cuts") &
      (successiveInverseDiffGhost(p) *) &
      verboseDebugT(s"$loggingPrefix Finished successive inverse diff ghosts") &
      ODETactics.diffSolveConstraintT(p) &
      verboseDebugT(s"$loggingPrefix Finished DS& application at t' = 1 (hopefully)")
  }

  /**
   * Reduces the output of solveT to arithmetic and tries to close.
   */
  def solveAndProve(p: Position): Tactic = solveT(p) & reduceToArithmetic(p)

  /**
   * These final steps of the LogicalODESolver should always just work,
   * and have been separated out so that they can be more easily executed
   * from test cases.
   */
  def reduceToArithmetic(p : Position) : Tactic =
    FOQuantifierTacticsImpl.skolemizeT(p) &
    ImplyRightT(p) & ImplyRightT(p) & debugT("After imply right") &
    HybridProgramTacticsImpl.boxAssignT(p) &
    arithmeticT

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // tactics for the advanced solver
  // The advanced solver is the <strike>same as the</strike> nothing like the simple solver.
  // Instead of diffWeaken it does successive inverse ghosts and inverse cuts until finally only
  // time remains, and then solves just for t' = 0*t + 1. This allows the selection of only specific
  // points in time.
  //////////////////////////////////////////////////////////////////////////////////////////////////

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Successive inverse diff ghosts
  //////////////////////////////////////////////////////////////////////////////////////////////////
  def successiveInverseDiffGhost : PositionTactic =
  new PositionTactic("[LODE Solver] successiveInverseDiffGhost") {
    override def applies(s: Sequent, p: Position): Boolean = TacticHelper.getFormula(s, p) match {
      case Box(ODESystem(program : DifferentialProgram, _), _) => {
        val t = timeVar(program)
        val primedVars = getPrimedVariables(program)
        primedVars.length > 1 && // When primedVars = 1 we should move to solving for time.
        t.isDefined && // We need a time variable b/c it must be moved from the head to the tail (?)
        t.get.equals(primedVars.last) && // time var needs to be in the back because DG++ system peels off from the back.
        s.succ.length == 1 // Cleaning up after this tactic requires knowing the structure of the succedent.
      }
      case _ => false
    }

    override def apply(p: Position): Tactic = new ConstructionTactic("construct " + name) {
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        val atApplicationPos = TacticHelper.getFormula(node.sequent, p)

        atApplicationPos match {
          case Box(ODESystem(program : DifferentialProgram, _), _) => {
            val pvs = getPrimedVariables(program)
            val nextVariable : Variable = pvs.head
            val cutUsePos = AntePos(node.sequent.ante.length)

            // ghostTactic chooses the correct diffGhost++ tactic based up whether this is a system w/
            // 3 or more primed variables.
            val (ghostTactic, usingSystemAxiom) =
              if(pvs.length > 2)  (ODETactics.DiffGhostPlusPlusSystemT, true)
              else                (ODETactics.DiffGhostPPT, false)

            Some(
              debugT(s"[successiveInverseDiffGhost] begin (system axiom used: ${usingSystemAxiom})") &
              PropositionalTacticsImpl.cutT(Some(Forall(nextVariable :: Nil, atApplicationPos))) &
                onBranch(
                  // positioning in the cutShow branch is justified by applies check that succ length = 1
                  (BranchLabels.cutShowLbl, hideT(p) & ghostTactic(p) & debugT("[successiveInverseDiffGhost] output")),
                  (BranchLabels.cutUseLbl, FOQuantifierTacticsImpl.allEliminateT(cutUsePos) & AxiomCloseT ~ errorT("Should have closed"))
                )
            )
          }
        }
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Successive inverse diff cuts
  //////////////////////////////////////////////////////////////////////////////////////////////////
  //Should be private but for testing.
  def successiveInverseCut : PositionTactic with ApplicableAtFormula =
  new PositionTactic("successiveInverseCut") with ApplicableAtFormula {

    override def applies(f: Formula): Boolean = f match {
      case Box(pi:DifferentialProgram, f: Formula) => pi match {
        case a:AtomicODE => false
        case ODESystem(pipi, ff) => timeVar(pi).isDefined && getLastPartialSoln(pi).isDefined
        case DifferentialProduct(l,r) => timeVar(pi).isDefined
      }
    }

    override def applies(s: Sequent, p: Position): Boolean = {
      val f = TacticHelper.getFormula(s,p)
      //Some temporary debugging output.
      val doesApply = applies(f)
      if(doesApply) println(this.name + " Applies to " + f)
      else println(this.name + " Does not apply to " + f);
      doesApply
    }

    // ([c&H(?);]p(?) <-> [c&(H(?)&r(?));]p(?)) <- [c&H(?);]r(?)
    override def apply(p: Position): Tactic = new ConstructionTactic("construct next " + name) {
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(p) match {
        case Box(program : DifferentialProgram, formula) => {
          val lastPartial = getLastPartialSoln(program).getOrElse(
            throw new Exception("This tactic should not because apply if there are no more partial solutions left in " + program.prettyString)
          )

          Some(
            debugger("Trying to perform a successive inverse cut.") &
            mvPartialSolnToEnd(lastPartial)(p) &
            debugger("Trying to reassociate Ands") &
//            (SearchTacticsImpl.locateLargestSubformula(Formatters.leftAssociateConj)(p) *) &
            Formatters.leftAssociateConj(p) & //Note: only the outermose formula hs toe be correct.
            debugger("After moving to end and left-associating ev dom constraint") &
            debugger(s"Successfully moved partial soln $lastPartial to end") &
            ODETactics.diffInverseCutT(p) & onBranch(
              (BranchLabels.cutUseLbl, debugger("Axiom use")),
              (BranchLabels.cutShowLbl,
                debugger("Showing condition for inverse diff cut equivalence to hold for inverse cut of " + lastPartial.prettyString) ~
                ODETactics.diffInvariantT(p) ~
                errorT("Should have closed.")
              )
            )
          )

        }
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }

  }

  /**
   * A *partial solution* is a formula of the form x = \theta occuring in the evolution domain
   * constraint of an ODE s.t. x is primed in the differential program.
   * Positive examples of partial solutions (for x):
   *    {x' = y, y' = x, x = theta}
   *    {x' = v, v' = a, x = theta & v = theta2 & true}
   *    {x' = v, v' = a, x = theta & v = theta2 & true}
   * Negative examples of partial solutions (for x):
   *    {v' = a, x = \theta}
   *    {x' = v, v' = a & v = \theta & true}
   *
   * Partial solutions are so-called because they are part of a solution to a system of
   * differential equations.
   *
   * @param program A differential program.
   * @return The right-most "partial solution" in an ODE, or else None if the domain constraint does
   *         not contain any partial solutions.
   */
  private def getLastPartialSoln(program : DifferentialProgram) : Option[Formula] = program match {
    case ODESystem(odes, constraint) => {
      extractInitialConditions(Some(program))(constraint).lastOption
    }
    case _ => throw new Exception("Need to implement all cases. Not sure." + program)
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // G,K, diff cuts, diff ghost, diff solve for time, assignment, arith.
  //////////////////////////////////////////////////////////////////////////////////////////////////
  /**
   * This is the G,K step of the proof on page 25 of the uniform substitution calculus paper.
   * However, I couldn't see how that could possibly follow from just G and K...
   *
   * Input: [pi, x=\theta&...;](x=\theta&... --> f(x...))
   * Output: [pi, x=\theta&...;](\thetas replace xs in f)
   */
  private def renameAndDropImpl : PositionTactic = new PositionTactic("renameAndDropImpl") {
    override def applies(s: Sequent, p: Position): Boolean = s(p) match {
      case Box(pi : DifferentialProgram, Imply(evolutionDomain, originalConclusion)) => true
      case _ => false
    }

    override def apply(p: Position): Tactic = new ConstructionTactic("Construct " + name) {
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(p) match {
        case Box(pi: DifferentialProgram, Imply(evolutionDomain, originalConclusion)) => {
          val newConclusion = constructNewConclusion(evolutionDomain, originalConclusion)

          val rewritingFormula = Equiv(Box(pi, Imply(evolutionDomain, originalConclusion)), Box(pi, newConclusion))

          Some(
            cutT(Some(rewritingFormula)) & onBranch(
            //Um yeah not sure what was meant here but it's definitely not G,K...
//              (BranchLabels.cutShowLbl, dischargeEquivalence(pi, Imply(evolutionDomain, originalConclusion), newConclusion)(SuccPos(node.sequent.succ.length))),
              (BranchLabels.cutShowLbl,
                lastSucc(PropositionalTacticsImpl.cohideT) &
                  debugT("[LODE Solver] About to show GK Equivalence") ~
                  showGKEquivalenceTactic ~
                  errorT("[LODE Solver] All goals should've closed.")
              ),
              (BranchLabels.cutUseLbl, {
                val equivPos = AntePos(node.sequent.ante.length)
                assertPT(rewritingFormula, "Precond check failed: Expected equivalence")(equivPos) &
                EqualityRewritingImpl.equivRewriting(equivPos, p) ~
                assertPT(Box(pi, newConclusion), "Postcond check failed: Expected new conclusion")(p)
                /* Output */
              })
            )
          )
        }
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }

    /**
     * Proves:
     *  [{c & x=\theta...}](x = \theta -> x >= 0) <-> [{c & x=\theta...}](\theta >= 0)
     *
     * The proof for the -> direction is really easy -- just monotonicity and arithmetic.
     *
     * The proof for the <- direction is more involved, I think because we need the evolution domain
     * constraint in order to get x = \theta. However, there may be a simpler proof for this branch.
     */
    def showGKEquivalenceTactic = new ConstructionTactic("Show Equivalence for GK Step in page 25 of USubst paper") {
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent.succ.head match {
        case Equiv(Box(ODESystem(dp, h), Imply(l,r)), right) => {
          val left = Box(ODESystem(dp, h), Imply(l,r))
          val conjunction = Box(ODESystem(dp, h),And(l,r))

          Some(Tactics.assertT(0,1) &
            lastSucc(EquivRightT) & onBranch(
            //To show: [a]p->q ==> [a].
            (BranchLabels.equivLeftLbl, cutT(Some(conjunction)) & onBranch(
              (BranchLabels.cutShowLbl,
                Tactics.assertT(1,2) &
                  assertT(s => s.succ.head.equals(right)) &
                  hideT(SuccPos(0)) &
                  InverseImplyRightT() ~
                    debugT("After inverse") ~
                    kModalModusPonensT(SuccPos(0)) ~
                    debugT("After k modal") ~
                    diffWeakenT(SuccPos(0)) ~
                    debugT("after DW") ~
                    arithmeticT ~
                    errorT("Should have closed.")
                ),
              (BranchLabels.cutUseLbl,
                Tactics.assertT(2,1) &
                  Tactics.assertT(s => s.ante.head.equals(left)) &
                  hideT(AntePos(0)) &
                  assertT(s => s.ante.length == 1 && s.ante.head.equals(conjunction)) &
                  boxMonotoneT &
                  arithmeticT ~ Tactics.errorT("Should have closed.")
                )
            )),
            (BranchLabels.equivRightLbl, boxMonotoneT & arithmeticT )
          ))
        }
      }

      override def applicable(node: ProofNode): Boolean =
        node.sequent.ante.isEmpty && node.sequent.succ.length == 1
    }

    private def constructNewConclusion(evolutionDomain : Formula, originalConclusion : Formula) = {
      //Compute the new conclusion.
      val fvsConclusion = StaticSemantics.freeVars(originalConclusion) //Free vars of conc'l
      val variablesToReplace : List[Equal] = extractInitialConditions(None)(evolutionDomain).filter(_ match {
          case Equal(x: Variable, _) => fvsConclusion.contains(x)
          case _ => false
        }).asInstanceOf[List[Equal]]

      variablesToReplace.foldLeft(originalConclusion)(
        (currentFormula, nextEquality) =>
          SubstitutionHelper.replaceFree(currentFormula)(nextEquality.left, nextEquality.right))
    }
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Tactics of the weak solver
  //////////////////////////////////////////////////////////////////////////////////////////////////
  def weakSolveT : PositionTactic = new PositionTactic("Solve ODE w. Weaken") {
    override def applies(s: Sequent, p: Position): Boolean = true //@todo

    override def apply(p: Position): Tactic =
      LogicalODESolver.setupTimeVarT(p) ~
        (cutInSolnsT(p) *) &
        cutTimeLB(p) &
        ODETactics.diffWeakenT(p) &
        arithmeticT
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Setting up explicit time and add solutions to the evolution domain constraint
  //////////////////////////////////////////////////////////////////////////////////////////////////
  private def cutTimeLB : PositionTactic = new PositionTactic("DiffCut and prove a lower-bound on time.") {
    override def applies(s: Sequent, p: Position): Boolean = s(p) match {
      case Box(odes:ODESystem, _) => true //@todo
      case _ => false
    }

    override def apply(p: Position): Tactic = new ConstructionTactic("Construct " + name) {
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(p) match {
        case Box(program : DifferentialProgram, f) => {
          val t = timeVar(program).getOrElse(throw new Exception("Need time var"))

          //Should always be 0, but let's be safe.
          val timeInitialCondition : Term = node.sequent.ante.flatMap(extractInitialConditions(Some(program))).find(f => f match {
            case Equal(x, _) if x.equals(t) => true
            case _ => false
          }).getOrElse(throw new Exception("Need initial condition on time variable " + t)) match {
            case Equal(x, term) => term
            case _ => throw new Exception("find failed.")
          }

          val theCut = diffCutT(GreaterEqual(t, timeInitialCondition))(p) & onBranch(
            (BranchLabels.cutShowLbl, diffInvariant(p)),
            (BranchLabels.cutUseLbl, /*yield*/NilT)
          ) & debugT("yield from cutTimeLB")

          Some(theCut)
        }
      }


      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }

  private def setupTimeVarT : PositionTactic = new PositionTactic("Introduce time into ODE") {

    override def applies(s: Sequent, p: Position): Boolean = s(p) match {
      case Box(dp : DifferentialProgram, f) => timeVar(dp).isEmpty
      case _ => false
    }

    override def apply(p: Position): Tactic = new ConstructionTactic("Construct " + name) {

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(p) match {
        case Box(program : DifferentialProgram, f) => {
          //Copied from DiffSolutionT
          // HACK need some convention for internal names
          val initialTime: Variable = freshNamedSymbol(Variable("kxtime", None, Real), node.sequent)
          // universal quantifier and skolemization in ghost tactic (t:=0) will increment index twice
          val time = Variable(initialTime.name,
            initialTime.index match { case None => Some(1) case Some(a) => Some(a+2) }, initialTime.sort)

          val lastAntePos = AntePos(node.sequent.ante.length + 1)

          val setTimer = HybridProgramTacticsImpl.nonAbbrvDiscreteGhostT(Some(initialTime), Number(0))(p) & boxAssignT(p)

          val tempTime = Variable(time.name, time.index match {
            case None => Some(1)
            case Some(a) => Some(a + 1)
          })
          val introTime =
            setTimer &
            ODETactics.diffAuxiliaryT(time, Number(0), Number(1))(p) &
            errorT("Need exists monotone") &
            hasTimeAssertionT(p) //Check post-cond holds.

          Some(introTime)
        }
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      /**
       * Post-condition of setupTimeVarT
       * A test that passes if and only if there is a time variable in the ODE.
       */
      private val hasTimeAssertionT = assertPT( (s,p) => {
        val fAtPos : Formula = s(p)
        fAtPos match {
          case Box(differentialProgram : DifferentialProgram, cond) => {
            val tv = timeVar(differentialProgram)
            if(tv.isDefined) {
              println("Found a time variable: " + tv.get.prettyString)
              true
            }
            else {
              println("Did not find time variable.")
              false
            }
          }
          case _ => {
            println("Variable did not have correct form: " + fAtPos.prettyString);
            false
          }
        }
      }, "Expected to find [differnetialProgram]phi, where differentialProgram has a time variable.")
    }
  }

  /**
   * @return A tactic that cuts in a solution to an ODE in a system. This should be saturated.
   */
  private def cutInSolnsT : PositionTactic = new PositionTactic("Logical ODE Solver") {
    override def applies(s: Sequent, p: Position): Boolean = s(p) match {
      case Box(program : DifferentialProgram, _) => {
        val hasNextStep = atomicODEs(program).filter(ode => !timeVar(program).getOrElse( () ).equals(ode.xp.x)).find(ode => isUnsolved(ode.xp.x, program)) match {
          case Some(_) => true
          case None => false
        }
        timeVar(program).isDefined && hasNextStep
      }
      case _ => false
    }

    override def apply(p: Position): Tactic = new ConstructionTactic("Construct " + name) {
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        val initialConditions : List[Formula] = node.sequent.ante.flatMap(extractInitialConditions(None)).toList

        node.sequent(p) match {
          case Box(program : DifferentialProgram, f) => {
            val sortedOdes = sortAtomicOdes(atomicODEs(program))
            val nextOde = sortedOdes
              .filter(ode => !timeVar(program).getOrElse( () ).equals(ode.xp.x)) //Skip time var, which we deal with using diff solve instead of diff inv.
              .find(ode => isUnsolved(ode.xp.x, program)).getOrElse(throw new Exception("applies method failed."))
            val toCut = Equal(nextOde.xp.x, integralOf(nextOde.xp.x, program, initialConditions))



            Some(ODETactics.diffCutT(toCut)(p) & onBranch(
              (BranchLabels.cutUseLbl, /*yield*/NilT),
              (BranchLabels.cutShowLbl, ODETactics.diffInvariantT(p))
            ))
          }
          case _ => throw new Exception
        }
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }


  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Helper methods for step tactic.
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  /**
   *
   * @param f A formula.
   * @return A list of formulas with no top-level andss.
   */
  private def decomposeAnds(f : Formula) : List[Formula] = f match {
    case And(l,r) => decomposeAnds(l) ++ decomposeAnds(r)
    case _ => f :: Nil
  }

  /**
   * Converts list of formulas possibly containing Ands into list of formulas that does not contain any ANDs.
   * @param fs A list of formulas, possibly containing Ands.
   */
  private def flattenAnds(fs : List[Formula]) = fs.flatMap(decomposeAnds)

  /**
   *
   * @param f A formula containing conjunctions.
   * @return A list of equality formulas after deconstructing Ands. E.g., A&B&C -> A::B::C::Nil
   */
  private def extractInitialConditions(ode : Option[DifferentialProgram])(f : Formula) : List[Formula] =
    flattenAnds(f match {
      case And(l, r) => extractInitialConditions(ode)(l) ++ extractInitialConditions(ode)(r)
      case Equal(v: Variable, _) => {if(isPrimedVariable(v, ode)) (f :: Nil) else Nil}
      case Equal(_, v: Variable) => {if(isPrimedVariable(v, ode)) (f :: Nil) else Nil}
      case _ => Nil //ignore?
    })

  private def isPrimedVariable(v : Variable, ode : Option[DifferentialProgram]) = ode match {
    case Some(odes) => {
      //@todo
//      getPrimedVariables(ode).contains(v)
      true
    }
    case None => true
  }
  private def getPrimedVariables(ode : DifferentialProgram) : List[Variable] = ode match {
    case AtomicODE(pv, term) => pv.x :: Nil
    case ODESystem(ode, constraint) => getPrimedVariables(ode)
    case DifferentialProduct(l,r) => getPrimedVariables(l) ++ getPrimedVariables(r)
    case _: AtomicDifferentialProgram => ???
  }

  /**
   *
   * @param v A variable occuring in the odes program.
   * @param program An ode system.
   * @return true if the program does not already contain an = constraint (a.k.a. sol'n) for v in the evolution domain.
   */
  def isUnsolved(v : Variable, program : DifferentialProgram) = {
    val odes = atomicODEs(program)
    if(odes.find(_.xp.x.equals(v)).isEmpty) false //Variables that don't occur in the ODE are trivially already solved.
    else if(timeVar(program).equals(v)) false //Don't need to solve for the time var.
    //In non-special cases, check for a = evolution domain constraint in the ode.
    else {
      val vConstraints = odeConstraints(program).flatMap(decomposeAnds).find(_ match {
        case Equal(l, r) => l.equals(v)
        case _ => false
      })
      vConstraints.isEmpty
    }
  }

  /**
   * @param odes
   * @return
   */
  private def sortAtomicOdes(odes : List[AtomicODE]) : List[AtomicODE] = {
    sortAtomicOdesHelper(odes).map(v => odes.find(_.xp.x.equals(v)).get)
  }

  //@todo check this implementation.
  private def sortAtomicOdesHelper(odes : List[AtomicODE], prevOdes : List[AtomicODE] = Nil) : List[Variable] = {
    var primedVars = odes.map(_.xp.x)

    def dependencies(v : Variable) : List[Variable] = {
      val vTerm = odes.find(_.xp.x.equals(v)).get.e
      //remove self-references to cope with the fact that t' = 0*t + 1, which is necessary due to DG.
      primedVars.filter(StaticSemantics.freeVars(vTerm).contains(_)).filter(!_.equals(v))
    }

    var nonDependentSet : List[Variable] = primedVars.filter(dependencies(_).isEmpty)
    val possiblyDependentOdes = odes.filter(ode => !nonDependentSet.contains(ode.xp.x))

    if(possiblyDependentOdes.isEmpty) nonDependentSet
    else {
      if(prevOdes.equals(possiblyDependentOdes)) throw new Exception("Cycle detected!")
      nonDependentSet ++ sortAtomicOdesHelper(possiblyDependentOdes, odes)
    }
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Integrals of a single ODE.
  //////////////////////////////////////////////////////////////////////////////////////////////////

  /**
   * If v' = term occurs in the system of ODEs, then this function computes the integral of term.
   * Assumes that the ODEs have a time variable, that a formula of the form v=f occurs in the initialConditions formulas,
   * and that the system of odes is blah blah.
   * @param v
   * @param program
   * @param initialConditions
   * @return Integral of f assuming v' = f occurs in ODEs.
   */
  def integralOf(v : Variable, program : DifferentialProgram, initialConditions : List[Formula]) : Term = {
    val termToIntegrate = resolveRecurrences(v, program, initialConditions)
    println("Integrating term " + termToIntegrate)

    val t = timeVar(program) match {
      case Some(t) => t
      case None    => throw new Exception("Could not find time variable in ODEs")
    }

    val v_0 : Term = conditionsToValues(initialConditions).get(v) match {
      case Some(x) => x
      case None => throw new Exception("Could not find initial condition for " + v.name)
    }

    Plus(integrator(termToIntegrate, t), v_0)
  }

  /**
   * A syntactic integrator for @todo something like sums of terms over polynomials univariable in t.
   * @param term The term
   * @param t Time variable
   * @return Integral term dt
   */
  private def integrator(term : Term, t : Variable) : Term = term match {
    case Plus(l, r) => Plus(integrator(l, t), integrator(r, t))
    case Minus(l, r) => Minus(integrator(l, t), integrator(r, t))
    case Times(c, x) if x.equals(t) && !StaticSemantics.freeVars(c).contains(t) => Times(Divide(c, Number(2)), Power(x, Number(2)))
    case Times(c, Power(x, exp)) if x.equals(t) && !StaticSemantics.freeVars(exp).contains(t) && !StaticSemantics.freeVars(c).contains(t) => {
      val newExp = exp match {
        case Number(n) => Number(n+1)
        case _ => Plus(exp, Number(1))
      }
      Times(Divide(c, newExp), Power(t, newExp))
    }
    case Neg(c) => Neg(integrator(c, t))
    case Power(base, exp) => exp match {
      case Number(n) =>
        if(n == 1) integrator(base, t)
        else       Times(Divide(Number(1), Number(n+1)), integrator(Power(base, Number(n-1)), t))
      case _ => throw new Exception("Cannot integrate terms with non-number exponents!")
    }
    case x : Term if !StaticSemantics.freeVars(x).contains(t) => Times(x, t)
  }

  /**
   * Given x' = f, replaces all variables in f with their recurrences or initial conditions.
   * @param v A variable s.t. v' = f occurs in the ODEs.
   * @param program ODE(s) with a time variable (some x s.t. x' = 1).
   * @param initialConditions Any initial conditions for the ODE.
   * @return f with all variables replaced by their recurrences or initial conditions.
   */
  def resolveRecurrences(v : Variable, program : DifferentialProgram, initialConditions : List[Formula]) : Term = {
    val odes         = atomicODEs(program)

    val time : Variable = timeVar(program) match {
      case Some(theTimeVar) => theTimeVar
      case None             => throw new Exception("A time variable should exist prior to calling solutionForVariable.")
    }

    //The assertion message is not technically true becuase the solution would just be zero.
    //But if the variable requested is not in the ODE, it's most likely this indicates a programming error rather than
    //an honest inquiry.
    assert(odes.find(ode => ode.xp.x.equals(v)).isDefined, "Cannot solve for a variable that does not occur in the ODE")

    val primedVariables : Set[Variable] = odes.map(_.xp.x).toSet

    //Compute the free variables in the ode corresponding to v'.
    val ode = odes.find(_.xp.x.equals(v)).getOrElse(throw new Exception("Could not find ODE associated with " + v))
    val varsInOde = StaticSemantics.freeVars(ode.e).toSet.map((x : NamedSymbol) => {
        assert(x.isInstanceOf[Variable], "Only variables should occur as the child of the LHS of an ODE")
        x.asInstanceOf[Variable]
      })

    //Variables that occur in the term associated with v' and also occur primed in the ODE.
    val recurrenceVars : Set[Variable] = (varsInOde intersect primedVariables) //for lack of a better name.

    //Variables that occur in the term associated with v' but do not occur primed in the ODE.
    val nonRecurringVars : Set[Variable] = varsInOde -- recurrenceVars

    if(recurrenceVars.isEmpty) {
      // If x' = a where a is not a variable occurring in the system of odes, then the solution is
      // x = at + x_0 where t is the time variable and x_0 is the value in initialValues associated with
      val f_initValuesResolved = nonRecurringVars.foldLeft[Term](ode.e)((currTerm, x) => {
        val x_0 = initValue(initialConditions, x)
        assert(x_0.isDefined, "Need an initial condition for non-recurring variable " + x + " while solve for " + v)
        SubstitutionHelper.replaceFree(currTerm)(x, x_0.get)
      })

      f_initValuesResolved
    }
    else {
      //Replace all instance of primed variables in the term assocaited with v'
      val f_substRecurrences = recurrenceVars.foldLeft[Term](ode.e)((currTerm, x) => {
        val xSoln = recurrence(program, initialConditions, x)
        assert(xSoln.isDefined, "Need a solution for recurring variable " + x + " while solving for " + v)
        SubstitutionHelper.replaceFree(currTerm)(x, xSoln.get)
      })
      val f_substInitValues = nonRecurringVars.foldLeft[Term](f_substRecurrences)((currTerm, x) => {
        val x_0 = initValue(initialConditions, x)
        assert(x_0.isDefined, "Need an initial condition for non-recurring variable " + x + " while solve for " + v)
        SubstitutionHelper.replaceFree(currTerm)(x, x_0.get)
      })
      f_substInitValues
    }
  }

  /**
   * Converts formulas of the form x = term into a map x -> term, and ignores all formulas of other forms.
   * @param fs A list of formulas.
   * @return A map (f -> term) which maps each f in fs of the foram f=term to term.
   */
  private def conditionsToValues(fs : List[Formula]) : Map[Variable, Term] = {
    val flattened = flattenAnds(fs)
    val vOnLhs = flattened.map({
      case Equal(left, right) => left match {
        case v : Variable => Some(v, right)
        case _ => None
      }
      case _ => None
    })

    val vOnRhs = flattened.map({
      case Equal(left, right) => right match {
        case v : Variable => Some(v, left)
        case _ => None
      }
      case _ => None
    })

    (vOnLhs ++ vOnRhs)
      .filter(_.isDefined)
      .map(e => e.get._1 -> e.get._2)
      .toMap
  }

  /**
   * @param program (An system of) odes.
   * @param initialConstraints Formulas describing initial values.
   * @param x A variable that occurs on the left hand side of some ode.
   * @return Some(term) if x = term occurs in either the ev.dom. constraint or the initial constraints. Otherwise, None.
   */
  private def recurrence(program : DifferentialProgram, initialConstraints : List[Formula], x : Variable) : Option[Term] = {
    val odeConditions = conditionsToValues(flattenAnds(odeConstraints(program)))
    val initialConditions = conditionsToValues(flattenAnds(initialConstraints))
    if(odeConditions.contains(x)) odeConditions.get(x)
    else if(initialConditions.contains(x)) initialConditions.get(x)
    else None
  }

  /**
   *
   * @param iniitalConstraints
   * @param x The variable whose initial value is requested.
   * @return The initial value of x.
   */
  private def initValue(iniitalConstraints : List[Formula], x : Variable) : Option[Term] = {
    val initialConditions = conditionsToValues(iniitalConstraints)
    initialConditions.get(x)
  }

  /**
   * @param ode
   * @return The list of atomic differential equations occurring in the differential program.
   * @author Nathan Fulton
   */
  private def odeConstraints(ode : DifferentialProgram) : List[Formula] = ode match {
    case AtomicODE(x,e)                   => Nil
    case ODESystem(ode, constraint)       => constraint :: Nil
    case DifferentialProduct(left, right) => odeConstraints(left) ++ odeConstraints(right)
  }

  /**
   * @param ode
   * @return The list of atomic differential equations occurring in the differential program.
   * @author Nathan Fulton
   */
  private def atomicODEs(ode : DifferentialProgram) : List[AtomicODE] = ode match {
    case AtomicODE(x, e)                  => AtomicODE(x,e) :: Nil
    case ODESystem(ode, constraint)       => atomicODEs(ode)
    case DifferentialProduct(left, right) => atomicODEs(left) ++ atomicODEs(right)
  }

  /**
   * @param ode Any differential program.
   * @return A variable x s.t. x'=1 occurs in ode.
   * @author Nathan Fulton
   */
  def timeVar(ode : DifferentialProgram) : Option[Variable] = {
    //The second value is the one that we cut in. @todo maybe actually we really need time to be 0*t + 1?
    def isTimeVar(atomic : AtomicODE) = atomic.e.equals(Number(1)) || atomic.e.equals(Plus(Times(Number(0), atomic.xp.x), Number(1)))

    ode match {
      case atomic:AtomicODE => if(isTimeVar(atomic)) Some(atomic.xp.x) else None
      case ODESystem(ode, constraint)       => timeVar(ode)
      case DifferentialProduct(left, right) => (timeVar(left), timeVar(right)) match {
        case (Some(t), Some(t2)) => if(t.equals(t2)) Some(t) else ???
        case (Some(t), None)     => Some(t)
        case (None, Some(t))     => Some(t)
        case (None, None)        => None
      }
    }
  }

  private def freshTimeVar(s : Sequent) : Variable =
    Variable("t",TacticHelper.freshIndexInSequent("t", s), Real)

  private def freshTimeVar(f : Formula) : Variable =
    Variable("t", TacticHelper.freshIndexInFormula("t", f), Real)



  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Reordering the conjunctions of evolution domain constraints
  // This tactic is used in the LogicalODESolver to move the next relevant partial solution
  // constraint to the end of a conjunction so that the inverse Diff Cut axiom has the appropriate
  // form.
  // [c & (H() & q());]p() <-> [c & (q() & H());]p()
  //////////////////////////////////////////////////////////////////////////////////////////////////
  /**
   * @todo Might need to re-order the conjunction at the end so that And's always right-associate.
   */
  def AndReoderingT : PositionTactic = {
    def axiomInstance(fml: Formula): Formula = fml match {
      case Box(ODESystem(c, And(h, q)), p) =>
        Equiv(fml, Box(ODESystem(c, And(q, h)), p))
      case _ => False
    }

    def condT: PositionTactic = new PositionTactic("Label") {
      override def applies(s: Sequent, p: Position): Boolean = true
      override def apply(p: Position): Tactic = LabelBranch(cutShowLbl)
    }

    uncoverAxiomT("Domain Constraint Conjunction Reordering", axiomInstance, _ => andReorderingAxiomBaseT)
  }

  def andReorderingAxiomBaseT: PositionTactic = { // diffcut = thing to remove
  def subst(fml: Formula) : List[SubstitutionPair] = fml match {
      case Equiv(Box(ODESystem(c, And(h, q)), p), _) =>
        val aC = DifferentialProgramConst("c")
        val aH = PredOf(Function("H", None, Real, Bool), Anything)
        val aP = PredOf(Function("p", None, Real, Bool), Anything)
        val aQ = PredOf(Function("q", None, Real, Bool), Anything)
        SubstitutionPair(aC, c) :: SubstitutionPair(aH, h) :: SubstitutionPair(aP, p):: SubstitutionPair(aQ, q) :: Nil
    }
    axiomLookupBaseT("Domain Constraint Conjunction Reordering", subst, _ => NilPT, (f, ax) => ax) //@todo not sure the ax is necessary here.
  }

  //@todo might be a duplicate implementation.
  def conjunctionToList(f : Formula) : List[Formula] = f match {
    case And(l, r) => conjunctionToList(l) ++ conjunctionToList(r)
    case _ => f :: Nil
  }

  /**
   * Moves soln to the last position in a conjunctive evolution domain constraint.
   * @todo enforce assumption that constraint is conjunctive.
   */
  def mvPartialSolnToEnd(soln: Formula): PositionTactic = new PositionTactic("mvPartialSoln") {
    override def applies(s: Sequent, p: Position): Boolean = p.isTopLevel && (s(p) match {
      case Box(ODESystem(_, constraint), _) => conjunctionToList(constraint).contains(soln)
      case _ => false
    })

    override def apply(p: Position): Tactic = debugT("About to try mv") & (mvPartialSolnStep(soln)(p) *) & assertT(s => s(p) match {
      case Box(ODESystem(_, constraint), _) => conjunctionToList(constraint).last.equals(soln)
    }, s"Post-Cond: last element of ev dom constraint should be $soln.")
  }
  /**
   *
   * @param soln A portion of a (conjunctive) evolution domain constraint
   * @return A tactic that moves soln to the end of the ev dom constraint.
   */
  def mvPartialSolnStep(soln: Formula) : PositionTactic = new PositionTactic("mvPartialSolnStep") {
    assert(soln match {
      case Equal(x:Variable, _) => true
      case _ => false
    }, "Expected soln to be an Equal with a variable on the LHS.");

    override def applies(s: Sequent, p: Position): Boolean = p.isTopLevel && (s(p) match {
      case Box(ODESystem(odes, constraint), _) => {
        val list = conjunctionToList(constraint)
        !list.last.equals(soln) && list.contains(soln)
      }
    })

    override def apply(p: Position): Tactic = new ConstructionTactic("Construct " + name) {
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(p) match {
        case Box(ODESystem(_, constraint), _) => Some(debugT("About to step.") & AndReoderingT(p))
        case _ => None
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }



//  /**
//   * Given a system of form:
//   *    [x1' = theta1, ..., t' = 0*t+1 & x1=s1, ...]p
//   * produces a system of form:
//   *    [x2' = theta2, ..., t' = 0*t+1 & x1=s1, ...]p
//   * that is, it removes the first ODE from the system that is not required.
//   *
//   * @return The tactic.
//   */
//  /*
//  private def stepRemoveT : PositionTactic = new PositionTactic("Remove solved ODE from system") {
//    override def applies(s: Sequent, p: Position): Boolean = s(p) match {
//      case program : DifferentialProduct => {
//        val solvedEquations = conditionsToValues(odeConstraints(program))
//        val variables = atomicODEs(program).map(_.xp.x)
//
//        val nextVariable : Option[Variable] = ???
//
//        (variables.toSet - timeVar(program) -- solvedEquations.keys.toSet).isEmpty && nextVariable.isDefined
//      }
//    }
//
//    override def apply(p: Position): Tactic = new ConstructionTactic() {
//      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(p) match {
//        case program : DifferentialProduct => {
//          val solvedEquations = conditionsToValues(odeConstraints(program))
//          val variables = atomicODEs(program).map(_.xp.x)
//          require((variables.toSet - timeVar(program) -- solvedEquations.keys.toSet).isEmpty,
//            "All primed variables should have solution")
//
//          ???
//        }
//      }
//
//      override def applicable(node: ProofNode): Boolean = ???
//    }
//  }
//  */

//  private def removeTimeVar : PositionTactic = ???
}
