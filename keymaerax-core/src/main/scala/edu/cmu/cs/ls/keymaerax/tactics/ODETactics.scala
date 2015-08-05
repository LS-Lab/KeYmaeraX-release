/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.tactics

import ExpressionTraversal.{StopTraversal, ExpressionTraversalFunction}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tactics.AxiomaticRuleTactics.{boxMonotoneT, goedelT}
import edu.cmu.cs.ls.keymaerax.tactics.AxiomTactic.{uncoverAxiomT,uncoverConditionalAxiomT,axiomLookupBaseT}
import edu.cmu.cs.ls.keymaerax.tactics.BranchLabels._
import edu.cmu.cs.ls.keymaerax.tactics.ContextTactics.{cutInContext, peelT}
import edu.cmu.cs.ls.keymaerax.tactics.FormulaConverter._
import edu.cmu.cs.ls.keymaerax.tactics.FOQuantifierTacticsImpl._
import edu.cmu.cs.ls.keymaerax.tactics.FOQuantifierTacticsImpl.skolemizeT
import edu.cmu.cs.ls.keymaerax.tactics.HybridProgramTacticsImpl._
import edu.cmu.cs.ls.keymaerax.tactics.HybridProgramTacticsImpl.boxAssignT
import edu.cmu.cs.ls.keymaerax.tactics.HybridProgramTacticsImpl.boxDerivativeAssignT
import edu.cmu.cs.ls.keymaerax.tactics.PropositionalTacticsImpl.{AndRightT, AxiomCloseT, EquivRightT, ImplyRightT, cutT,
  EquivLeftT, ImplyLeftT, uniformSubstT, NotLeftT, AndLeftT, cohideT, cohide2T, PropositionalRightT}
import edu.cmu.cs.ls.keymaerax.tactics.SearchTacticsImpl.{onBranch, lastAnte, lastSucc}
import edu.cmu.cs.ls.keymaerax.tactics.EqualityRewritingImpl.equivRewriting
import edu.cmu.cs.ls.keymaerax.tactics.Tactics._
import edu.cmu.cs.ls.keymaerax.tactics.TacticLibrary._
import edu.cmu.cs.ls.keymaerax.tactics.TacticLibrary.TacticHelper.{getFormula, freshNamedSymbol, findFormulaByStructure}
import AlphaConversionHelper._
import edu.cmu.cs.ls.keymaerax.tools.{Mathematica, Tool}

import scala.collection.immutable.List
import scala.language.postfixOps

/**
 * Created by smitsch on 1/9/15.
 * @author Stefan Mitsch
 * @author aplatzer
 */
object ODETactics {

  /**
   * Creates a new tactic to solve ODEs in diamonds. The tactic introduces ghosts for initial values, asks Mathematica
   * for a solution, and proves that the returned solution is indeed correct.
   * @return The newly created tactic.
   */
  def diamondDiffSolveT: PositionTactic = new PositionTactic("<'> differential solution") {
    override def applies(s: Sequent, p: Position): Boolean = getFormula(s, p) match {
      case Diamond(ODESystem(AtomicODE(_, _), _), _) => true
      case _ => false
    }

    override def apply(p: Position): Tactic = new Tactic("") {
      def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      def apply(tool: Tool, node: ProofNode) = {
        val t = constructTactic(p)
        t.scheduler = Tactics.MathematicaScheduler
        t.continuation = continuation
        t.dispatch(this, node)
      }
    }

    private def constructTactic(p: Position) = new ConstructionTactic(name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      private def primedSymbols(ode: DifferentialProgram) = {
        var primedSymbols = Set[Variable]()
        ExpressionTraversal.traverse(new ExpressionTraversalFunction {
          override def preT(p: PosInExpr, t: Term): Either[Option[StopTraversal], Term] = t match {
            case DifferentialSymbol(ps) => primedSymbols += ps; Left(None)
            case Differential(_) => throw new IllegalArgumentException("Only derivatives of variables supported")
            case _ => Left(None)
          }
        }, ode)
        primedSymbols
      }

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        def createTactic(ode: DifferentialProgram, solution: Term, time: Variable, iv: Map[Variable, Variable],
                         diffEqPos: Position) = {
          val ivfn = iv.map(e => (e._1, FuncOf(Function(e._2.name, e._2.index, Unit, e._2.sort), Nothing)))
          val iiv = iv.map(_.swap).map(e => (FuncOf(Function(e._1.name, e._1.index, Unit, e._1.sort), Nothing), e._2))
          val ivLessSol = iiv.foldRight(solution)((iv, sol) => SubstitutionHelper.replaceFree(sol)(iv._1, iv._2))

          def g(t: Term, x: Term): Term = ode match {
            case ODESystem(AtomicODE(DifferentialSymbol(origX), _), _) =>
              SubstitutionHelper.replaceFree(SubstitutionHelper.replaceFree(ivLessSol)(time, t))(origX, x)
          }

          val t = Variable("t", None, Real)
          val s = Variable("s", None, Real)
          val (x, checkInit, checkInitFn, checkStep, odeF, solF) = getFormula(node.sequent, p) match {
            case f@Diamond(ODESystem(AtomicODE(DifferentialSymbol(x), c), h), phi) =>
              val checkInit = Equal(g(Number(0), x), x)
              val checkInitFn = Equal(g(Number(0), ivfn(x)), x)
              val checkStep = Box(ODESystem(AtomicODE(DifferentialSymbol(t), Number(1)), True),
                Equal(Differential(g(t, ivfn(x))), SubstitutionHelper.replaceFree(c)(x, g(t, ivfn(x)))))
              val sol = Exists(t::Nil, And(
                GreaterEqual(t, Number(0)),
                And(
                  Forall(s::Nil, Imply(
                    And(LessEqual(Number(0), s), LessEqual(s, t)),
                    Diamond(Assign(x, g(s, x)), h)
                  )),
                  Diamond(Assign(x, g(t, x)), phi)
                )
              ))
              (x, checkInit, checkInitFn, checkStep, f, sol)
          }

          val odeSolEquiv = Equiv(odeF, solF)
          val solFFn = SubstitutionHelper.replaceFree(solF)(x, ivfn(x))

          val baseT = new PositionTactic("Base Foo") {
            override def applies(s: Sequent, p: Position): Boolean = true

            override def apply(p: Position): Tactic = new ConstructionTactic(name) {
              override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
                val lookupODE = findFormulaByStructure(node.sequent, odeF) match {
                  case Some(fml) => fml
                  case None => odeF
                }
                val lookupSol = findFormulaByStructure(node.sequent, solFFn) match {
                  case Some(fml) => fml
                  case None => solF
                }
                val checkInitCtx = checkInit.renameAllByExample(odeF, lookupODE)
                val (checkInitCtxFn, lookupSolFFn, subst) = lookupODE match {
                  case Diamond(ODESystem(AtomicODE(DifferentialSymbol(y), _), _), _) =>
                    (Equal(g(Number(0), ivfn(x)), y),
                      SubstitutionHelper.replaceFree(lookupSol)(y, ivfn(x)),
                      SubstitutionPair(ivfn(x), y) :: Nil)
                }

                val desiredSubstResult = Map[Formula, Formula](Imply(checkInitCtx, Equiv(lookupODE, lookupSol)) -> Imply(checkInitCtxFn, Equiv(lookupODE, lookupSolFFn)))

                Some(cutT(Some(Equiv(lookupODE, lookupSol))) & onBranch(
                  (cutShowLbl, lastSucc(cohideT) & cutT(Some(checkInitCtx)) & onBranch(
                    (cutShowLbl, /* show solution holds initially */ lastSucc(cohideT) & arithmeticT),
                    (cutUseLbl, cutT(Some(Imply(checkInitCtx, Equiv(lookupODE, lookupSol)))) & onBranch(
                      (cutShowLbl, lastSucc(cohideT) & uniformSubstT(subst, desiredSubstResult) &
                        cutT(Some(Imply(checkStep, Imply(checkInitCtxFn, Equiv(lookupODE, lookupSolFFn))))) & onBranch(
                        (cutShowLbl, lastSucc(cohideT) & lastSucc(diamondDiffSolveBaseT(g(_, ivfn(x))))),
                        (cutUseLbl, /* show solution */ lastAnte(ImplyLeftT) && (
                          debugT("Show solution") & lastSucc(cohideT) & debugT("Deriving syntactically") &
                            SyntacticDerivationInContext.SyntacticDerivationT(SuccPosition(0).second) & debugT("Syntactic derivation done") &
                            lastSucc(diffEffectSystemT) & debugT("Differential effect") &
                            goedelT & lastSucc(boxDerivativeAssignT) & (arithmeticT | debugT("Solution not provable") & stopT),
                          AxiomCloseT
                          ))
                      )),
                      (cutUseLbl, lastAnte(ImplyLeftT) & AxiomCloseT)
                    ))
                  )),
                  (cutUseLbl, lastAnte(EquivLeftT) & lastAnte(AndLeftT) & (AxiomCloseT |
                    lastAnte(NotLeftT) & lastAnte(NotLeftT) & AxiomCloseT
                    ))
                ))
              }

              override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
            }
          }

          Some(cutInContext(odeSolEquiv, p) & onBranch(
            (cutShowLbl, lastSucc(cohideT) & lastSucc(EquivRightT) &
              assertT(1,1) & lastSucc(peelT(AntePosition(0), p.inExpr, baseT))
              ),
            (cutUseLbl, equivRewriting(AntePosition(node.sequent.ante.length), p.topLevel))
          ))
        }

        val diffEq = getFormula(node.sequent, p) match {
          case Diamond(ode: DifferentialProgram, _) => ode
          case _ => throw new IllegalStateException("Checked by applies to never happen")
        }

        val iv = primedSymbols(diffEq).map(v => v -> freshNamedSymbol(v, node.sequent(p))).toMap
        val ivm = iv.map(e =>  (e._1, Function(e._2.name, e._2.index, Unit, e._2.sort)))

        val time = Variable("t", None, Real)
        val theSolution = tool match {
          case x: Mathematica => x.diffSol(diffEq, time, ivm)
          case _ => None
        }

        val diffEqPos = SuccPosition(p.index)
        theSolution match {
          case Some(Equal(_, s)) => createTactic(diffEq, s, time, iv, diffEqPos)
          case _ => None
        }
      }
    }
  }

  /**
   * Returns a tactic for the diamond ODE solution axiom.
   * @param g The symbolic solution of the ODE.
   * @return The newly created tactic.
   */
  def diamondDiffSolveBaseT(g: Term => Term): PositionTactic = new PositionTactic("<'> differential solution") {
    def applies(s: Sequent, p: Position): Boolean = p.isTopLevel && (s(p) match {
      case Imply(_, Imply(_, Equiv(
      Diamond(ODESystem(AtomicODE(DifferentialSymbol(_), _), _), _),
      Exists(_, _)))) => true
      case _ => false
    })

    def apply(pos: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node : ProofNode): Boolean = applies(node.sequent, pos)
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(pos) match {
        case fml@Imply(_, Imply(_, Equiv(
        Diamond(ODESystem(AtomicODE(DifferentialSymbol(x), c), h), p),
        Exists(_, _)))) =>
          val aP = PredOf(Function("p", None, Real, Bool), DotTerm)
          val aH = PredOf(Function("H", None, Real, Bool), DotTerm)
          val aF = FuncOf(Function("f", None, Real, Real), DotTerm)
          val aG = FuncOf(Function("g", None, Real, Real), DotTerm)
          val subst = SubstitutionPair(aP, SubstitutionHelper.replaceFree(p)(x, DotTerm)) ::
            SubstitutionPair(aH, SubstitutionHelper.replaceFree(h)(x, DotTerm)) ::
            SubstitutionPair(aF, SubstitutionHelper.replaceFree(c)(x, DotTerm)) ::
            SubstitutionPair(aG, g(DotTerm)) :: Nil

          val aX = Variable("x", None, Real)
          val alphaT = new PositionTactic("Alpha") {
            override def applies(s: Sequent, p: Position): Boolean = s(p) match {
              case Imply(_, Imply(_, Equiv(_, Exists(_, _)))) => true
              case _ => false
            }

            override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
              override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] =
                Some(globalAlphaRenamingT(x, aX))

              override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
            }
          }

          val axiom = Axiom.axioms.get("<'> differential solution") match {
            case Some(f) => f
          }

          val (axiomAfterAlpha, alpha) =
            if (x.name != aX.name || x.index != aX.index) (replace(axiom)(aX, x), alphaT(SuccPosition(0)))
            else (axiom, NilT)

          Some(
            uniformSubstT(subst, Map(fml -> axiomAfterAlpha)) &
              assertT(0, 1) &
              alpha &
              AxiomTactic.axiomT("<'> differential solution")
          )
      }
    }
  }

  def diamondDiffSolve2DT: PositionTactic = new PositionTactic("<','> differential solution") {
    override def applies(s: Sequent, p: Position): Boolean = getFormula(s, p) match {
      case Diamond(ODESystem(DifferentialProduct(
        AtomicODE(DifferentialSymbol(_), _),
        AtomicODE(DifferentialSymbol(_), _)), _), _) => true
      case _ => false
    }

    override def apply(p: Position): Tactic = new Tactic("") {
      def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      def apply(tool: Tool, node: ProofNode) = {
        val t = constructTactic(p)
        t.scheduler = Tactics.MathematicaScheduler
        t.continuation = continuation
        t.dispatch(this, node)
      }
    }

    private def constructTactic(p: Position) = new ConstructionTactic(name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      private def primedSymbols(ode: DifferentialProgram) = {
        var primedSymbols = Set[Variable]()
        ExpressionTraversal.traverse(new ExpressionTraversalFunction {
          override def preT(p: PosInExpr, t: Term): Either[Option[StopTraversal], Term] = t match {
            case DifferentialSymbol(ps) => primedSymbols += ps; Left(None)
            case Differential(_) => throw new IllegalArgumentException("Only derivatives of variables supported")
            case _ => Left(None)
          }
        }, ode)
        primedSymbols
      }

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        def flattenConjunctions(f: Formula): List[Formula] = {
          var result: List[Formula] = Nil
          ExpressionTraversal.traverse(new ExpressionTraversalFunction {
            override def preF(p: PosInExpr, f: Formula): Either[Option[StopTraversal], Formula] = f match {
              case And(l, r) => result = result ++ flattenConjunctions(l) ++ flattenConjunctions(r); Left(Some(ExpressionTraversal.stop))
              case a => result = result :+ a; Left(Some(ExpressionTraversal.stop))
            }
          }, f)
          result
        }

        def createTactic(ode: DifferentialProgram, solution: Formula, time: Variable, iv: Map[Variable, Variable],
                         diffEqPos: Position) = {
          val ivfn = iv.map(e => (e._1, FuncOf(Function(e._2.name, e._2.index, Unit, e._2.sort), Nothing)))
          val iiv = iv.map(_.swap).map(e => (FuncOf(Function(e._1.name, e._1.index, Unit, e._1.sort), Nothing), e._2))
          val ivLessSol = iiv.foldRight(solution)((iv, sol) => SubstitutionHelper.replaceFree(sol)(iv._1, iv._2))

          val sol = flattenConjunctions(ivLessSol)
          assert(sol.length == 2)
          val gysol = sol.head match { case Equal(_, s) => s }
          val gxsol = sol.last match { case Equal(_, s) => s }

          def gx(t: Term, x: Term): Term = ode match {
            case ODESystem(DifferentialProduct(AtomicODE(DifferentialSymbol(origY), _), AtomicODE(DifferentialSymbol(origX), _)), _) =>
              SubstitutionHelper.replaceFree(SubstitutionHelper.replaceFree(gxsol)(time, t))(origX, x)
          }
          def gy(t: Term, y: Term): Term = ode match {
            case ODESystem(DifferentialProduct(AtomicODE(DifferentialSymbol(origY), _), AtomicODE(DifferentialSymbol(origX), _)), _) =>
              SubstitutionHelper.replaceFree(SubstitutionHelper.replaceFree(gysol)(time, t))(origY, y)
          }

          val t = Variable("t", None, Real)
          val s = Variable("s", None, Real)
          val (x, y, checkInit, checkStep, odeF, solF) = getFormula(node.sequent, p) match {
            case f@Diamond(ODESystem(DifferentialProduct(AtomicODE(DifferentialSymbol(y), d), AtomicODE(DifferentialSymbol(x), c)), h), phi) =>
              val checkInit = And(Equal(gx(Number(0), x), x), Equal(gy(Number(0), y), y))
              val checkStep = Box(ODESystem(AtomicODE(DifferentialSymbol(t), Number(1)), True),
                And(
                  Equal(Differential(gx(t, ivfn(x))), SubstitutionHelper.replaceFree(c)(x, gx(t, ivfn(x)))),
                  Equal(Differential(gy(t, ivfn(y))), SubstitutionHelper.replaceFree(d)(y, gy(t, ivfn(y))))))
              val sol = Exists(t::Nil, And(
                GreaterEqual(t, Number(0)),
                And(
                  Forall(s::Nil, Imply(
                    And(LessEqual(Number(0), s), LessEqual(s, t)),
                    Diamond(Assign(x, gx(s, x)), Diamond(Assign(y, gy(s, y)), h))
                  )),
                  Diamond(Assign(x, gx(t, x)), Diamond(Assign(y, gy(t, y)), phi))
                )
              ))
              (x, y, checkInit, checkStep, f, sol)
          }

          val odeSolEquiv = Equiv(odeF, solF)
          val solFFn = SubstitutionHelper.replaceFree(SubstitutionHelper.replaceFree(solF)(x, ivfn(x)))(y, ivfn(y))

          val baseT = new PositionTactic("Base Foo") {
            override def applies(s: Sequent, p: Position): Boolean = true

            override def apply(p: Position): Tactic = new ConstructionTactic(name) {
              override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
                val lookupODE = findFormulaByStructure(node.sequent, odeF) match {
                  case Some(fml) => fml
                  case None => odeF
                }
                val lookupSol = findFormulaByStructure(node.sequent, solFFn) match {
                  case Some(fml) => fml
                  case None => solF
                }
                val checkInitCtx = checkInit.renameAllByExample(odeF, lookupODE)
                val (checkInitCtxFn, lookupSolFFn, subst) = lookupODE match {
                  case Diamond(ODESystem(DifferentialProduct(AtomicODE(DifferentialSymbol(yy), _), AtomicODE(DifferentialSymbol(xx), _)), _), _) =>
                    (And(Equal(gx(Number(0), ivfn(x)), xx), Equal(gy(Number(0), ivfn(y)), yy)),
                      SubstitutionHelper.replaceFree(SubstitutionHelper.replaceFree(lookupSol)(xx, ivfn(x)))(yy, ivfn(y)),
                      SubstitutionPair(ivfn(x), xx) :: SubstitutionPair(ivfn(y), yy) :: Nil)
                }

                val desiredSubstResult = Map[Formula, Formula](Imply(checkInitCtx, Equiv(lookupODE, lookupSol)) -> Imply(checkInitCtxFn, Equiv(lookupODE, lookupSolFFn)))

                Some(cutT(Some(Equiv(lookupODE, lookupSol))) & onBranch(
                  (cutShowLbl, lastSucc(cohideT) & cutT(Some(checkInitCtx)) & onBranch(
                    (cutShowLbl, /* show solution holds initially */ lastSucc(cohideT) & (arithmeticT | debugT("Unable to prove solution holds initially") & stopT)),
                    (cutUseLbl, cutT(Some(Imply(checkInitCtx, Equiv(lookupODE, lookupSol)))) & onBranch(
                      (cutShowLbl, lastSucc(cohideT) & uniformSubstT(subst, desiredSubstResult) &
                        cutT(Some(Imply(checkStep, Imply(checkInitCtxFn, Equiv(lookupODE, lookupSolFFn))))) & onBranch(
                        (cutShowLbl, lastSucc(cohideT) & debugT("About to call base tactic") & lastSucc(diamondDiffSolve2DBaseT(gx(_, ivfn(x)), gy(_, ivfn(y))))),
                        (cutUseLbl, /* show solution */ lastAnte(ImplyLeftT) && (
                          debugT("Show solution") & lastSucc(cohideT) & debugT("Deriving syntactically") &
                            SyntacticDerivationInContext.SyntacticDerivationT(SuccPosition(0).second) & debugT("Syntactic derivation done") &
                            lastSucc(diffEffectSystemT) & debugT("Diff effect result") &
                            boxDerivativeAssignT(SuccPosition(0).second) & debugT("Derivative assignment result") &
                            lastSucc(diffWeakenT) & debugT("Diff weaken result") &
                            /*goedelT & lastSucc(boxDerivativeAssignT) &*/ (arithmeticT | debugT("Solution not provable") & stopT),
                          AxiomCloseT | debugT("Unable to prove by axiom") & stopT
                          ))
                      )),
                      (cutUseLbl, lastAnte(ImplyLeftT) & (AxiomCloseT | debugT("Unable to prove by axiom 2") & stopT))
                    ))
                  )),
                  (cutUseLbl, lastAnte(EquivLeftT) & lastAnte(AndLeftT) & (AxiomCloseT |
                    lastAnte(NotLeftT) & lastAnte(NotLeftT) & AxiomCloseT
                    ))
                ))
              }

              override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
            }
          }

          Some(cutInContext(odeSolEquiv, p) & onBranch(
            (cutShowLbl, lastSucc(cohideT) & lastSucc(EquivRightT) &
              assertT(1,1) & lastSucc(peelT(AntePosition(0), p.inExpr, baseT))
              ),
            (cutUseLbl, equivRewriting(AntePosition(node.sequent.ante.length), p.topLevel))
          ))

        }

        val diffEq = getFormula(node.sequent, p) match {
          case Diamond(ode: DifferentialProgram, _) => ode
          case _ => throw new IllegalStateException("Checked by applies to never happen")
        }

        val iv = primedSymbols(diffEq).map(v => v -> freshNamedSymbol(v, node.sequent(p))).toMap
        val ivm = iv.map(e =>  (e._1, Function(e._2.name, e._2.index, Unit, e._2.sort)))

        val time = Variable("t_", None, Real)
        val theSolution = tool match {
          case x: Mathematica => x.diffSol(diffEq, time, ivm)
          case _ => None
        }

        val diffEqPos = SuccPosition(p.index)
        theSolution match {
          case Some(s) => createTactic(diffEq, s, time, iv, diffEqPos)
          case _ => None
        }
      }
    }
  }

  /**
   * Returns a tactic for the diamond ODE solution axiom.
   * @param gx The symbolic solution of the ODE for x'=f(x).
   * @param gy The symbolic solution of the ODE for y'=f(x).
   * @return The newly created tactic.
   */
  def diamondDiffSolve2DBaseT(gx: Term => Term, gy: Term => Term): PositionTactic = new PositionTactic("<','> differential solution") {
    def applies(s: Sequent, p: Position): Boolean = p.isTopLevel && (s(p) match {
      case Imply(_, Imply(
      _,
      Equiv(
      Diamond(ODESystem(
        DifferentialProduct(AtomicODE(DifferentialSymbol(_), _), AtomicODE(DifferentialSymbol(_), _)), _), _),
      Exists(_, _)))) => true
      case _ => false
    })

    def apply(pos: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node : ProofNode): Boolean = applies(node.sequent, pos)
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(pos) match {
        case fml@Imply(_, Imply(
        _,
        Equiv(
        Diamond(ODESystem(
          DifferentialProduct(AtomicODE(DifferentialSymbol(y), d), AtomicODE(DifferentialSymbol(x), c)), h), p),
        Exists(_, _)))) =>
          val aP = PredOf(Function("p", None, Real, Bool), Anything)
          val aH = PredOf(Function("H", None, Real, Bool), Anything)
          val aFx = FuncOf(Function("fx", None, Real, Real), DotTerm)
          val aGx = FuncOf(Function("gx", None, Real, Real), DotTerm)
          val aFy = FuncOf(Function("fy", None, Real, Real), DotTerm)
          val aGy = FuncOf(Function("gy", None, Real, Real), DotTerm)
          val subst = SubstitutionPair(aP, p) ::
            SubstitutionPair(aH, h) ::
            SubstitutionPair(aFx, SubstitutionHelper.replaceFree(c)(x, DotTerm)) ::
            SubstitutionPair(aGx, gx(DotTerm)) ::
            SubstitutionPair(aFy, SubstitutionHelper.replaceFree(d)(y, DotTerm)) ::
            SubstitutionPair(aGy, gy(DotTerm)) ::
            Nil

          // rename to match axiom if necessary
          val aX = Variable("x", None, Real)
          val aY = Variable("y", None, Real)
          def alpha(from: Variable, to: Variable) = new PositionTactic("Alpha") {
            override def applies(s: Sequent, p: Position): Boolean = s(p) match {
              case Imply(_, Imply(_, Equiv(_, Exists(_, _)))) => true
              case _ => false
            }

            override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
              override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] =
                Some(globalAlphaRenamingT(from, to))

              override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
            }
          }

          val axiom = Axiom.axioms.get("<','> differential solution") match {
            case Some(f) => f
          }

          val (axiomAfterAlpha: Formula, alphaT: Tactic) =
            List((x, aX), (y, aY)).foldRight((axiom, NilT))((elem, result) =>
              if (elem._1.name != elem._2.name || elem._1.index != elem._2.index)
                (replace(result._1)(elem._2, elem._1), result._2 & alpha(elem._1, elem._2)(SuccPosition(0)))
              else result
            )

          Some(
            uniformSubstT(subst, Map(fml -> axiomAfterAlpha)) &
              assertT(0, 1) &
              alphaT &
              AxiomTactic.axiomT("<','> differential solution")
          )
      }
    }
  }

  /**
   * Creates a new tactic to handle differential effect atomic/system.
   * @return The newly created tactic
   */
  def diffEffectT: PositionTactic = new PositionTactic("DE differential effect") {
    override def applies(s: Sequent, p: Position): Boolean = getFormula(s, p) match {
      case Box(ODESystem(_, _), _) => true
      case _ => false
    }

    // TODO just call appropriate tactic without scheduler (needs base class change: inspect sequent)
    override def apply(p: Position): Tactic = diffEffectAtomicT(p) | (debugT("Diff effect system") & diffEffectSystemT(p))
  }

  /**
   * Creates a new tactic for the differential effect axiom.
   * @return The newly created tactic
   */
  private def diffEffectAtomicT: PositionTactic = {
    def axiomInstance(fml: Formula): Formula = fml match {
      case Box(ode@ODESystem(AtomicODE(dx@DifferentialSymbol(x), t), q), p) =>
        // [x'=f(x)&q(x);]p(x) <-> [x'=f(x)&q(x);][x':=f(x);]p(x)
        Equiv(fml, Box(ode, Box(DiffAssign(dx, t), p)))
      case _ => False
    }
    uncoverAxiomT("DE differential effect", axiomInstance, _ => diffEffectAtomicBaseT)
  }
  /** Base tactic for diff effect */
  private def diffEffectAtomicBaseT: PositionTactic = {
    def subst(fml: Formula): List[SubstitutionPair] = fml match {
      case Equiv(Box(ode@ODESystem(AtomicODE(dx@DifferentialSymbol(x), t), q), p), _) =>
        val aP = PredOf(Function("p", None, Real, Bool), Anything)
        val aQ = PredOf(Function("q", None, Real, Bool), DotTerm)
        val aF = FuncOf(Function("f", None, Real, Real), DotTerm)
        SubstitutionPair(aP, p) ::
          SubstitutionPair(aQ, SubstitutionHelper.replaceFree(q)(x, DotTerm)) ::
          SubstitutionPair(aF, SubstitutionHelper.replaceFree(t)(x, DotTerm)) :: Nil
    }

    val aX = Variable("x", None, Real)
    def alpha(fml: Formula): PositionTactic = fml match {
      case Equiv(Box(ode@ODESystem(AtomicODE(dx@DifferentialSymbol(x), t), q), p), _) =>
        if (x.name != aX.name || x.index != aX.index) {
          new PositionTactic("Alpha") {
            override def applies(s: Sequent, p: Position): Boolean = s(p) match {
              // TODO DiffSymbol :=
              case Equiv(Box(ODESystem(_, _), _), Box(ODESystem(_, _), Box(DiffAssign(DifferentialSymbol(_), _), _))) => true
              case _ => false
            }

            override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
              override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] =
                Some(globalAlphaRenamingT(x, aX))

              override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
            }
          }
        } else NilPT
    }

    def axiomInstance(fml: Formula, axiom: Formula): Formula = fml match {
      case Equiv(Box(ode@ODESystem(AtomicODE(dx@DifferentialSymbol(x), _), _), _), _) =>
        if (x.name != aX.name || x.index != aX.index) replace(axiom)(aX, x)
        else axiom
    }
    axiomLookupBaseT("DE differential effect", subst, alpha, axiomInstance)
  }

  /**
   * Whether diffSolution will work on the given Formula, because its differential equation is solvable.
   * @todo implement in a reliable way
   */
  def isDiffSolvable(f: Formula) = false

  /**
   * Returns a tactic to use the solution of an ODE as a differential invariant.
   * @param solution The solution. If None, the tactic uses Mathematica to find a solution.
   * @return The tactic.
   */
  def diffSolution(solution: Option[Formula]): PositionTactic = new PositionTactic("differential solution") {
    override def applies(s: Sequent, p: Position): Boolean = !p.isAnte && p.isTopLevel && (s(p) match {
      case Box(odes: DifferentialProgram, _) => true
      case _ => false
    }) && (solution match {
      case Some(f) => true
      case None => MathematicaScheduler.isInitialized
    })

    /**
     * Searches for a time variable (some derivative x'=1) in the specified formula.
     * @param f The formula.
     * @return The time variable, if found. None, otherwise.
     */
    private def findTimeInOdes(f: Formula): Option[Variable] = {
      val odes = f match {
        case Box(prg: DifferentialProgram, _) => prg
        case _ => throw new IllegalStateException("Checked by applies to never happen")
      }

      var timeInOde: Option[Variable] = None
      ExpressionTraversal.traverse(new ExpressionTraversalFunction {
        import ExpressionTraversal.stop
        override def preP(p: PosInExpr, prg: Program): Either[Option[StopTraversal], Program] = prg match {
          // TODO could be complicated 1
          case AtomicODE(DifferentialSymbol(v), theta) if theta == Number(1) =>
            timeInOde = Some(v); Left(Some(stop))
          case _ => Left(None)
        }
      }, odes)
      timeInOde
    }

    override def apply(p: Position): Tactic = new Tactic("") {
      def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      def apply(tool: Tool, node: ProofNode) = {
        import FOQuantifierTacticsImpl.vacuousExistentialQuanT
        import SearchTacticsImpl.onBranch
        import BranchLabels.{equivLeftLbl,equivRightLbl}

        val (time, timeTactic, timeZeroInitially) = findTimeInOdes(node.sequent(p)) match {
          case Some(existingTime) => (existingTime, NilT, false)
          case None =>
            // HACK need some convention for internal names
            val initialTime: Variable = freshNamedSymbol(Variable("kxtime", None, Real), node.sequent)
            // universal quantifier and skolemization in ghost tactic (t:=0) will increment index twice
            val time = Variable(initialTime.name,
              initialTime.index match { case None => Some(1) case Some(a) => Some(a+2) }, initialTime.sort)
            // boxAssignT and equivRight will extend antecedent by 2 -> length + 1
            val lastAntePos = AntePosition(node.sequent.ante.length + 1)
            val introTime = nonAbbrvDiscreteGhostT(Some(initialTime), Number(0))(p) & boxAssignT(p) &
              diffAuxiliaryT(time, Number(0), Number(1))(p) & FOQuantifierTacticsImpl.instantiateT(time, time)(p)

            (time, introTime, true)
        }

        val t = constructTactic(p, time, tIsZero = timeZeroInitially)
        t.scheduler = Tactics.MathematicaScheduler
        val diffSolTactic = timeTactic & t
        diffSolTactic.continuation = continuation
        diffSolTactic.dispatch(this, node)
      }
    }

    private def constructTactic(p: Position, time: Variable, tIsZero: Boolean) = new ConstructionTactic(this.name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      private def primedSymbols(ode: DifferentialProgram) = {
        var primedSymbols = Set[Variable]()
        ExpressionTraversal.traverse(new ExpressionTraversalFunction {
          override def preT(p: PosInExpr, t: Term): Either[Option[StopTraversal], Term] = t match {
            case DifferentialSymbol(ps) => primedSymbols += ps; Left(None)
            case Differential(_) => throw new IllegalArgumentException("Only derivatives of variables supported")
            case _ => Left(None)
          }
        }, ode)
        primedSymbols
      }

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        import HybridProgramTacticsImpl.{discreteGhostT, boxAssignT}

        def flattenConjunctions(f: Formula): List[Formula] = {
          var result: List[Formula] = Nil
          ExpressionTraversal.traverse(new ExpressionTraversalFunction {
            override def preF(p: PosInExpr, f: Formula): Either[Option[StopTraversal], Formula] = f match {
              case And(l, r) => result = result ++ flattenConjunctions(l) ++ flattenConjunctions(r); Left(Some(ExpressionTraversal.stop))
              case a => result = result :+ a; Left(Some(ExpressionTraversal.stop))
            }
          }, f)
          result
        }

        def sizeOf[T](s: SetLattice[T]): Int = s.toSet.size

        def createTactic(ode: DifferentialProgram, solution: Formula, time: Variable, iv: Map[Variable, Variable],
                         diffEqPos: Position) = {
          val initialGhosts = primedSymbols(ode).foldLeft(NilT)((a, b) =>
            a & (discreteGhostT(Some(iv(b)), b)(diffEqPos) & boxAssignT(skolemizeToFnT(_))(diffEqPos)))

          // flatten conjunctions and sort by number of right-hand side symbols to approximate ODE dependencies
          val flatSolution = flattenConjunctions(solution).
            sortWith((f, g) => StaticSemantics.symbols(f).size < StaticSemantics.symbols(g).size).reverse

          val cuts = flatSolution.foldLeft(diffWeakenT(p))((a, b) =>
            debugT(s"About to cut in $b at $p") & diffCutT(b)(p) & onBranch(
              (cutShowLbl,
                debugT("Substituting with constants") & (diffIntroduceConstantT(p) | NilT) &
                debugT(s"Prove Solution using DI at $p") & diffInvariantT(p)),
              (cutUseLbl, a)))

          Some(initialGhosts && cuts)
        }

        val diffEq = node.sequent(p) match {
          case Box(ode: DifferentialProgram, _) => ode
          case _ => throw new IllegalStateException("Checked by applies to never happen")
        }

        val iv = primedSymbols(diffEq).map(v => v -> freshNamedSymbol(v, node.sequent(p))).toMap
        // boxAssignT will increment the index twice (universal quantifier, skolemization) -> tell Mathematica
        val ivm = iv.map(e =>  (e._1, Function(e._2.name, Some(e._2.index.get + 2), Unit, e._2.sort))).toMap

        val theSolution = solution match {
          case sol@Some(_) => sol
          case None => tool match {
            case x: Mathematica if x.isInitialized => x.diffSol(diffEq, time, ivm)
            case _ => None
          }
        }

        val diffEqPos = SuccPosition(p.index)
        theSolution match {
          // add relation to initial time
          case Some(s) =>
            val sol = And(if (tIsZero) s
                          else SubstitutionHelper.replaceFree(s)(time, Minus(time, FuncOf(ivm(time), Nothing))),
                          GreaterEqual(time, FuncOf(ivm(time), Nothing)))
            createTactic(diffEq, sol, time, iv, diffEqPos)
          case None => None
        }
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Differential Weakening Section.
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  /**
   * Returns the differential weaken tactic.
   * @return The tactic.
   */
  def diffWeakenT: PositionTactic = new PositionTactic("DW differential weakening") {
    override def applies(s: Sequent, p: Position): Boolean = !p.isAnte && p.isTopLevel && (s(p) match {
      case Box(ODESystem(_, _), _) => true
      case _ => false
    })

    def apply(p: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node : ProofNode) = applies(node.sequent, p)
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(p) match {
        case Box(ODESystem(_, _), _) =>
          Some(diffWeakenAxiomT(p) & abstractionT(p) & debugT("Skolemize in DiffWeaken") & (skolemizeT(p)*)
            & assertT(s => s(p) match { case Forall(_, _) => false case _ => true }, "Diff. weaken did not skolemize all quantifiers"))
        case _ => None
      }
    }
  }

  def diamondDiffWeakenAxiomT: PositionTactic = new ByDualityAxiomTactic(diffWeakenAxiomT)

  def diffWeakenAxiomT: PositionTactic = {
    def axiomInstance(fml: Formula): Formula = fml match {
      case Box(ode@ODESystem(c, h), p) => Equiv(fml, Box(ode, Imply(h, p)))
      case _ => False
    }
    uncoverAxiomT("DW differential weakening", axiomInstance, _ => diffWeakenAxiomBaseT)
  }
  /** Base tactic for diff weaken */
  private def diffWeakenAxiomBaseT: PositionTactic = {
    def subst(fml: Formula): List[SubstitutionPair] = fml match {
      case Equiv(Box(ode@ODESystem(c, h), p), _) =>
        val aP = PredOf(Function("p", None, Real, Bool), Anything)
        val aC = DifferentialProgramConst("c")
        val aH = PredOf(Function("H", None, Real, Bool), Anything)
        SubstitutionPair(aP, p) :: SubstitutionPair(aC, c) :: SubstitutionPair(aH, h) :: Nil
    }
    axiomLookupBaseT("DW differential weakening", subst, _ => NilPT, (f, ax) => ax)
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inverse Differential Cuts
  // Used for linear ordinary differential equation solver, when removing domain constraints form the ODE.
  //////////////////////////////////////////////////////////////////////////////////////////////////

  /**
   * Applies an inverse differential cut with the last formula in the ev dom constraint.
   * Assumes that formulas are ordered correctly (by dependency; most dependent on the right.
   * @author Nathan Fulton
   */
  def diffInverseCutT: PositionTactic = new PositionTactic("DC differential cut") {
    override def applies(s: Sequent, p: Position): Boolean = !p.isAnte && p.isTopLevel && (s(p) match {
      case Box(ODESystem(c, And(h,q)), _) => true
      case _ => false
    })

    def apply(p: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node : ProofNode) = applies(node.sequent, p)
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(p) match {
        case Box(ODESystem(_, _), _) =>
          val anteLength = node.sequent.ante.length
          Some(diffInverseCutAxiomT(p) & onBranch(
            (axiomUseLbl,
              /* use axiom: here we have to show that our cut was correct */ LabelBranch(cutShowLbl)),
            (axiomShowLbl,
              /* show axiom: here we continue with equiv rewriting so that desired result remains */
              equivRewriting(AntePosition(anteLength), p) & LabelBranch(cutUseLbl) /*@TODO equalityRewriting(whereTheEquivalenceWentTo, p) apply the remaining diffcut equivalence to replace the original p */)
          ))
        case _ => None
      }
    }
  }

  /**
   * Adds an instance of the differential cut axiom for the given cut formula,
   * with instantiation patterns supporting and inverse cut.
   * @author Nathan Fulton
   */
  private def diffInverseCutAxiomT: PositionTactic = {
    def axiomInstance(fml: Formula): Formula = fml match {
      case Box(ODESystem(c, And(h, r)), p) =>
        val showDC = Box(ODESystem(c, h), r)
        val useDC = Box(ODESystem(c, h), p)
        Imply(showDC, Equiv(useDC, fml))
      case _ => False
    }

    def condT: PositionTactic = new PositionTactic("Label") {
      override def applies(s: Sequent, p: Position): Boolean = true
      override def apply(p: Position): Tactic = LabelBranch(cutShowLbl)
    }

    uncoverConditionalAxiomT("DC differential cut", axiomInstance, _ => condT, _ => diffInverseCutAxiomBaseT)
  }
  /** Base tactic for inverse differential cuts */
  private def diffInverseCutAxiomBaseT: PositionTactic = {
    def subst(fml: Formula): List[SubstitutionPair] = fml match {
      case Imply(_, Equiv(_, Box(ODESystem(c, And(h, r)), p))) =>
        val aC = DifferentialProgramConst("c")
        val aH = PredOf(Function("H", None, Real, Bool), Anything)
        val aP = PredOf(Function("p", None, Real, Bool), Anything)
        val aR = PredOf(Function("r", None, Real, Bool), Anything)
        SubstitutionPair(aC, c) :: SubstitutionPair(aH, h) :: SubstitutionPair(aP, p):: SubstitutionPair(aR, r) :: Nil
    }
    axiomLookupBaseT("DC differential cut", subst, _ => NilPT, (f, ax) => ax)
  }

  //////////////////////////////
  // Differential Cuts
  //////////////////////////////

  /**
   * Prove the given list of differential invariants in that order by DC+DI.
   * The operational effect of {x'=f(x)&q(x)}@invariant(f1,f2,f3) is diffInvariant(List(f1,f2,f3))
   * @author aplatzer
   */
  def diffInvariant(invariants: List[Formula]): PositionTactic = new PositionTactic("diffInvariant") {
    /** Find the first invariant among given invariants that is not a conjunct of the evolution domain constraint already */
    private def nextInvariant(ode: ODESystem): Option[Formula] = {
      val evos = FormulaTools.conjuncts(ode.constraint)
      invariants.find(inv => !evos.contains(inv))
    } ensuring(r => remainingInvariants(ode).isEmpty && r==None || r==Some(remainingInvariants(ode).head), "compatible with remainingInvariants")

    /** Find all remaining invariants among given invariants that are not a conjunct of the evolution domain constraint already */
    private def remainingInvariants(ode: ODESystem): List[Formula] = {
      val evos = FormulaTools.conjuncts(ode.constraint)
      invariants.filter(inv => !evos.contains(inv))
    }
    override def applies(s: Sequent, p: Position): Boolean = !p.isAnte && p.isTopLevel && (s(p) match {
      case Box(ode:ODESystem, _) => !nextInvariant(ode).isEmpty
      case _ => false
    })

    def apply(p: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node : ProofNode) = applies(node.sequent, p)
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(p) match {
        case Box(ode:ODESystem, _) =>
          val remaining = remainingInvariants(ode)
          assert(!remaining.isEmpty, "Only non-empty lists of remaining invariants are applicable")
          val cut = remaining.head
          Some(diffCutT(cut)(p) & onBranch(
            (BranchLabels.cutShowLbl, diffInvariantT(p)),
            (BranchLabels.cutUseLbl, diffInvariant(remaining.tail)(p))))
        case _ => None
      }
    }
  }

  /**
   * Applies a differential cut with the given cut formula. If the cut formula contains old(x), the tactic introduces
   * ghosts first to keep track of the initial value of x, and replaces occurrences of old(x) with that ghost.
   * @author aplatzer
   * @author smitsch
   */
  def diffCutT(diffcut: Formula): PositionTactic = new PositionTactic("DC differential cut") {
    override def applies(s: Sequent, pos: Position): Boolean = !pos.isAnte && pos.isTopLevel && (s(pos) match {
      case Box(_: ODESystem, _) => true
      case _ => false
    })

    private def oldVars(fml: Formula): Set[Variable] = {
      var oldVars = Set[Variable]()
      ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
        override def preT(p: PosInExpr, t: Term): Either[Option[StopTraversal], Term] = t match {
          case FuncOf(Function("old", None, Real, Real), v: Variable) => oldVars += v; Left(None)
          case _ => Left(None)
        }
      }, diffcut)
      oldVars
    }

    private def replaceOld(fml: Formula, ghostsByOld: Map[Variable, FuncOf]): Formula = {
      ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
        override def preT(p: PosInExpr, t: Term): Either[Option[StopTraversal], Term] = t match {
          case FuncOf(Function("old", None, Real, Real), v: Variable) => Right(ghostsByOld(v))
          case _ => Left(None)
        }
      }, diffcut) match {
        case Some(f) => f
      }
    }

    private def diffCut(node: ProofNode, pos: Position, fml: Formula): Tactic = {
      val anteLength = node.sequent.ante.length
      diffCutAxiomT(fml)(pos) & onBranch(
        (axiomUseLbl,
          /* use axiom: here we have to show that our cut was correct */ LabelBranch(cutShowLbl)),
        (axiomShowLbl,
          /* show axiom: here we continue with equiv rewriting so that desired result remains */
          equivRewriting(AntePosition(anteLength), pos) & LabelBranch(cutUseLbl) /*@TODO equalityRewriting(whereTheEquivalenceWentTo, p) apply the remaining diffcut equivalence to replace the original p */)
      )
    }

    def apply(pos: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node : ProofNode) = applies(node.sequent, pos)
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(pos) match {
        case Box(ODESystem(_, _), _) =>
          val ov = oldVars(diffcut)
          if (ov.isEmpty) {
            Some(diffCut(node, pos, diffcut))
          } else {
            val ghosts: Set[((Variable, FuncOf), Tactic)] = ov.map(old => {
              val ghost = freshNamedSymbol(Variable(old.name + "0"), node.sequent)
              val varAfterAssign = FuncOf(Function(ghost.name, ghost.index match {
                case Some(i) => Some(i+2)
                case None => Some(1)
              }, Unit, ghost.sort), Nothing)
              (old -> varAfterAssign,
               discreteGhostT(Some(ghost), old)(pos) & boxAssignT(FOQuantifierTacticsImpl.skolemizeToFnT(_))(pos))
            })
            Some(ghosts.map(_._2).reduce(_ & _) & diffCut(node, pos, replaceOld(diffcut, ghosts.map(_._1).toMap)))
          }
        case _ => None
      }
    }
  }

  /**
   * Adds an instance of the differential cut axiom for the given cut formula.
   * @author aplatzer
   * @author Stefan Mitsch
   */
  private def diffCutAxiomT(diffcut: Formula): PositionTactic = {
    def axiomInstance(fml: Formula): Formula = fml match {
      case Box(ODESystem(c, h), p) =>
        val showDC = Box(ODESystem(c, h), diffcut)
        val useDC = Box(ODESystem(c, And(h,diffcut)), p)
        Imply(showDC, Equiv(fml, useDC))
      case _ => False
    }

    def condT: PositionTactic = new PositionTactic("Label") {
      override def applies(s: Sequent, p: Position): Boolean = true
      override def apply(p: Position): Tactic = LabelBranch(cutShowLbl)
    }

    uncoverConditionalAxiomT("DC differential cut", axiomInstance, _ => condT, _ => diffCutAxiomBaseT(diffcut))
  }
  /** Base tactic for differential cuts */
  private def diffCutAxiomBaseT(diffcut: Formula): PositionTactic = {
    def subst(fml: Formula): List[SubstitutionPair] = fml match {
      case Imply(_, Equiv(Box(ODESystem(c, h), p), _)) =>
        val aC = DifferentialProgramConst("c")
        val aH = PredOf(Function("H", None, Real, Bool), Anything)
        val aP = PredOf(Function("p", None, Real, Bool), Anything)
        val aR = PredOf(Function("r", None, Real, Bool), Anything)
        SubstitutionPair(aC, c) :: SubstitutionPair(aH, h) :: SubstitutionPair(aP, p):: SubstitutionPair(aR, diffcut) :: Nil
    }
    axiomLookupBaseT("DC differential cut", subst, _ => NilPT, (f, ax) => ax)
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Diff Solve w/ ev dom constraint axiom
  // DS& differential equation solution
  // [x'=c()&q(x);]p(x) <->
  // \forall t. (t>=0 -> ((\forall s. ((0<=s&s<=t) -> q(x+c()*s))) -> [x:=x+c()*t;]p(x)))
  //////////////////////////////////////////////////////////////////////////////////////////////////
  def diffSolveConstraintT : PositionTactic = {
    def freshT(fml : Formula) = {
      val tName = "T"
      Variable(tName, TacticHelper.freshIndexInFormula(tName, fml))
    }
    def freshS(fml : Formula) = {
      val sName = "S"
      Variable(sName, TacticHelper.freshIndexInFormula(sName, fml))
    }

    def axiomInstance(fml : Formula) = fml match {
      case Box(ODESystem(AtomicODE(DifferentialSymbol(x), c), q), p) => {
        val t = freshT(fml)
        val s = freshS(fml)
        val newQ = SubstitutionHelper.replaceFree(q)(x, Plus(x, Times(c, s)))
        val zero = Number(BigDecimal(0))
        Equiv(
          fml,
          Forall(t :: Nil,
            Imply(
              GreaterEqual(t, zero),
              Imply(
                Forall(s :: Nil, Imply(And(LessEqual(zero, s), LessEqual(s, t)), newQ)),
                Box(Assign(x, Plus(x, Times(c, t))), p)
              )
            )
          )
        )
      }
      case _ => False
    }

    uncoverAxiomT("DS& differential equation solution", axiomInstance, _ => diffSolveConstraintBaseT)
  }

  def diffSolveConstraintBaseT : PositionTactic = {
    def subst(fml : Formula) : List[SubstitutionPair] = fml match {
      case Equiv(
        Box(ODESystem(AtomicODE(DifferentialSymbol(x), c), q), p),
        Forall(t :: Nil, Imply(_, Imply(Forall(s :: Nil, _), _)))
      ) => {
        //forall t. (t>=0 -> ((\forall s. ((0<=s&s<=t) -> q(x+c()*s))) -> [x:=x+c()*t;]p(x)))
        val aC = FuncOf(Function("c", None, Unit, Real), Nothing)
        val aP = PredOf(Function("p", None, Real, Bool), DotTerm)
        val aQ = PredOf(Function("q", None, Real, Bool), DotTerm)

        SubstitutionPair(aC, c) ::
        SubstitutionPair(aP, SubstitutionHelper.replaceFree(p)(x, DotTerm)) ::
        SubstitutionPair(aQ, SubstitutionHelper.replaceFree(q)(x, DotTerm)) :: Nil
      }
    }

    val aX = Variable("x", None, Real)
    def theX(fml : Formula) = fml match {
      case Equiv(Box(ODESystem(AtomicODE(DifferentialSymbol(x), c), q), p), _) => x
    }

    val aT = Variable("t", None, Real)
    def theT(fml : Formula) = fml match {
      case Equiv(_, Forall(t :: Nil, Imply(_, Imply(Forall(s :: Nil, _),_)))) => t
    }

    val aS = Variable("s", None, Real)
    def theS(fml : Formula) = fml match {
      case Equiv(_, Forall(t :: Nil, Imply(_, Imply(Forall(s :: Nil, _),_)))) => s
    }

    def alpha(fml: Formula): PositionTactic =
      TacticHelper.axiomAlphaT(theT(fml), aT) & TacticHelper.axiomAlphaT(theS(fml), aS) & TacticHelper.axiomAlphaT(theX(fml), aX)

    def axiomInstance(fml: Formula, axiom: Formula): Formula = {
      val x = theX(fml)
      val t = theT(fml)
      val s = theS(fml)
      val xRenamed = if (x.name != aX.name || x.index != aX.index) AlphaConversionHelper.replace(axiom)(aX, x) else axiom
      val tRenamed = if(t.name != aT.name || t.index != aT.index) AlphaConversionHelper.replace(xRenamed)(aT, t) else xRenamed
      if(s.name != aS.name || s.index != aS.index) AlphaConversionHelper.replace(tRenamed)(aS, s) else tRenamed
    }

    axiomLookupBaseT("DS& differential equation solution", subst, alpha, axiomInstance)
  }


  ////
  // Diff Solve axiom
  // [x'=c();]p(x) <-> \forall t. (t>=0 -> [x:=x+c()*t;]p(x))
  //
  def diffSolveAxiomT: PositionTactic = {
    val axiomInstance  = (fml : Formula) => fml match {
      case Box(AtomicODE(DifferentialSymbol(x), c), p) => {
        val nameOfvar = "explicitTime"
        val t = Variable(nameOfvar, TacticHelper.freshIndexInFormula(nameOfvar, fml), Real)
        Equiv(
          fml,
          Forall(t :: Nil, Imply(GreaterEqual(t, Number(0)), Box(Assign(x, Plus(x, Times(c, t))), p)))
        )
      }
    }
    uncoverAxiomT("DS differential equation solution", axiomInstance, _ => diffSolveAxiomBaseT)
  }

  def diffSolveAxiomBaseT : PositionTactic = {
    val aX = Variable("x", None, Real)
    val zero = Number(BigDecimal(0))

    def subst(fml : Formula) : List[SubstitutionPair] = fml match {
      case Equiv(Box(AtomicODE(DifferentialSymbol(x), c), p), Forall(t :: Nil, Imply(GreaterEqual(tt, zero), Box(Assign(xx, Plus(xxx, Times(cc, ttt))), pp)))) => {
        //@todo these assertions should be possible to get implicitly by pattern matching on t,t,t instead of t,tt,ttt.
        //@todo Check docs.
        assert(t.equals(tt), "quantified and guarded time")
        assert(tt.equals(ttt), "guarded and linear time")
        assert(c.equals(cc), "terms of atomicODE")
        assert(p.equals(pp), "post conditions")
        assert(x.equals(xx), "primed and assigned time")
        assert(xx.equals(xxx), "assigned and constant var")

        val aP = PredOf(Function("p", None, Real, Bool), Anything)
        val aC = DifferentialProgramConst("c")
        val aS = Variable("s", None, Real)
        SubstitutionPair(aX, x) :: SubstitutionPair(aP, p) :: SubstitutionPair(aC, c) :: SubstitutionPair(aS, t) :: Nil
      }
    }

    def theX(fml : Formula) : Variable = fml match {
      case Equiv(Box(AtomicODE(DifferentialSymbol(x),c), _), _) => x
    }

    def alpha(fml: Formula): PositionTactic = {
      val x = theX(fml)
      if (x.name != aX.name || x.index != aX.index) {
        new PositionTactic("Alpha") {
          override def applies(s: Sequent, p: Position): Boolean = s(p) match {
            case Equiv(Box(_, _), Forall(_, _)) => true
            case _ => false
          }

          override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
            override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] =
              Some(globalAlphaRenamingT(x, aX))

            override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
          }
        }
      } else NilPT
    }

    def axiomInstance(fml: Formula, axiom: Formula): Formula = {
      val x = theX(fml)
      if (x.name != aX.name || x.index != aX.index) AlphaConversionHelper.replaceBound(axiom)(aX, x)
      else axiom
    }

    axiomLookupBaseT("DS differential equation solution", subst, alpha, axiomInstance)
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inverse Lipschitz Diff Ghost
  // DG differential Lipschitz ghost system
  // [c&H(?);]p(?) <-> \exists y. [y'=g(?),c&H(?);]p(?)
  // <- (\exists L . \forall x . \forall a . \forall b . \forall u . \forall v . (a>=b -> [y:=a;u:=g(?);y:=b;v:=g(?)] (-L*(a-b) <= u-v & u-v <= L*(a-b))))
  //////////////////////////////////////////////////////////////////////////////////////////////////

  def inverseLipschitzGhostT : PositionTactic = {
    def fresh(fml : Formula, name : String) = Variable(name, TacticHelper.freshIndexInFormula(name, fml))

    def LFresh(fml : Formula) = fresh(fml, "L")
    def xFresh(fml : Formula) = fresh(fml, "x")
    def aFresh(fml : Formula) = fresh(fml, "a")
    def bFresh(fml: Formula) = fresh(fml, "b")
    def uFresh(fml: Formula) = fresh(fml, "u")
    def vFresh(fml : Formula) = fresh(fml, "v")

    def axiomInstance(fml : Formula) : Formula = fml match {
      case Exists(y :: Nil, Box(ODESystem(DifferentialProduct(AtomicODE(dy, g), c), h), p)) => {
        require(dy.x.equals(y), "Quantified and primed variable should agree.")
        val l = LFresh(fml)
        val x = xFresh(fml)
        val a = aFresh(fml)
        val b = bFresh(fml)
        val v = vFresh(fml)
        val u = uFresh(fml)
        //(a>=b -> [y:=a;u:=g(?);y:=b;v:=g(?)] (-L*(a-b) <= u-v & u-v <= L*(a-b))))
        val implicant = {
          //@todo assuming default assoc of Compose, but that's not enforced in the data structures.
          val boxAssignments = Compose(
            Assign(y, a),Compose(
              Assign(u, g), Compose(
                Assign(y, b),
                Assign(v, g)
              )
            )
          )
          val postcond : Formula = And(
            LessEqual(Times(Neg(l), Minus(a,b)), Minus(u,v)),
            LessEqual(Minus(u,v), Times(l, Minus(a,b)))
          )
          val implicantBody : Formula = Imply(GreaterEqual(a,b), Box(boxAssignments, postcond))

          Exists(l :: Nil,
//            Forall(x :: Nil,
              Forall(a :: Nil,
                Forall(b :: Nil,
                  Forall(u :: Nil,
                    Forall(v :: Nil, implicantBody)))))
        }

        //[c&H(?);]p(?) <-> \exists y. [y'=g(?),c&H(?);]p(?)
        val implicand = {
          val left = Box(ODESystem(c, h), p)
          val right = Exists(y :: Nil,
            Box(ODESystem(DifferentialProduct(AtomicODE(dy, g), c), h), p)
          )
          Equiv(left, right)
        }

        Imply(implicant, implicand)
      }
    }

    def condT: PositionTactic = new PositionTactic("Label") {
      override def applies(s: Sequent, p: Position): Boolean = true
      override def apply(p: Position): Tactic = LabelBranch(cutShowLbl)
    }

    uncoverConditionalAxiomT("DG differential Lipschitz ghost system", axiomInstance, _ => condT, _ => inverseLipschitzGhostBaseT)
  }

  // [c&H(?);]p(?) <-> \exists y. [y'=g(?),c&H(?);]p(?)
  // <- (\exists L . \forall x . \forall a . \forall b . \forall u . \forall v . (a>=b -> [y:=a;u:=g(?);y:=b;v:=g(?)] (-L*(a-b) <= u-v & u-v <= L*(a-b))))
  def inverseLipschitzGhostBaseT : PositionTactic = {
    val aY = Variable("y", None, Real)
//    val aX = Variable("x", None, Real)
    val aL = Variable("L", None, Real)
    val aA = Variable("a", None, Real)
    val aB = Variable("b", None, Real)
    val aU = Variable("u", None, Real)
    val aV = Variable("v", None, Real)

    val aC = DifferentialProgramConst("c")
    val aG = FuncOf(Function("g", None, Real, Real), Anything)
    val aH = PredOf(Function("H", None, Real, Bool), Anything)
    val aP = PredOf(Function("p", None, Real, Bool), Anything)

    def subst(fml : Formula) = fml match {
      case Imply(_, Equiv(_, Exists(y :: Nil, Box(ODESystem(DifferentialProduct(AtomicODE(dy, g), c), h), p)))) => {
        SubstitutionPair(aC, c) :: SubstitutionPair(aG, g) :: SubstitutionPair(aP, p) ::
        SubstitutionPair(aH, h) :: Nil
      }
    }

    def alpha(fml : Formula) : PositionTactic = fml match {
      case Imply(Exists(l :: Nil,
//      Forall(x :: Nil,
      Forall(a :: Nil,
      Forall(b :: Nil,
      Forall(u :: Nil,
      Forall(v :: Nil, _))))), Equiv(_, Exists(y :: Nil, _)))
      => {
        TacticHelper.axiomAlphaT(y, aY) &
//        TacticHelper.axiomAlphaT(x, aX) &
        TacticHelper.axiomAlphaT(a, aA) &
        TacticHelper.axiomAlphaT(b, aB) &
        TacticHelper.axiomAlphaT(u, aU) &
        TacticHelper.axiomAlphaT(v, aV)
      }
      case _ => ???
    }

    def axiomInstance(fml: Formula, axiom: Formula) =fml match {
      case Imply(Exists(l :: Nil,
//      Forall(x :: Nil,
      Forall(a :: Nil,
      Forall(b :: Nil,
      Forall(u :: Nil,
      Forall(v :: Nil, _))))), Equiv(_, Exists(y :: Nil, _)))
      => {
        val afterY = if (!y.equals(aY)) AlphaConversionHelper.replace(axiom)(aY, y) else axiom
        val afterX = afterY //if (!x.equals(aX)) AlphaConversionHelper.replaceBound(afterY)(aX, x) else afterY
        val afterA = if (!a.equals(aA)) AlphaConversionHelper.replaceBound(afterX)(aA, a) else afterX
        val afterB = if (!b.equals(aB)) AlphaConversionHelper.replaceBound(afterA)(aB, b) else afterA
        val afterU = if (!u.equals(aU)) AlphaConversionHelper.replaceBound(afterB)(aU, u) else afterB
                     if (!v.equals(aV)) AlphaConversionHelper.replaceBound(afterU)(aV, v) else afterU
      }
    }

    axiomLookupBaseT("DG differential Lipschitz ghost system", subst, alpha, axiomInstance)
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inverse Differential Auxiliary
  //////////////////////////////////////////////////////////////////////////////////////////////////
  /**
   * Tactic Input: \exists y . [c, y' = t()*y + s() & H(?);]p().
   * Tactic Output: [c & H(?)]p()
   */
  def inverseDiffAuxiliaryT: PositionTactic = {
    def axiomInstance(fml: Formula): Formula = fml match {
      case Exists(y :: Nil, Box(ODESystem(product: DifferentialProduct, h), p)) => {
        val (c, atom) = {
          val l = SystemHelpers.toList(product)
          (SystemHelpers.toProduct(l.tail), l.head)
        }

        atom match {
          case AtomicODE(DifferentialSymbol(yy), Plus(Times(t, yyy), s)) => {
            assert(y.equals(yy), "quantified and final primed variable are the same.")
            assert(yy.equals(yyy), "primed and linear variable are the same.")
            Equiv(
              Box(ODESystem(c, h), p),
              fml
            )
          }
          case _ => throw new Exception("Term not of correct form " + atom)
        }
      }
      case _ => False
    }
    uncoverAxiomT("DA inverse differential ghost", axiomInstance, _ => inverseDiffAuxiliaryBaseT)
  }

  private def inverseDiffAuxiliaryBaseT: PositionTactic = {
    /**
     * Extracts the last primed variable and the uniform substitution from the axiom instance (fml)
     */
    val extractFrom : Formula => (List[SubstitutionPair], Variable) =
      (fml: Formula) => fml match {
        case Equiv(Box(ode@ODESystem(alsoC, alsoH), alsoP), Exists(y :: Nil, Box(ODESystem(product : DifferentialProduct, h), p))) => {
          //Extract portions of the ODE. tail is the final (linear) ODE.
          val (hd, c) = product match {
            case DifferentialProduct(hd : AtomicODE, tl: DifferentialProduct) => (hd, tl)
          }
          val (yy, yyy, t, s) = hd match {
            case AtomicODE(DifferentialSymbol(yy), Plus(Times(t, yyy), s)) => (yy, yyy, t, s)
          }

          assert(y.equals(yy), "quantified variable and last primed variable are the same")
          assert(yy.equals(yyy), "last primed variable and linear variable are the same.")
//          assert(c.equals(alsoC), "non-linear parts of diff eq are the same") @todo false b/c reodering in cAndTail but we can still proceed (I think).
          assert(h.equals(alsoH), "ode constraints are the same")
          assert(p.equals(alsoP), "post conds are the same.")

          val aP = PredOf(Function("p", None, Real, Bool), Anything)
          val aH = PredOf(Function("H", None, Real, Bool), Anything)
          val aC = DifferentialProgramConst("c")
          val aS = FuncOf(Function("s", None, Unit, Real), Nothing)
          val aT = FuncOf(Function("t", None, Unit, Real), Nothing)
          val subst =
            SubstitutionPair(aP, p) :: SubstitutionPair(aH, h) ::
            SubstitutionPair(aC, c) :: SubstitutionPair(aS, s) :: SubstitutionPair(aT, t) :: Nil
          (subst, y)
        }
      }
    val subst = (fml : Formula) => extractFrom(fml)._1
    val theY  = (fml : Formula) => extractFrom(fml)._2

    val aY = Variable("y", None, Real)
    def alpha(fml: Formula): PositionTactic = {
      val y = theY(fml)
      if (y.name != aY.name || y.index != aY.index) {
        new PositionTactic("Alpha") {
          override def applies(s: Sequent, p: Position): Boolean = s(p) match {
            case Equiv(Box(_, _), Exists(_, _)) => true
            case _ => false
          }

          override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
            override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] =
              Some(globalAlphaRenamingT(y, aY))

            override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
          }
        }
      } else NilPT
    }

    def axiomInstance(fml: Formula, axiom: Formula): Formula = {
      val y = theY(fml)
      if (y.name != aY.name || y.index != aY.index) AlphaConversionHelper.replaceBound(axiom)(aY, y)
      else axiom
    }
    axiomLookupBaseT("DA inverse differential ghost", subst, alpha, axiomInstance)
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Comma Commute an ODE -- (no longer) used in master inv aux tactic
  //////////////////////////////////////////////////////////////////////////////////////////////////
  //@todo this was marked as no longer used but it has one use site. Is that a mistake?
  def commaCommuteT : PositionTactic = {
    val axiomInstance = (fml : Formula) => fml match {
      case Box(ODESystem(DifferentialProduct(l,r), h), p) => {
        Equiv(fml, Box(ODESystem(DifferentialProduct(r,l), h), p))
      }
    }
    uncoverAxiomT(", commute", axiomInstance, _ => commaCommuteAxiomBaseT)
  }

  def commaCommuteAxiomBaseT : PositionTactic = {
    def subst(fml : Formula) = fml match {
      case Equiv(Box(ODESystem(DifferentialProduct(c,d), h), p), _) => {
        val aP = PredOf(Function("p", None, Real, Bool), Anything)
        val aC = DifferentialProgramConst("c")
        val aD = DifferentialProgramConst("d")
        val aH = PredOf(Function("H", None, Real, Bool), Anything)
        SubstitutionPair(aP, p) :: SubstitutionPair(aC, c) :: SubstitutionPair(aD, d) :: SubstitutionPair(aH, h) :: Nil
      }
    }
    axiomLookupBaseT(", commute", subst, _ => NilPT, (f, ax) => ax)
  }


  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Differential Auxiliary Section.
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  /**
   * Tactic Input: [c & H(?)]p()
   * Tactic Output: \exists y . [c, y' = t()*y + s() & H(?);]p().
   */
  def diffAuxiliaryT(x: Variable, t: Term, s: Term): PositionTactic = {
    def axiomInstance(fml: Formula): Formula = fml match {
      case Box(ode@ODESystem(c, h), p) if !StaticSemantics(ode).bv.contains(x) &&
        !StaticSemantics.symbols(t).contains(x) && !StaticSemantics.symbols(s).contains(x) =>
        // construct instance
        // [c&H(?);]p(?) <-> \exists y. [c,y'=t()*y+s()&H(?);]p(?)
        Equiv(
          fml,
          Exists(x :: Nil, Box(ODESystem(DifferentialProduct(c,
            AtomicODE(DifferentialSymbol(x), Plus(Times(t, x), s))), h), p)))
      case _ => False
    }
    uncoverAxiomT("DA differential ghost", axiomInstance, _ => diffAuxiliaryBaseT(x, t, s))
  }

  private def diffAuxiliaryBaseT(y: Variable, t: Term, s: Term): PositionTactic = {
    def subst(fml: Formula): List[SubstitutionPair] = fml match {
      case Equiv(Box(ode@ODESystem(c, h), p), _) =>
        val aP = PredOf(Function("p", None, Real, Bool), Anything)
        val aH = PredOf(Function("H", None, Real, Bool), Anything)
        val aC = DifferentialProgramConst("c")
        val aS = FuncOf(Function("s", None, Unit, Real), Nothing)
        val aT = FuncOf(Function("t", None, Unit, Real), Nothing)
        SubstitutionPair(aP, p) :: SubstitutionPair(aH, h) ::
          SubstitutionPair(aC, c) :: SubstitutionPair(aS, s) :: SubstitutionPair(aT, t) :: Nil
    }

    val aY = Variable("y", None, Real)
    def alpha(fml: Formula): PositionTactic = {
      if (y.name != aY.name || y.index != aY.index) {
        new PositionTactic("Alpha") {
          override def applies(s: Sequent, p: Position): Boolean = s(p) match {
            case Equiv(Box(_, _), Exists(_, _)) => true
            case _ => false
          }

          override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
            override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] =
              Some(globalAlphaRenamingT(y, aY))

            override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
          }
        }
      } else NilPT
    }

    def axiomInstance(fml: Formula, axiom: Formula): Formula = {
      if (y.name != aY.name || y.index != aY.index) AlphaConversionHelper.replaceBound(axiom)(aY, y)
      else axiom
    }
    axiomLookupBaseT("DA differential ghost", subst, alpha, axiomInstance)
  }

  /**
   * Tactic to derive the differential auxiliaries proof rule from DG and monotonicity.
   * p(x) <-> \exists y. r(x,y)       r(x,y) -> [x'=f(x),y'=g(x,y)&q(x)]r(x,y)
   * -------------------------------------------------------------------------
   * p(x) -> [x'=f(x)&q(x)]p(x)
   *
   * Tactic input: [x'=f(x)&q(x)]p(x)
   * Tactic output: ... -> p(x)
   *                p(x) <-> \exists y. r(x,y)
   *                \exists y. r(x,y) -> p(x)
   *                r(x,y) -> [x'=f(x),y'=g(x,y)&q(x)]r(x,y)
   *
   * Note, that one side of the equivalence shows up a second time as an implication, and we cut in p(x) just in
   * case p(x) does not literally occur (tactic inefficiency).
   *
   * @param y The new diff. auxiliary.
   * @param gl Linear portion of g: g(x,y) = gl*y+gc
   * @param gc Constant portion of g: g(x,y) = gl*y+gc
   * @param r The replacement for p(x).
   * @return The tactic instance.
   */
  def diffAuxiliariesRule(y: Variable, gl: Term, gc: Term, r: Formula): PositionTactic = new PositionTactic("DA") {
    override def applies(s: Sequent, pos: Position): Boolean = getFormula(s, pos) match {
      case Box(ode@ODESystem(c, h), p) if !StaticSemantics(ode).bv.contains(y) &&
        !StaticSemantics.symbols(gc).contains(y) && !StaticSemantics.symbols(gl).contains(y) => true
      case _ => false
    }

    override def apply(pos: Position): Tactic = new ConstructionTactic("DA") {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = getFormula(node.sequent, pos) match {
        case Box(ode@ODESystem(c, h), p) if !StaticSemantics(ode).bv.contains(y) &&
          !StaticSemantics.symbols(gc).contains(y) && !StaticSemantics.symbols(gl).contains(y) =>
          val desiredBox = Box(ODESystem(DifferentialProduct(c, AtomicODE(DifferentialSymbol(y), Plus(Times(gl, y), gc))), h), r)

          //@todo tactic inefficiency: cutting in p would not be necessary if p is already in antecedent
          Some(cutT(Some(p)) & onBranch(
            (cutShowLbl, hideT(pos) &
              /* remains as proof obligation 0 */ LabelBranch("Diff. Aux. P Initially Valid")),
            (cutUseLbl, cutT(Some(Equiv(p, Exists(y::Nil, r)))) & onBranch(
              (cutShowLbl, lastSucc(cohideT) &
                /* remains as proof obligation 1 */ LabelBranch("Diff. Aux. Show Equivalence (1)")),
              (cutUseLbl,
                equivRewriting(AntePosition(node.sequent.ante.length+1), AntePosition(node.sequent.ante.length)) &
                  lastAnte(skolemizeT) &
                  diffAuxiliaryT(y, gl, gc)(pos) &
                  instantiateT(pos) &
                  cutT(Some(desiredBox)) &
                  onBranch(
                    (cutShowLbl, hideT(pos) & (SearchTacticsImpl.locateAnte(hideT, _ == p)*) &
                      /* remains as proof obligation 2 */ LabelBranch("Diff. Aux. Result")),
                    (cutUseLbl, cohide2T(AntePosition(node.sequent.ante.length+1), pos) &
                      boxMonotoneT & lastAnte(existentialGenT(y, y)) &
                      /* remains, but see proof obligation 1 */ LabelBranch("Diff. Aux. Show Equivalence (2)"))
                  ))
            ))
          ))
        case _ => ???
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // DI for Systems of Differential Equations
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  def diffInvariantAxiomT: PositionTactic = {
    def axiomInstance(fml: Formula): Formula = fml match {
      case Box(ode@ODESystem(c, h), p) =>
        //[c&H]p <- (p & [{c}&H](H->p')
        val g = Imply(h,
          And(p,
            Box(
              ode, DifferentialFormula(p)
            )
          ))
        Imply(g, fml)
      case _ => False
    }
    uncoverAxiomT("DI differential invariant", axiomInstance, _ => diffInvariantAxiomBaseT)
  }
  /** Base tactic for diff invariant */
  private def diffInvariantAxiomBaseT: PositionTactic = {
    def subst(fml: Formula): List[SubstitutionPair] = fml match {
      case Imply(Imply(_, And(_, Box(ODESystem(c, h), DifferentialFormula(p)))), _) =>
        val aC = DifferentialProgramConst("c")
        val aP = PredOf(Function("p", None, Real, Bool), Anything)
        val aH = PredOf(Function("H", None, Real, Bool), Anything)
        SubstitutionPair(aC, c) :: SubstitutionPair(aP, p) :: SubstitutionPair(aH, h) :: Nil
    }
    axiomLookupBaseT("DI differential invariant", subst, _ => NilPT, (f, ax) => ax)
  }

  private def diffEffectSystemT: PositionTactic = new PositionTactic("DE differential effect (system)") {
    override def applies(s: Sequent, p: Position): Boolean = !p.isAnte && p.isTopLevel && (getFormula(s, p) match {
      case Box(ODESystem(cp: DifferentialProduct, _),_) => cp match {
        case DifferentialProduct(AtomicODE(DifferentialSymbol(_), _), _) => true
        case _ => false
      }
      case f => println("Does not apply to: " + f.prettyString); false
    })

    override def apply(p: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = getFormula(node.sequent, p) match {
        case f@Box(ODESystem(a, h), phi) => a match {
          case cp: DifferentialProduct => cp match {
            case DifferentialProduct(AtomicODE(d@DifferentialSymbol(x), t: Term), c: DifferentialProgram) =>
              val g = Box(
                ODESystem(DifferentialProduct(c, AtomicODE(d, t)), h),
                Box(DiffAssign(d, t), phi)
              )
              val instance = Equiv(f, g)

              //construct substitution
              val aF = FuncOf(Function("f", None, Real, Real), Anything)
              val aH = PredOf(Function("H", None, Real, Bool), Anything)
              val aC = DifferentialProgramConst("c")
              val aP = PredOf(Function("p", None, Real, Bool), Anything)

              val subst = SubstitutionPair(aF, t) :: SubstitutionPair(aC, c) :: SubstitutionPair(aP, phi) ::
                SubstitutionPair(aH, h) :: Nil

              // alpha rename if necessary
              val aX = Variable("x", None, Real)
              val alpha =
                if (x.name != aX.name || x.index != aX.index) new PositionTactic("Alpha") {
                  override def applies(s: Sequent, p: Position): Boolean = s(p) match {
                    case Equiv(Box(ODESystem(_, _), _),
                               Box(ODESystem(_, _), Box(DiffAssign(_: DifferentialSymbol, _), _))) => true
                    case _ => false
                  }

                  override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
                    override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] =
                      Some(globalAlphaRenamingT(x.name, x.index, aX.name, aX.index))

                    override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
                  }
                } else NilPT

              Some(diffEffectSystemT(instance, subst, alpha, x)(p))
          }
        }
      }
    }
  }

  /** Uncovering differential equation system from context */
  private def diffEffectSystemT(axInstance: Formula, subst: List[SubstitutionPair],
                                alpha: PositionTactic, x: Variable): PositionTactic = {
    uncoverAxiomT("DE differential effect (system)", _ => axInstance, _ => diffEffectSystemBaseT(subst, alpha, x))
  }
  /** Base tactic for DE differential effect (system) */
  private def diffEffectSystemBaseT(subst: List[SubstitutionPair], alpha: PositionTactic,
                                           x: Variable): PositionTactic = {
    def axiomInstance(fml: Formula, axiom: Formula): Formula = {
      val aX = Variable("x", None, Real)
      if (x.name != aX.name || x.index != aX.index) replace(axiom)(aX, x)
      else axiom
    }
    axiomLookupBaseT("DE differential effect (system)", _ => subst, _ => alpha, axiomInstance)
  }

  /**
   * The "master" DI tactic for differential invariants.
   * @todo no testing yet.
   */
  def diffInvariantT: PositionTactic = new PositionTactic("DI differential invariant") {
    override def applies(s: Sequent, p: Position): Boolean = !p.isAnte && p.isTopLevel && (s(p) match {
      case Box(_: ODESystem, _) => true
      case _ => false
    })

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        node.sequent(p) match {
          case Box(ODESystem(ode, _), _) => {
            val n = {
              var numAtomics = 0
              ExpressionTraversal.traverse(new ExpressionTraversalFunction {
                override def preP(p: PosInExpr, e: Program): Either[Option[StopTraversal], Program] = e match {
                  case _: AtomicODE => numAtomics += 1; Left(None)
                  case _ => Left(None)
                }
              }, ode)
              numAtomics
            }

            def dDebugT(s : String) = debugT("[DiffInvT]" + s)

            val successTactic = (diffInvariantAxiomT(p) & ImplyRightT(p) & AndRightT(p) & (
              dDebugT("left branch") & ((AxiomCloseT | PropositionalRightT(p))*) & arithmeticT,
              dDebugT("right branch") & (diffEffectT(p) * n) & dDebugT("differential effect complete") &
                dDebugT("About to NNF rewrite") & NNFRewrite(p.second) && dDebugT("Finished NNF rewrite") &
                SyntacticDerivationInContext.SyntacticDerivationT(p.second) ~ dDebugT("Done with syntactic derivation") &
                (boxDerivativeAssignT(p.second)*) & dDebugT("Box assignments complete") &
                diffWeakenT(p) & dDebugT("ODE removed") &
                (arithmeticT | NilT) & dDebugT("Finished result")
            ))

            //@todo we should have some form of error catching on this tactic b/c it's pretty huge and intended to be self-contained
            //@todo what happens when the last arith step fails? Is that supposed to happen for true formulas?
            Some(successTactic /*| errorT("Diff Invariant tactic failed!")*/)
          }
        }
      }
    }
  }

  /**
   * Turns things that are constant in ODEs into function symbols.
   * @example Turns v>0, a>0 |- [v'=a;]v>0, a>0 into v>0, a()>0 |- [v'=a();]v>0, a()>0
   * @return
   */
  def diffIntroduceConstantT: PositionTactic = new PositionTactic("IDC introduce differential constants") {
    override def applies(s: Sequent, p: Position): Boolean = getFormula(s, p) match {
      case Box(ode@ODESystem(_, _), _) => true
      case Diamond(ode@ODESystem(_, _), _) => true
      case _ => false
    }

    private def primedSymbols(ode: DifferentialProgram): Set[Variable] = {
      var primedSymbols = Set[Variable]()
      ExpressionTraversal.traverse(new ExpressionTraversalFunction {
        override def preT(p: PosInExpr, t: Term): Either[Option[StopTraversal], Term] = t match {
          case DifferentialSymbol(ps) => primedSymbols += ps; Left(None)
          case Differential(_) => throw new IllegalArgumentException("Only derivatives of variables supported")
          case _ => Left(None)
        }
      }, ode)
      primedSymbols
    }

    private def freeVars(fml: Formula): Set[Variable] =
      StaticSemantics.freeVars(fml).toSet.filter(_.isInstanceOf[Variable]).map(_.asInstanceOf[Variable])

    override def apply(pos: Position): Tactic = new ConstructionTactic("IDC introduce differential constants") {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = getFormula(node.sequent, pos) match {
        case Box(ode@ODESystem(_, _), p) => introduceConstants(freeVars(p) -- primedSymbols(ode), node.sequent)
        case Diamond(ode@ODESystem(_, _), p) => introduceConstants(freeVars(p) -- primedSymbols(ode), node.sequent)
        case _ => throw new IllegalArgumentException("Checked by applies to never happen")
      }

      private def introduceConstants(cnsts: Set[Variable], sequent: Sequent) = {
        if (cnsts.isEmpty) {
          None
        } else {
          val subst = cnsts.map(c => SubstitutionPair(FuncOf(Function(c.name, c.index, Unit, c.sort), Nothing), c)).toList
          val fsWithDCFree = (sequent.ante ++ sequent.succ).
            filter(f => StaticSemantics.freeVars(f).toSet.intersect(cnsts.toSet[NamedSymbol]).nonEmpty)
          val constified = fsWithDCFree.map(f => f -> constify(f, cnsts)).toMap
          Some(uniformSubstT(subst, constified))
        }
      }

      private def constify(f: Formula, consts: Set[Variable]): Formula = {
        if (consts.isEmpty) f
        else {
          val c = consts.head
          constify(SubstitutionHelper.replaceFree(f)(c, FuncOf(Function(c.name, c.index, Unit, c.sort), Nothing)),
            consts.tail)
        }
      }
    }
  }


  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Helper methods for tactics that must interrogate the structure of an ODE
  //////////////////////////////////////////////////////////////////////////////////////////////////

  object SystemHelpers {
    def toList(p : DifferentialProduct) : List[AtomicODE] = {
      assert(isProductOfAtomics(p))
      val left : List[AtomicODE] =
        if (p.left.isInstanceOf[AtomicODE]) (p.left.asInstanceOf[AtomicODE] :: Nil)
        else toList(p.left.asInstanceOf[DifferentialProduct])

      val right : List[AtomicODE] =
        if(p.right.isInstanceOf[AtomicODE]) (p.right.asInstanceOf[AtomicODE] :: Nil)
        else toList(p.right.asInstanceOf[DifferentialProduct])

      left ++ right
    }

    //@todo reimplement and enforce contract that toList and toProduct are inverses.
    def toProduct(as : List[AtomicODE]) =
      as.tail.tail.foldLeft(DifferentialProduct(as.head, as.tail.head))((ode, a) => DifferentialProduct(a, ode))

    def isProductOfAtomics(p : DifferentialProgram) : Boolean = p match {
      case AtomicODE(_, _) => true
      case DifferentialProduct(l, r) => isProductOfAtomics(l) && isProductOfAtomics(r)
      case _ => false
    }
  }
}


