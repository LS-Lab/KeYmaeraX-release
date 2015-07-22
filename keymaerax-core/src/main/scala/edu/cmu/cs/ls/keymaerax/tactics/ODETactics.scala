/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.tactics

import ExpressionTraversal.{StopTraversal, ExpressionTraversalFunction}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tactics
import edu.cmu.cs.ls.keymaerax.tactics.AxiomaticRuleTactics.goedelT
import edu.cmu.cs.ls.keymaerax.tactics.AxiomTactic.{uncoverAxiomT,uncoverConditionalAxiomT,axiomLookupBaseT}
import edu.cmu.cs.ls.keymaerax.tactics.BranchLabels._
import edu.cmu.cs.ls.keymaerax.tactics.ContextTactics.{cutInContext, peelT}
import edu.cmu.cs.ls.keymaerax.tactics.FormulaConverter._
import edu.cmu.cs.ls.keymaerax.tactics.FOQuantifierTacticsImpl._
import edu.cmu.cs.ls.keymaerax.tactics.FOQuantifierTacticsImpl.skolemizeT
import edu.cmu.cs.ls.keymaerax.tactics.HybridProgramTacticsImpl._
import edu.cmu.cs.ls.keymaerax.tactics.HybridProgramTacticsImpl.boxAssignT
import edu.cmu.cs.ls.keymaerax.tactics.PropositionalTacticsImpl.{AndRightT, AxiomCloseT, EquivRightT, ImplyRightT, cutT,
  EquivLeftT, ImplyLeftT, uniformSubstT, NotLeftT, AndLeftT, cohideT, PropositionalRightT}
import edu.cmu.cs.ls.keymaerax.tactics.SearchTacticsImpl._
import edu.cmu.cs.ls.keymaerax.tactics.EqualityRewritingImpl.equivRewriting
import edu.cmu.cs.ls.keymaerax.tactics.Tactics._
import edu.cmu.cs.ls.keymaerax.tactics.TacticLibrary.{abstractionT, globalAlphaRenamingT, debugT, arithmeticT}
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
              AxiomTactic.axiomT("<'> differential solution") & assertT(1, 1) & AxiomCloseT
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
              AxiomTactic.axiomT("<','> differential solution") & assertT(1, 1) & (AxiomCloseT | debugT("Unable to prove from axiom <','> differential solution") & stopT)
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
              (cutShowLbl, debugT(s"Prove Solution using DI at $p") & diffInvariantT(p)),
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

  ///
  // Inverse Differential Cuts
  // Used for linear ordinary differential equation solver, when removing domain constraints form the ODE.
  ///

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
   * Applies a differential cut with the given cut formula.
   * @author aplatzer
   */
  def diffCutT(diffcut: Formula): PositionTactic = new PositionTactic("DC differential cut") {
    override def applies(s: Sequent, p: Position): Boolean = !p.isAnte && p.isTopLevel && (s(p) match {
      case Box(_: ODESystem, _) => true
      case _ => false
    })

    def apply(p: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node : ProofNode) = applies(node.sequent, p)
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(p) match {
        case Box(ODESystem(_, _), _) =>
          val anteLength = node.sequent.ante.length
          Some(diffCutAxiomT(diffcut)(p) & onBranch(
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

    private def diffConstants(ode: DifferentialProgram): Set[Variable] =
      (StaticSemantics.symbols(ode) -- primedSymbols(ode)).filter(_.isInstanceOf[Variable]).map(_.asInstanceOf[Variable])

    override def apply(p: Position): Tactic = new ConstructionTactic("IDC introduce differential constants") {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = getFormula(node.sequent, p) match {
        case Box(ode@ODESystem(_, _), _) => introduceConstants(ode, node.sequent)
        case Diamond(ode@ODESystem(_, _), _) => introduceConstants(ode, node.sequent)
        case _ => throw new IllegalArgumentException("Checked by applies to never happen")
      }

      private def introduceConstants(ode: ODESystem, sequent: Sequent) = {
        val dc = diffConstants(ode)
        if (dc.isEmpty) {
          None
        } else {
          val subst = dc.map(c => SubstitutionPair(FuncOf(Function(c.name, c.index, Unit, c.sort), Nothing), c)).toList
          val fsWithDCFree = (sequent.ante ++ sequent.succ).
            filter(f => StaticSemantics.freeVars(f).toSet.intersect(dc.toSet[NamedSymbol]).nonEmpty)
          val constified = fsWithDCFree.map(f => f -> constify(f, dc)).toMap
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
}


