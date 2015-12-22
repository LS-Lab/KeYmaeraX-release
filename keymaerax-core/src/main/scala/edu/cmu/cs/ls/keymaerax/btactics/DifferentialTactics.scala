package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tactics.{Position, PosInExpr}
import edu.cmu.cs.ls.keymaerax.tactics.Augmentors._

import scala.collection.immutable.IndexedSeq

/**
 * [[DifferentialTactics]] provides tactics for differential equations.
 * @note Container for "complicated" tactics. Single-line implementations are in [[TactixLibrary]].
 * @see [[TactixLibrary.DW]], [[TactixLibrary.DC]]
 */
object DifferentialTactics {

  /**
   * Differential effect: exhaustively extracts differential equations from an atomic ODE or an ODE system into
   * differential assignments.
   * {{{
   *   G |- [{x'=f(??)&H(??)}][x':=f(??);]p(??), D
   *   -------------------------------------------
   *   G |- [{x'=f(??)&H(??)}]p(??), D
   * }}}
   * @example{{{
   *    |- [{x'=1}][x':=1;]x>0
   *    -----------------------DE(1)
   *    |- [{x'=1}]x>0
   * }}}
   * @example{{{
   *    |- [{x'=1, y'=x & x>0}][y':=x;][x':=1;]x>0
   *    -------------------------------------------DE(1)
   *    |- [{x'=1, y'=x & x>0}]x>0
   * }}}
   */
  lazy val DE: DependentPositionTactic = new DependentPositionTactic("DE") {
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
      override def computeExpr(sequent: Sequent): BelleExpr =
        if (isODESystem(sequent, pos)) {
          DESystemStep(pos)*getODEDim(sequent, pos)
          //@todo unification fails
          // TactixLibrary.useAt("DE differential effect (system)")(pos)*getODEDim(provable.subgoals.head, pos)
        } else {
          useAt("DE differential effect")(pos)
        }
      }

    /** A single step of DE system (@todo replace with useAt when unification for this example works) */
    private lazy val DESystemStep: DependentPositionTactic = new DependentPositionTactic("DE system step") {
      override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
        override def computeExpr(sequent: Sequent): BelleExpr = sequent.sub(pos) match {
          case Some(f@Box(ODESystem(DifferentialProduct(AtomicODE(d@DifferentialSymbol(x), t), c), h), p)) =>
            val g = Box(
              ODESystem(DifferentialProduct(c, AtomicODE(d, t)), h),
              Box(DiffAssign(d, t), p)
            )

            //construct substitution
            val aF = FuncOf(Function("f", None, Real, Real), Anything)
            val aH = PredOf(Function("H", None, Real, Bool), Anything)
            val aC = DifferentialProgramConst("c")
            val aP = PredOf(Function("p", None, Real, Bool), Anything)

            val subst = SubstitutionPair(aF, t) :: SubstitutionPair(aC, c) :: SubstitutionPair(aP, p) ::
              SubstitutionPair(aH, h) :: Nil
            val origin = Sequent(Nil, IndexedSeq(), IndexedSeq(s"[{${d.prettyString}=f(??),c&H(??)}]p(??) <-> [{c,${d.prettyString}=f(??)&H(??)}][${d.prettyString}:=f(??);]p(??)".asFormula))

            cutLR(g)(pos) <(
              /* use */ skip,
              /* show */ cohide('Rlast) & equivifyR(1) & commuteEquivR(1) & US(USubst(subst), origin) & byUS("DE differential effect (system)"))
        }
      }
    }
  }

  /**
   * diffInd: Differential Invariant proves a formula to be an invariant of a differential equation (by DI, DW, DE, QE)
   * @param qeTool Quantifier elimination tool for final QE step of tactic.
   * @example{{{
   *         *
   *    ---------------------diffInd(qeTool)(1)
   *    x>=5 |- [{x'=2}]x>=5
   * }}}
   * @example{{{
   *    x>=5 |- [x:=x+1;](true -> x>=5&2>=0)
   *    -------------------------------------diffInd(qeTool)(1, 1::Nil)
   *    x>=5 |- [x:=x+1;][{x'=2}]x>=5
   * }}}
   * @incontext
   */
  def diffInd(implicit qeTool: QETool): DependentPositionTactic = new DependentPositionTactic("diffInd") {
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
      override def computeExpr(sequent: Sequent): BelleExpr = {
        require(pos.isSucc && (sequent.sub(pos) match {
          case Some(Box(_: ODESystem, _)) => true
          case _ => false
        }), "diffInd only at ODE system in succedent, but got " + sequent.sub(pos))
        //@todo Dconstify usually needed for DI
        if (pos.isTopLevel)
          DI(pos) &
            (implyR(pos) & andR(pos)) <(
              close | QE,
              //@note derive before DE to keep positions easier
              derive(pos.append(PosInExpr(1::Nil))) &
                DE(pos) &
                Dassignb(pos.append(PosInExpr(1::Nil)))*getODEDim(sequent,pos) &
                //@note DW after DE to keep positions easier
                (if (hasODEDomain(sequent, pos)) DW(pos) else skip) &
                abstractionb(pos) & (close | QE)
              )
        else
          DI(pos) &
            //@note derive before DE to keep positions easier
            shift(PosInExpr(1::1::Nil), new DependentPositionTactic("Shift") {
              override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
                override def computeExpr(sequent: Sequent): BelleExpr = {
                  shift(PosInExpr(1::Nil), derive)(pos) &
                    DE(pos) &
                    (shift(PosInExpr(1::Nil), Dassignb)(pos) * getODEDim(sequent, pos)) &
                    //@note DW after DE to keep positions easier
                    (if (hasODEDomain(sequent, pos)) DW(pos) else skip) &
                    abstractionb(pos)
                }
              }
            }
            )(pos)
      }
    }
  }

  /** Indicates whether there is a proper ODE System at the indicated position of a sequent with >=2 ODEs */
  private val isODESystem: (Sequent,Position)=>Boolean = (sequent,pos) => {
    sequent.sub(pos) match {
      case Some(Box(ODESystem(_:DifferentialProduct,_), _))     => true
      case Some(Diamond(ODESystem(_:DifferentialProduct,_), _)) => true
      case Some(e) => false
      case None => throw new IllegalArgumentException("ill-positioned " + pos + " in " + sequent)
    }
  }

  /** Computes the dimension of ODE at indicated position of a sequent */
  private val getODEDim: (Sequent,Position)=>Int = (sequent,pos) => {
    def odeDim(ode: ODESystem): Int = StaticSemantics.boundVars(ode).toSymbolSet.count(_.isInstanceOf[DifferentialSymbol])
    sequent.sub(pos) match {
      case Some(Box(ode: ODESystem, _))     => odeDim(ode)
      case Some(Diamond(ode: ODESystem, _)) => odeDim(ode)
      case Some(e) => throw new IllegalArgumentException("no ODE at position " + pos + " in " + sequent + "\nFound: " + e)
      case None => throw new IllegalArgumentException("ill-positioned " + pos + " in " + sequent)
    }
  }

  /** Whether the ODE at indicated position of a sequent has a nontrivial domain */
  private val hasODEDomain: (Sequent,Position)=>Boolean = (sequent,pos) => {
    sequent.sub(pos) match {
      case Some(Box(ode: ODESystem, _))     => ode.constraint != True
      case Some(Diamond(ode: ODESystem, _)) => ode.constraint != True
      case Some(e) => throw new IllegalArgumentException("no ODE at position " + pos + " in " + sequent + "\nFound: " + e)
      case None => throw new IllegalArgumentException("ill-positioned " + pos + " in " + sequent)
    }
  }
}
