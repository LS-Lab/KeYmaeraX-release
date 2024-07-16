/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics.helpers

import org.keymaerax.bellerophon.TacticInapplicableFailure
import org.keymaerax.btactics.SimplifierV3._
import org.keymaerax.btactics._
import org.keymaerax.btactics.macros.DerivationInfoAugmentors._
import org.keymaerax.core._
import org.keymaerax.infrastruct.Augmentors._
import org.keymaerax.infrastruct._
import org.keymaerax.parser.StringConverter._
import org.keymaerax.tools.ext.SimplificationTool

import scala.annotation.nowarn
import scala.collection.immutable.{Map, Nil}
import scala.util.Try

/**
 * @todo
 *   move to formula tools? Or make this ProgramTools?
 * @author
 *   Nathan Fulton
 */
object DifferentialHelper {

  /** Returns all of the AtomicODE's in a system. */
  def atomicOdes(system: ODESystem): List[AtomicODE] = atomicOdes(system.ode)
  @nowarn("msg=match may not be exhaustive")
  def atomicOdes(dp: DifferentialProgram): List[AtomicODE] = dp match {
    case DifferentialProgramConst(c, _) => ???
    case DifferentialProduct(x, y) => atomicOdes(x) ++ atomicOdes(y)
    case ode: AtomicODE => ode :: Nil
  }

  /** Sorts ODEs in dependency order; so v'=a, x'=v is sorted into x'=v,v'=a. */
  def sortAtomicOdes(odes: List[AtomicODE], diffArg: Term): List[AtomicODE] = {
    val sorted = sortAtomicOdesHelper(odes).map(v => odes.find(_.xp.x == v).get)
    val (l1, l2) = sorted.partition(atom => atom.xp.x == diffArg)
    l2 ++ l1
  }

  // @todo check this implementation.
  def sortAtomicOdesHelper(odes: List[AtomicODE], prevOdes: List[AtomicODE] = Nil): List[Variable] = {
    val primedVars = odes.map(_.xp.x)

    def dependencies(v: Variable): List[Variable] = {
      val vTerm = odes.find(_.xp.x == v).get.e
      // remove self-references to cope with the fact that t' = 0*t + 1, which is necessary due to DG.
      primedVars.filter(StaticSemantics.freeVars(vTerm).contains(_)).filter(_ != v)
    }

    val nonDependentSet: List[Variable] = primedVars.filter(dependencies(_).isEmpty)
    val possiblyDependentOdes = odes.filter(ode => !nonDependentSet.contains(ode.xp.x))

    if (possiblyDependentOdes.isEmpty) nonDependentSet
    else if (prevOdes.equals(possiblyDependentOdes)) throw new Exception("Cycle detected!")
    else nonDependentSet ++ sortAtomicOdesHelper(possiblyDependentOdes, odes)
  }

  /** Returns true iff v occurs primed in the ode. */
  def isPrimedVariable(v: Variable, ode: Option[Program]): Boolean = ode match {
    case Some(x) => StaticSemantics.boundVars(x).contains(v)
    case None => true // over-approximate set of initial conditions if no ODE is provided.
  }

  /** Indicates whether the variables `vs` is primed in the ODE `system`. */
  def containsPrimedVariables(vs: Set[Variable], system: ODESystem): Boolean = vs
    .exists(v => isPrimedVariable(v, Some(system.ode)))

  /**
   * Extracts all comparisons that look like initial conditions from the formula f.
   *
   * @param ode
   *   Optionally an ODE; if None, then all comparisons are extracted from f. This may include non-initial-conds.
   * @param f
   *   A formula containing conjunctions.
   * @return
   *   A list of comparison formulas after deconstructing Ands. E.g., A&B&C -> A::B::C::Nil
   */
  def extractInitialConditions(ode: Option[Program])(f: Formula): List[Formula] = FormulaTools.conjuncts(f match {
    case And(l, r) => extractInitialConditions(ode)(l) ++ extractInitialConditions(ode)(r)
    // @todo search in other formulas using polarity
    case cf: ComparisonFormula =>
      val leftInitials = cf.left match {
        case v: Variable if isPrimedVariable(v, ode) => f :: Nil
        case _ => Nil
      }
      val rightInitials = cf.right match {
        case v: Variable if isPrimedVariable(v, ode) => f :: Nil
        case _ => Nil
      }
      leftInitials ++ rightInitials
    case _ => Nil
  })

  /** Returns the list of variables that have differential equations in an ODE. */
  def getPrimedVariables(ode: Program): List[Variable] = ode match {
    case AtomicODE(pv, _) => pv.x :: Nil
    case ODESystem(odes, _) => getPrimedVariables(odes)
    case DifferentialProduct(l, r) => getPrimedVariables(l) ++ getPrimedVariables(r)
    case _: AtomicDifferentialProgram => ???
    case _ =>
      throw new TacticInapplicableFailure(s"Expected a differential program or ODE system but found ${ode.getClass}")
  }

  /** Split a differential program into its ghost constituents: parseGhost("y'=a*x+b".asProgram) is (y,a,b) */
  @nowarn("msg=match may not be exhaustive")
  def parseGhost(ghost: DifferentialProgram): (Variable, Term, Term) = {
    val y = Variable("y_")
    val yp = DifferentialSymbol(y)
    val a = UnitFunctional("a", Except(y :: Nil), Real)
    val b = UnitFunctional("b", Except(y :: Nil), Real)

    def neg(t: Term): Term = t match {
      case Number(n) => Number(BigDecimal("-" + n))
      case Neg(t) => t
      case t => Neg(t)
    }

    // Four cases contain both a and b: +a+b, +a-b, -a+b, -a-b
    // y' = ay + b
    {
      val shape = AtomicODE(yp, Plus(Times(a, y), b))
      Try(UnificationMatch.unifiable(shape, ghost)).toOption.flatten match {
        case Some(s) if s(shape) == ghost => return (s(y).asInstanceOf[Variable], s(a), s(b))
        case None =>
      }
    }

    // y' = ay - b
    {
      val shape = AtomicODE(yp, Minus(Times(a, y), b))
      Try(UnificationMatch.unifiable(shape, ghost)).toOption.flatten match {
        case Some(s) if s(shape) == ghost => return (s(y).asInstanceOf[Variable], s(a), neg(s(b)))
        case None =>
      }
    }

    // y' = -ay + b
    {
      val shape = AtomicODE(yp, Plus(Neg(Times(a, y)), b))
      Try(UnificationMatch.unifiable(shape, ghost)).toOption.flatten match {
        case Some(s) if s(shape) == ghost => return (s(y).asInstanceOf[Variable], neg(s(a)), s(b))
        case None =>
      }
    }
    {
      val shape = AtomicODE(yp, Plus(Times(Neg(a), y), b))
      Try(UnificationMatch.unifiable(shape, ghost)).toOption.flatten match {
        case Some(s) if s(shape) == ghost => return (s(y).asInstanceOf[Variable], neg(s(a)), s(b))
        case None =>
      }
    }

    // y' = -ay - b
    {
      val shape = AtomicODE(yp, Minus(Neg(Times(a, y)), b))
      Try(UnificationMatch.unifiable(shape, ghost)).toOption.flatten match {
        case Some(s) if s(shape) == ghost => return (s(y).asInstanceOf[Variable], neg(s(a)), neg(s(b)))
        case None =>
      }
    }
    {
      val shape = AtomicODE(yp, Minus(Times(Neg(a), y), b))
      Try(UnificationMatch.unifiable(shape, ghost)).toOption.flatten match {
        case Some(s) if s(shape) == ghost => return (s(y).asInstanceOf[Variable], neg(s(a)), neg(s(b)))
        case None =>
      }
    }

    // Four cases contain both 1/a and b: +1/a+b, +1/a-b, -1/a+b, -1/a-b
    // y' = y/a + b
    {
      val shape = AtomicODE(yp, Plus(Divide(y, a), b))
      Try(UnificationMatch.unifiable(shape, ghost)).toOption.flatten match {
        case Some(s) if s(shape) == ghost => return (s(y).asInstanceOf[Variable], s(Divide(Number(1), a)), s(b))
        case None =>
      }
    }

    // y' = y/a - b
    {
      val shape = AtomicODE(yp, Minus(Divide(y, a), b))
      Try(UnificationMatch.unifiable(shape, ghost)).toOption.flatten match {
        case Some(s) if s(shape) == ghost => return (s(y).asInstanceOf[Variable], s(Divide(Number(1), a)), neg(s(b)))
        case None =>
      }
    }

    // y' = -y/a + b
    {
      val shape = AtomicODE(yp, Plus(Neg(Divide(y, a)), b))
      Try(UnificationMatch.unifiable(shape, ghost)).toOption.flatten match {
        case Some(s) if s(shape) == ghost => return (s(y).asInstanceOf[Variable], neg(s(Divide(Number(1), a))), s(b))
        case None =>
      }
    }
    {
      val shape = AtomicODE(yp, Plus(Divide(Neg(y), a), b))
      Try(UnificationMatch.unifiable(shape, ghost)).toOption.flatten match {
        case Some(s) if s(shape) == ghost => return (s(y).asInstanceOf[Variable], neg(s(Divide(Number(1), a))), s(b))
        case None =>
      }
    }

    // y' = -y/a - b
    {
      val shape = AtomicODE(yp, Minus(Neg(Divide(y, a)), b))
      Try(UnificationMatch.unifiable(shape, ghost)).toOption.flatten match {
        case Some(s) if s(shape) == ghost =>
          return (s(y).asInstanceOf[Variable], neg(s(Divide(Number(1), a))), neg(s(b)))
        case None =>
      }
    }
    {
      val shape = AtomicODE(yp, Minus(Divide(Neg(y), a), b))
      Try(UnificationMatch.unifiable(shape, ghost)).toOption.flatten match {
        case Some(s) if s(shape) == ghost =>
          return (s(y).asInstanceOf[Variable], neg(s(Divide(Number(1), a))), neg(s(b)))
        case None =>
      }
    }

    // 4 cases contain implicit a=1 and b: +y+b, +y-b, -y+b, -y-b
    // y' = y + b
    {
      val shape = AtomicODE(yp, Plus(y, b))
      Try(UnificationMatch.unifiable(shape, ghost)).toOption.flatten match {
        case Some(s) if s(shape) == ghost => return (s(y).asInstanceOf[Variable], Number(1), s(b))
        case None =>
      }
    }

    // y' = y - b
    {
      val shape = AtomicODE(yp, Minus(y, b))
      Try(UnificationMatch.unifiable(shape, ghost)).toOption.flatten match {
        case Some(s) if s(shape) == ghost => return (s(y).asInstanceOf[Variable], Number(1), neg(s(b)))
        case None =>
      }
    }

    // y' = -y + b
    {
      val shape = AtomicODE(yp, Plus(Neg(y), b))
      Try(UnificationMatch.unifiable(shape, ghost)).toOption.flatten match {
        case Some(s) if s(shape) == ghost => return (s(y).asInstanceOf[Variable], Number(-1), s(b))
        case None =>
      }
    }

    // y' = -y - b
    {
      val shape = AtomicODE(yp, Minus(Neg(y), b))
      Try(UnificationMatch.unifiable(shape, ghost)).toOption.flatten match {
        case Some(s) if s(shape) == ghost => return (s(y).asInstanceOf[Variable], Number(-1), neg(s(b)))
        case None =>
      }
    }

    // 2 cases contain just a: +a and -a
    // y' = ay
    {
      val shape = AtomicODE(yp, Times(a, y))
      Try(UnificationMatch.unifiable(shape, ghost)).toOption.flatten match {
        case Some(s) if s(shape) == ghost => return (s(y).asInstanceOf[Variable], s(a), Number(0))
        case _ =>
      }
    }

    // y' = -ay
    {
      val shape = AtomicODE(yp, Neg(Times(a, y)))
      Try(UnificationMatch.unifiable(shape, ghost)).toOption.flatten match {
        case Some(s) if s(shape) == ghost => return (s(y).asInstanceOf[Variable], neg(s(a)), Number(0))
        case None =>
      }
    }
    {
      val shape = AtomicODE(yp, Times(Neg(a), y))
      Try(UnificationMatch.unifiable(shape, ghost)).toOption.flatten match {
        case Some(s) if s(shape) == ghost => return (s(y).asInstanceOf[Variable], neg(s(a)), Number(0))
        case None =>
      }
    }

    // 2 cases contain just 1/a: +1/a and -1/a
    // y' = ay
    {
      val shape = AtomicODE(yp, Divide(y, a))
      Try(UnificationMatch.unifiable(shape, ghost)).toOption.flatten match {
        case Some(s) if s(shape) == ghost => return (s(y).asInstanceOf[Variable], s(Divide(Number(1), a)), Number(0))
        case None =>
      }
    }

    // y' = -a/y
    {
      val shape = AtomicODE(yp, Neg(Divide(y, a)))
      Try(UnificationMatch.unifiable(shape, ghost)).toOption.flatten match {
        case Some(s) if s(shape) == ghost =>
          return (s(y).asInstanceOf[Variable], neg(s(Divide(Number(1), a))), Number(0))
        case None =>
      }
    }
    {
      val shape = AtomicODE(yp, Divide(Neg(y), a))
      Try(UnificationMatch.unifiable(shape, ghost)).toOption.flatten match {
        case Some(s) if s(shape) == ghost =>
          return (s(y).asInstanceOf[Variable], neg(s(Divide(Number(1), a))), Number(0))
        case None =>
      }
    }

    // 2 cases contain just b: +b and -b
    // y' = b
    {
      val shape = AtomicODE(yp, b)
      Try(UnificationMatch.unifiable(shape, ghost)).toOption.flatten match {
        case Some(s) if s(shape) == ghost => return (s(y).asInstanceOf[Variable], Number(0), s(b))
        case None =>
      }
    }
    // y' = b
    {
      val shape = AtomicODE(yp, Neg(b))
      Try(UnificationMatch.unifiable(shape, ghost)).toOption.flatten match {
        case Some(s) if s(shape) == ghost => return (s(y).asInstanceOf[Variable], Number(0), neg(s(b)))
        case None =>
      }
    }

    // Two cases contain neither a or b: y'=y and y'=-y
    // y' = y
    {
      val shape = AtomicODE(yp, y)
      Try(UnificationMatch.unifiable(shape, ghost)).toOption.flatten match {
        case Some(s) if s(shape) == ghost => return (s(y).asInstanceOf[Variable], Number(1), Number(0))
        case None =>
      }
    }

    // y' = -y
    {
      val shape = AtomicODE(yp, Neg(y))
      Try(UnificationMatch.unifiable(shape, ghost)).toOption.flatten match {
        case Some(s) if s(shape) == ghost => return (s(y).asInstanceOf[Variable], Number(-1), Number(0))
        case None =>
      }
    }

    // @note last because Darboux assumes shapes guaranteed by unification above
    ToolProvider.algebraTool() match {
      case Some(at) => ghost match {
          case AtomicODE(DifferentialSymbol(lhs), rhs) =>
            val (quotient, remainder) = at.quotientRemainder(rhs, lhs, lhs)
            return (lhs, quotient, remainder)
          case _ =>
        }
      case _ =>
    }

    throw new IllegalArgumentException(
      s"Ghost ${ghost.prettyString} is not of the form y'=a*y+b or y'=a*y or y'=b or y'=a*y-b or y'=y"
    )
  }

  /**
   * @param iniitalConstraints
   * @param x
   *   The variable whose initial value is requested.
   * @return
   *   The initial value of x.
   */
  def initValue(iniitalConstraints: List[Formula], x: Variable): Option[Term] = {
    val initialConditions = conditionsToValues(iniitalConstraints)
    initialConditions.get(x)
  }

  /**
   * Converts formulas of the form x = term into a map x -> term, and ignores all formulas of other forms.
   *
   * @param fs
   *   A list of formulas.
   * @return
   *   A map (f -> term) which maps each f in fs of the foram f=term to term.
   */
  def conditionsToValues(fs: List[Formula]): Map[Variable, Term] = {
    val flattened = FormulaTools.conjuncts(fs)
    val vOnLhs = flattened.map({
      case Equal(left, right) => left match {
          case v: Variable => Some(v, right)
          case _ => None
        }
      case _ => None
    })

    val vOnRhs = flattened.map({
      case Equal(left, right) => right match {
          case v: Variable => Some(v, left)
          case _ => None
        }
      case _ => None
    })

    (vOnLhs ++ vOnRhs).filter(_.isDefined).map(e => e.get._1 -> e.get._2).toMap
  }

  /** Returns true if the ODE is a linear system in dependency order. */
  def isCanonicallyLinear(program: DifferentialProgram): Boolean = {
    var primedSoFar: Set[Variable] = Set()
    atomicOdes(program).forall(ode => {
      val rhsVars = StaticSemantics.freeVars(ode.e).toSet
      val returnValue = if (primedSoFar.intersect(rhsVars).isEmpty) true else false
      primedSoFar = primedSoFar ++ Set(ode.xp.x)
      returnValue
    })
  }

  /**
   * Computes the Lie derivative of the given `term` with respect to the differential equations `ode`. This
   * implementation constructs by DI proof, so will be correct.
   */
  @nowarn("msg=Exhaustivity analysis reached max recursion depth") @nowarn("msg=match may not be exhaustive")
  def lieDerivative(ode: DifferentialProgram, term: Term): Term =
    lieDerivative(ode, Equal(term, Number(0))) match { case Equal(out, Number(n)) if n == 0 => out }
  // @todo performance: could consider replacing this by a direct recursive computation without proof.
  def lieDerivative(ode: DifferentialProgram, fml: Formula): Formula = {
    TactixLibrary
      .proveBy(
        Box(ODESystem(ode, True), fml),
        TactixLibrary.dI(Symbol("diffInd"))(1) <
          (
            TactixLibrary.skip,
            TactixLibrary.Dassignb(1) *
              (StaticSemantics.boundVars(ode).symbols.count(_.isInstanceOf[DifferentialSymbol])),
          ),
      )
      .subgoals(1)
      .succ(0)
  }

  // Simplification with either term simplifier or using simplification tool if available
  def simpWithTool(tool: Option[SimplificationTool], t: Term): Term = {
    tool match {
      case None => termSimp(t, emptyCtx, defaultTaxs)._1
      case Some(tl) => {
        val interp = ToolTactics.interpretedFuncsOf(t).distinct
        val renvar = "SIMP_" // TODO: better to rename free
        val renvari = (0 to interp.length).map(i => Variable(renvar, Some(i)))
        val renames = interp zip renvari
        val tren = renames.foldRight(t)((e, t) => t.replaceAll(e._1, e._2))
        val a = tl.simplify(tren, List())

        renames.foldRight(a)((e, t) => t.replaceAll(e._2, e._1))
      }
    }
  }

  // Computes and simplifies the lie derivative
  // Firstly, it turns all remaining differentials into 0, then it simplifies and strips out things like x^0 = 1
  // The simplifier can't do the last simplification with proof (since 0^0 is nasty)
  def stripConstants(t: Term): Term = {
    t match {
      case v: DifferentialSymbol => { Number(0) }
      case bop: BinaryCompositeTerm => bop.reapply(stripConstants(bop.left), stripConstants(bop.right))
      case uop: UnaryCompositeTerm => uop.reapply(stripConstants(uop.child))
      case _ => t
    }
  }

  def stripPowZero(t: Term): Term = {
    t match {
      case Power(v, n: Number) if n.value.isValidInt && n.value.intValue == 0 => Number(1)
      case bop: BinaryCompositeTerm => bop.reapply(stripPowZero(bop.left), stripPowZero(bop.right))
      case uop: UnaryCompositeTerm => uop.reapply(stripPowZero(uop.child))
      case _ => t
    }
  }

  private def derive(t: Term, odes: Map[BaseVariable, Term]): Term = {
    t match {
      case _: Number => Number(0) // c'=0
      case x: BaseVariable => odes.getOrElse(x, Number(0)) // x'
      case Neg(t) => Neg(derive(t, odes)) // (-e)' = -(e')
      case Times(l, r) => Plus(Times(derive(l, odes), r), Times(l, derive(r, odes))) // (l*r)' = l'r + lr'
      case Power(l, e) => // e is allowed to be symbolic, but is only correctly simplified if it is a number
        e match {
          case n: Number =>
            if (n.value == 1) derive(l, odes)
            else if (n.value == 0) Number(0)
            else Times(Times(n, Power(l, Number(n.value - 1))), derive(l, odes))
          case _ => Times(Times(e, Power(l, Minus(e, Number(1)))), derive(l, odes))
        }
      case Divide(l, r) => // (l/r)' = (l'r - l r')/(r^2)
        Divide(Minus(Times(derive(l, odes), r), Times(l, derive(r, odes))), Times(r, r))
      case Plus(l, r) => // (l+r)' = l'+r'
        Plus(derive(l, odes), derive(r, odes))
      case Minus(l, r) => // (l-r)' = l'-r'
        Minus(derive(l, odes), derive(r, odes))
      case FuncOf(_, Nothing) => Number(0)
      case FuncOf(f @ Function(_, _, _, _, Some(_)), arg) =>
        val dAx = ImplicitAx.getDiffAx(f)
        if (dAx.isEmpty) throw new IllegalArgumentException("Unable to derive: " + t)
        // todo: hardcoded removal of |t_| space
        val concl = dAx.get.provable.conclusion.succ(0).replaceAll("g(|t_|)".asTerm, "g(||)".asTerm)

        // (_)' = _ * (_)'
        val lhs = concl.sub(PosInExpr(0 :: 0 :: 0 :: Nil)).get
        val rhsL = concl.sub(PosInExpr(1 :: 0 :: Nil)).get.asInstanceOf[Term]
        val rhsR = concl.sub(PosInExpr(1 :: 1 :: 0 :: Nil)).get.asInstanceOf[Term]

        val u = RenUSubst(USubst(lhs.asInstanceOf[Term] ~> arg :: Nil))
        Times(u(rhsL), derive(u(rhsR), odes))
      // case FuncOf(_,args) =>
      //  //note: this handles both
      //  // (c())'=0 and
      //  // (f(x,y))' where x,y do not appear in the ODEs
      //  if (StaticSemantics.freeVars(args).intersect(odes.keySet.map(_.asInstanceOf[Variable])).isEmpty)
      //    Number(0)
      //  else throw new IllegalArgumentException("Unable to derive function applied to non-constant arguments: "+t)
      case _ => throw new IllegalArgumentException(
          "Unable to derive: " + t + ". Try expanding all function symbols present in the model."
        )
      // Unimplemented stuff should never be derived
    }
  }

  // Compute the simplified Jacobian of a term with respect to a list of variables
  def simplifiedJacobian(t: Term, vars: List[BaseVariable], tool: Option[SimplificationTool]): List[Term] = {
    vars.map(v => simpWithTool(tool, derive(t, Map(v -> Number(1)))))
  }

  // Compute the simplified Lie derivative of a term with respect to an ODE
  def simplifiedLieDerivative(p: DifferentialProgram, t: Term, tool: Option[SimplificationTool]): Term = {
    val ld = derive(t, DependencyAnalysis.collapseODE(p))
    val ts1 = simpWithTool(tool, ld)
    ts1
  }

  /**
   * Find an ODE of the form {x'=x}
   * @param dp
   *   The differential program to search.
   * @return
   *   The variable x or else nothing.
   */
  def hasExp(dp: DifferentialProgram): Option[Variable] = {
    val expODE = DifferentialHelper
      .atomicOdes(dp)
      .find({
        case AtomicODE(DifferentialSymbol(x1), x2) => x1 == x2 // @todo QE-check x1=x2 instead of syntactic check.
        case _ => false
      })

    expODE match {
      case Some(ode) => Some(ode.xp.x)
      case None => None
    }
  }

  /**
   * Finds an ODE of the form {s'=c,c'=-s}.
   * @param dp
   *   The differential program.
   * @return
   *   ("cos" , "sin") where {sin'=cos, cos=-sin}, or else nothing.
   */
  def hasSinCos(dp: DifferentialProgram): Option[(Variable, Variable)] = {
    val eqns = DifferentialHelper.atomicOdes(dp)

    // Find all equations of the form {x'=-v} for any variable v. Returns a pair (cosVar, sinVar)
    val candidates = eqns
      .filter(p =>
        p.e match {
          case Neg(t) if (t.isInstanceOf[Variable]) => true
          case _ => false
        }
      )
      .map(ode => (ode.xp.x, ode.e.asInstanceOf[Neg].child.asInstanceOf[Variable]))

    // For each of the candidates try to find a corresponding equation of the form {v'=x}
    candidates.find(p => {
      val (cos, sin) = p
      eqns.contains(AtomicODE(DifferentialSymbol(sin), cos))
    })
  }
}
