/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

/**
 * Uniform Substitution for KeYmaera X
 * @author
 *   Andre Platzer
 * @author
 *   smitsch
 * @see
 *   Andre Platzer.
 *   [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]].
 *   Journal of Automated Reasoning, 59(2), pp. 219-266, 2017.
 * @see
 *   Andre Platzer.
 *   [[https://doi.org/10.1007/978-3-319-21401-6_32 A uniform substitution calculus for differential dynamic logic]]. In
 *   Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin,
 *   Germany, Proceedings, LNCS. Springer, 2015. [[http://arxiv.org/pdf/1503.01981.pdf arXiv 1503.01981]]
 * @see
 *   Andre Platzer. [[https://doi.org/10.1007/978-3-319-94205-6_15 Uniform substitution for differential game logic]].
 *   In Didier Galmiche, Stephan Schulz and Roberto Sebastiani, editors, Automated Reasoning, 9th International Joint
 *   Conference, IJCAR 2018, volume 10900 of LNCS, pp. 211-227. Springer 2018.
 * @see
 *   Andre Platzer. [[https://doi.org/10.1145/2817824 Differential game logic]]. ACM Trans. Comput. Log. 17(1), 2015.
 *   [[http://arxiv.org/pdf/1408.1980 arXiv 1408.1980]]
 * @note
 *   Code Review: 2020-02-17
 */
package org.keymaerax.core

// require favoring immutable Seqs for soundness

import scala.collection.immutable
import SetLattice.bottom
import SetLattice.allVars

/** Admissibility conditions. */
object SubstitutionAdmissibility {

  /**
   * Checks whether the term `t` used as a function/predicate argument is admissible for substitution, i.e., is Nothing,
   * a DotTerm, or composed of only DotTerms.
   */
  def isSubstitutableArg(t: Term): Boolean = t match {
    case Nothing => true
    case _: DotTerm => true
    case Pair(l, r) => isSubstitutableArg(l) && isSubstitutableArg(r)
    case _ => false
  }
}

/**
 * Representation of a substitution replacing `what` with `repl` uniformly, everywhere. Data structure invariant: Only
 * substitutable expressions will be accepted for `what` with compatible `repl`.
 *
 * @param what
 *   the expression to be replaced. `what` can have one of the following forms:
 *   - [[PredOf]](p:[[Function]], [[DotTerm]]/[[Nothing]]/Nested [[Pair]] of [[DotTerm]])
 *   - [[FuncOf]](f:[[Function]], [[DotTerm]]/[[Nothing]]/Nested [[Pair]] of [[DotTerm]])
 *   - [[ProgramConst]] or [[DifferentialProgramConst]] or [[SystemConst]]
 *   - [[UnitPredicational]]
 *   - [[UnitFunctional]]
 *   - [[PredicationalOf]](p:[[Function]], [[DotFormula]])
 *   - [[DotTerm]]
 *   - [[DotFormula]]
 * @param repl
 *   the expression to be used in place of `what`.
 * @requires
 *   what.kind==repl.kind && what.sort==repl.sort && what has an acceptable shape
 * @see
 *   [[USubstOne]]
 * @see
 *   [[USubstChurch]]
 * @see
 *   Andre Platzer.
 *   [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]].
 *   Journal of Automated Reasoning, 59(2), pp. 219-266, 2017.
 * @see
 *   Andre Platzer. [[https://doi.org/10.1007/978-3-030-29436-6_25 Uniform substitution at one fell swoop]]. In Pascal
 *   Fontaine, editor, International Conference on Automated Deduction, CADE'19, Natal, Brazil, Proceedings, volume
 *   11716 of LNCS, pp. 425-441. Springer, 2019.
 */
final case class SubstitutionPair(what: Expression, repl: Expression) {
  insist(
    what.kind == repl.kind,
    "Substitution to same kind of expression (terms for terms, formulas for formulas, programs for programs): " + this +
      " substitutes " + what.kind + " ~> " + repl.kind,
  )
  insist(
    what.sort == repl.sort,
    "Sorts have to match in substitution pairs: " + this + " substitutes " + what.sort + " ~> " + repl.sort,
  )
  assert(
    what match {
      case _: Term => repl.isInstanceOf[Term]
      case _: Formula => repl.isInstanceOf[Formula]
      case _: DifferentialProgram => repl.isInstanceOf[DifferentialProgram]
      case _: Program => repl.isInstanceOf[Program]
      case _ => false
    },
    "(redundant test) substitution to same kind of expression (terms for terms, formulas for formulas, programs for programs) " +
      this + " substitutes " + what.kind + " ~> " + repl.kind,
  )
  insist(noException(matchKey), "Substitutable expression expected: " + this)
  insist(
    what match {
      case sp: SpaceDependent => sp.space match {
          case AnyArg => true
          case Except(taboos) =>
            // @note dtaboos is the taboo variables and associated taboo' in taboos
            val dtaboos = StaticSemantics.spaceTaboos(taboos).toSet

            sp match {
              // @note by previous insists, repl has to be a DifferentialProgram in this case
              case _: DifferentialProgramConst =>
                val vc = StaticSemantics(repl.asInstanceOf[DifferentialProgram])
                vc.fv.intersect(dtaboos).isEmpty && vc.bv.intersect(dtaboos).isEmpty
              // @note by previous insists, repl has to be a Program in this case
              case _: ProgramConst =>
                val vc = StaticSemantics(repl.asInstanceOf[Program])
                vc.fv.intersect(dtaboos).isEmpty && vc.bv.intersect(dtaboos).isEmpty
              // @note by previous insists, repl has to be a Program in this case
              case _: SystemConst =>
                val vc = StaticSemantics(repl.asInstanceOf[Program])
                vc.fv.intersect(dtaboos).isEmpty && vc.bv.intersect(dtaboos).isEmpty &&
                dualFree(repl.asInstanceOf[Program])
              case _: UnitPredicational => StaticSemantics.freeVars(repl).intersect(dtaboos).isEmpty
              case _: UnitFunctional => StaticSemantics.freeVars(repl).intersect(dtaboos).isEmpty
            }
        }
      // only space-dependents have space-compatibility requirements
      case _ => true
    },
    "Space-compatible substitution expected: " + this,
  )

  /** Check whether given program is dual-free, so a hybrid system and not a proper hybrid game. */
  private def dualFree(program: Program): Boolean = program match {
    // ProgramConst could be replaced by a hybrid game
    case a: ProgramConst => false
    // SystemConst can only be replaced by a hybrid program, never a hybrid game
    case a: SystemConst => true
    case Assign(x, e) => true
    case AssignAny(x) => true
    case Test(f) => true /* even if f contains duals, since they're different nested games) */
    case ODESystem(a, h) => true /*|| dualFreeODE(a)*/ /* @note Optimized assuming no differential games */
    case Choice(a, b) => dualFree(a) && dualFree(b)
    case Compose(a, b) => dualFree(a) && dualFree(b)
    case Loop(a) => dualFree(a)
    case Dual(a) => false
    // improper/internal cases
    case _: AtomicODE => true
    case _: DifferentialProduct => true
    case _: DifferentialProgramConst => true
  }

  /**
   * The (new) free variables that this substitution introduces (without DotTerm/DotFormula arguments). That is the
   * (new) free variables introduced by this substitution, i.e. free variables of repl that are not bound as arguments
   * in what.
   * @return
   *   essentially freeVars(repl) except for special handling of UnitFunctional and UnitPredicational arguments.
   * @see
   *   Definition 19 in Andre Platzer.
   *   [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]].
   *   Journal of Automated Reasoning, 59(2), pp. 219-266, 2017.
   * @see
   *   [[StaticSemantics.freeVars(f:edu\.cmu\.cs\.ls\.keymaerax\.core\.Formula):edu\.cmu\.cs\.ls\.keymaerax\.core\.SetLattice[edu\.cmu\.cs\.ls\.keymaerax\.core\.Variable]*]]
   */
  lazy val freeVars: SetLattice[Variable] = what match {
    // @note semantic state-dependent symbols have no free variables.
    case what: StateDependent => what match {
        // unit functionals are like Predicationals
        // predicationals are not function nor predicate symbols
        // DotFormula is a nullary Predicational
        // unit predicationals are nullary Predicationals
        // program constants are always admissible, since their meaning doesn't depend on state
        // DifferentialProgramConst are handled in analogy to program constants, since space-compatibility already checked
        case UnitFunctional(_, _, _) | UnitPredicational(_, _) | PredicationalOf(_, DotFormula) | DotFormula |
            ProgramConst(_, _) | SystemConst(_, _) | DifferentialProgramConst(_, _) => bottom
        case PredicationalOf(_, _) => throw SubstitutionClashException(
            toString,
            "<none>",
            what.toString,
            repl.toString,
            "Nonsubstitutable expression. Already found in matchKey",
          )
      }
    case _ => StaticSemantics.freeVars(repl)
  }

  /**
   * The (new) bound variables that this substitution introduces. That is the (new) bound variables introduces by this
   * substitution, i.e. all bound variables of `repl`. These are all the bound variables of the formula or program
   * `repl` (and irrelevant bottom for terms).
   * @see
   *   [[StaticSemantics.boundVars(a:edu\.cmu\.cs\.ls\.keymaerax\.core\.Program):edu\.cmu\.cs\.ls\.keymaerax\.core\.SetLattice[edu\.cmu\.cs\.ls\.keymaerax\.core\.Variable]*]]
   */
  lazy val boundVars: SetLattice[Variable] = repl match {
    case replf: Formula => StaticSemantics.boundVars(replf)
    case replp: Program => StaticSemantics.boundVars(replp)
    // terms have no bound variables
    case replt: Term => bottom
    // An isolated Function that has not been applied a FuncOf is no Term and has no bound variables
    case replf: Function => bottom
  }

  /**
   * The signature of the replacement introduced by this substitution.
   * @note
   *   DotTerm and DotFormula arguments don't literally occur if bound by p(DotTerm) ~> DotTerm>5
   */
  lazy val signature: immutable.Set[NamedSymbol] = what match {
    case what: ApplicationOf => what match {
        case FuncOf(_, d: DotTerm) => StaticSemantics.signature(repl) - d
        case PredOf(_, d: DotTerm) => StaticSemantics.signature(repl) - d
        case PredicationalOf(_, DotFormula) => StaticSemantics.signature(repl) - DotFormula
        case _ => StaticSemantics.signature(repl)
      }
    case _ => StaticSemantics.signature(repl)
  }

  /**
   * Occurrences of what top-level symbol this SubstitutionPair will be replacing.
   * @return
   *   Function/predicate/predicational or DotTerm or (Differential)ProgramConst whose occurrences we will replace.
   * @note
   *   Data structure invariant: Checks that `what` is a substitutable expression.
   */
  private[core] lazy val matchKey: NamedSymbol = what match {
    case p: UnitPredicational => p
    case f: UnitFunctional => f
    case a: ProgramConst => a
    case a: SystemConst => a
    case a: DifferentialProgramConst => a
    case PredOf(p: Function, arg) if !p.interpreted && SubstitutionAdmissibility.isSubstitutableArg(arg) => p
    case FuncOf(f: Function, arg) if !f.interpreted && SubstitutionAdmissibility.isSubstitutableArg(arg) => f
    case PredicationalOf(p: Function, DotFormula) if !p.interpreted => p
    case d: DotTerm => d
    case DotFormula => DotFormula
    case Nothing =>
      assert(repl == Nothing, "can replace Nothing only by Nothing, and nothing else");
      Nothing // it makes no sense to substitute Nothing
    case _ =>
      throw SubstitutionClashException(toString, "<none>", what.toString, repl.toString, "Nonsubstitutable expression")
  }

  /**
   * Check whether we match on the term other, i.e. both have the same head so the occurrence in other should be
   * replaced according to this SubstitutionPair.
   */
  private[core] def sameHead(other: ApplicationOf): Boolean = what match {
    case FuncOf(lf, arg) =>
      // redundant: assert(SubstitutionAdmissibility.isSubstitutableArg(arg), "Only DotTerm/Nothing allowed as argument")
      other match {
        case FuncOf(rf, _) => lf == rf
        case _ => false
      }
    case PredOf(lf, arg) =>
      // redundant: assert(SubstitutionAdmissibility.isSubstitutableArg(arg), "Only DotTerm/Nothing allowed as argument")
      other match {
        case PredOf(rf, _) => lf == rf
        case _ => false
      }
    case PredicationalOf(lf, arg) =>
      // redundant: assert(arg match { case DotFormula => true case _ => false }, "Only DotFormula allowed as argument")
      other match {
        case PredicationalOf(rf, _) => lf == rf
        case _ => false
      }
    case _ => assert(false, "sameHead only used for ApplicationOf"); false
  }

  override def toString: String = "(" + what.prettyString + "~>" + repl.prettyString + ")"
}
