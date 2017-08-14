 /*
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.btactics.helpers.DifferentialHelper

/**
  * Approximations
  * More Ideas:
  *     - Allow approximations at non-top-level.
  *     - Pre-processing -- add time var w/ t_0=0, etc.
  *     - Post-processing -- after reducing the arithmetic, hide all approximate terms except the last one.
  *       It might even be possible to do this during the tactic by remving all but the most recent <= and >=, but I'm
  *       not sure if that's true for any/all expansions.
  *     - Generalized tactics. Not sure this makes much sense though.
  * @author Nathan Fulton
  */
object Approximator {
  /** Debugging for the Approximator. */
  val ADEBUG = true

  //region The [[approximate]] tactic with helpers for figuring out which approximation to use.

  /**
    * Approximates the variable {{{t}}} in the ODE up to the {{{n^th}}} term.
    * @param n The number of terms to expand the series/
    * @return
    */
  def approximate(n: Number) = new DependentPositionWithAppliedInputTactic("approximate", n::Nil) {
    override def factory(pos: Position): DependentTactic = anon((sequent: Sequent) => sequent.sub(pos) match {
      case m:Modal if(m.program.isInstanceOf[ODESystem]) => {
        val system = m.program.asInstanceOf[ODESystem]
        val t = timeVar(system.ode)

        hasExp(system.ode) match {
          case Some(v) => expApproximation(v, n)(pos)
          case None    => TactixLibrary.debug("Auto-Sin/Cos approximate is not implemented yet.")
        }
      }
      case _ => throw new BelleFriendlyUserMessage(s"approximate should only be called on positions of form [{ODE}]P")
    })
  }

  private def hasExp(dp: DifferentialProgram): Option[Variable] = {
    val expODE = DifferentialHelper.atomicOdes(dp).find(_ match {
        case AtomicODE(DifferentialSymbol(x1), x2) if(x1.equals(x2)) => true //@todo QE-check x1=x2 instead of syntactic check.
        case _ => false
      })

    expODE match {
      case Some(ode) => Some(ode.xp.x)
      case None => None
    }
  }

  /**
    * Finds an ODE of the form {s'=c,c'=-s}.
    * @param dp The differential program.
    * @return (cos variable, sin variable)
    */
  private def hasSinCos(dp: DifferentialProgram): Option[(Variable, Variable)] = {
    val eqns = DifferentialHelper.atomicOdes(dp)

    //Find all equations of the form {x'=-v} for any variable v. Returns a pair (cosVar, sinVar)
    val candidates = eqns
      .filter(p => p.e match {
        case Neg(t) if(t.isInstanceOf[Variable]) => true
        case _ => false
      })
      .map(ode => (ode.xp.x, ode.e.asInstanceOf[Neg].child.asInstanceOf[Variable]) )

    //For each of the candidates try to find a corresponding equation of the form {v'=x}
    candidates.find(p => {
        val (cos,sin) = p
        eqns.contains(AtomicODE(DifferentialSymbol(sin), cos))
    })
  }

  //endregion

  //region Approximation for {{{e'=e}}}

  def expApproximation(e: Variable, n: Number) =
    new DependentPositionWithAppliedInputTactic("expApproximation", e::n::Nil) {
      override def factory(pos: Position): DependentTactic = {
        anon((sequent: Sequent) => {
          val t = timeVarInModality(sequent.apply(pos.topLevel))

          val N = n.value.toInt
          assert(N >= 0, s"${this.name} expects a non-negative number as its 3rd argument (# of terms to expand the Taylor series.)")

          val cuts = Range(0,N).map(i => GreaterEqual(e, expExpansion(t,i)))

          if(ADEBUG) println(s"exp approximator performing these cuts:\n\t ${cuts.mkString("\n\t")}")

          val cutTactics: Seq[BelleExpr] =
            cuts.map(cut =>
              TactixLibrary.dC(cut)(pos) < (
                nil,
                DebuggingTactics.debug("Trying to prove this by dI or by ODE", ADEBUG) &
                //dI handles the normal case, ODE handles the base case.
                (TactixLibrary.dI()(pos) | TactixLibrary.ODE(pos)) & DebuggingTactics.done("Expected dI to succeed.")
              ) & DebuggingTactics.assertProvableSize(1) & DebuggingTactics.debug(s"Successfully cut ${cut}", ADEBUG)
            )
          DebuggingTactics.debug(s"Beginning expApproximation on ${e.prettyString}, ${n.prettyString}", ADEBUG) & cutTactics.reduce(_ & _)
        })
      }
    }

  /** Cuts in Taylor approixmations for circular dynamics {{{x'=y,y'=-x}}}.
    * @todo Handle the first two cuts
    * @todo Good error messages for when the first cut or two fail ==> "missing assumptions." */
  def taylorCircular(s: Variable, c: Variable, n: Number) =
    new DependentPositionWithAppliedInputTactic("taylorCircular", s::c::n::Nil) {
      override def factory(pos: Position): DependentTactic = {
        anon((sequent: Sequent) => {
          val t = timeVarInModality(sequent.apply(pos.topLevel))

          //Get the number of terms we should expand.
          val N = n.value.toInt
          assert(N >= 0, s"${this.name} expects a non-negative number as its 3rd argument (# of terms to expand the Taylor series.)")

          //Compute the series of cuts.
          val sinCuts = Range(0, N).map(i =>
            if (i % 2 == 0) LessEqual(s, taylorSin(t, i))
            else GreaterEqual(s, taylorSin(t, i))
          )
          val cosCuts = Range(0, N).map(i =>
            if (i % 2 == 0) LessEqual(c, taylorCos(t, i))
            else GreaterEqual(c, taylorCos(t, i))
          )

          //Prove that (c,s) is a circle. @todo allow for any radius.
          val isOnCircle = TactixLibrary.dC("s^2 + c^2 = 1".asFormula)(pos) < (
            nil
            ,
            TactixLibrary.dI()(pos) & DebuggingTactics.done("Expected dI to succeed")
          ) & DebuggingTactics.assertProvableSize(1) & DebuggingTactics.debug(s"Successfully cut isOnCircle", ADEBUG)

          val cuts = interleave(cosCuts, sinCuts)
          if (ADEBUG) println(s"Taylor Approximator performing these cuts: ${cuts.mkString("\n")}")

          //Construct a tactic that interleaves these cuts.
          val cutTactics: Seq[BelleExpr] =
            cuts.map(cut =>
              TactixLibrary.dC(cut)(pos) < (
                nil
                ,
                //dW&QE handles the base case, dI handles all others.
                DebuggingTactics.debug("Trying to prove next bound: ", ADEBUG) & (TactixLibrary.dI()(pos) | (TactixLibrary.dW(pos)&QE)) & DebuggingTactics.done("Expected dI to succeed")
              ) & DebuggingTactics.assertProvableSize(1) & DebuggingTactics.debug(s"Successfully cut ${cut}", ADEBUG)
            )

          isOnCircle & cutTactics.reduce(_ & _)
        })
      }
    }

  //region Definitions of series.

  /** The nth term of a Taylor series approximation of sin(t) */
  private def taylorCos(t: Term, N: Int) = sumTerms(t, taylorCosTerm, N)
  private def taylorCosTerm(t: Term, n: Int):Term = {
    assert(n >= 0, "Series are 0-indexed.")
    if(n == 0) "1".asTerm
    else if(n % 2 == 0) s"${t.prettyString}^${2*n}/${fac(2*n)}".asTerm
    else s"-${t.prettyString}^${2*n}/${fac(2*n)}".asTerm
  }

  /** The nth term of a Taylor series approximation of cos(t) */
  private def taylorSin(t: Term, N: Int) = sumTerms(t, taylorSinTerm, N)
  private def taylorSinTerm(t: Term, n: Int):Term =
    if(n == 0) t
    else if(n % 2 == 0) s"${t.prettyString}^${2*n+1}/${fac(2*n+1)}".asTerm
    else s"-${t.prettyString}^${2*n+1}/${fac(2*n+1)}".asTerm


  private def expExpansion(t: Term, N: Int):Term = sumTerms(t, ithExpTerm, N)
  private def ithExpTerm(t: Term, n: Int):Term =
    if(n == 0) Number(1)
    else if(n == 1) t //We don't need these two special cases but it keeps things readable.
    else Divide(Power(t, Number(n)), Number(fac(n)))

  private def sumTerms(t: Term, ithTerm : (Term,Int) => Term, N: Int) = Range(0,N+1).map(ithTerm(t,_)).reduce(Plus.apply)

  //endregion


  //region Generic helper functions that should be replaced by library implementations.

  //@todo replace with built-in

  private def fac(n: Int):Int = {
    assert(n>0)
    if(n == 1) 1
    else n * fac(n-1)
  }

  /** Interleaves A with B: A_0 B_0 A_1 B_1 ... A_n B_n */
  private def interleave[T](A : Seq[T], B: Seq[T]) = {
    assert(A.length == B.length, "Cannot interleave sequences of uneven length.")
    Range(0, 2*A.length).map(i =>
      if(i % 2 == 0) A(i/2)
      else B((i-1)/2)
    )
  }

  private def timeVar(ode: DifferentialProgram) : Option[Variable] = ode match {
    case AtomicODE(xp, e) => if(e.equals(Number(1))) Some(xp.x) else None
    case DifferentialProduct(l,r) => timeVar(l) match {
      case Some(t) => Some(t)
      case None => timeVar(r)
    }
  }

  private def timeVarInModality(e:Option[Expression]) = e match {
    case None => throw new BelleFriendlyUserMessage("Approximator was given a non-existent position.")
    case Some(m) if m.isInstanceOf[Modal] => m.asInstanceOf[Modal].program match {
      case ODESystem(ode,child) => timeVar(ode) match {
        case Some(t) => t
        case None => throw new BelleFriendlyUserMessage("Approximation tactics require existence of an explicit time variable; i.e., expected to find t'=1 in the ODE but no such t was found.")
      }
      case _ => throw new BelleFriendlyUserMessage("Approximation tactics should only be applied to modalities containing ODEs in the top level")
    }
    case _ => throw new BelleFriendlyUserMessage("Approximation tactics should only be applied to modalities")
  }

  //endregion
}
