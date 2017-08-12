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

/**
  * Approximations
  * More Ideas:
  *     - Add more functions: exp,ln,etc.
  *     - Pre-processing -- add time var, auto base tactics instead of assuming already in domain constraint, t_0=0, etc.
  *     - Post-processing -- after reducing the arithmetic, hide all approximate terms except the last one.
  *       It might even be possible to do this during the tactic by remving all but the most recent <= and >=, but I'm
  *       not sure if that's true for any/all expansions.
  *     - Generalized tactics. Not sure this makes much sense though.
  * @author Nathan Fulton
  */
object Approximator {
  /** Debugging for the Approximator. */
  val ADEBUG = true

  /** Cuts in Taylor approixmations for circular dynamics {{{x'=y,y'=-x}}}. */
  def taylorCircular(s: Variable, c: Variable, n: Number) =
    new DependentPositionWithAppliedInputTactic("taylorCircular", s::c::n::Nil) {
      override def factory(pos: Position): DependentTactic = {
        val tactic = {
          anon((sequent: Sequent) => sequent.apply(pos.topLevel) match {
            case m: Modal => {
              assert(m.program.isInstanceOf[ODESystem], s"Expected a differential program but found ${m.program.prettyString}")
              //Find the time variable.
              val t = timeVar(m.program.asInstanceOf[ODESystem].ode) match {
                case Some(v) => v
                case None => throw new BelleFriendlyUserMessage(s"${this.name} expects and ODE with a time variable already introduced (i.e., t'=1 expected but not found in ODE)")
              }

              //Get the number of terms we should expand.
              val N = n.value.toInt
              assert(N >= 0, s"${this.name} expects a non-negative number as its 3rd argument (# of terms to expand the Taylor series.)")

              //Compute th series of cuts.
              //@todo alternate inequalities in each sequence.
              val sinCuts = Range(0, N).map(i =>
                if(i % 2 == 0) LessEqual(s, taylorSin(t, i))
                else GreaterEqual(s, taylorSin(t, i))
              )
              val cosCuts = Range(0, N).map(i =>
                if(i % 2 == 0) LessEqual(c, taylorCos(t, i))
                else GreaterEqual(c, taylorCos(t,i))
              )

              val cuts = interleave(sinCuts, cosCuts)
              if(ADEBUG) println(s"Taylor Approximator performing these cuts: ${cuts.mkString("\n")}")

              //Construct a tactic that interleaves these cuts.
              val cutTactics : Seq[BelleExpr] =
                cuts.map(cut =>
                  TactixLibrary.dC(cut)(pos) <(
                    TactixLibrary.dI()(pos)
                    ,
                    nil
                  ) & DebuggingTactics.debug(s"Successfully cut ${cut}", ADEBUG)
                )
              cutTactics.reduce(_ & _)
            }
          })
        }
        tactic
      }

    }

  //region Definitions of series.

  /** The nth term of a Taylor series approximation of sin(t) */
  private def taylorCosTerm(t: Term, n: Int):Term = {
    assert(n >= 0, "Series are 0-indexed.")
    if(n == 0) "1".asTerm
    else if(n % 2 == 0) s"${t.prettyString}^${2*n}/${fac(2*n)}".asTerm
    else s"-${t.prettyString}^${2*n}/${fac(2*n)}".asTerm
  }
  private def taylorCos(t: Term, N: Int) = Range(0,N+1).map(taylorCosTerm(t,_)).reduce(Plus.apply)

  /** The nth term of a Taylor series approximation of cos(t) */
  private def taylorSinTerm(t: Term, n: Int):Term =
    if(n == 0) t
    else if(n % 2 == 0) s"${t.prettyString}^${2*n+1}/${fac(2*n+1)}".asTerm
    else s"-${t.prettyString}^${2*n+1}/${fac(2*n+1)}".asTerm
  private def taylorSin(t: Term, N: Int) = Range(0,N+1).map(taylorSinTerm(t,_)).reduce(Plus.apply)

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

  private def timeVarInModality(e:Expression) = e match {
    case m:Modal => m.program match {
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
