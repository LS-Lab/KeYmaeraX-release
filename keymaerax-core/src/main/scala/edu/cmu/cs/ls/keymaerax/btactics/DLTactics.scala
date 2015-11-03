package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.ProofRuleTactics._
import edu.cmu.cs.ls.keymaerax.core._

/**
 * The tactic library [[DLTactics]] provides tactics for box/diamond properties over hybrid programs.
 */
object DLTactics {
  /**
   * Box monotonicity.
   * {{{
   *      p |- q
   *   -------------monb
   *   [a]p |- [a]q
   * }}}
   * @return The tactic.
   */
  def monb: DependentTactic = new DependentTactic("[] monotone") {
    override def computeExpr(v: BelleValue): BelleExpr = v match {
      case BelleProvable(provable) =>
        require(provable.subgoals.size == 1, "Expected sole open goal, but got " + provable.subgoals.size + " open goals")
        val sequent = provable.subgoals.head
        require(sequent.ante.length == 1 && sequent.succ.length == 1, "Expected 1 antecedent formula and 1 succedent formula")
        sequent.ante.head match {
          case Box(a, p) => sequent.succ.head match {
            case Box(b, q) if a == b =>
              val aX = ProgramConst("a_")
              val pX = Function("p_", None, Real, Bool)
              val qX = Function("q_", None, Real, Bool)
              val s = USubst(SubstitutionPair(aX, a) ::
                SubstitutionPair(PredOf(pX, Anything), p) ::
                SubstitutionPair(PredOf(qX, Anything), q) :: Nil)
              axiomatic("[] monotone", s)
            case Box(b, q) if a != b => throw new BelleError("Expected sole box property [a]q in succedent, matching [a]p from antecedent, but " +
              "got program " + a + " in antecedent and non-matching program " + b + " in succedent")
            case _ => throw new BelleError("Expected sole box property [a]q in succedent, matching [a]p from antecedent, but got " + sequent.succ.head)
          }
          case _ => throw new BelleError("Expected sole box property [a]p in antecedent, but got " + sequent.ante.head)
        }
    }
  }

  /**
   * Diamond monotonicity.
   * {{{
   *      p |- q
   *   -------------mond
   *   <a>p |- <a>q
   * }}}
   * @return The tactic.
   */
  def mond: DependentTactic = new DependentTactic("<> monotone") {
    override def computeExpr(v: BelleValue): BelleExpr = v match {
      case BelleProvable(provable) =>
        require(provable.subgoals.size == 1, "Expected sole open goal, but got " + provable.subgoals.size + " open goals")
        val sequent = provable.subgoals.head
        require(sequent.ante.length == 1 && sequent.succ.length == 1, "Expected 1 antecedent formula and 1 succedent formula")
        sequent.ante.head match {
          case Diamond(a, p) => sequent.succ.head match {
            case Diamond(b, q) if a == b =>
              val aX = ProgramConst("a_")
              val pX = Function("p_", None, Real, Bool)
              val qX = Function("q_", None, Real, Bool)
              val s = USubst(SubstitutionPair(aX, a) ::
                SubstitutionPair(PredOf(pX, Anything), p) ::
                SubstitutionPair(PredOf(qX, Anything), q) :: Nil)
              axiomatic("<> monotone", s)
            case Diamond(b, q) if a != b => throw new BelleError("Expected sole diamond property <a>q in succedent, matching <a>p from antecedent, but " +
              "got program " + a + " in antecedent and non-matching program " + b + " in succedent")
            case _ => throw new BelleError("Expected sole diamond property <a>q in succedent, matching <a>p from antecedent, but got " + sequent.succ.head)
          }
          case _ => throw new BelleError("Expected sole diamond property <a>p in antecedent, but got " + sequent.ante.head)
        }
    }
  }
}
