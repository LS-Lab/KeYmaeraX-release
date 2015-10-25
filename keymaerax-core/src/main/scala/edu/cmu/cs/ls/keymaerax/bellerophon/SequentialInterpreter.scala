package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.core.{Sequent, Provable}

import scala.annotation.tailrec

/**
 * Sequential interpreter for
 * @param listeners todo -- this is intended as an extension point for things like :
 *                  * the forward/backward debugger
 *                  * GUI view updates
 *                  * History recording
 *                  but I'm not sure how these are going to work yet.
 * @author Nathan Fulton
 */
case class SequentialInterpreter(listeners : Seq[((BelleExpr, BelleValue) => _)] = Seq()) extends Interpreter {
  override def apply(expr: BelleExpr, v: BelleValue): BelleValue = {
    listeners.foreach(f => f(expr, v))
    expr match {
      case builtIn : BuiltInTactic => v match {
        case BelleProvable(provable) => BelleProvable(builtIn.result(provable))
        case _ => throw BelleError(s"Attempted to apply a built-in tactic to a non-Provable value: ${v.getClass.getName}")
      }
      case BuiltInPositionTactic(_) | BuiltInLeftTactic(_) | BuiltInRightTactic(_) | BuiltInTwoPositionTactic(_) =>
        throw BelleError(s"Need to instantiate position tactic ($expr) before evaluating with top-level interpreter.")
      case SeqTactic(left, right) => {
        val leftResult = apply(left, v)
        apply(right, leftResult)
      }
      case EitherTactic(left, right) => {
        try {
          apply(left, v)
        }
        catch {
          case e : BelleError => apply(right, v)
          case _ => apply(right, v)
        }
      }
      case x: SaturateTactic => tailrecSaturate(x, v)
      case BranchTactic(children) => v match {
        case BelleProvable(p) => {
          if(children.length != p.subgoals.length)
            throw BelleError("<(e)(v) is only defined when len(e) = len(v).")

          //Compute the results of piecewise applications of children to provable subgoals.
          val results : Seq[Provable] =
            (children zip p.subgoals) map (pair => {
              val e_i = pair._1
              val s_i = pair._2
              apply(e_i, bval(s_i)) match {
                case BelleProvable(resultingProvable) => resultingProvable
                case _ => throw BelleError("Each piecewise application in a Branching tactic should result in a provable.")
              }
            })

          // Compute a single provable that contains the combined effect of all the piecewise computations.
          // The Int is threaded through to keep track of indexes changing.
          val combinedEffect =
            results.foldLeft((p, 0))((op : (Provable, Int), subderivation : Provable) => {
              replaceConclusion(op._1, op._2, subderivation)
            })
          BelleProvable(combinedEffect._1)
        }
        case _ => throw BelleError("Cannot perform branching on a non-provable goal.")
      }
    }
  }

  @tailrec
  private def tailrecSaturate(e : SaturateTactic, v: BelleValue): BelleValue = {
    val step = apply(e.child, v) //@todo effect on listeners etc.
    if(step == v) v
    else tailrecSaturate(e, step)
  }

  /** Maps sequents to BelleProvables. */
  private def bval(s: Sequent) = BelleProvable(Provable.startProof(s))

  /**
   * Replaces the nth subgoal of original with the remaining subgoals of result.
   * @param original A Provable whose nth subgoal is equal to "result".
   * @param n The numerical index of the subgoal of original to rewrite (Seqs are zero-indexed)
   * @param subderivation
   * @return A pair of:
   *         * A new provable that is identical to original, except that the nth subgoal is replaced with the remaining subgoals of result; and
   *         * The new index of the (n+1)th goal.
   */
  private def replaceConclusion(original: Provable, n: Int, subderivation: Provable): (Provable, Int) = {
    assert(original.subgoals.length > n, s"${n} is a bad index for ${original}")
    assert(original.subgoals(n) == subderivation.conclusion, s"The nth subgoal of ${original} should be equal to the conclusion of ${subderivation}")
    val newProvable = original(subderivation, n)
    (newProvable, n + subderivation.subgoals.length)
  }
}