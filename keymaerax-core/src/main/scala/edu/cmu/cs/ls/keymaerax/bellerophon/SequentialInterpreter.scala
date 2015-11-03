package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.btactics.RenUSubst
import edu.cmu.cs.ls.keymaerax.core.{Sequent, Provable}
import edu.cmu.cs.ls.keymaerax.btactics.{UnificationException, UnificationMatch}

import scala.annotation.tailrec

/**
 * Sequential interpreter for BelleExprs
 * @param listeners Pre- and pos-processing hooks for step-wise tactic execution.
 * @author Nathan Fulton
 */
case class SequentialInterpreter(listeners : Seq[IOListener] = Seq()) extends Interpreter {
  override def apply(expr: BelleExpr, v: BelleValue): BelleValue = {
    listeners.map(_.begin(v, expr))

    val result = expr match {
      case builtIn : BuiltInTactic => v match {
        case BelleProvable(provable) => BelleProvable(builtIn.result(provable))
        case _ => throw BelleError(s"Attempted to apply a built-in tactic to a non-Provable value: ${v.getClass.getName}")
      }
      case BuiltInPositionTactic(_) | BuiltInLeftTactic(_) | BuiltInRightTactic(_) | BuiltInTwoPositionTactic(_) | DependentPositionTactic(_) =>
        throw BelleError(s"Need to instantiate position tactic ($expr) before evaluating with top-level interpreter.")
      case AppliedPositionTactic(positionTactic, pos) => v match {
        case BelleProvable(p) => BelleProvable(positionTactic.computeResult(p, pos))
      }
      case SeqTactic(left, right) => {
        val leftResult = apply(left, v)
        apply(right, leftResult)
      }
      case d : DependentTactic => {
        val valueDependentTactic = d.computeExpr(v)
        apply(valueDependentTactic, v)
      }
      case e : InputTactic[_] => {
        apply(e.computeExpr(), v)
      }
      case PartialTactic(child) => apply(child, v)
      case EitherTactic(left, right) => {
        try {
          val leftResult = apply(left, v)
          (leftResult, left) match {
            case (_, x:PartialTactic) => leftResult
            case (BelleProvable(p), _) if(p.isProved) => leftResult
            case _ => throw BelleError("Non-partials must close proof.")
          }
        }
        catch {
          //@todo catch a little less. Just catching proper tactic exceptions, maybe some ProverExceptions et al., not swallow everything
          case _ => {
            val rightResult = apply(right, v)
            (rightResult, right) match {
              case (_, x:PartialTactic) => rightResult
              case (BelleProvable(p), _) if(p.isProved) => rightResult
              case _ => throw BelleError("Non-partials must close proof.")
            }
            //@todo throw compound exception if neither worked
          }
        }
      }
      case x: SaturateTactic => tailrecSaturate(x, v)
      case BranchTactic(children) => v match {
        case BelleProvable(p) => {
          if(children.length != p.subgoals.length)
            throw BelleError("<(e)(v) is only defined when len(e) = len(v), but " + children.length + "!=" + p.subgoals.length)
          //@todo .inContext(e)

          //Compute the results of piecewise applications of children to provable subgoals.
          val results : Seq[Provable] =
            (children zip p.subgoals) map (pair => {
              val e_i = pair._1
              val s_i = pair._2
              val ithResult =  apply(e_i, bval(s_i))
              ithResult match {
                case BelleProvable(resultingProvable) =>
                  if(resultingProvable.isProved || e_i.isInstanceOf[PartialTactic]) resultingProvable
                  else throw BelleError("Every branching tactic must close its associated goal or else be annotated as a PartialTactic")
                case _ => throw BelleError("Each piecewise application in a Branching tactic should result in a provable.")
              }
            })

          // Compute a single provable that contains the combined effect of all the piecewise computations.
          // The Int is threaded through to keep track of indexes changing, which can occur when a subgoal
          // is replaced with 0 new subgoals.
          val combinedEffect =
            results.foldLeft((p, 0))((op : (Provable, Int), subderivation : Provable) => {
              replaceConclusion(op._1, op._2, subderivation)
            })
          BelleProvable(combinedEffect._1)
        }
        case _ => throw BelleError("Cannot perform branching on a non-provable goal.")
      }
      case DoAll(e) => {
        val provable = v match {
          case BelleProvable(p) => p
          case _ => throw BelleError("Cannot attempt DoAll with a non-Provable value.")
        }
        apply(BranchTactic(Seq.tabulate(provable.subgoals.length)(_ => e)), v)
      }
      case USubstPatternTactic(children) => {
        val provable = v match {
          case BelleProvable(p) => p
          case _ => throw BelleError("Cannot attempt US unification with a non-Provable value.")
        }

        if(provable.subgoals.length != 1)
          throw BelleError("Unification of multi-sequent patterns is not currently supported.")

        //Attempt to find a child that unifies with the input.
        val unification : (UnificationMatch.Subst, RenUSubst => BelleExpr) = children.map(pair => {
          val ty = pair._1
          val expr = pair._2
          ty match {
            case SequentType(s) => try {
              Some((UnificationMatch(s, provable.subgoals.head), expr))
            } catch {
              // in contrast to .unifiable, this suppresses "Sequent un-unifiable Un-Unifiable" message, which clutter STDIO.
              case e: UnificationException => None
            }
            case _ => throw BelleError("Cannot unify non-sequent types.")
          }
          })
          .filter(_.isDefined).map(_.get)
          .headOption.getOrElse(throw BelleError("USubst Pattern Incomplete -- could not find a unifier for any option"))

        apply(unification._2(unification._1.asInstanceOf[RenUSubst]), v)
      }
    }
    listeners.foreach(l => l.end(v, expr, result))
    result
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
   *         * The new index of the (n+1)th goal. //@todo clarify
   * @todo result is undefined. Subderivation rather
   */
  private def replaceConclusion(original: Provable, n: Int, subderivation: Provable): (Provable, Int) = {
    assert(original.subgoals.length > n, s"${n} is a bad index for Provable with ${original.subgoals.length} subgoals: ${original}")
    if(original.subgoals(n) != subderivation.conclusion)
      throw BelleError(s"Subgoal #${n} of the original provable (${original.subgoals(n)}}) should be equal to the conclusion of the subderivation (${subderivation.conclusion}})")
    val newProvable = original(subderivation, n)
    val nextIdx = if(subderivation.isProved) n else n + 1
    (newProvable, nextIdx)
  }
}