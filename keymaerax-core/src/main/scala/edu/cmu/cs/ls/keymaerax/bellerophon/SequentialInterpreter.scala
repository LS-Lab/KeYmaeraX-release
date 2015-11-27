package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.btactics.RenUSubst
import edu.cmu.cs.ls.keymaerax.core.{Sequent, Provable}
import edu.cmu.cs.ls.keymaerax.btactics.{UnificationException, UnificationMatch}

/**
 * Sequential interpreter for BelleExprs
 * @param listeners Pre- and pos-processing hooks for step-wise tactic execution.
 * @author Nathan Fulton
 */
case class SequentialInterpreter(listeners : Seq[IOListener] = Seq()) extends Interpreter {
  override def apply(expr: BelleExpr, v: BelleValue): BelleValue = {
    listeners.foreach(_.begin(v, expr))

    val result = expr match {
      case builtIn : BuiltInTactic => v match {
        case BelleProvable(pr) => try { BelleProvable(builtIn.execute(pr)) } catch { case e: BelleError => throw e.inContext(BelleDot, pr.prettyString) }
        case _ => throw new BelleError(s"Attempted to apply a built-in tactic to a non-Provable value: ${v.getClass.getName}").inContext(BelleDot, "")
      }
      case BuiltInPositionTactic(_) | BuiltInLeftTactic(_) | BuiltInRightTactic(_) | BuiltInTwoPositionTactic(_) | DependentPositionTactic(_) =>
        throw new BelleError(s"Need to instantiate position tactic ($expr) before evaluating with top-level interpreter.").inContext(expr, "")
      case positionTactic@AppliedPositionTactic(_, pos) => v match {
        case BelleProvable(pr) => try { BelleProvable(positionTactic.computeResult(pr)) } catch { case e: BelleError => throw e.inContext(positionTactic, pr.prettyString) }
      }
      case positionTactic@AppliedTwoPositionTactic(_, posOne, posTwo) => v match {
        case BelleProvable(pr) => try { BelleProvable(positionTactic.computeResult(pr)) } catch { case e: BelleError => throw e.inContext(positionTactic, pr.prettyString) }
      }
      case SeqTactic(left, right, location) =>
        val leftResult = try { apply(left, v) } catch {case e: BelleError => throw e.inContext(SeqTactic(e.context, right, location), "Failed left-hand side of &: " + left)}
        try { apply(right, leftResult) } catch {case e: BelleError => throw e.inContext(SeqTactic(left, e.context, location), "Failed right-hand side of &: " + right)}
      case d : DependentTactic => try {
        val valueDependentTactic = d.computeExpr(v)
        apply(valueDependentTactic, v)
      } catch { case e: BelleError => throw e.inContext(d.toString, v.prettyString) }
      case e : InputTactic[_] => try {
        apply(e.computeExpr(), v)
      } catch { case e: BelleError => throw e.inContext(e.toString, v.prettyString) }
      case PartialTactic(child) => try { apply(child, v) } catch {case e: BelleError => throw e.inContext(PartialTactic(e.context), "Failed partial child: " + child) }
      case EitherTactic(left, right, location) => try {
          val leftResult = apply(left, v)
          (leftResult, left) match {
            case (BelleProvable(p), _) if p.isProved => leftResult
            case (_, x: PartialTactic) => leftResult
            case _ => throw new BelleError("Non-partials must close proof.").inContext(EitherTactic(BelleDot, right, location), "Failed left-hand side of |:" + left)
          }
        } catch {
          //@todo catch a little less. Just catching proper tactic exceptions, maybe some ProverExceptions et al., not swallow everything
          case eleft: BelleError =>
            val rightResult = try { apply(right, v) } catch {case e: BelleError => throw new CompoundException(eleft, e).inContext(EitherTactic(eleft.context, e.context, location), "Failed: both left-hand side and right-hand side " + expr)}
            (rightResult, right) match {
              case (_, x:PartialTactic) => rightResult
              case (BelleProvable(p), _) if p.isProved => rightResult
              case _ => throw new BelleError("Non-partials must close proof.").inContext(EitherTactic(left, BelleDot, location), "Failed right-hand side of |: " + right)
            }
        }
      case SaturateTactic(child, annotation, location) =>
        var prev: BelleValue = null
        var result: BelleValue = v
        var rep = 1
        do {
          prev = result
          //@todo effect on listeners etc.
          try { result = apply(child, result) } catch {case e: BelleError => throw e.inContext(SaturateTactic(e.context, annotation, location), "Failed * saturation on repetition " + rep + ": " + child)}
          rep += 1
        } while (result != prev)
        result
      case RepeatTactic(child, times, annotation, location) => try {
        var result = v
        for (i <- 1 to times) try { result = apply(child, result) } catch {case e: BelleError => throw e.inContext(RepeatTactic(e.context, times, annotation, location), "Failed on repetition " + i + " of " + times + ": " + child)}
        result
      }
      case BranchTactic(children, location) => v match {
        case BelleProvable(p) =>
          if(children.length != p.subgoals.length)
            throw new BelleError("<(e)(v) is only defined when len(e) = len(v), but " + children.length + "!=" + p.subgoals.length).inContext(expr, "")
          //Compute the results of piecewise applications of children to provable subgoals.
          val results : Seq[Provable] =
            (children zip p.subgoals) map (pair => {
              val e_i = pair._1
              val s_i = pair._2
              val ithResult =  try { apply(e_i, bval(s_i)) } catch {case e: BelleError => throw e.inContext(BranchTactic(children.map(c => if (c != e_i) c else e.context), location), "Failed on branch " + e_i)}
              ithResult match {
                case BelleProvable(resultingProvable) =>
                  if(resultingProvable.isProved || e_i.isInstanceOf[PartialTactic]) resultingProvable
                  else throw new BelleError("Every branching tactic must close its associated goal or else be annotated as a PartialTactic").inContext(expr, "")
                case _ => throw new BelleError("Each piecewise application in a Branching tactic should result in a provable.").inContext(expr, "")
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
        case _ => throw new BelleError("Cannot perform branching on a goal that is not a BelleValue of type Provable.").inContext(expr, "")
        }
      case DoAll(e, location) =>
        val provable = v match {
          case BelleProvable(p) => p
          case _ => throw new BelleError("Cannot attempt DoAll with a non-Provable value.").inContext(expr, "")
        }
        //@todo actually it would be nice to throw without wrapping inside an extra BranchTactic context
        try { apply(BranchTactic(Seq.tabulate(provable.subgoals.length)(_ => e), location), v) } catch {case e: BelleError => throw e.inContext(DoAll(e.context, location), "") }
      case t@USubstPatternTactic(children, location) => {
        val provable = v match {
          case BelleProvable(p) => p
          case _ => throw new BelleError("Cannot attempt US unification with a non-Provable value.").inContext(expr, "")
        }

        if(provable.subgoals.length != 1)
          throw new BelleError("Unification of multi-sequent patterns is not currently supported.").inContext(expr, "")

        //@todo loop through all using the first one whose unificatoin and tactic application ends up being successful as opposed to committing to first unifiable case.
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
            case _ => throw new BelleError("Cannot unify non-sequent types.").inContext(t, "")
          }
          })
          .filter(_.isDefined).map(_.get)
          .headOption.getOrElse(throw new BelleError("USubst Pattern Incomplete -- could not find a unifier for any option").inContext(t, ""))

        apply(unification._2(unification._1.asInstanceOf[RenUSubst]), v)
      }
    }

    listeners.foreach(l => l.end(v, expr, result))
    result
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
    assert(original.subgoals.length > n, s"$n is a bad index for Provable with ${original.subgoals.length} subgoals: $original")
    if(original.subgoals(n) != subderivation.conclusion)
      throw new BelleError(s"Subgoal #$n of the original provable (${original.subgoals(n)}}) should be equal to the conclusion of the subderivation (${subderivation.conclusion}})")
    val newProvable = original(subderivation, n)
    val nextIdx = if(subderivation.isProved) n else n + 1
    (newProvable, nextIdx)
  }
}