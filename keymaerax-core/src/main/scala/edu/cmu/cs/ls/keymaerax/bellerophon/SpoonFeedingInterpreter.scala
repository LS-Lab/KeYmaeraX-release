/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.core._

/**
  * Sequential interpreter for Bellerophon tactic expressions: breaks apart combinators and spoon-feeds "atomic" tactics
  * to another interpreter.
  * @param listeners Creates listeners from tactic names.
  * @param inner Processes atomic tactics.
  * @author Nathan Fulton
  * @author Andre Platzer
  * @author Stefan Mitsch
  */
case class SpoonFeedingInterpreter(listeners: (String, Int) => Seq[IOListener], inner: Seq[IOListener] => Interpreter) extends Interpreter {
  override def apply(expr: BelleExpr, v: BelleValue): BelleValue = apply(expr, v, 0)

  def apply(expr: BelleExpr, v: BelleValue, branch: Int): BelleValue = {
    expr match {
      case SeqTactic(left, right) =>
        val leftResult = try {
          apply(left, v, branch)
        } catch {
          case e: BelleError => throw e.inContext(SeqTactic(e.context, right), "Failed left-hand side of &: " + left)
        }
        try {
          apply(right, leftResult, branch)
        } catch {
          case e: BelleError => throw e.inContext(SeqTactic(left, e.context), "Failed right-hand side of &: " + right)
        }
      case EitherTactic(left, right) => try {
        val leftResult = apply(left, v, branch)
        (leftResult, left) match {
          case (BelleProvable(p, _), _) /*if p.isProved*/ => leftResult
          case (_, x: PartialTactic) => leftResult
          case _ => throw new BelleError("Tactics must close their proof unless declared as partial. Use \"t partial\" instead of \"t\".").inContext(EitherTactic(BelleDot, right), "Failed left-hand side of |:" + left)
        }
      } catch {
        //@todo catch a little less. Just catching proper tactic exceptions, maybe some ProverExceptions et al., not swallow everything
        case eleft: BelleError =>
          val rightResult = try {
            apply(right, v, branch)
          } catch {
            case e: BelleError => throw e.inContext(EitherTactic(eleft.context, e.context), "Failed: both left-hand side and right-hand side " + expr)
          }
          (rightResult, right) match {
            case (BelleProvable(p, _), _) /*if p.isProved*/ => rightResult
            case (_, x: PartialTactic) => rightResult
            case _ => throw new BelleError("Tactics must close their proof unless declared as partial. Use \"t partial\" instead of \"t\".").inContext(EitherTactic(left, BelleDot), "Failed right-hand side of |: " + right)
          }
      }
      case SaturateTactic(child) =>
        var prev: BelleValue = null
        var result: BelleValue = v
        do {
          prev = result
          //@todo effect on listeners etc.
          try {
            result = apply(child, result, branch)
          } catch {
            case e: BelleError => /*@note child no longer applicable */ result = prev
          }
        } while (result != prev)
        result
      case RepeatTactic(child, times) =>
        var result = v
        for (i <- 1 to times) try {
          result = apply(child, result, branch)
        } catch {
          case e: BelleError => throw e.inContext(RepeatTactic(e.context, times),
            "Failed while repating tactic " + i + "th iterate of " + times + ": " + child)
        }
        result
      case BranchTactic(children) => v match {
        case BelleProvable(p, labels) =>
          if (children.length != p.subgoals.length)
            throw new BelleError("<(e)(v) is only defined when len(e) = len(v), but " + children.length + "!=" + p.subgoals.length).inContext(expr, "")
          children.foldLeft((v, p.subgoals.length, branch))({ case ((vv, numBranches, branchIdx), tactic) =>
            apply(tactic, vv, branchIdx) match {
              case BelleProvable(result, _) =>
                // result.subgoals.length == numBranches - 1: branch tactic closed current branch -> next branch has same index
                // result.subgoals.length == numBranches: branch tactic neither closed the current goal nor created any additional goals
                // result.subgoals.length > numBranches: branch tactic created additional goals
                (BelleProvable(result, labels), result.subgoals.length, branchIdx+(result.subgoals.length-numBranches)+1)
            }
          })._1
        case _ => throw new BelleError("Cannot perform branching on a goal that is not a BelleValue of type Provable.").inContext(expr, "")
      }
      case OnAll(e) =>
        val provable = v match {
          case BelleProvable(p, _) => p
          case _ => throw new BelleError("Cannot attempt OnAll with a non-Provable value.").inContext(expr, "")
        }
        //@todo actually it would be nice to throw without wrapping inside an extra BranchTactic context
        try {
          apply(BranchTactic(Seq.tabulate(provable.subgoals.length)(_ => e)), v, branch)
        } catch {
          case e: BelleError => throw e.inContext(OnAll(e.context), "")
        }

      case ChooseSome(options, e) =>
        //@todo specialization to A=Formula should be undone
        val opts = options().asInstanceOf[Iterator[Formula]]
        var errors = ""
        while (opts.hasNext) {
          val o = opts.next()
          if (BelleExpr.DEBUG) println("ChooseSome: try " + o)
          val someResult: Option[BelleValue] = try {
            Some(apply(e.asInstanceOf[Formula=>BelleExpr](o.asInstanceOf[Formula]), v, branch))
          } catch { case err: BelleError => errors += "in " + o + " " + err + "\n"; None }
          if (BelleExpr.DEBUG) println("ChooseSome: try " + o + " got " + someResult)
          (someResult, e) match {
            case (Some(BelleProvable(p, _)), _) /*if p.isProved*/ => return someResult.get
            case (Some(_), x: PartialTactic) => return someResult.get
            case (Some(_), _) => errors += "option " + o + " " + new BelleError("Tactics must close their proof unless declared as partial. Use \"t partial\" instead of \"t\".").inContext(ChooseSome(options, e), "Failed option in ChooseSome: " + o) + "\n" // throw new BelleError("Non-partials must close proof.").inContext(ChooseSome(options, e), "Failed option in ChooseSome: " + o)
            case (None, _) => // option o had an error, so consider next option
          }
        }
        throw new BelleError("ChooseSome did not succeed with any of its options").inContext(ChooseSome(options, e), "Failed all options in ChooseSome: " + options() + "\n" + errors)

      case _ => v match {
        case BelleProvable(provable, labels) =>
          val result = inner(listeners(expr.prettyString, branch))(expr, BelleProvable(provable.sub(branch))) match {
            case BelleProvable(innerProvable, _) => BelleProvable(provable(innerProvable, branch), labels)
          }
          result
      }
    }
  }
}