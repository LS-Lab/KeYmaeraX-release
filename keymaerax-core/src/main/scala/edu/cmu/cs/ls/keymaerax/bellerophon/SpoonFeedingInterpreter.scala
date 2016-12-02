/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig

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
  override def apply(expr: BelleExpr, v: BelleValue): BelleValue = apply((expr, v)::Nil, 0)

  def apply(branches: Seq[(BelleExpr, BelleValue)], branch: Int): BelleValue = {
    branches(branch)._1 match {
      case SeqTactic(left, right) =>
        val leftResult = try {
          apply(branches.updated(branch, (left, branches(branch)._2)), branch)
        } catch {
          case e: BelleThrowable => throw e.inContext(SeqTactic(e.context, right), "Failed left-hand side of &: " + left)
        }
        try {
          apply(branches.updated(branch, (right, leftResult)), branch)
        } catch {
          case e: BelleThrowable => throw e.inContext(SeqTactic(left, e.context), "Failed right-hand side of &: " + right)
        }
      case EitherTactic(left, right) => try {
        val leftResult = apply(branches.updated(branch, (left, branches(branch)._2)), branch)
        (leftResult, left) match {
          case (BelleProvable(p, _), _) /*if p.isProved*/ => leftResult
          case (_, x: PartialTactic) => leftResult
          case _ => throw new BelleThrowable("Tactics must close their proof unless declared as partial. Use \"t partial\" instead of \"t\".").inContext(EitherTactic(BelleDot, right), "Failed left-hand side of |:" + left)
        }
      } catch {
        //@todo catch a little less. Just catching proper tactic exceptions, maybe some ProverExceptions et al., not swallow everything
        case eleft: BelleThrowable =>
          val rightResult = try {
            apply(branches.updated(branch, (right, branches(branch)._2)), branch)
          } catch {
            case e: BelleThrowable => throw e.inContext(EitherTactic(eleft.context, e.context), "Failed: both left-hand side and right-hand side " + branches(branch)._1)
          }
          (rightResult, right) match {
            case (BelleProvable(p, _), _) /*if p.isProved*/ => rightResult
            case (_, x: PartialTactic) => rightResult
            case _ => throw new BelleThrowable("Tactics must close their proof unless declared as partial. Use \"t partial\" instead of \"t\".").inContext(EitherTactic(left, BelleDot), "Failed right-hand side of |: " + right)
          }
      }
      case SaturateTactic(child) =>
        var prev: BelleValue = null
        var result: BelleValue = branches(branch)._2
        do {
          prev = result
          //@todo effect on listeners etc.
          try {
            result = apply(branches.updated(branch, (child, result)), branch)
          } catch {
            case e: BelleThrowable => /*@note child no longer applicable */ result = prev
          }
        } while (result != prev)
        result
      case RepeatTactic(child, times) =>
        var result = branches(branch)._2
        for (i <- 1 to times) try {
          result = apply(branches.updated(branch, (child, result)), branch)
        } catch {
          case e: BelleThrowable => throw e.inContext(RepeatTactic(e.context, times),
            "Failed while repating tactic " + i + "th iterate of " + times + ": " + child)
        }
        result
      case BranchTactic(children) => branches(branch)._2 match {
        case BelleProvable(p, labels) =>
          if (children.length != p.subgoals.length)
            throw new BelleThrowable("<(e)(v) is only defined when len(e) = len(v), but " + children.length + "!=" + p.subgoals.length).inContext(branches(branch)._1, "")

          val branchTactics: Seq[(BelleExpr, BelleValue)] = children.zip(p.subgoals.map(sg => BelleProvable(ProvableSig.startProof(sg), labels)))
          val newBranches = branches.updated(branch, branchTactics.head) ++ branchTactics.tail
          val branchIdx = branches.length until (branches.length+children.length-1)
          //@todo compose result
          branchIdx.foldLeft((0, 0, newBranches, apply(newBranches, 0)))({
            case ((previ, prevClosed, remainingBranches, BelleProvable(branchResult, _)), i) =>
              val closed = prevClosed + (if (branchResult.subgoals.isEmpty) 1 else 0)
              val remainder = remainingBranches.patch(previ, Nil, 1)
              (i-closed, closed, remainder, apply(remainder, i-closed))
          })._4
        case _ => throw new BelleThrowable("Cannot perform branching on a goal that is not a BelleValue of type Provable.").inContext(branches(branch)._1, "")
      }
      case OnAll(e) =>
        val provable = branches(branch)._2 match {
          case BelleProvable(p, _) => p
          case _ => throw new BelleThrowable("Cannot attempt OnAll with a non-Provable value.").inContext(branches(branch)._1, "")
        }
        //@todo actually it would be nice to throw without wrapping inside an extra BranchTactic context
        try {
          apply(branches.updated(branch, (BranchTactic(Seq.tabulate(provable.subgoals.length)(_ => e)), branches(branch)._2)), branch)
        } catch {
          case e: BelleThrowable => throw e.inContext(OnAll(e.context), "")
        }

      case ChooseSome(options, e) =>
        //@todo specialization to A=Formula should be undone
        val opts = options().asInstanceOf[Iterator[Formula]]
        var errors = ""
        while (opts.hasNext) {
          val o = opts.next()
          if (BelleExpr.DEBUG) println("ChooseSome: try " + o)
          val someResult: Option[BelleValue] = try {
            Some(apply(branches.updated(branch, (e.asInstanceOf[Formula=>BelleExpr](o.asInstanceOf[Formula]), branches(branch)._2)), branch))
          } catch { case err: BelleThrowable => errors += "in " + o + " " + err + "\n"; None }
          if (BelleExpr.DEBUG) println("ChooseSome: try " + o + " got " + someResult)
          (someResult, e) match {
            case (Some(BelleProvable(p, _)), _) /*if p.isProved*/ => return someResult.get
            case (Some(_), x: PartialTactic) => return someResult.get
            case (Some(_), _) => errors += "option " + o + " " + new BelleThrowable("Tactics must close their proof unless declared as partial. Use \"t partial\" instead of \"t\".").inContext(ChooseSome(options, e), "Failed option in ChooseSome: " + o) + "\n" // throw new BelleThrowable("Non-partials must close proof.").inContext(ChooseSome(options, e), "Failed option in ChooseSome: " + o)
            case (None, _) => // option o had an error, so consider next option
          }
        }
        throw new BelleThrowable("ChooseSome did not succeed with any of its options").inContext(ChooseSome(options, e), "Failed all options in ChooseSome: " + options() + "\n" + errors)

      case _ => branches(branch)._2 match {
        case BelleProvable(provable, labels) if provable.subgoals.isEmpty=> inner(Seq())(branches(branch)._1, branches(branch)._2)
        case BelleProvable(provable, labels) if provable.subgoals.nonEmpty =>
          inner(listeners(branches(branch)._1.prettyString, branch))(branches(branch)._1, BelleProvable(provable.sub(0), labels)) match {
            case BelleProvable(innerProvable, _) => BelleProvable(provable(innerProvable, 0), labels)
          }
      }
    }
  }
}