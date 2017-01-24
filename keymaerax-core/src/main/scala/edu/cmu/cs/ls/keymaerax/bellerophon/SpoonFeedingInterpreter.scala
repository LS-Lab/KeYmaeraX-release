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
case class SpoonFeedingInterpreter(listeners: (String, Int) => Seq[IOListener], inner: Seq[IOListener] => Interpreter, descend: Int = 0) extends Interpreter {
  override def apply(expr: BelleExpr, v: BelleValue): BelleValue = runTactic((expr, v)::Nil, 0, descend)

  private def runTactic(branches: Seq[(BelleExpr, BelleValue)], branch: Int, level: Int): BelleValue = {
    branches(branch)._1 match {
      // combinators
      case SeqTactic(left, right) =>
        val leftResult = try {
          runTactic(branches.updated(branch, (left, branches(branch)._2)), branch, level)
        } catch {
          case e: BelleThrowable => throw e.inContext(SeqTactic(e.context, right), "Failed left-hand side of &: " + left)
        }
        try {
          runTactic(branches.updated(branch, (right, leftResult)), branch, level)
        } catch {
          case e: BelleThrowable => throw e.inContext(SeqTactic(left, e.context), "Failed right-hand side of &: " + right)
        }
      case EitherTactic(left, right) => try {
          runTactic(branches.updated(branch, (left, branches(branch)._2)), branch, level)
        } catch {
          case eleft: BelleThrowable => try {
            runTactic(branches.updated(branch, (right, branches(branch)._2)), branch, level)
          } catch {
            case eright: BelleThrowable => throw eright.inContext(EitherTactic(eleft.context, eright.context),
              "Failed: both left-hand side and right-hand side " + branches(branch)._1)
          }
        }

      case SaturateTactic(child) =>
        var prev: BelleValue = null
        var result: BelleValue = branches(branch)._2
        do {
          prev = result
          try {
            result = runTactic(branches.updated(branch, (child, result)), branch, level)
          } catch {
            case e: BelleThrowable => /*@note child no longer applicable */ result = prev
          }
        } while (result != prev)
        result
      case RepeatTactic(child, times) =>
        var result = branches(branch)._2
        for (i <- 1 to times) try {
          result = runTactic(branches.updated(branch, (child, result)), branch, level)
        } catch {
          case e: BelleThrowable => throw e.inContext(RepeatTactic(e.context, times),
            "Failed while repating tactic " + i + "th iterate of " + times + ": " + child)
        }
        result
      case BranchTactic(children) => branches(branch)._2 match {
        case BelleProvable(p, labels) =>
          if (children.length != p.subgoals.length)
            throw new BelleThrowable("<(e)(v) is only defined when len(e) = len(v), but " + children.length + "!=" + p.subgoals.length).inContext(branches(branch)._1, "")

          // patch branches b consistent with number of p's subgoals
          def patchBranches(p: ProvableSig, b: Seq[(BelleExpr, BelleValue)], pos: Int): Seq[(BelleExpr, BelleValue)] =
            if (p.subgoals.isEmpty) b.patch(pos, Nil, 1)
            else if (p.subgoals.size == 1) b
            else b ++ p.subgoals.tail.map(sg => (b(pos)._1, BelleProvable(ProvableSig.startProof(sg))))

          //@note execute in reverse for stable global subgoal indexing
          val branchTactics: Seq[(BelleExpr, BelleValue)] = children.zip(p.subgoals.map(sg => BelleProvable(ProvableSig.startProof(sg), labels)))
          val allBranches = branches.updated(branch, branchTactics.head) ++ branchTactics.tail

          val reverseBranches = allBranches.zipWithIndex.reverse.filter(nt => branchTactics.contains(nt._1))
          val BelleProvable(last, _) = runTactic(allBranches, reverseBranches.head._2, level)
          val remainingBranches = patchBranches(last, allBranches, reverseBranches.head._2)

          val result = reverseBranches.tail.foldLeft((p(last, p.subgoals.size-1), remainingBranches))({ case ((r, nb), (_, i)) =>
            val BelleProvable(current, _) = runTactic(nb, i, level)
            val localBranchIdx = r.subgoals.indexOf(current.conclusion)
            (r(current, localBranchIdx), patchBranches(current, nb, i))
          })

          BelleProvable(result._1)
        case _ => throw new BelleThrowable("Cannot perform branching on a goal that is not a BelleValue of type Provable.").inContext(branches(branch)._1, "")
      }
      case OnAll(e) =>
        val provable = branches(branch)._2 match {
          case BelleProvable(p, _) => p
          case _ => throw new BelleThrowable("Cannot attempt OnAll with a non-Provable value.").inContext(branches(branch)._1, "")
        }
        //@todo actually it would be nice to throw without wrapping inside an extra BranchTactic context
        try {
          runTactic(branches.updated(branch, (BranchTactic(Seq.tabulate(provable.subgoals.length)(_ => e)), branches(branch)._2)), branch, level)
        } catch {
          case e: BelleThrowable => throw e.inContext(OnAll(e.context), "")
        }

      case ChooseSome(options, e) =>
        val ec = e.asInstanceOf[Formula=>BelleExpr]
        //@todo specialization to A=Formula should be undone
        val opts: Iterator[Formula] = options().asInstanceOf[Iterator[Formula]]
        var errors = ""
        var result: Option[BelleValue] = None
        while (opts.hasNext && result.isEmpty) {
          val o = opts.next()
          if (BelleExpr.DEBUG) println("ChooseSome: try " + o)
          val someResult: Option[BelleValue] = try {
            Some(runTactic(branches.updated(branch, (ec(o), branches(branch)._2)), branch, level))
          } catch { case err: BelleThrowable => errors += "in " + o + " " + err + "\n"; None }
          if (BelleExpr.DEBUG) println("ChooseSome: try " + o + " got " + someResult)
          (someResult, e) match {
            case (Some(p@BelleProvable(_, _)), _) => result = Some(p)
            case (Some(p), _: PartialTactic) => result = Some(p)
            case (Some(_), _) => errors += "option " + o + " " + new BelleThrowable("Tactics must close their proof unless declared as partial. Use \"t partial\" instead of \"t\".").inContext(ChooseSome(options, e), "Failed option in ChooseSome: " + o) + "\n" // throw new BelleThrowable("Non-partials must close proof.").inContext(ChooseSome(options, e), "Failed option in ChooseSome: " + o)
            case (None, _) => // option o had an error, so consider next option
          }
        }
        result match {
          case Some(r) => r
          case None => throw new BelleThrowable("ChooseSome did not succeed with any of its options").inContext(ChooseSome(options, e), "Failed all options in ChooseSome: " + opts.toList + "\n" + errors)
        }

      // look into tactics
      case d: DependentTactic if level > 0 || d.name == "ANON" => try {
        val v = branches(branch)._2
        val valueDependentTactic = d.computeExpr(v)
        val levelDecrement = if (d.name == "ANON") 0 else 1
        runTactic(branches.updated(branch, (valueDependentTactic, branches(branch)._2)), branch, level-levelDecrement)
      } catch {
        case e: BelleThrowable => throw e.inContext(d, branches(branch)._2.prettyString)
        //@todo unable to create is a serious error in the tactic not just an "oops whatever try something else exception"
        case e: Throwable => throw new BelleThrowable("Unable to create dependent tactic", e).inContext(d, "")
      }

      case n@NamedTactic(name, t) if level > 0 || name == "ANON" =>
        val levelDecrement = if (name == "ANON") 0 else 1
        runTactic(branches.updated(branch, (t, branches(branch)._2)), branch, level-levelDecrement)

      // forward to inner interpreter
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