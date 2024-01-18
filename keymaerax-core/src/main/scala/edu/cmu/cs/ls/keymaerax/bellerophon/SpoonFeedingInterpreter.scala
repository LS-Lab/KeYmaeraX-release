/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.Logging
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.{BelleParser, BellePrettyPrinter}
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.DebuggingTactics
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.{RenUSubst, RestrictedBiDiUnificationMatch}
import edu.cmu.cs.ls.keymaerax.parser.Declaration
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig

import scala.annotation.tailrec
import scala.collection.mutable
import scala.util.{Failure, Success, Try}

trait ExecutionContext {
  def store(e: BelleExpr): ExecutionContext
  def branch(count: Int): List[ExecutionContext]
  def glue(ctx: ExecutionContext, createdSubgoals: Int): ExecutionContext
  def closeBranch(): ExecutionContext
  def onBranch: Int
  def parentId: Int
}

/** Computes IDs for atomic steps stored in the database. Anticipates how the DB issues IDs. */
case class DbAtomPointer(id: Int) extends ExecutionContext {
  override def store(e: BelleExpr): ExecutionContext = DbAtomPointer(id+1)
  override def branch(count: Int): List[ExecutionContext] = (0 until count).map(DbBranchPointer(id, _, id)).toList
  override def glue(ctx: ExecutionContext, createdSubgoals: Int): ExecutionContext = ctx
  override def closeBranch(): ExecutionContext = this
  override def onBranch: Int = 0
  override def parentId: Int = id
}

/** Computes IDs for branching steps stored in the database. Anticipates how the DB issues IDs. */
case class DbBranchPointer(parent: Int, branch: Int, predStep: Int, openBranchesAfterExec: List[Int] = Nil) extends ExecutionContext {
  override def store(e: BelleExpr): ExecutionContext = DbAtomPointer(predStep+1)
  override def branch(count: Int): List[ExecutionContext] =
    if (count == 1) DbAtomPointer(predStep)::Nil
    else if (openBranchesAfterExec.isEmpty) (0 until count).map(DbBranchPointer(predStep, _, predStep, openBranchesAfterExec)).toList
    else {
      assert(openBranchesAfterExec.size == count, "Remaining open branches " + openBranchesAfterExec.size + " and " + count + " subgoal tactics do not match")
      // create branch indexes for elements with same parent but keep order stable (groupBy destroys order)
      val grouped = openBranchesAfterExec.map(s => DbBranchPointer(s, 0, predStep, Nil)).zipWithIndex.groupBy(_._1.parent)
      val lhm = mutable.LinkedHashMap(grouped.toSeq.sortBy(_._2.head._2): _*)
      lhm.mapValues(elems => elems.zipWithIndex.map({ case (e, i) => e._1.copy(branch = i) -> e._2 })).values.flatten.
        toList.sortBy(_._2).map(_._1)
    }
  override def glue(ctx: ExecutionContext, createdSubgoals: Int): ExecutionContext =
    //@see [[Provable.apply]] applies first subgoal in place, appends rest at the end
    if (this != ctx) ctx match {
      case DbAtomPointer(id) =>
        val newGoals = List.fill(createdSubgoals)(id)
        if (newGoals.nonEmpty) DbBranchPointer(parent, branch, id, newGoals.head :: openBranchesAfterExec ++ newGoals.tail)
        else DbBranchPointer(parent, branch, id, openBranchesAfterExec)
      case DbBranchPointer(_, _, pc2, ob2) =>
        // continue after pc2 (final step of the other branch)
        if (ob2.nonEmpty) DbBranchPointer(parent, branch, pc2, ob2.head :: openBranchesAfterExec ++ ob2.tail)
        else DbBranchPointer(parent, branch, pc2, openBranchesAfterExec)
    } else this
  // branch=-1 indicates the merging point after branch tactics (often points to a closed provable when the branches all close,
  // but may point to a provable of arbitrary size)
  override def closeBranch(): ExecutionContext = DbBranchPointer(parent, -1, predStep, openBranchesAfterExec)
  override def onBranch: Int = branch
  override def parentId: Int = parent
}

/**
  * Sequential interpreter for Bellerophon tactic expressions: breaks apart combinators and spoon-feeds "atomic" tactics
  * to another interpreter.
  * @param rootProofId The ID of the proof this interpreter is working on.
  * @param startStepIndex The index in the proof trace where the interpreter starts appending steps (-1 for none, e.g., in a fresh proof).
  * @param idProvider Provides IDs for child provables created in this interpreter.
  * @param listenerFactory Creates listener that are notified from the inner interpreter, takes (tactic name, parent step index in trace, branch).
  * @param inner Processes atomic tactics.
  * @param descend How far to descend into depending tactics (default: do not descend)
  * @param strict If true, follow tactic strictly; otherwise perform some optimizations (e.g., do not execute nil).
  * @author Nathan Fulton
  * @author Andre Platzer
  * @author Stefan Mitsch
  */
case class SpoonFeedingInterpreter(rootProofId: Int,
                                   startStepIndex: Int,
                                   idProvider: ProvableSig => Int,
                                   defs: Declaration,
                                   listenerFactory: Int => (String, Int, Int) => scala.collection.immutable.Seq[IOListener],
                                   inner: scala.collection.immutable.Seq[IOListener] => Interpreter,
                                   descend: Int,
                                   strict: Boolean,
                                   convertPending: Boolean,
                                   recordInternal: Boolean) extends Interpreter with Logging {
  var innerProofId: Option[Int] = None

  private var runningInner: Interpreter = _

  var isDead = false

  /** The spoon-feeding interpreter itself does not have listeners. */
  val listeners: scala.collection.immutable.Seq[IOListener] = Nil

  override def start(): Unit = isDead = false

  override def apply(expr: BelleExpr, v: BelleValue): BelleValue = {
    if (runningInner == null) {
      runTactic(expr, v, descend, DbAtomPointer(startStepIndex), strict, convertPending, executePending=true)._1
    } else {
      logger.debug("Handing auxiliary proof of an already running tactic (like initiated by UnifyUSCalculus or Simplifier) to fresh inner interpreter")
      inner(Nil)(expr, v)
    }
  }

  /** Updates the labels `orig` at position `at` to include the labels of `p`. Keeps original labels if `p.label`==None. */
  private def updateLabels(orig: Option[List[BelleLabel]], at: Int, p: BelleProvable): Option[List[BelleLabel]] = p.label match {
    case Some(l) => Some(orig.map(_.patch(at, l, 1)).getOrElse(l))
    case None => if (p.p.subgoals.isEmpty) orig.map(_.patch(at, List.empty, 1)) else orig
  }
  /** Updates the labels `orig` at position `at` to include the labels of `p`. Keeps original labels if `p.label`==None. */
  private def updateLabels(orig: List[BelleLabel], at: Int, p: BelleProvable): List[BelleLabel] = updateLabels(Some(orig), at, p).getOrElse(Nil)

  private def runTactic(tactic: BelleExpr, goal: BelleValue, level: Int, ctx: ExecutionContext, strict: Boolean,
                        convertPending: Boolean, executePending: Boolean): (BelleValue, ExecutionContext) = synchronized {
    if (isDead) (goal, ctx)
    else try {
      val (result, resultCtx) = tactic match {
        case SeqTactic(s) =>
          val nonNilSteps = s.filterNot(t => nilNames.contains(t.prettyString))
          nonNilSteps.zipWithIndex.foldLeft((goal, ctx))({
            case ((g, c), (t, i)) => try {
              runTactic(t, g, level, c, strict, convertPending, executePending)
            } catch {
              case e: BelleThrowable =>
                val remainder = nonNilSteps.drop(i+1)
                if (convertPending && remainder.nonEmpty) remainder.head match {
                  case pt: StringInputTactic if pt.name == "pending" =>
                    return runTactic(SeqTactic(DebuggingTactics.pending(BellePrettyPrinter(t) + "; " + pt.inputs.head) +: remainder.tail), g, level, c,
                      strict, convertPending = false, executePending = false)
                  case _ =>
                    return runTactic(DebuggingTactics.pending(BellePrettyPrinter(SeqTactic(remainder))), g, level, c,
                      strict, convertPending = false, executePending = false)
                } else throw e.inContext(SeqTactic(nonNilSteps.patch(i, Seq(e.context), 1)), "Failed component of ; sequential composition: " + t.prettyString)
            }
          })
        case EitherTactic(s) =>
          for ((t, i) <- s.zipWithIndex.dropRight(1)) {
            try {
              val result = runTactic(t, goal, level, ctx, strict, convertPending=false, executePending)
              if (progress(goal, result._1)) return result
            } catch {
              case _: BelleProofSearchControl => // continue
              case e: BelleThrowable =>
                if (convertPending) runTactic(DebuggingTactics.pending(BellePrettyPrinter(tactic)), goal, level, ctx,
                  strict, convertPending = false, executePending = false)
                else throw e.inContext(EitherTactic(s.patch(i, Seq(e.context), 1)),
                  "Failed component of | alternative composition " + goal)
            }
          }
          runTactic(s.last, goal, level, ctx, strict, convertPending=false, executePending)
        case SaturateTactic(child) =>
          var result: (BelleValue, ExecutionContext) = (goal, ctx)
            def progress(o: BelleValue, n: BelleValue) = (o, n) match {
              case (BelleProvable(op, _), BelleProvable(np, _)) => np.subgoals != op.subgoals
              case _ => false
            }

            var prevResult = result
            do {
              try {
                prevResult = result
                result = runTactic(child, result._1, level, result._2, strict, convertPending=false, executePending=true) match {
                  case (rp: BelleProvable, rc) => (rp, rc)
                  case _ => prevResult
                }
              } catch {
                case _: BelleProofSearchControl =>
              }
            } while (progress(prevResult._1, result._1))
          result
        case RepeatTactic(_, times) if times < 1 => (goal, ctx) // nothing to do
        case RepeatTactic(child, times) if times >= 1 =>
          //assert(times >= 1, "Invalid number of repetitions " + times + ", expected >= 1")
          var result: (BelleValue, ExecutionContext) = (goal, ctx)
          try {
            result = runTactic(if (times == 1) child else SeqTactic(Seq(child, RepeatTactic(child, times - 1))),
              result._1, level, result._2, strict, convertPending, executePending)
          } catch {
            case e: BelleThrowable => throw e.inContext(RepeatTactic(e.context, times),
              "Failed while repeating tactic with " + times + " repetitions remaining: " + child)
          }
          result
        case CaseTactic(children) => goal match {
          case BelleProvable(p, Some(labels)) =>
            if (p.subgoals.size != labels.size) throw new BelleUnexpectedProofStateError("Number of labels does not match number of subgoals, got\nlabels  " + labels.map(_.prettyString).mkString("\n  ") + "\nfor " + p.prettyString, p.underlyingProvable)
            if (children.size != labels.size) throw new IllFormedTacticApplicationException("Number of cases does not match number of subgoals, got\ncases\n  " + children.map(_._1.prettyString).mkString("\n  ") + "\nfor\n  " + labels.map(_.prettyString).mkString("\n  "))
            def getBranchTactic(l: BelleLabel): BelleExpr = children.filter(c => l.endsWith(c._1)).toList match {
              case c :: Nil => c._2
              case Nil => throw new IllFormedTacticApplicationException("Tactic has branch labels\n\t" + children.map(_._1.prettyString).mkString("\n\t") + "\nbut no case for branch\n\t" + l.prettyString)
              case c => throw new IllFormedTacticApplicationException("Multiple labels apply to branch\n\t" + l.prettyString + "\n\tPlease disambiguate cases\n\t" + c.map(_._1.prettyString).mkString("\n\t"))
            }
            runTactic(BranchTactic(labels.map(getBranchTactic)), goal, level, ctx, strict, convertPending, executePending)
          case _ => throw new IllFormedTacticApplicationException("Case tactic applied on a proof state without labels")
        }
        case BranchTactic(children) if children.isEmpty => throw new IllFormedTacticApplicationException("Branching with empty children")
        case BranchTactic(children) if children.nonEmpty => goal match {
          case BelleProvable(p, labels) =>
            if (children.length != p.subgoals.length)
              throw new IllFormedTacticApplicationException("<(e)(v) is only defined when len(e) = len(v), but " +
                children.length + "!=" + p.subgoals.length + " subgoals (v)\n" +
                p.subgoals.map(_.prettyString).mkString("\n===================\n")).inContext(tactic, "")

            val branchTactics: Seq[(BelleExpr, BelleValue)] = children.zip(p.subgoals.indices.map(i =>
              BelleProvable(p.sub(i), labels.map(_(i) :: Nil))))
            val branchCtxs = ctx.branch(children.size)

            //@note execute in reverse for stable global subgoal indexing
            val (provables, resultCtx) = branchTactics.zipWithIndex.foldRight((List[BelleValue](), branchCtxs.last))({ case (((ct, cp), i), (accProvables, accCtx)) =>
              val localCtx = branchCtxs(i).glue(accCtx, 0)
              // must execute at least some tactic on every branch, even if no-op
              val branchResult = runTactic(ct, cp, level, localCtx, strict = if (ct.isInstanceOf[NoOpTactic]) true else strict,
                convertPending, executePending) match {
                case r@(rp: BelleDelayedSubstProvable, rctx) =>
                  if (rp.p.isProved) {
                    // apply delayed constification replacements
                    val (constification, remaining) = rp.subst.subsDefsInput.partition({
                      case SubstitutionPair(FuncOf(Function(fn, fi, Unit, Real, _), Nothing), v: Variable)  => fn == v.name && fi == v.index
                      case _ => false
                    })
                    if (constification.nonEmpty) {
                      val subst = rp.p(USubst(constification))
                      val result = rp.parent.map({ case (p, i) => exhaustiveSubst(p, USubst(remaining))(subst, i) }).getOrElse(subst)
                      if (remaining.isEmpty) (BelleProvable(result, rp.label), rctx)
                      else (new BelleDelayedSubstProvable(result, rp.label, USubst(remaining), None), rctx)
                    } else r
                  } else r
                case r => r
              }

              val branchOpenGoals = branchResult._1 match {
                case bdp: BelleDelayedSubstProvable => bdp.parent match {
                  case Some((pp, i)) =>
                    assertSubMatchesModuloConstification(pp, bdp.p, i, bdp.subst)
                    cp match { case BelleProvable(cbp, _) => assertSubMatchesModuloConstification(cbp, pp, 0, bdp.subst) }
                    bdp.p.subgoals.size
                  case None =>
                    cp match { case BelleProvable(cbp, _) => assertSubMatchesModuloConstification(cbp, bdp.p, 0, bdp.subst) }
                    bdp.p.subgoals.size
                }
                case BelleProvable(bp, _) =>
                  cp match { case BelleProvable(cbp, _) => assertSubMatchesModuloConstification(cbp, bp, 0, USubst(Nil)) }
                  bp.subgoals.size
                case _: BelleThrowable => 1
              }
              (accProvables :+ branchResult._1, accCtx.glue(branchResult._2, branchOpenGoals))
            })

            val origLabels = labels match {
              case None => p.subgoals.indices.map(i => BelleTopLevelLabel("__" + i)).toList
              case Some(l) => l
            }

            val (resultProvable, mergedLabels, _) = provables.reverse.zipWithIndex.foldRight[(ProvableSig, List[BelleLabel], List[SubstitutionPair])]((p, origLabels, List.empty))({
              case ((p: BelleDelayedSubstProvable, i), (provable, labels, substs)) =>
                val combinedSubsts = combineSubsts(List(p.subst, USubst(substs)))
                (applySubDerivation(provable, i, p.p, combinedSubsts)._2, updateLabels(labels, i, p), combinedSubsts.subsDefsInput.toList)
              case ((sp@BelleProvable(cp, _), i), (provable, labels, substs)) =>
                // provables may have expanded or not expanded definitions arbitrarily
                if (provable.subgoals(i) == cp.conclusion) (provable(cp, i), updateLabels(labels, i, sp), substs)
                else {
                  val (p, s) = applySub(provable, cp, i)
                  (p, updateLabels(labels, i, sp), combineSubsts(List(s, USubst(substs))).subsDefsInput.toList)
                }
            })

            val resultLabels = if (mergedLabels.forall(_.label.startsWith("__"))) None else Some(mergedLabels)

            //@note close branching in a graph t0; <(t1, ..., tn); tx with BranchPointer(parent, -1, _)
            val substs = provables.flatMap({ case p: BelleDelayedSubstProvable => Some(p.subst) case _ => None })
            val rp = if (substs.isEmpty) goal match {
              case dp: BelleDelayedSubstProvable => new BelleDelayedSubstProvable(resultProvable, resultLabels, dp.subst, dp.parent)
              case _: BelleProvable => BelleProvable(resultProvable, resultLabels)
            } else new BelleDelayedSubstProvable(resultProvable, resultLabels, combineSubsts(substs),
              goal match { case dp: BelleDelayedSubstProvable => dp.parent case _ => None })
            (rp, resultCtx.closeBranch())
          case _ => throw new IllFormedTacticApplicationException("Cannot perform branching on a goal that is not a BelleValue of type Provable.").inContext(tactic, "")
        }

        case t@USubstPatternTactic(children) =>
          val provable = goal match {
            case BelleProvable(p, _) => p
            case _ => throw new IllFormedTacticApplicationException("Cannot attempt US unification with a non-Provable value.").inContext(tactic, "")
          }

          if (provable.subgoals.length != 1)
            throw new IllFormedTacticApplicationException("Unification of multi-sequent patterns is not currently supported.").inContext(tactic, "")

          //@todo loop through all using the first one whose unificatoin and tactic application ends up being successful as opposed to committing to first unifiable case.
          //Attempt to find a child that unifies with the input.
          val unifications = children.map(pair => {
            val ty = pair._1
            val expr = pair._2
            ty match {
              case SequentType(s) => try {
                (RestrictedBiDiUnificationMatch(s, provable.subgoals.head), expr)
              } catch {
                // in contrast to .unifiable, this suppresses "Sequent un-unifiable Un-Unifiable" message, which clutter STDIO.
                // fall back to user-provided substitution
                case _: UnificationException =>
                  //if (BelleExpr.DEBUG) println("USubst Pattern Incomplete -- could not find a unifier for any option" + t)
                  (RenUSubst(Nil), expr)
              }
              case _ => throw new IllFormedTacticApplicationException("Cannot unify non-sequent types.").inContext(t, "")
            }
          })

          //@note try user-provided last unification
          val unification: (RestrictedBiDiUnificationMatch.Subst, RenUSubst => BelleExpr) =
            if (unifications.forall(_._1.isEmpty)) unifications.last
            else unifications.filterNot(_._1.isEmpty).head

          runTactic(unification._2(unification._1), goal, level, ctx, strict, convertPending, executePending)

        case OnAll(e) =>
          val provable = goal match {
            case BelleProvable(p, _) => p
            case _ => throw new IllFormedTacticApplicationException("Cannot attempt OnAll with a non-Provable value.").inContext(tactic, "")
          }
          //@todo actually it would be nice to throw without wrapping inside an extra BranchTactic context
          try {
            if (provable.subgoals.size <= 1) runTactic(e, goal, level, ctx, strict, convertPending, executePending)
            else runTactic(BranchTactic(Seq.tabulate(provable.subgoals.length)(_ => e)), goal, level, ctx,
              strict, convertPending, executePending)
          } catch {
            case e: BelleThrowable => throw e.inContext(OnAll(e.context), "")
          }

        case Let(abbr, value, innerTactic) =>
          val (provable, lbl) = goal match {
            case BelleProvable(p, l) => (p, l)
            case _ => throw new IllFormedTacticApplicationException("Cannot attempt Let with a non-Provable value.").inContext(tactic, "")
          }
          if (provable.subgoals.length != 1)
            throw new IllFormedTacticApplicationException("Let of multiple goals is not currently supported.").inContext(tactic, "")

          def subst(abbr: Expression, value: Expression): SubstitutionPair = (abbr, value) match {
            case (FuncOf(name, arg), t: Term) =>
              val dotArg = if (arg.sort == Unit) Nothing else arg.sort.toDots(0)._1
              SubstitutionPair(FuncOf(name, dotArg), t.replaceFree(arg, dotArg))
            case (PredOf(name, arg), f: Formula) =>
              val dotArg = if (arg.sort == Unit) Nothing else arg.sort.toDots(0)._1
              SubstitutionPair(PredOf(name, dotArg), f.replaceFree(arg, dotArg))
          }

          // flatten nested Lets into a single inner proof
          @tailrec
          def flattenLets(it: BelleExpr, substs: List[SubstitutionPair],
                          repls: List[(Expression, Expression)]): (ProvableSig, USubst, BelleExpr) = it match {
            case Let(a, v, c) => flattenLets(c, substs :+ subst(a, v), repls :+ v -> a)
            case t => (
              ProvableSig.startProof(repls.foldLeft(provable.subgoals.head)({ case (s, (v, a)) => s.replaceAll(v, a) }), provable.defs),
              USubst(substs),
              t
            )
          }

          //@todo sometimes may want to offer some unification for: let j(x)=x^2>0 in tactic for sequent mentioning both x^2>0 and (x+y)^2>0 so j(x) and j(x+y).
          val (in: ProvableSig, us: USubst, innerMost) = try {
            flattenLets(innerTactic, subst(abbr, value) :: Nil, value -> abbr :: Nil)
          } catch {
            case e: Throwable => throw new IllFormedTacticApplicationException("Unable to start inner proof in let: " + e.getMessage, e)
          }
          logger.debug(s"$tactic considers\n$in\nfor outer\n$provable")
          if (descend > 0) {
            val innerId = idProvider(in)
            innerProofId = Some(innerId)
            val innerFeeder = SpoonFeedingInterpreter(innerId, -1, idProvider, defs, listenerFactory, inner, descend, strict, convertPending, recordInternal)
            val result = innerFeeder.runTactic(innerMost, BelleProvable(in, None), level, DbAtomPointer(-1),
              strict, convertPending, executePending) match {
              case (BelleProvable(derivation, _), _) =>
                val backsubst: ProvableSig = derivation(us)
                //@todo store inner steps as part of this proof
                (BelleProvable(provable(backsubst, 0), lbl), ctx /*.store(tactic)*/ )
              case _ => throw new IllFormedTacticApplicationException("Let expected sub-derivation")
            }
            innerFeeder.kill()
            result
          } else {
            runningInner = inner(listenerFactory(rootProofId)(tactic.prettyString, ctx.parentId, ctx.onBranch))
            runningInner(tactic, BelleProvable(provable.sub(0), lbl)) match {
              case p: BelleDelayedSubstProvable =>
                val r = applySubDerivation(provable, 0, p.p, p.subst) match {
                  case (true, mergedProvable) => (new BelleDelayedSubstProvable(mergedProvable, lbl, p.subst, p.parent), ctx.store(tactic))
                }
                runningInner = null
                r
              case BelleProvable(innerProvable, _) =>
                val r = (BelleProvable(provable(innerProvable, 0), lbl), ctx.store(tactic))
                runningInner = null
                r
              case e: BelleThrowable => throw e
            }
          }
        case ChooseSome(options, e) =>
          val opts = options()
          var errors = ""
          var result: Option[(BelleValue, ExecutionContext)] = None
          while (opts.hasNext && result.isEmpty) {
            val o = opts.next()
            logger.debug("ChooseSome: try " + o)
            val someResult: Option[(BelleValue, ExecutionContext)] = try {
              Some(runTactic(e(o), goal, level, ctx, strict, convertPending=false, executePending=true))
            } catch {
              case err: BelleThrowable => errors += "in " + o + " " + err + "\n"; None
            }
            logger.debug("ChooseSome: try " + o + " got " + someResult)
            (someResult, e) match {
              case (Some((p: BelleProvable, pctx)), _) => result = Some((p, pctx))
              case (Some((p, pctx)), _: PartialTactic) => result = Some((p, pctx))
              case (Some(_), _) => errors += "option " + o + " " + new IllFormedTacticApplicationException("Tactics must close their proof unless declared as partial. Use \"t partial\" instead of \"t\".").inContext(ChooseSome(options, e), "Failed option in ChooseSome: " + o) + "\n" // throw new BelleThrowable("Non-partials must close proof.").inContext(ChooseSome(options, e), "Failed option in ChooseSome: " + o)
              case (None, _) => // option o had an error, so consider next option
            }
          }
          result match {
            case Some(r) => r
            case None => throw new BelleNoProgress("ChooseSome did not succeed with any of its options").inContext(ChooseSome(options, e), "Failed all options in ChooseSome: " + opts.toList + "\n" + errors)
          }

        // look into tactics
        case d: DependentTactic if level > 0 || d.isInternal => try {
          val v = goal
          val valueDependentTactic = d.computeExpr(v)
          val levelDecrement = if (d.isInternal) 0 else 1
          runTactic(valueDependentTactic, goal, level - levelDecrement, ctx, strict, convertPending, executePending)
        } catch {
          case e: BelleThrowable => throw e.inContext(d, goal.prettyString)
          case e: Throwable =>
            val prefix = if (!d.isInternal) "Unable to execute tactic '" + d.name + "', cause: " else ""
            throw new IllFormedTacticApplicationException(prefix + e.getMessage, e).inContext(d, "")
        }

        case n@NamedTactic(_, t) if level > 0 || n.isInternal =>
          val levelDecrement = if (n.isInternal) 0 else 1
          runTactic(t, goal, level - levelDecrement, ctx, strict, convertPending, executePending)

        case TryCatch(t, catchClazz, doCatch, doFinally) =>
          @tailrec
          def matchingCause(ex: Throwable): Option[Throwable] = {
            if (ex == null) None
            else if (catchClazz.isAssignableFrom(ex.getClass)) Some(ex)
            else matchingCause(ex.getCause)
          }

          Try(runTactic(t, goal, level, ctx, strict, convertPending, executePending)) match {
            case Success(r) => doFinally match {
              case None => r
              case Some(ft) => runTactic(ft, r._1, level, r._2, strict, convertPending, executePending)
            }
            case Failure(ex) => matchingCause(ex) match {
              case None => doFinally match {
                case None => throw ex
                case Some(ft) =>
                  runTactic(ft, goal, level, ctx, strict, convertPending, executePending)
                  throw ex
              }
              case Some(cause) =>
                Try(runTactic(doCatch(catchClazz.cast(cause)), goal, level, ctx, strict, convertPending, executePending)) match {
                  case Success(r) => doFinally match {
                    case None => r
                    case Some(ft) => runTactic(ft, r._1, level, r._2, strict, convertPending, executePending)
                  }
                  case Failure(ex) => doFinally match {
                    case None => throw ex
                    case Some(ft) =>
                      runTactic(ft, goal, level, ctx, strict, convertPending, executePending)
                      throw ex
                  }
                }
            }
          }

        case t: StringInputTactic if t.name == "pending" && executePending =>
          val pending = BelleParser.parseBackwardsCompatible(t.inputs.head.replace("\\\"", "\""), defs)
          runTactic(pending, goal, level-1, ctx, strict, convertPending, executePending)

        case t: InputTactic if level > 0 =>
          runTactic(t.computeExpr(), goal, level-1, ctx, strict, convertPending, executePending)

        // region unsteppable tactics
        case t: CoreLeftTactic => runTactic(t, goal, 0, ctx, strict, convertPending, executePending)
        case t: CoreRightTactic => runTactic(t, goal, 0, ctx, strict, convertPending, executePending)
        // endregion

        // forward to inner interpreter
        case _ =>
          if (level > 0) logger.debug("Missing feature: unable to step into " + tactic.prettyString)
          if (!strict && tactic.isInstanceOf[NoOpTactic]) {
            // skip recording no-op tactics in non-strict mode (but execute, may throw exceptions that we expect)
            runningInner = inner(Nil)
            runningInner(tactic, goal) match { case _: BelleProvable => runningInner = null }
            (goal, ctx)
          } else goal match { // record no-op tactics in strict mode
            case BelleProvable(provable, _) if provable.subgoals.isEmpty =>
              runningInner = inner(Nil)
              val result = (runningInner(tactic, goal), ctx)
              runningInner = null
              result
            case BelleProvable(provable, labels) if provable.subgoals.nonEmpty =>
              if (ctx.onBranch >= 0) tactic match {
                case t: NoOpTactic if BelleExpr.isInternal(t.prettyString) =>
                  //@note execute but do not store anonymous no-op tactics
                  runningInner = inner(Nil)
                  runningInner(tactic, goal) match { case _: BelleProvable => runningInner = null }
                  (goal, ctx)
                case _ =>
                  if (provable.subgoals.size > 1) {
                    //@note tactic operating on multiple subgoals without OnAll
                    //@note tactic annotations do not retain NoOpTactic type, so on e.g. andR(1);print/nil/... we get into
                    // this case; workaround: execute without recording and check that nothing changed
                    runningInner = inner(Nil)
                    val result = (runningInner(tactic, goal), ctx)
                    runningInner = null
                    //@todo record a NoOpTactic that operates on all subgoals (print, assert etc)

                    //@todo change for STTT Example 2 delayed tactic, but then still fails in ProofTree subgoal application (wrong order)
                    result._1 match {
                      case dp: BelleDelayedSubstProvable =>
                        if (BelleProvable(dp.p, dp.label) != goal) throw new IllFormedTacticApplicationException("Tactic " + tactic.prettyString + " not suitable for " + provable.subgoals.size + " subgoals")
                        else result
                      case r =>
                        if (r != goal) throw new IllFormedTacticApplicationException("Tactic " + tactic.prettyString + " not suitable for " + provable.subgoals.size + " subgoals")
                        else result
                    }
                  } else {
                    assert(recordInternal || !BelleExpr.isInternal(tactic.prettyString), "Unable to record internal tactic")
                    runningInner = inner(listenerFactory(rootProofId)(tactic.prettyString, ctx.parentId, ctx.onBranch))
                    runningInner(tactic, BelleProvable(provable.sub(0), labels)) match {
                      case p: BelleDelayedSubstProvable =>
                        val resultLabels = updateLabels(labels, 0, p)
                        val (wasMerged, mergedProvable) = applySubDerivation(provable, 0, p.p, p.subst)
                        val parent = p.parent match {
                          case None => if (!wasMerged) Some(provable -> 0) else None
                          case Some((pparent, pidx)) =>
                            if (pparent == provable) p.parent
                            else if (pparent.conclusion == provable.subgoals(pidx)) Some(provable(pparent, pidx), pidx)
                            //@todo pparent.conclusion constified subgoal need to first finish dIRule subproof to unconstify
                            else throw new NotImplementedError("Delayed substitution parent provables: missing implementation to merge " + pparent.prettyString + " with " + provable.prettyString)
                        }
                        val result = (new BelleDelayedSubstProvable(mergedProvable, resultLabels, p.subst, parent), ctx.store(tactic))
                        runningInner = null
                        result
                      case sp@BelleProvable(innerProvable, _) =>
                        val resultLabels = updateLabels(labels, 0, sp)
                        val result =
                          if (innerProvable.conclusion == provable.subgoals(0)) {
                            (BelleProvable(provable(innerProvable, 0), resultLabels), ctx.store(tactic))
                          } else {
                            // some tactics (e.g., QE, dI) internally expand definitions
                            val (p, substs) = applySub(provable, innerProvable, 0)
                            (new BelleDelayedSubstProvable(p, resultLabels, substs, None), ctx.store(tactic))
                          }
                        runningInner = null
                        result
                    }
                  }
              } else if (provable.subgoals.size == 1) {
                // onBranch < 0 indicates closed DbBranchPointer, and here all but one subgoals were closed, so
                // adapt context to continue on the sole open subgoal (either nil or some other atom to follow up on)
                val newCtx = ctx match {
                  case DbBranchPointer(_, _, predStep, soleBranch :: Nil) => DbBranchPointer(soleBranch, 0, predStep) //DbAtomPointer(soleBranch)
                  case DbBranchPointer(_, _, predStep, Nil) => DbAtomPointer(predStep)
                }
                runTactic(tactic, goal, level, newCtx, strict, convertPending, executePending) match {
                  case (bp@BelleProvable(p, _), resultCtx) => ctx match {
                    // replaced the remaining goal of a branching tactic
                    case dbp@DbBranchPointer(_, _, predStep, openBranchesAfterExec) =>
                      val numSteps = (newCtx, resultCtx) match {
                        case (DbAtomPointer(i), DbAtomPointer(j)) => j-i
                        case (DbBranchPointer(_, _, i, Nil), DbAtomPointer(j)) => j-i
                        case (DbBranchPointer(_, _, i, Nil), DbBranchPointer(_, _, j, Nil)) => j-i
                        case (DbAtomPointer(i), _: DbBranchPointer) => ???
                      }
                      if (p.subgoals.size != provable.subgoals.size) (bp, dbp.copy(predStep = predStep + numSteps, openBranchesAfterExec = openBranchesAfterExec.dropRight(1)))
                      else (bp, DbAtomPointer(predStep + numSteps))
                  }
                }
              } else {
                //@todo support additional cases for storing and reloading a trace with branch -1 (=merging point of a branching tactic)
                (goal, ctx) match {
                  case (BelleProvable(goalP, _), DbBranchPointer(_, _, _, openBranches)) =>
                    assert(goalP.subgoals.size == openBranches.size, "Open subgoals and expected open subgoals do not match")
                    val newCtx = DbAtomPointer(openBranches.last)
                    runTactic(tactic, goal, level, newCtx, strict, convertPending, executePending) match {
                      case (bp@BelleProvable(resultP, _), resultCtx) => ctx match {
                        // replaced the previous goal with a new goal
                        case dbp@DbBranchPointer(_, _, predStep, openBranchesAfterExec) if openBranchesAfterExec.size == openBranches.size =>
                          val numSteps = (newCtx, resultCtx) match {
                            case (DbAtomPointer(i), DbAtomPointer(j)) => j-i
                            case (DbAtomPointer(i), _: DbBranchPointer) => ???
                          }
                          if (resultP.subgoals.size != provable.subgoals.size) (bp, dbp.copy(predStep = predStep + numSteps, openBranchesAfterExec = openBranchesAfterExec.dropRight(1)))
                          else (bp, DbAtomPointer(predStep + numSteps))
                        case _ => ???
                      }
                      case r => r
                    }
                }
              }
          }
      }

      val preservedSubstResult = goal match {
        case p: BelleDelayedSubstProvable => result match {
          case fp: BelleDelayedSubstProvable =>
            assert(p.parent.isEmpty || fp.parent.isEmpty || exhaustiveSubst(p.parent.get._1, p.subst ++ fp.subst) == exhaustiveSubst(fp.parent.get._1, p.subst ++ fp.subst),
              "Delayed substitution parents disagree")
            new BelleDelayedSubstProvable(fp.p, fp.label, p.subst ++ fp.subst, fp.parent)
          case fp: BelleProvable => new BelleDelayedSubstProvable(fp.p, fp.label, p.subst, p.parent)
          case _ => result
        }
        case _: BelleProvable => result
      }
      (preservedSubstResult, resultCtx)
    } catch {
      case e: BelleThrowable =>
        if (convertPending) tactic match {
          case CaseTactic(children) => runTactic(
            BranchTactic(children.map({ case (l, t) =>
              DebuggingTactics.pending("\"" + l.prettyString + "\": " + BellePrettyPrinter(t))
            })), goal, level, ctx,
            strict, convertPending = false, executePending = false)
          case BranchTactic(children) => runTactic(
            BranchTactic(children.map(c => DebuggingTactics.pending(BellePrettyPrinter(c)))), goal, level, ctx,
            strict, convertPending = false, executePending = false)
          case _ => runTactic(DebuggingTactics.pending(BellePrettyPrinter(tactic)), goal, level, ctx,
            strict, convertPending = false, executePending = false)
        }
        else throw e
    }
  }

  override def kill(): Unit = /* cannot stop if synchronized */{
    isDead = true
    if (runningInner != null) runningInner.kill()
  }

  /** Applies `sub` to subgoal `i` of `goal`. Expands definitions `defs` and substitutions found by unification prior
   * to merging provables, if necessary. Returns the merged provable and the applied substitutions. */
  private def applySub(goal: ProvableSig, sub: ProvableSig, i: Int): (ProvableSig, USubst) = {
    val allSymbols = StaticSemantics.symbols(goal.subgoals(i)) ++ StaticSemantics.symbols(sub.conclusion)
    val symbols = allSymbols -- StaticSemantics.symbols(goal.subgoals(i)).intersect(StaticSemantics.symbols(sub.conclusion))
    val defSubsts = USubst(goal.defs.substs.filter({ case SubstitutionPair(what, _) => symbols.intersect(StaticSemantics.symbols(what)).nonEmpty }))
    val substGoal = exhaustiveSubst(goal, defSubsts)
    val substSub = exhaustiveSubst(sub, defSubsts)
    if (substGoal.subgoals(i) == substSub.conclusion) (substGoal(substSub, i), defSubsts)
    else {
      if (substGoal != goal || substSub != sub) applySub(substGoal, substSub, i) match { case (p, s) => (p, defSubsts ++ s) }
      else {
        val proofSubsts = RestrictedBiDiUnificationMatch(substGoal.subgoals(i), substSub.conclusion).usubst
        (exhaustiveSubst(substGoal, proofSubsts)(exhaustiveSubst(substSub, proofSubsts), i), defSubsts ++ proofSubsts)
      }
    }
  }

  /** Combines `substs` into a single combined substitution. */
  private def combineSubsts(substs: List[USubst]): USubst = {
    if (substs.size == 1) substs.head
    else {
      val ts = combineSubsts(substs.tail).subsDefsInput
      val hs = substs.head.subsDefsInput
      USubst(hs ++ ts.filterNot(sp => hs.exists(_.what == sp.what)))
    }
  }
}
