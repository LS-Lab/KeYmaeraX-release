/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.bellerophon

import java.util.concurrent.ExecutionException
import edu.cmu.cs.ls.keymaerax.Logging
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.{BelleParser, BellePrettyPrinter}
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.DebuggingTactics
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.{RenUSubst, UnificationMatch}
import edu.cmu.cs.ls.keymaerax.parser.Declaration
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig

import scala.annotation.tailrec
import scala.collection.mutable
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.{Await, TimeoutException}
import scala.concurrent.duration.{Duration, MILLISECONDS}
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
      lhm.mapValues(elems => elems.zipWithIndex.map({ case (e, i) => e._1.copy(branch = i) })).values.flatten.toList
    }
  override def glue(ctx: ExecutionContext, createdSubgoals: Int): ExecutionContext =
    if (this != ctx) ctx match {
      case DbAtomPointer(id) => DbBranchPointer(parent, branch, id, List.fill(createdSubgoals)(id) ++ openBranchesAfterExec)
      case DbBranchPointer(_, _, pc2, ob2) => DbBranchPointer(parent, branch, pc2, ob2++openBranchesAfterExec) // continue after pc2 (final step of the other branch)
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
                                   convertPending: Boolean) extends Interpreter with Logging {
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

  /** Updates the labels `orig` at position `at` to include the labels `repl`. */
  private def updateLabels(orig: Option[List[BelleLabel]], at: Int, repl: Option[List[BelleLabel]]): Option[List[BelleLabel]] = repl match {
    case Some(l) => Some(orig.map(_.patch(at, l, 1)).getOrElse(l))
    case None => orig.map(_.patch(at, Nil, 1))
  }
  private def updateLabels(orig: List[BelleLabel], at: Int, repl: Option[List[BelleLabel]]): List[BelleLabel] = updateLabels(Some(orig), at, repl).getOrElse(Nil)

  private def runTactic(tactic: BelleExpr, goal: BelleValue, level: Int, ctx: ExecutionContext, strict: Boolean,
                        convertPending: Boolean, executePending: Boolean): (BelleValue, ExecutionContext) = synchronized {
    if (isDead) (goal, ctx)
    else try {
      val (result, resultCtx) = tactic match {
        // combinators
        case SeqTactic(left, right) =>
          val (leftResult, leftCtx) = try {
            runTactic(left, goal, level, ctx, strict, convertPending, executePending)
          } catch {
            case e: BelleThrowable =>
              if (convertPending) right match {
                case t: StringInputTactic if t.name == "pending" =>
                  return runTactic(DebuggingTactics.pending(BellePrettyPrinter(left) + "; " + t.inputs.head), goal, level, ctx,
                    strict, convertPending = false, executePending = false)
                case _ =>
                  return runTactic(DebuggingTactics.pending(BellePrettyPrinter(tactic)), goal, level, ctx,
                    strict, convertPending = false, executePending = false)
              } else throw e.inContext(SeqTactic(e.context, right), "Failed left-hand side of &: " + left)
          }
          try {
            runTactic(right, leftResult, level, leftCtx, strict, convertPending, executePending)
          } catch {
            case e: BelleThrowable =>
              throw e.inContext(SeqTactic(left, e.context), "Failed right-hand side of &: " + right)
          }
        case EitherTactic(left, right) => try {
          runTactic(left, goal, level, ctx, strict, convertPending=false, executePending)
        } catch {
          // critical tactic exceptions (including StackOverflowErrors) were swallowed here so far; keep for compatibility with old proofs
          // they are caused by the deeply nested structures generated by tacticChase (unfold etc.)
          case eleft: BelleThrowable/*BelleProofSearchControl*/ => try {
            runTactic(right, goal, level, ctx, strict, convertPending=false, executePending)
          } catch {
            case eright: BelleThrowable =>
              if (convertPending) runTactic(DebuggingTactics.pending(BellePrettyPrinter(tactic)), goal, level, ctx,
                strict, convertPending = false, executePending = false)
              else throw eright.inContext(EitherTactic(eleft.context, eright.context),
              "Failed: both left-hand side and right-hand side " + goal)
          }
          case eleft: BelleThrowable if convertPending =>
            if (convertPending) runTactic(DebuggingTactics.pending(BellePrettyPrinter(tactic)), goal, level, ctx,
              strict, convertPending = false, executePending = false)
            else throw eleft.inContext(tactic, "Failed: left-hand side " + goal)
        }
        case SaturateTactic(child) =>
          var result: (BelleValue, ExecutionContext) = (goal, ctx)
            def progress(o: BelleValue, n: BelleValue) = (o, n) match {
              case (BelleProvable(op, _, _), BelleProvable(np, _, _)) => np.subgoals != op.subgoals
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
            result = runTactic(if (times == 1) child else SeqTactic(child, RepeatTactic(child, times - 1)),
              result._1, level, result._2, strict, convertPending, executePending)
          } catch {
            case e: BelleThrowable => throw e.inContext(RepeatTactic(e.context, times),
              "Failed while repeating tactic with " + times + " repetitions remaining: " + child)
          }
          result
        case CaseTactic(children) => goal match {
          case BelleProvable(p, Some(labels), _) =>
            if (p.subgoals.size != labels.size) throw new BelleUnexpectedProofStateError("Number of labels does not match number of subgoals, got\nlabels  " + labels.map(_.prettyString).mkString("\n  ") + "\nfor " + p.prettyString, p.underlyingProvable)
            if (children.size != labels.size) throw new IllFormedTacticApplicationException("Number of cases does not match number of subgoals, got\ncases\n  " + children.map(_._1.prettyString).mkString("\n  ") + "\nfor\n  " + labels.map(_.prettyString).mkString("\n  "))
            def getBranchTactic(l: BelleLabel): BelleExpr = children.filter(c => l.endsWith(c._1)).toList match {
              case c :: Nil => c._2
              case Nil => throw new IllFormedTacticApplicationException("No case for branch " + l.prettyString)
              case c => throw new IllFormedTacticApplicationException("Multiple labels apply to branch " + l.prettyString + "; please disambiguate cases " + c.map(_._1.prettyString).mkString("::"))
            }
            runTactic(BranchTactic(labels.map(getBranchTactic)), goal, level, ctx, strict, convertPending, executePending)
          case _ => throw new IllFormedTacticApplicationException("Case tactic applied on a proof state without labels")
        }
        case BranchTactic(children) if children.isEmpty => throw new IllFormedTacticApplicationException("Branching with empty children")
        case BranchTactic(children) if children.nonEmpty => goal match {
          case BelleProvable(p, labels, defs) =>
            if (children.length != p.subgoals.length)
              throw new IllFormedTacticApplicationException("<(e)(v) is only defined when len(e) = len(v), but " +
                children.length + "!=" + p.subgoals.length + " subgoals (v)\n" +
                p.subgoals.map(_.prettyString).mkString("\n===================\n")).inContext(tactic, "")

            val branchTactics: Seq[(BelleExpr, BelleValue)] = children.zip(p.subgoals.zipWithIndex.map({
              case (sg, i) => BelleProvable(ProvableSig.startProof(sg), labels.map(_(i) :: Nil), defs)
            }))
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
                      val result = rp.parent.map({ case (p, i) => p(USubst(remaining))(subst, i) }).getOrElse(subst)
                      if (remaining.isEmpty) (BelleProvable(result, rp.label, rp.defs), rctx)
                      else (new BelleDelayedSubstProvable(result, rp.label, rp.defs, USubst(remaining), None), rctx)
                    } else r
                  } else r
                case r => r
              }

              val branchOpenGoals = branchResult._1 match {
                case bdp: BelleDelayedSubstProvable =>
                  cp match { case BelleProvable(cbp, _, _) => assertSubMatchesModuloConstification(cbp, bdp.p, 0, bdp.subst) }
                  bdp.p.subgoals.size
                case BelleProvable(bp, _, _) =>
                  cp match { case BelleProvable(cbp, _, _) => assertSubMatchesModuloConstification(cbp, bp, 0, USubst(Nil)) }
                  bp.subgoals.size
                case _: BelleThrowable => 1
              }
              (accProvables :+ branchResult._1, accCtx.glue(branchResult._2, branchOpenGoals))
            })

            val origLabels = labels match {
              case None => p.subgoals.indices.map(i => BelleTopLevelLabel("__" + i)).toList
              case Some(l) => l
            }

            val (resultProvable, mergedLabels) = provables.reverse.zipWithIndex.foldRight[(ProvableSig, List[BelleLabel])]((p, origLabels))({
              case ((p: BelleDelayedSubstProvable, i), (provable, labels)) =>
                (applySubDerivation(provable, i, p.p, p.subst)._2, updateLabels(labels, i, p.label))
              case ((BelleProvable(cp, cl, _), i), (provable, labels)) =>
                // provables may have expanded or not expanded definitions arbitrarily
                if (provable.subgoals(i) == cp.conclusion) (provable(cp, i), updateLabels(labels, i, cl))
                else try {
                  val downSubst = UnificationMatch(provable.subgoals(i), cp.conclusion).usubst
                  (exhaustiveSubst(provable, downSubst)(cp, i), updateLabels(labels, i, cl))
                } catch {
                  case _: UnificationException =>
                    val upSubst = UnificationMatch(cp.conclusion, provable.subgoals(i)).usubst
                    (provable(exhaustiveSubst(cp, upSubst), i), updateLabels(labels, i, cl))
                }
            })

            val resultLabels = if (mergedLabels.forall(_.label.startsWith("__"))) None else Some(mergedLabels)

            //@note close branching in a graph t0; <(t1, ..., tn); tx with BranchPointer(parent, -1, _)
            val substs = provables.flatMap({ case p: BelleDelayedSubstProvable => Some(p.subst) case _ => None })
            val rp = if (substs.isEmpty) goal match {
              case dp: BelleDelayedSubstProvable => new BelleDelayedSubstProvable(resultProvable, resultLabels, defs, dp.subst, dp.parent)
              case _: BelleProvable => BelleProvable(resultProvable, resultLabels, defs)
            } else new BelleDelayedSubstProvable(resultProvable, resultLabels, defs, substs.reduce(_++_),
              goal match { case dp: BelleDelayedSubstProvable => dp.parent case _ => None })
            (rp, resultCtx.closeBranch())
          case _ => throw new IllFormedTacticApplicationException("Cannot perform branching on a goal that is not a BelleValue of type Provable.").inContext(tactic, "")
        }

        case t@USubstPatternTactic(children) =>
          val provable = goal match {
            case BelleProvable(p, _, _) => p
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
                (UnificationMatch(s, provable.subgoals.head), expr)
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
          val unification: (UnificationMatch.Subst, RenUSubst => BelleExpr) =
            if (unifications.forall(_._1.isEmpty)) unifications.last
            else unifications.filterNot(_._1.isEmpty).head

          runTactic(unification._2(unification._1), goal, level, ctx, strict, convertPending, executePending)

        case OnAll(e) =>
          val provable = goal match {
            case BelleProvable(p, _, _) => p
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
          val (provable, lbl, defs) = goal match {
            case BelleProvable(p, l, defs) => (p, l, defs)
            case _ => throw new IllFormedTacticApplicationException("Cannot attempt Let with a non-Provable value.").inContext(tactic, "")
          }
          if (provable.subgoals.length != 1)
            throw new IllFormedTacticApplicationException("Let of multiple goals is not currently supported.").inContext(tactic, "")

          // flatten nested Lets into a single inner proof
          @tailrec
          def flattenLets(it: BelleExpr, substs: List[SubstitutionPair],
                          repls: List[(Expression, Expression)]): (ProvableSig, USubst, BelleExpr) = it match {
            case Let(a, v, c) => flattenLets(c, substs :+ SubstitutionPair(a, v), repls :+ v -> a)
            case t => (
              ProvableSig.startProof(repls.foldLeft(provable.subgoals.head)({ case (s, (v, a)) => s.replaceAll(v, a) })),
              USubst(substs),
              t
            )
          }

          val (in: ProvableSig, us: USubst, innerMost) = flattenLets(innerTactic, SubstitutionPair(abbr, value) :: Nil, value -> abbr :: Nil)
          logger.debug(tactic + " considers\n" + in + "\nfor outer\n" + provable)
          if (descend > 0) {
            val innerId = idProvider(in)
            innerProofId = Some(innerId)
            val innerFeeder = SpoonFeedingInterpreter(innerId, -1, idProvider, defs, listenerFactory, inner, descend, strict, convertPending)
            val result = innerFeeder.runTactic(innerMost, BelleProvable(in, None, defs), level, DbAtomPointer(-1),
              strict, convertPending, executePending) match {
              case (BelleProvable(derivation, _, defs), _) =>
                val backsubst: ProvableSig = derivation(us)
                //@todo store inner steps as part of this proof
                (BelleProvable(provable(backsubst, 0), lbl, defs), ctx /*.store(tactic)*/ )
              case _ => throw new IllFormedTacticApplicationException("Let expected sub-derivation")
            }
            innerFeeder.kill()
            result
          } else {
            runningInner = inner(listenerFactory(rootProofId)(tactic.prettyString, ctx.parentId, ctx.onBranch))
            runningInner(tactic, BelleProvable(provable.sub(0), lbl, defs)) match {
              case p: BelleDelayedSubstProvable =>
                val r = applySubDerivation(provable, 0, p.p, p.subst) match {
                  case (true, mergedProvable, _) => (new BelleDelayedSubstProvable(mergedProvable, lbl, defs, p.subst, p.parent), ctx.store(tactic))
                }
                runningInner = null
                r
              case BelleProvable(innerProvable, _, defs) =>
                val r = (BelleProvable(provable(innerProvable, 0), lbl, defs), ctx.store(tactic))
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
          val pending = BelleParser.parseBackwardsCompatible(t.inputs.head.replaceAllLiterally("\\\"", "\""), defs)
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
            case BelleProvable(provable, _, _) if provable.subgoals.isEmpty =>
              runningInner = inner(Nil)
              val result = (runningInner(tactic, goal), ctx)
              runningInner = null
              result
            case BelleProvable(provable, labels, defs) if provable.subgoals.nonEmpty =>
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
                    if (result._1 != goal) throw new IllFormedTacticApplicationException("Tactic " + tactic.prettyString + " not suitable for " + provable.subgoals.size + " subgoals")
                    //@todo record a NoOpTactic that operates on all subgoals (print, assert etc)
                    else result
                  } else {
                    assert(!BelleExpr.isInternal(tactic.prettyString), "Unable to record internal tactic")
                    runningInner = inner(listenerFactory(rootProofId)(tactic.prettyString, ctx.parentId, ctx.onBranch))
                    runningInner(tactic, BelleProvable(provable.sub(0), labels, defs)) match {
                      case p: BelleDelayedSubstProvable =>
                        val resultLabels = updateLabels(labels, 0, p.label)
                        val (wasMerged, mergedProvable, _) = applySubDerivation(provable, 0, p.p, p.subst)
                        val parent = p.parent match {
                          case None => if (!wasMerged) Some(provable -> 0) else None
                          case Some((pparent, pidx)) =>
                            if (pparent == provable) p.parent
                            else if (pparent.conclusion == provable.subgoals(pidx)) Some(provable(pparent, pidx), pidx)
                            else throw new NotImplementedError("Delayed substitution parent provables: missing implementation to merge " + pparent.prettyString + " with " + provable.prettyString)
                        }
                        val result = (new BelleDelayedSubstProvable(mergedProvable, resultLabels, p.defs, p.subst, parent), ctx.store(tactic))
                        runningInner = null
                        result
                      case BelleProvable(innerProvable, innerLabels, defs) =>
                        val resultLabels = updateLabels(labels, 0, innerLabels)
                        val result = (BelleProvable(provable(innerProvable, 0), resultLabels, defs), ctx.store(tactic))
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
                  case (bp@BelleProvable(p, _, _), resultCtx) => ctx match {
                    // replaced the remaining goal of a branching tactic
                    case dbp@DbBranchPointer(_, _, predStep, openBranchesAfterExec) =>
                      val numSteps = (newCtx, resultCtx) match {
                        case (DbAtomPointer(i), DbAtomPointer(j)) => j-i
                        case (DbBranchPointer(_, _, i, Nil), DbAtomPointer(j)) => j-i
                        case (DbAtomPointer(i), _: DbBranchPointer) => ???
                      }
                      if (p.subgoals.size != provable.subgoals.size) (bp, dbp.copy(predStep = predStep + numSteps, openBranchesAfterExec = openBranchesAfterExec.dropRight(1)))
                      else (bp, DbAtomPointer(predStep + numSteps))
                  }
                }
              } else {
                //@todo support additional cases for storing and reloading a trace with branch -1 (=merging point of a branching tactic)
                (goal, ctx) match {
                  case (BelleProvable(goalP, _, _), DbBranchPointer(_, _, _, openBranches)) =>
                    assert(goalP.subgoals.size == openBranches.size, "Open subgoals and expected open subgoals do not match")
                    val newCtx = DbAtomPointer(openBranches.last)
                    runTactic(tactic, goal, level, newCtx, strict, convertPending, executePending) match {
                      case (bp@BelleProvable(resultP, _, _), resultCtx) => ctx match {
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
            assert(p.parent.isEmpty || exhaustiveSubst(p.parent.get._1, p.subst ++ fp.subst) == exhaustiveSubst(fp.parent.get._1, p.subst ++ fp.subst),
              "Delayed substitution parents disagree")
            new BelleDelayedSubstProvable(fp.p, fp.label, p.defs, p.subst ++ fp.subst, fp.parent)
          case fp: BelleProvable => new BelleDelayedSubstProvable(fp.p, fp.label, p.defs, p.subst, p.parent)
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
}
