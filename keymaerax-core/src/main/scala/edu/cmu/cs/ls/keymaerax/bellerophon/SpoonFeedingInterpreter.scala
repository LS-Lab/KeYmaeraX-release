/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.bellerophon

import java.util.concurrent.ExecutionException

import edu.cmu.cs.ls.keymaerax.bellerophon.parser.{BelleParser, BellePrettyPrinter}
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.{DebuggingTactics, Idioms}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.{RenUSubst, UnificationMatch}
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import org.apache.logging.log4j.scala.Logging

import scala.annotation.tailrec
import scala.collection.mutable
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.{Await, TimeoutException}
import scala.concurrent.duration.{Duration, MILLISECONDS}

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
case class SpoonFeedingInterpreter(rootProofId: Int, startStepIndex: Int, idProvider: ProvableSig => Int,
                                   listenerFactory: Int => ((String, Int, Int) => scala.collection.immutable.Seq[IOListener]),
                                   inner: scala.collection.immutable.Seq[IOListener] => Interpreter, descend: Int = 0,
                                   strict: Boolean = true, convertPending: Boolean = true) extends Interpreter with Logging {
  var innerProofId: Option[Int] = None

  private var runningInner: Interpreter = _

  var isDead = false

  /** The spoon-feeding interpreter itself does not have listeners. */
  val listeners: scala.collection.immutable.Seq[IOListener] = Nil

  override def apply(expr: BelleExpr, v: BelleValue): BelleValue = {
    if (runningInner == null) {
      runTactic(expr, v, descend, DbAtomPointer(startStepIndex), strict, convertPending, executePending=true)._1
    } else {
      logger.debug("Handing auxiliary proof of an already running tactic (like initiated by UnifyUSCalculus or Simplifier) to fresh inner interpreter")
      inner(Nil)(expr, v)
    }
  }

  private def runTactic(tactic: BelleExpr, goal: BelleValue, level: Int, ctx: ExecutionContext, strict: Boolean,
                        convertPending: Boolean, executePending: Boolean): (BelleValue, ExecutionContext) = synchronized {
    if (isDead) (goal, ctx)
    else try {
      val (result, resultCtx) = tactic match {
        // combinators
        case SeqTactic(left, right) =>
          val (leftResult, leftCtx) = try {
            runTactic(left, goal, level, ctx, strict, convertPending = false, executePending)
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
          case eleft: BelleThrowable => try {
            runTactic(right, goal, level, ctx, strict, convertPending=false, executePending)
          } catch {
            case eright: BelleThrowable =>
              if (convertPending) runTactic(DebuggingTactics.pending(BellePrettyPrinter(tactic)), goal, level, ctx,
                strict, convertPending = false, executePending = false)
              else throw eright.inContext(EitherTactic(eleft.context, eright.context),
              "Failed: both left-hand side and right-hand side " + goal)
          }
        }
        case SaturateTactic(child) =>
          var result: (BelleValue, ExecutionContext) = (goal, ctx)
          try {
            val repeatOnChange = new DependentTactic("ANON") {
              override def computeExpr(provable: ProvableSig): BelleExpr = goal match {
                case BelleProvable(p, _) => provable.subgoals.headOption match {
                  case Some(s) if s != p.subgoals.head => tactic
                  case _ => Idioms.nil
                }
              }
            }
            result = runTactic(child & repeatOnChange, result._1, level, result._2, strict, convertPending=false, executePending=true)
          } catch {
            case _: BelleThrowable =>
          }
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
        case BranchTactic(children) if children.isEmpty => throw new IllFormedTacticApplicationException("Branching with empty children")
        case BranchTactic(children) if children.nonEmpty => goal match {
          case BelleProvable(p, labels) =>
            if (children.length != p.subgoals.length)
              throw new IllFormedTacticApplicationException("<(e)(v) is only defined when len(e) = len(v), but " +
                children.length + "!=" + p.subgoals.length + " subgoals (v)\n" +
                p.subgoals.map(_.prettyString).mkString("\n===================\n")).inContext(tactic, "")

            val branchTactics: Seq[(BelleExpr, BelleValue)] = children.zip(p.subgoals.map(sg => BelleProvable(ProvableSig.startProof(sg), labels)))
            val branchCtxs = ctx.branch(children.size)

            //@note execute in reverse for stable global subgoal indexing
            val (provables, resultCtx) = branchTactics.zipWithIndex.foldRight((List[BelleValue](), branchCtxs.last))({ case (((ct, cp), i), (accProvables, accCtx)) =>
              val localCtx = branchCtxs(i).glue(accCtx, 0)
              // must execute at least some tactic on every branch, even if no-op
              val branchResult = runTactic(ct, cp, level, localCtx, strict = if (ct.isInstanceOf[NoOpTactic]) true else strict,
                convertPending, executePending)
              val branchOpenGoals = branchResult._1 match {
                case BelleProvable(bp, _) => bp.subgoals.size
              }
              (accProvables :+ branchResult._1, accCtx.glue(branchResult._2, branchOpenGoals))
            })

            val result = provables.reverse.zipWithIndex.foldRight(p)({
              case ((p: BelleDelayedSubstProvable, i), provable) => replaceConclusion(provable, i, p.p, p match {
                case p: BelleDelayedSubstProvable => Some(p.subst)
                case _ => None
              })._1
              case ((BelleProvable(cp, _), i), provable) => provable(cp, i)
            })

            //@note close branching in a graph t0; <(t1, ..., tn); tx with BranchPointer(parent, -1, _)
            val substs = provables.flatMap({ case p: BelleDelayedSubstProvable => Some(p.subst) case _ => None })
            if (substs.isEmpty) (BelleProvable(result), resultCtx.closeBranch())
            else (new BelleDelayedSubstProvable(result, None, substs.reduce(_++_)), resultCtx.closeBranch())
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
                (UnificationMatch(s, provable.subgoals.head), expr)
              } catch {
                // in contrast to .unifiable, this suppresses "Sequent un-unifiable Un-Unifiable" message, which clutter STDIO.
                // fall back to user-provided substitution
                case e: UnificationException =>
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

          runTactic(unification._2(unification._1.asInstanceOf[RenUSubst]), goal, level, ctx, strict, convertPending, executePending)

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
            val innerFeeder = SpoonFeedingInterpreter(innerId, -1, idProvider, listenerFactory, inner, descend, strict = strict)
            val result = innerFeeder.runTactic(innerMost, BelleProvable(in), level, DbAtomPointer(-1),
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
                val r = (new BelleDelayedSubstProvable(replaceConclusion(provable, 0, p.p, Some(p.subst))._1, lbl, p.subst), ctx.store(tactic))
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
              case (Some((p@BelleProvable(_, _), pctx)), _) => result = Some((p, pctx))
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
        case d: DependentTactic if level > 0 || d.name == "ANON" => try {
          val v = goal
          val valueDependentTactic = d.computeExpr(v)
          val levelDecrement = if (d.name == "ANON") 0 else 1
          runTactic(valueDependentTactic, goal, level - levelDecrement, ctx, strict, convertPending, executePending)
        } catch {
          case e: BelleThrowable => throw e.inContext(d, goal.prettyString)
          case e: Throwable => throw new IllFormedTacticApplicationException("Unable to create dependent tactic", e).inContext(d, "")
        }

        case n@NamedTactic(name, t) if level > 0 || name == "ANON" =>
          val levelDecrement = if (name == "ANON") 0 else 1
          runTactic(t, goal, level - levelDecrement, ctx, strict, convertPending, executePending)

        case t: StringInputTactic if t.name == "pending" && executePending =>
          runTactic(BelleParser(t.inputs.head.replaceAllLiterally("\\\"", "\"")), goal, level-1, ctx, strict, convertPending, executePending)

        case TimeoutAlternatives(alternatives, timeout) => alternatives.headOption match {
          case Some(alt) =>
            val c = Cancellable(runTactic(alt, goal, level, ctx, strict, convertPending, executePending))
            try {
              Await.result(c.future, Duration(timeout, MILLISECONDS))
            } catch {
              // current alternative failed within timeout, try next
              case ex: ExecutionException => ex.getCause match {
                case _: BelleThrowable => runTactic(TimeoutAlternatives(alternatives.tail, timeout), goal, level, ctx, strict, convertPending, executePending)
                case e => throw e
              }
              case ex: TimeoutException =>
                c.cancel()
                throw new BelleNoProgress("Alternative timed out", ex)
            }
          case None => throw new BelleNoProgress("Exhausted all timeout alternatives")
        }

        // forward to inner interpreter
        case _ =>
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
              if (ctx.onBranch >= 0) {
                if (provable.subgoals.size > 1) tactic match {
                  case _: NoOpTactic =>
                    //@note execute but do not store no-op tactics
                    runningInner = inner(Nil)
                    runningInner(tactic, goal) match { case _: BelleProvable => runningInner = null }
                    (goal, ctx)
                  case _ =>
                    //@note tactic operating on multiple subgoals without OnAll
                    throw new IllFormedTacticApplicationException("Tactic " + tactic.prettyString + " not suitable for " + provable.subgoals.size + " subgoals")
                } else {
                  runningInner = inner(listenerFactory(rootProofId)(tactic.prettyString, ctx.parentId, ctx.onBranch))
                  runningInner(tactic, BelleProvable(provable.sub(0), labels)) match {
                    case p: BelleDelayedSubstProvable =>
                      val result = (new BelleDelayedSubstProvable(replaceConclusion(provable, 0, p.p, Some(p.subst))._1,  labels, p.subst), ctx.store(tactic))
                      runningInner = null
                      result
                    case BelleProvable(innerProvable, _) =>
                      val result = (BelleProvable(provable(innerProvable, 0), labels), ctx.store(tactic))
                      runningInner = null
                      result
                  }
                }
              } else if (provable.subgoals.size == 1) {
                // onBranch < 0 indicates closed DbBranchPointer, and here all but one subgoals were closed, so
                // adapt context to continue on the sole open subgoal (either nil or some other atom to follow up on)
                val newCtx = ctx match {
                  case DbBranchPointer(_, _, _, openBranchesAfterExec) if openBranchesAfterExec.size == 1 =>
                    DbAtomPointer(openBranchesAfterExec.head)
                }
                runTactic(tactic, goal, level, newCtx, strict, convertPending, executePending) match {
                  case (bp@BelleProvable(p, _), resultCtx) => ctx match {
                    // replaced the remaining goal of a branching tactic
                    case dbp@DbBranchPointer(_, _, predStep, openBranchesAfterExec) if openBranchesAfterExec.size == 1 =>
                      val numSteps = (newCtx, resultCtx) match {
                        case (DbAtomPointer(i), DbAtomPointer(j)) => j-i
                        case (DbAtomPointer(i), _: DbBranchPointer) => ???
                      }
                      if (p.subgoals.size != provable.subgoals.size) (bp, dbp.copy(predStep = predStep + numSteps, openBranchesAfterExec = openBranchesAfterExec.drop(1)))
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

      // preserve delayed substitutions
      val preservedSubstResult = goal match {
        case p: BelleDelayedSubstProvable => result match {
          case fp: BelleDelayedSubstProvable => new BelleDelayedSubstProvable(fp.p, fp.label, p.subst ++ fp.subst)
          case fp: BelleProvable => new BelleDelayedSubstProvable(fp.p, fp.label, p.subst)
          case _ => result
        }
        case _ => result
      }
      (preservedSubstResult, resultCtx)
    } catch {
      case e: BelleThrowable =>
        if (convertPending) runTactic(DebuggingTactics.pending(BellePrettyPrinter(tactic)), goal, level, ctx,
          strict, convertPending = false, executePending = false)
        else throw e
    }
  }

  override def kill(): Unit = /* cannot stop if synchronized */{
    isDead = true
    if (runningInner != null) runningInner.kill()
  }
}
