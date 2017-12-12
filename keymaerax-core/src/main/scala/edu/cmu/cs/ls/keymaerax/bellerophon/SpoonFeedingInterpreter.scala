/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig

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
    else (0 until count).map(DbBranchPointer(predStep, _, predStep)).toList
  override def glue(ctx: ExecutionContext, createdSubgoals: Int): ExecutionContext = ctx match {
    case DbAtomPointer(id) => DbBranchPointer(parent, branch, id, openBranchesAfterExec ++ List.fill(createdSubgoals)(id))
    case DbBranchPointer(_, _, pc2, ob2) => DbBranchPointer(parent, branch, pc2, openBranchesAfterExec++ob2) // continue after pc2 (final step of the other branch)
  }
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
  * @param listeners Creates listener that are notified from the inner interpreter, takes (tactic name, parent step index in trace, branch).
  * @param inner Processes atomic tactics.
  * @param descend How far to descend into depending tactics (default: do not descend)
  * @param strict If true, follow tactic strictly; otherwise perform some optimizations (e.g., do not execute nil).
  * @author Nathan Fulton
  * @author Andre Platzer
  * @author Stefan Mitsch
  */
case class SpoonFeedingInterpreter(rootProofId: Int, startStepIndex: Int, idProvider: ProvableSig => Int,
                                   listeners: Int => ((String, Int, Int) => Seq[IOListener]),
                                   inner: Seq[IOListener] => Interpreter, descend: Int = 0,
                                   strict: Boolean = true) extends Interpreter {
  var innerProofId: Option[Int] = None

  private var runningInner: Interpreter = _

  private var isDead = false

  override def apply(expr: BelleExpr, v: BelleValue): BelleValue = runTactic(expr, v, descend, DbAtomPointer(startStepIndex))._1

  private def runTactic(tactic: BelleExpr, goal: BelleValue, level: Int, ctx: ExecutionContext): (BelleValue, ExecutionContext) = synchronized {
    if (isDead) (goal, ctx)
    else tactic match {
      // combinators
      case SeqTactic(left, right) =>
        val (leftResult, leftCtx) = try {
          runTactic(left, goal, level, ctx)
        } catch {
          case e: BelleThrowable => throw e.inContext(SeqTactic(e.context, right), "Failed left-hand side of &: " + left)
        }
        try {
          runTactic(right, leftResult, level, leftCtx)
        } catch {
          case e: BelleThrowable => throw e.inContext(SeqTactic(left, e.context), "Failed right-hand side of &: " + right)
        }
      case EitherTactic(left, right) => try {
          runTactic(left, goal, level, ctx)
        } catch {
          case eleft: BelleThrowable => try {
            runTactic(right, goal, level, ctx)
          } catch {
            case eright: BelleThrowable => throw eright.inContext(EitherTactic(eleft.context, eright.context),
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
          result = runTactic(child & repeatOnChange, result._1, level, result._2)
        } catch {
          case _: BelleThrowable =>
        }
        result
      case RepeatTactic(_, times) if times < 1 => throw new BelleThrowable("RepeatTactic done")
      case RepeatTactic(child, times) if times >= 1 =>
        //assert(times >= 1, "Invalid number of repetitions " + times + ", expected >= 1")
        var result: (BelleValue, ExecutionContext) = (goal, ctx)
        try {
          result = runTactic(if (times == 1) child else SeqTactic(child, RepeatTactic(child, times-1)), result._1, level, result._2)
        } catch {
            case e: BelleThrowable => throw e.inContext(RepeatTactic(e.context, times),
              "Failed while repeating tactic with " + times + " repetitions remaining: " + child)
        }
        result
      case BranchTactic(children) if children.isEmpty => throw new BelleThrowable("Branching with empty children")
      case BranchTactic(children) if children.nonEmpty => goal match {
        case BelleProvable(p, labels) =>
          if (children.length != p.subgoals.length)
            throw new BelleThrowable("<(e)(v) is only defined when len(e) = len(v), but " + children.length + "!=" + p.subgoals.length).inContext(tactic, "")

          val branchTactics: Seq[(BelleExpr, BelleValue)] = children.zip(p.subgoals.map(sg => BelleProvable(ProvableSig.startProof(sg), labels)))
          val branchCtxs = ctx.branch(children.size)

          //@note execute in reverse for stable global subgoal indexing
          val (provables, resultCtx) = branchTactics.zipWithIndex.foldRight((List[BelleValue](), branchCtxs.last))({ case (((ct, cp), i), (accProvables, accCtx)) =>
            val localCtx = branchCtxs(i).glue(accCtx, 0)
            assert(i == localCtx.onBranch, "Expected context branch and branch tactic index to agree, but got context=" + localCtx.onBranch + " vs. index=" + i)
            val branchResult = runTactic(ct, cp, level, localCtx)
            val branchOpenGoals = branchResult._1 match {
              case BelleProvable(bp, _) => bp.subgoals.size
            }
            (accProvables :+ branchResult._1, accCtx.glue(branchResult._2, branchOpenGoals))
          })

          val result = provables.reverse.zipWithIndex.foldRight(p)({case ((BelleProvable(cp, _), i), provable) => provable(cp, i) })

          //@note close branching in a graph t0; <(t1, ..., tn); tx with BranchPointer(parent, -1, _)
          (BelleProvable(result), resultCtx.closeBranch())
        case _ => throw new BelleThrowable("Cannot perform branching on a goal that is not a BelleValue of type Provable.").inContext(tactic, "")
      }
      case OnAll(e) =>
        val provable = goal match {
          case BelleProvable(p, _) => p
          case _ => throw new BelleThrowable("Cannot attempt OnAll with a non-Provable value.").inContext(tactic, "")
        }
        //@todo actually it would be nice to throw without wrapping inside an extra BranchTactic context
        try {
          if (provable.subgoals.size <= 1) runTactic(e, goal, level, ctx)
          else runTactic(BranchTactic(Seq.tabulate(provable.subgoals.length)(_ => e)), goal, level, ctx)
        } catch {
          case e: BelleThrowable => throw e.inContext(OnAll(e.context), "")
        }

      case Let(abbr, value, innerTactic) =>
        val (provable,lbl) = goal match {
          case BelleProvable(p, l) => (p,l)
          case _ => throw new BelleThrowable("Cannot attempt Let with a non-Provable value.").inContext(tactic, "")
        }
        if (provable.subgoals.length != 1)
          throw new BelleThrowable("Let of multiple goals is not currently supported.").inContext(tactic, "")

        // flatten nested Lets into a single inner proof
        def flattenLets(it: BelleExpr, substs: List[SubstitutionPair],
                        repls: List[(Expression, Expression)]): (ProvableSig, USubst, BelleExpr) = it match {
          case Let(a, v, c) => flattenLets(c, substs :+ SubstitutionPair(a, v), repls :+ v->a)
          case t => (
            ProvableSig.startProof(repls.foldLeft(provable.subgoals.head)({ case (s, (v, a)) => s.replaceAll(v, a) })),
            USubst(substs),
            t
          )
        }

        val (in: ProvableSig, us: USubst, innerMost) = flattenLets(innerTactic, SubstitutionPair(abbr, value)::Nil, value->abbr::Nil)
        println("INFO: " + tactic + " considers\n" + in + "\nfor outer\n" + provable)
        val innerId = idProvider(in)
        innerProofId = Some(innerId)
        val innerFeeder = SpoonFeedingInterpreter(innerId, -1, idProvider, listeners, inner, descend, strict = strict)
        val result = innerFeeder.runTactic(innerMost, BelleProvable(in), level, DbAtomPointer(-1)) match {
          case (BelleProvable(derivation, _), _) =>
            val backsubst: ProvableSig = derivation(us)
            //@todo store inner steps as part of this proof
            (BelleProvable(provable(backsubst, 0), lbl), ctx.store(Idioms.nil))
          case _ => throw new BelleThrowable("Let expected sub-derivation")
        }
        innerFeeder.kill()
        result

      case ChooseSome(options, e) =>
        val opts = options()
        var errors = ""
        var result: Option[(BelleValue, ExecutionContext)] = None
        while (opts.hasNext && result.isEmpty) {
          val o = opts.next()
          if (BelleExpr.DEBUG) println("ChooseSome: try " + o)
          val someResult: Option[(BelleValue, ExecutionContext)] = try {
            Some(runTactic(e(o), goal, level, ctx))
          } catch { case err: BelleThrowable => errors += "in " + o + " " + err + "\n"; None }
          if (BelleExpr.DEBUG) println("ChooseSome: try " + o + " got " + someResult)
          (someResult, e) match {
            case (Some((p@BelleProvable(_, _), pctx)), _) => result = Some((p, pctx))
            case (Some((p, pctx)), _: PartialTactic) => result = Some((p, pctx))
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
        val v = goal
        val valueDependentTactic = d.computeExpr(v)
        val levelDecrement = if (d.name == "ANON") 0 else 1
        runTactic(valueDependentTactic, goal, level-levelDecrement, ctx)
      } catch {
        case e: BelleThrowable => throw e.inContext(d, goal.prettyString)
        //@todo unable to create is a serious error in the tactic not just an "oops whatever try something else exception"
        case e: Throwable => throw new BelleThrowable("Unable to create dependent tactic", e).inContext(d, "")
      }

      case n@NamedTactic(name, t) if level > 0 || name == "ANON" =>
        val levelDecrement = if (name == "ANON") 0 else 1
        runTactic(t, goal, level-levelDecrement, ctx)

      // forward to inner interpreter
      case _ =>
        if (!strict && tactic == Idioms.nil) (goal, ctx)
        else goal match {
          case BelleProvable(provable, _) if provable.subgoals.isEmpty =>
            runningInner = inner(Seq())
            val result = (runningInner(tactic, goal), ctx)
            runningInner = null
            result
          case BelleProvable(provable, labels) if provable.subgoals.nonEmpty =>
            if (ctx.onBranch >= 0) {
              runningInner = inner(listeners(rootProofId)(tactic.prettyString, ctx.parentId, ctx.onBranch))
              runningInner(tactic, BelleProvable(provable.sub(0), labels)) match {
                case BelleProvable(innerProvable, _) =>
                  val result = (BelleProvable(provable(innerProvable, 0), labels), ctx.store(tactic))
                  runningInner = null
                  result
              }
            } else if (provable.subgoals.size == 1) {
              // adapt context to continue on the sole open subgoal (either nil or some other atom to follow up on)
              val newCtx = ctx match {
                case DbBranchPointer(_, _, _, openBranchesAfterExec) if openBranchesAfterExec.size == 1 => DbAtomPointer(openBranchesAfterExec.head)
              }
              runTactic(tactic, goal, level, newCtx)
            } else {
              //@todo store and reload a trace with branch -1 (=merging point of a branching tactic)
              // possible solution: store a nil/applyUsubst step with prevStepId=StartOfBranching and branchOrder=-1, without a local provable;
              // when referenced to with prevStepId/branchOrder, look up the appropriate last step of branchOrder
              // for example:
              // 2=(1,0) ; <(5=(2,0);6=(5,0) ; <nil,nil> , 3=(2,1);4=(3,0))> ; 7=(2,-1) ; <(10=(7,0)=(6,0), 9=(7,1)=(6,1), 8=(7,2)=(4,0))>
              // where stepId=(prevStepId,branch)
              assert(tactic == Idioms.nil, "Encountered non-trivial tactic after branch merge")
              (goal, ctx)
            }
        }
    }
  }

  override def kill(): Unit = synchronized {
    isDead = true
    if (runningInner != null) runningInner.kill()
  }
}