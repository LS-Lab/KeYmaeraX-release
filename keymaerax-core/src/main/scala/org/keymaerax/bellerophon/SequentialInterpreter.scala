/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.bellerophon

import org.keymaerax.Logging
import org.keymaerax.btactics.{
  Ax,
  ConfigurableGenerator,
  FixedGenerator,
  Generator,
  InvariantGenerator,
  TacticFactory,
  TactixLibrary,
}
import org.keymaerax.core._
import org.keymaerax.infrastruct.Augmentors._
import org.keymaerax.infrastruct.{Position, RenUSubst, RestrictedBiDiUnificationMatch}
import org.keymaerax.pt.ProvableSig

import java.util.concurrent.CancellationException
import scala.annotation.tailrec
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.duration.Duration
import scala.concurrent.{Await, Future, Promise}
import scala.util.control.Breaks._
import scala.util.{Failure, Success, Try}

/**
 * Sequential interpreter for Bellerophon tactic expressions.
 *
 * @param listeners
 *   Pre- and post-processing hooks for step-wise tactic execution.
 * @author
 *   Nathan Fulton
 * @author
 *   Andre Platzer
 */
abstract class BelleBaseInterpreter(
    val listeners: scala.collection.immutable.Seq[IOListener],
    val throwWithDebugInfo: Boolean = false,
) extends Interpreter with Logging {
  var isDead: Boolean = false

  override def start(): Unit = isDead = false

  override def apply(expr: BelleExpr, v: BelleValue): BelleValue = {
    if (Thread.currentThread().isInterrupted || isDead) {
      // ToolProvider.tools().foreach(_.cancel()) //@todo breaks TimeoutAlternatives+Mathematica
      // @note end executing the interpreter when its thread gets interrupted
      throw new BelleAbort(
        "Killed",
        "Execution stopped by killing the interpreter or interrupting the interpreter thread",
      )
    }
    listeners.foreach(_.begin(v, expr))
    try {
      val exprResult = runExpr(expr, v)
      // preserve delayed substitutions
      val result = v match {
        case p: BelleDelayedSubstProvable => exprResult match {
            case r: BelleDelayedSubstProvable => (p.parent, r.parent) match {
                case (Some(pp), None) =>
                  // if r is a lemma that was proved constified but it also expanded definitions
                  assert(
                    pp._1(p.subst ++ r.subst).subgoals(pp._2) == r.p(p.subst ++ r.subst).conclusion,
                    "Unsupported delayed substitution: even after substitution, conclusion of sub-derivation\n" +
                      r.p(p.subst ++ r.subst).conclusion + "\ndoes not fit subgoal\n" +
                      pp._1(p.subst ++ r.subst).subgoals(pp._2),
                  )
                  new BelleDelayedSubstProvable(r.p, r.label, p.subst ++ r.subst, p.parent)
                case (Some(pp), Some(rp)) =>
                  assert(pp == rp, "Unsupported delayed substitution: parent provables disagree")
                  new BelleDelayedSubstProvable(r.p, r.label, p.subst ++ r.subst, p.parent)
                case (None, _) => new BelleDelayedSubstProvable(r.p, r.label, p.subst ++ r.subst, r.parent)
              }
            case r: BelleProvable => new BelleDelayedSubstProvable(r.p, r.label, p.subst, p.parent)
            case _ => exprResult
          }
        case p: BelleProvable => exprResult match {
            case r: BelleDelayedSubstProvable => r.parent match {
                case None => r
                case Some((pp, i)) =>
                  if (r.p.isProved) {
                    val substGoal = exhaustiveSubst(pp, r.subst)
                    try {
                      val substSub = exhaustiveSubst(r.p, r.subst)
                      val other = collectSubst(substGoal, i, substSub)
                      new BelleDelayedSubstProvable(
                        exhaustiveSubst(substGoal, other)(exhaustiveSubst(substSub, other), i),
                        r.label,
                        r.subst ++ other,
                        None,
                      )
                    } catch {
                      case ex: SubstitutionClashException =>
                        // @note let(...) when initial conjecture has differentials, e.g.,
                        // *
                        // ----------------------
                        // |- [x':=5;](x+c())'>=0
                        // ---------------------- c()~>y clash even though subderivation proved
                        // |- [x':=5;](x+y)'>=0
                        //
                        // not relevant when differentials are intermediate (e.g., in dI) so ultimately delayed substitution won't clash
                        if (p.p == pp) r else throw ex
                    }
                  } else { r }
              }
            case r: BelleProvable =>
              if (p.p.conclusion == r.p.conclusion) r
              else {
                // @note proof may use US with user-provided substitution, without def in parent provable: merge definitions
                val subst = collectSubst(p.p.conclusion, r.p.conclusion, r.p.isProved, p.p.defs ++ r.p.defs)
                assert(
                  exhaustiveSubst(p.p, subst).conclusion == exhaustiveSubst(r.p, subst).conclusion,
                  "Expected matching conclusions:\nexpected\n" + p.p(subst).conclusion.prettyString + "\nbut got\n" +
                    r.p(subst).conclusion.prettyString,
                )
                new BelleDelayedSubstProvable(r.p, r.label, subst, None)
              }
            case _ => exprResult
          }
        case _ => exprResult
      }
      listeners.foreach(_.end(v, expr, Left(result)))
      result
    } catch {
      case e: Throwable => throw try {
          listeners.foreach(_.end(v, expr, Right(e)))
          e
        } catch { case ex: Throwable => ex.initCause(e) }
    }
  }

  override def kill(): Unit = {
    isDead = true
    listeners.synchronized(listeners.foreach(_.kill()))
  }

  /** Adjusts the number of labels to match the number of subgoals. */
  private def adjustLabels(p: ProvableSig, lbl: Option[List[BelleLabel]]): Option[List[BelleLabel]] = lbl match {
    case None => None
    case Some(labels) =>
      if (p.subgoals.size > labels.size) { Some(labels ++ List.fill(p.subgoals.size - labels.size)(labels.last)) }
      else if (p.subgoals.size < labels.size) { Some(labels.dropRight(labels.size - p.subgoals.size)) }
      else Some(labels)
  }

  /** Creates labels according to the number of subgoals of parent. */
  private def createLabels(parent: Option[BelleLabel], start: Int, end: Int): List[BelleLabel] = (start until end)
    .map(i =>
      parent match {
        case Some(l) => BelleSubLabel(l, s"$i")
        case None => BelleTopLevelLabel(s"$i")
      }
    )
    .toList

  /** Computes a single provable that contains the combined effect of all the piecewise computations. */
  protected final def combineBranchResults(results: Seq[BelleValue], parent: ProvableSig): BelleProvable = {
    // @todo preserve labels from parent p (turn new labels into sublabels)
    // @todo combine result defs?

    // @todo delayed substitution across results

    // @note when a subgoal is closed = replaced with 0 new subgoals: drop labels
    val (combinedResult, combinedLabels, combinedSubsts) = {
      results
        .zipWithIndex
        .reverse
        .foldLeft[(ProvableSig, Option[List[BelleLabel]], USubst)](
          (parent, None, USubst(scala.collection.immutable.Seq.empty))
        )({
          case (
                (cp: ProvableSig, clabels: Option[List[BelleLabel]], csubsts: USubst),
                (subderivation: BelleProvable, cidx: Int),
              ) =>
            val (substs, subProvable) =
              subderivation match {
                case p: BelleDelayedSubstProvable => p.parent match {
                    case Some((parent, i)) =>
                      if (
                        p.subst
                          .subsDefsInput
                          .exists({
                            case SubstitutionPair(FuncOf(n, Nothing), v: Variable) => n.name == v.name &&
                              n.index == v.index
                            case _ => false
                          })
                      ) {
                        if (p.p.isProved) {
                          (csubsts ++ p.subst ++ collectSubst(cp, cidx, parent), parent(p.p(p.subst), i))
                        } else {
                          // @note need to substitute p.p into p.parent and then p.parent into cp, but cannot apply substitutions because p.p is not proved
                          throw BelleUnfinished(
                            "Unable to merge provables: constified sub-derivation still has open goals\n  " +
                              p.p.prettyString + "\nand therefore cannot be applied to the " + i +
                              "-th subgoal of parent\n  " + parent.prettyString,
                            p.p.underlyingProvable,
                          )
                        }
                      } else (csubsts ++ p.subst ++ collectSubst(cp, cidx, parent), subderivation.p)
                    case None => (csubsts ++ p.subst ++ collectSubst(cp, cidx, subderivation.p), subderivation.p)
                  }
                // @note child tactics may expand definitions internally and succeed, so won't return a delayed provable (e.g. QE)
                case _ => (csubsts ++ collectSubst(cp, cidx, subderivation.p), subderivation.p)
              }
            val (_, combinedProvable) = applySubDerivation(cp, cidx, exhaustiveSubst(subProvable, csubsts), substs)
            // @todo want to keep names of cp abbreviated instead of substituted
            val combinedLabels: Option[List[BelleLabel]] =
              (clabels, subderivation.label) match {
                case (Some(origLabels), newLabels) =>
                  val labels = newLabels.getOrElse(createLabels(
                    origLabels.lift(cidx),
                    origLabels.length,
                    origLabels.length + subProvable.subgoals.length,
                  ))
                  if (labels.isEmpty) {
                    if (origLabels.size == combinedProvable.subgoals.size) Some(origLabels)
                    else Some(origLabels.patch(cidx, List.empty, 1)) // goal cidx was closed, remove label
                  } else {
                    val l :: rest = labels
                    Some(origLabels.patch(cidx, List(l), 1) ++ rest)
                  }
                case (None, Some(newLabels)) =>
                  if (newLabels.isEmpty && subderivation.p.isProved) None
                  else Some(createLabels(None, 0, cidx) ++ newLabels)
                case (None, None) => None
              }
            (combinedProvable, combinedLabels, substs)
        })
    }
    // @todo delayed parent?
    if (combinedSubsts.subsDefsInput.isEmpty)
      BelleProvable(combinedResult, if (combinedLabels.isEmpty) None else combinedLabels)
    else new BelleDelayedSubstProvable(
      combinedResult,
      if (combinedLabels.isEmpty) None else combinedLabels,
      combinedSubsts,
      None,
    )
  }

  /** Returns the result of running tactic `expr` on value `v`. */
  protected def runExpr(expr: BelleExpr, v: BelleValue): BelleValue = expr match {
    case builtIn: BuiltInTactic => v match {
        case BelleProvable(pr, lbl) =>
          try {
            val result = builtIn.execute(pr)
            // @todo builtIn tactic UnifyUSCalculus.US performs uniform substitutions that may need to be communicated
            // to the outside world but are not accessible here
            BelleProvable(result, adjustLabels(result, lbl))
          } catch { case e: BelleThrowable if throwWithDebugInfo => throw e.inContext(BelleDot, pr.prettyString) }
        case _ => throw new IllFormedTacticApplicationException(
            s"Attempted to apply a built-in tactic to a value that is not a Provable: ${v.getClass.getName}"
          ) // .inContext(BelleDot, "")
      }

    case SeqTactic(s) =>
      val nonNilSteps = s.filterNot(t => nilNames.contains(t.prettyString))
      nonNilSteps
        .zipWithIndex
        .foldLeft(v)({ case (v, (t, i)) =>
          try { apply(t, v) }
          catch {
            case e: BelleThrowable if throwWithDebugInfo =>
              throw e.inContext(
                SeqTactic(nonNilSteps.patch(i, Seq(e.context), 1)),
                "Failed component of ; sequential composition : " + t.prettyString,
              )
          }
        })

    case EitherTactic(s) =>
      for ((t, i) <- s.zipWithIndex.dropRight(1)) {
        try {
          val result = apply(t, v)
          if (progress(v, result)) return result
        } catch {
          case _: BelleProofSearchControl => // continue
          case e: BelleThrowable if throwWithDebugInfo =>
            throw e.inContext(
              EitherTactic(s.patch(i, Seq(e.context), 1)),
              "Failed component of | alternative composition : " + t.prettyString,
            )
        }
      }
      apply(s.last, v)

    case SaturateTactic(child) =>
      var prev: BelleValue = null
      var result: BelleValue = v

      breakable {
        do {
          prev = result
          try {
            result = apply(child, result)
            result match {
              case BelleProvable(pr, _) if pr.isProved => break()
              case _ => // continue
            }
          } catch { case _: BelleProofSearchControl => /*@note child no longer applicable */ result = prev }
        } while (progress(prev, result))
      }
      result

    case RepeatTactic(child, times) =>
      var result = v
      for (i <- 1 to times)
        try { result = apply(child, result) }
        catch {
          case e: BelleThrowable if throwWithDebugInfo =>
            throw e.inContext(
              RepeatTactic(e.context, times),
              "Failed while repating tactic " + i + "th iterate of " + times + ": " + child,
            )
          case e: BelleThrowable =>
            throw new IllFormedTacticApplicationException("RepeatTactic failed on repetition " + i, e)
        }
      result

    case CaseTactic(children) => v match {
        case BelleProvable(p, Some(labels)) =>
          if (p.subgoals.size != labels.size) throw new BelleUnexpectedProofStateError(
            "Number of labels does not match number of subgoals, got\nlabels  " +
              labels.map(_.prettyString).mkString("\n  ") + "\nfor " + p.prettyString,
            p.underlyingProvable,
          )
          if (children.size != labels.size) throw new IllFormedTacticApplicationException(
            "Number of cases does not match number of subgoals, got\ncases\n  " +
              children.map(_._1.prettyString).mkString("\n  ") + "\nfor\n  " +
              labels.map(_.prettyString).mkString("\n  ")
          )
          def getBranchTactic(l: BelleLabel): BelleExpr = children.filter(c => l.endsWith(c._1)).toList match {
            case c :: Nil => c._2
            case Nil => throw new IllFormedTacticApplicationException(
                "Tactic has branch labels\n\t" + children.map(_._1.prettyString).mkString("\n\t") +
                  "\nbut no case for branch\n\t" + l.prettyString
              )
            case c => throw new IllFormedTacticApplicationException(
                "Multiple labels apply to branch\n\t" + l.prettyString + "\nPlease disambiguate cases\n\t" +
                  c.map(_._1.prettyString).mkString("\n\t")
              )
          }
          apply(BranchTactic(labels.map(getBranchTactic)), v)
        case _ => throw new IllFormedTacticApplicationException("Case tactic applied on a proof state without labels")
      }

    case _: BuiltInPositionTactic | _: BuiltInLeftTactic | _: BuiltInRightTactic | _: CoreLeftTactic |
        _: CoreRightTactic | _: BuiltInTwoPositionTactic | _: DependentPositionTactic =>
      throw new IllFormedTacticApplicationException(
        s"Need to apply position tactic at a position before executing it: $expr(???)"
      ).inContext(expr, "")

    case AppliedPositionTactic(positionTactic, pos) => v match {
        case BelleProvable(pr, lbl) =>
          try {
            val result = positionTactic.apply(pos).computeResult(pr)
            BelleProvable(result, adjustLabels(result, lbl))
          } catch {
            case e: BelleThrowable if throwWithDebugInfo =>
              throw e.inContext(s"$positionTactic at $pos", pr.prettyString)
          }
      }

    case positionTactic @ AppliedBuiltinTwoPositionTactic(_, posOne, posTwo) => v match {
        case BelleProvable(pr, lbl) =>
          try {
            val result = positionTactic.computeResult(pr)
            BelleProvable(result, adjustLabels(result, lbl))
          } catch {
            case e: BelleThrowable if throwWithDebugInfo =>
              throw e.inContext(s"$positionTactic at $posOne, $posTwo", pr.prettyString)
          }
      }

    case d: DependentTactic =>
      try {
        val valueDependentTactic = d.computeExpr(v)
        apply(valueDependentTactic, v)
      } catch {
        case e: BelleThrowable => if (throwWithDebugInfo) throw e.inContext(d, v.prettyString) else throw e
        case e: Throwable =>
          val prefix = if (!d.isInternal) "Unable to execute tactic '" + d.name + "', cause: " else ""
          throw new IllFormedTacticApplicationException(prefix + e.getMessage, e).inContext(d, "")
      }

    case subst: InputTactic if subst.name == "US" =>
      val substs = collection
        .immutable
        .Seq(subst.inputs.head.asInstanceOf[List[SubstitutionPair]].map(sp => sp.what -> sp.repl): _*)
      apply(subst.computeExpr(), v) match {
        case p: BelleDelayedSubstProvable =>
          new BelleDelayedSubstProvable(p.p, p.label, p.subst ++ RenUSubst(substs).usubst, p.parent)
        case p: BelleProvable => new BelleDelayedSubstProvable(p.p, p.label, RenUSubst(substs).usubst, None)
        case v => v
      }

    case it: InputTactic =>
      try { apply(it.computeExpr(), v) }
      catch {
        case e: BelleThrowable => if (throwWithDebugInfo) throw e.inContext(it, v.prettyString) else throw e
        case e: Throwable => throw new IllFormedTacticApplicationException(
            "Unable to create input tactic '" + it.name + "', cause: " + e.getMessage,
            e,
          ).inContext(it, "")
      }

    case pt @ PartialTactic(child, None) =>
      try { apply(child, v) }
      catch {
        case e: BelleThrowable if throwWithDebugInfo =>
          throw e.inContext(pt, "Tactic declared as partial failed to run: " + child)
      }

    case pt @ PartialTactic(child, Some(label)) =>
      try {
        apply(child, v) match {
          case BelleProvable(pr, Some(labels)) => BelleProvable(pr, Some(labels.map(_.append(label))))
          case BelleProvable(pr, None) => BelleProvable(pr, Some(label :: Nil))
          case _ => throw new IllFormedTacticApplicationException(
              s"Attempted to give a label to a value that is not a Provable: ${v.getClass.getName}"
            ).inContext(BelleDot, "")
        }
      } catch {
        case e: BelleThrowable if throwWithDebugInfo =>
          throw e.inContext(pt, "Tactic declared as partial failed to run: " + child)
      }

    case OnAll(e) =>
      val provable = v match {
        case BelleProvable(p, _) => p
        case _ => throw new IllFormedTacticApplicationException("Cannot attempt OnAll with a non-Provable value.")
            .inContext(expr, "")
      }
      // @todo actually it would be nice to throw without wrapping inside an extra BranchTactic context
      try { apply(BranchTactic(Seq.tabulate(provable.subgoals.length)(_ => e)), v) }
      catch { case e: BelleThrowable if throwWithDebugInfo => throw e.inContext(OnAll(e.context), "") }

    case LabelBranch(label) => v match {
        case BelleProvable(pr, Some(labels)) => BelleProvable(pr, adjustLabels(pr, Some(labels.map(_.append(label)))))
        case BelleProvable(pr, None) =>
          if (label == BelleStartTxLabel || label == BelleRollbackTxLabel)
            BelleProvable(pr, adjustLabels(pr, Some(BelleLabelTx(BelleStartTxLabel, None) :: Nil)))
          else BelleProvable(pr, adjustLabels(pr, Some(label :: Nil)))
        case _ => throw new IllFormedTacticApplicationException(
            s"Attempted to give a label to a value that is not a Provable: ${v.getClass.getName}"
          ).inContext(BelleDot, "")
      }

    case DefTactic(_, _) => v // @note noop, but included for serialization purposes
    case ApplyDefTactic(DefTactic(_, t)) => apply(t, v)

    case named: NamedTactic => apply(named.tactic, v)

    case Let(abbr, value, inner) =>
      val (provable, lbl) = v match {
        case BelleProvable(p, l) => (p, l)
        case _ => throw new IllFormedTacticApplicationException("Cannot attempt Let with a non-Provable value.")
            .inContext(expr, "")
      }
      if (provable.subgoals.length != 1)
        throw new IllFormedTacticApplicationException("Let of multiple goals is not currently supported.")
          .inContext(expr, "")

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
      def flattenLets(
          it: BelleExpr,
          substs: List[SubstitutionPair],
          repls: List[(Expression, Expression)],
      ): (ProvableSig, USubst, BelleExpr) = it match {
        case Let(a, v, c) => flattenLets(c, substs :+ subst(a, v), repls :+ v -> a)
        case t => (
            ProvableSig.startProof(
              repls.foldLeft(provable.subgoals.head)({ case (s, (v, a)) => s.replaceAll(v, a) }),
              provable.defs,
            ),
            USubst(substs),
            t,
          )
      }

      // @todo flattening helps to avoid nested constifications, which are not yet supported by DelayedSubstProvable

      // @todo sometimes may want to offer some unification for: let j(x)=x^2>0 in tactic for sequent mentioning both x^2>0 and (x+y)^2>0 so j(x) and j(x+y).
      val (in: ProvableSig, us: USubst, innerMost) =
        try { flattenLets(inner, subst(abbr, value) :: Nil, value -> abbr :: Nil) }
        catch {
          case e: Throwable =>
            throw new IllFormedTacticApplicationException("Unable to start inner proof in let: " + e.getMessage, e)
        }
      logger.debug("INFO: " + expr + " considers\n" + in + "\nfor outer\n" + provable)
      apply(innerMost, BelleProvable(in, lbl)) match {
        case p: BelleDelayedSubstProvable =>
          try {
            val sub = p.p(us)
            val addSubst = collectSubst(provable, 0, sub)
            val substGoal = exhaustiveSubst(provable, addSubst)
            val substSub = exhaustiveSubst(sub, addSubst)
            new BelleDelayedSubstProvable(substGoal(substSub, 0), p.label, p.subst ++ addSubst, None)
          } catch {
            case _: SubstitutionClashException =>
              // happens on Let(v()=v, t) if t did not (yet) finish the proof, e.g., dIRule. postpone until subgoals are proved
              assert(p.parent.isEmpty)
              new BelleDelayedSubstProvable(p.p, p.label, p.subst ++ us, Some(provable, 0))
          }
        case BelleProvable(derivation, resultLbl) =>
          try { BelleProvable(provable(derivation(us), 0), resultLbl) }
          catch {
            case _: SubstitutionClashException =>
              // happens on Let(v()=v, t) if t did not (yet) finish the proof, e.g., dIRule. postpone until subgoals are proved
              new BelleDelayedSubstProvable(derivation, resultLbl, us, Some(provable, 0))
          }
        case e => throw new IllFormedTacticApplicationException(
            "Let expected a successful sub-derivation producing a BelleProvable, but got " + e
          )
      }

    case LetInspect(abbr, instantiator, inner) =>
      val (provable, lbl) = v match {
        case BelleProvable(p, l) => (p, l)
        case _ => throw new IllFormedTacticApplicationException("Cannot attempt LetInspect with a non-Provable value.")
            .inContext(expr, "")
      }
      if (provable.subgoals.length != 1)
        throw new IllFormedTacticApplicationException("LetInspect of multiple goals is not currently supported.")
          .inContext(expr, "")

      val in: ProvableSig = provable.sub(0)
      apply(inner, BelleProvable(in, lbl)) match {
        case BelleProvable(derivation, resultLbl) =>
          try {
            val value: Expression = instantiator(derivation)
            val us: USubst = USubst(SubstitutionPair(abbr, value) :: Nil)
            val backsubst: ProvableSig = derivation(us)
            BelleProvable(provable(backsubst, 0), resultLbl)
          } catch {
            case e: BelleThrowable => throw e.inContext(expr, "LetInspect backsubstitution failed")
            case e: ProverException =>
              throw new IllFormedTacticApplicationException("LetInspect backsubstitution failed", e)
                .inContext(expr.toString, "LetInspect backsubstitution failed")
          }
        case e =>
          throw new IllFormedTacticApplicationException("LetInspect expected successful sub-derivation, but got " + e)
      }

    case SearchAndRescueAgain(abbr, common, instantiator, continuation) =>
      val (provable, lbl) = v match {
        case BelleProvable(p, l) => (p, l)
        case _ => throw new IllFormedTacticApplicationException(
            "Cannot attempt SearchAndRescueAgain with a non-Provable value."
          ).inContext(expr, "")
      }
      if (provable.subgoals.length != 1) throw new IllFormedTacticApplicationException(
        "SearchAndRescueAgain of multiple goals is not currently supported."
      ).inContext(expr, "")

      val in: ProvableSig = provable.sub(0)
      apply(common, BelleProvable(in, lbl)) match {
        case BelleProvable(commonDerivation, lbl2) =>
          var lastProblem: ProverException = NoProverException
          while (!isDead) {
            val values = instantiator(commonDerivation, lastProblem)
            try {
              val us: USubst = USubst(abbr.zip(values).map({ case (what, repl) => what ~>> repl }))
              val backsubst: ProvableSig = commonDerivation(us)
              val remaining: BelleProvable = BelleProvable(provable(backsubst, 0), lbl2)
              apply(continuation, remaining) match {
                // return upon success of tactic
                case pr: BelleProvable => return pr
                case e: BelleThrowable => lastProblem = e
                case e => ???
              }
            } catch {
              // remember exception in lastProblem for next repetition
              case e: BelleThrowable => lastProblem = e
              case e: ProverException => lastProblem = e
            }
          }
          // cannot come here
          ???
        case e => throw new IllFormedTacticApplicationException(
            "SearchAndRescueAgain expected sub-derivation after running common"
          )
      }

    case t @ USubstPatternTactic(children) =>
      val provable = v match {
        case BelleProvable(p, _) => p
        case _ =>
          throw new IllFormedTacticApplicationException("Cannot attempt US unification with a non-Provable value.")
            .inContext(expr, "")
      }

      if (provable.subgoals.length != 1) throw new IllFormedTacticApplicationException(
        "Unification of multi-sequent patterns is not currently supported."
      ).inContext(expr, "")

      // @todo loop through all using the first one whose unificatoin and tactic application ends up being successful as opposed to committing to first unifiable case.
      // Attempt to find a child that unifies with the input.
      val unifications = children.map({ case (ty, expr) =>
        ty match {
          case SequentType(s) =>
            try { (RestrictedBiDiUnificationMatch(s, provable.subgoals.head), expr) }
            catch {
              // in contrast to .unifiable, this suppresses "Sequent un-unifiable Un-Unifiable" message, which clutter STDIO.
              // fall back to user-provided substitution
              case e: UnificationException =>
                // if (BelleExpr.DEBUG) println("USubst Pattern Incomplete -- could not find a unifier for any option" + t)
                (RenUSubst(Nil), expr)
            }
          case _ => throw new IllFormedTacticApplicationException("Cannot unify non-sequent types.").inContext(t, "")
        }
      })

      // @note try user-provided last unification
      val unification: (RestrictedBiDiUnificationMatch.Subst, RenUSubst => BelleExpr) =
        if (unifications.forall(_._1.isEmpty)) unifications.last else unifications.filterNot(_._1.isEmpty).head

      apply(unification._2(unification._1.asInstanceOf[RenUSubst]), v)

    // @todo this seems wrongly scoped, so AppliedDependentTwoPositionTactic and USubstPatternTactic are dead code
    case AppliedDependentTwoPositionTactic(t, p1, p2) =>
      val provable = v match {
        case BelleProvable(p, _) => p
        case _ => throw new IllFormedTacticApplicationException("two position tactics can only be run on Provables.")
      }
      apply(t.computeExpr(p1, p2).computeExpr(provable), v)

    case TryCatch(t, catchClazz, doCatch, doFinally) =>
      @tailrec
      def matchingCause(ex: Throwable): Option[Throwable] = {
        if (ex == null) None else if (catchClazz.isAssignableFrom(ex.getClass)) Some(ex) else matchingCause(ex.getCause)
      }

      Try(apply(t, v)) match {
        case Success(r) => doFinally match {
            case None => r
            case Some(ft) => apply(ft, r)
          }
        case Failure(ex) => matchingCause(ex) match {
            case None => doFinally match {
                case None => throw ex
                case Some(ft) =>
                  apply(ft, v)
                  throw ex
              }
            case Some(cause) => Try(apply(doCatch(catchClazz.cast(cause)), v)) match {
                case Success(r) => doFinally match {
                    case None => r
                    case Some(ft) => apply(ft, r)
                  }
                case Failure(ex) => doFinally match {
                    case None => throw ex
                    case Some(ft) =>
                      apply(ft, v)
                      throw ex
                  }
              }
          }
      }

    case Using(es, t) => v match {
        case bp @ BelleProvable(p, labels) =>
          val defs = p.defs

          def keepPos(seq: Sequent, pos: Position): Boolean = es.contains(seq(pos.top)) ||
            (t match {
              case d: AppliedDependentPositionTactic => d.locator.toPosition(seq).contains(pos)
              case d: AppliedPositionTactic => d.locator.toPosition(seq).contains(pos)
              case d: AppliedBuiltinTwoPositionTactic => d.posOne == pos || d.posTwo == pos
              case _ => false
            })

          def abbrv(f: Formula, i: Int, name: String): (PredOf, Option[SubstitutionPair]) = {
            val fv = StaticSemantics.freeVars(f).toSet.toList
            val dots = fv.zipWithIndex.map({ case (v, i) => (v, DotTerm(Real, Some(i))) })
            val arg = dots.map(_._1).reduceRightOption(Pair).getOrElse(Nothing)
            val dotsArg = dots.map(_._2).reduceRightOption(Pair).getOrElse(Nothing)
            val fDots = dots.foldRight(f)({ case ((what, repl), f) => Box(Assign(what, repl), f) })
            val fn = Function(name, Some(i), arg.sort, Bool, None)
            (PredOf(fn, arg), Some(SubstitutionPair(PredOf(fn, dotsArg), fDots)))
          }

          val missing = es
            .map(e => p.defs.implicitSubst(e))
            .filter(e => p.subgoals.map(p.defs.implicitSubst).map(s => (s.ante ++ s.succ).indexOf(e)).exists(_ < 0))
          if (missing.nonEmpty) throw new IllFormedTacticApplicationException(
            "Tactic t using es: Expressions\n" + missing.map(_.prettyString).mkString(",") +
              "\nare not present in provable\n" + p.prettyString
          )

          val filteredGoals = p
            .subgoals
            .map(s => {
              val antes =
                s.ante.zipWithIndex.map({ case (f, i) => if (keepPos(s, AntePos(i))) (f, None) else abbrv(f, i, "p_") })
              val succs =
                s.succ.zipWithIndex.map({ case (f, i) => if (keepPos(s, SuccPos(i))) (f, None) else abbrv(f, i, "q_") })

              (
                ProvableSig.startProof(Sequent(antes.map(_._1), succs.map(_._1)), defs),
                USubst(antes.flatMap(_._2) ++ succs.flatMap(_._2)),
              )
            })

          def backAssign(substs: Seq[SubstitutionPair]): BelleExpr = substs
            .map(s =>
              s.what match {
                case PredOf(Function(fn, Some(_), _, _, _), arg) =>
                  // @note positions are not stable, can't rely on p-index/q-index to refer to the right formula
                  TacticFactory.anon((seq: Sequent) => {
                    if (fn == "p_") {
                      // @note only accept matches with DotTerm LHS, otherwise already back-assigned predicates p(x,y,z)
                      // may match still abbreviated s.repl [x:=._0;][y:=._1;][z:=._2;]blah and find wrong index
                      val i = seq
                        .ante
                        .indexWhere(fml =>
                          RestrictedBiDiUnificationMatch.unifiable(s.repl, fml) match {
                            case Some(u) => u.usubst.subsDefsInput.map(_.what).forall(_.isInstanceOf[DotTerm])
                            case None => false
                          }
                        )
                      TactixLibrary.assignb(AntePos(i)) * StaticSemantics.symbols(arg).size
                    } else if (fn == "q_") {
                      val i = seq
                        .succ
                        .indexWhere(fml =>
                          RestrictedBiDiUnificationMatch.unifiable(s.repl, fml) match {
                            case Some(u) => u.usubst.subsDefsInput.map(_.what).forall(_.isInstanceOf[DotTerm])
                            case None => false
                          }
                        )
                      TactixLibrary.assignb(SuccPos(i)) * StaticSemantics.symbols(arg).size
                    } else throw new BelleCriticalException(
                      "Implementation error in Using: expected abbreviated p_ or q_"
                    ) {}
                  })
                case _ =>
                  throw new BelleCriticalException("Implementation error in Using: expected abbreviated p_ or q_") {}
              }
            )
            .reduceRightOption[BelleExpr](_ & _)
            .getOrElse(TactixLibrary.skip)

          def selfAssignFor(p: ProvableSig, substs: Seq[SubstitutionPair]): ProvableSig = substs
            .foldRight(p)({ case (s, pr) =>
                s.what match {
                  case PredOf(Function(fn, Some(i), _, _, _), arg) =>
                    if (fn == "p_") {
                      List
                        .fill(StaticSemantics.symbols(arg).size)(TactixLibrary.useFor(Ax.selfassignb)(AntePos(i)))
                        .foldRight(pr)({ case (t, p) => t(p) })
                    } else if (fn == "q_") {
                      List
                        .fill(StaticSemantics.symbols(arg).size)(TactixLibrary.useFor(Ax.selfassignb)(SuccPos(i)))
                        .foldRight(pr)({ case (t, p) => t(p) })
                    } else throw new BelleCriticalException(
                      "Implementation error in Using: expected abbreviated p_ or q_"
                    ) {}
                  case _ =>
                    throw new BelleCriticalException("Implementation error in Using: expected abbreviated p_ or q_") {}
                }
              }
            )

          val goalResults = filteredGoals.map({ case (p, s) =>
            val tr = apply(t, BelleProvable(p, labels)) match {
              case BelleProvable(rp, rl) => BelleProvable(selfAssignFor(rp(s), s.subsDefsInput), rl)
              case r => r
            }
            apply(OnAll(backAssign(s.subsDefsInput)), tr)
          })

          goalResults
            .zipWithIndex
            .reverse
            .foldLeft(bp)({ case (BelleProvable(p, l), (BelleProvable(sp, sl), i)) =>
              val substs = collectSubst(p, i, sp)
              val pSubst = exhaustiveSubst(p, substs)
              val spSubst = exhaustiveSubst(sp, substs)
              BelleProvable(
                pSubst(spSubst, i),
                l match {
                  case Some(labels) => Some(labels.patch(i, Nil, 1) ++ sl.getOrElse(Nil))
                  case None => sl match {
                      case Some(labels) => Some(
                          p.subgoals.indices.toList.map(i => BelleTopLevelLabel(i.toString)).patch(i, Nil, 1) ++ labels
                        )
                      case None => None
                    }
                },
              )
            })
      }

  }
}

/** Concurrent interpreter that runs parallel tactics concurrently. */
case class ConcurrentInterpreter(
    override val listeners: scala.collection.immutable.Seq[IOListener] = Nil,
    override val throwWithDebugInfo: Boolean = false,
) extends BelleBaseInterpreter(listeners, throwWithDebugInfo) with Logging {

  override def runExpr(expr: BelleExpr, v: BelleValue): BelleValue = expr match {
    case ParallelTactic(exprs) =>
      def firstToSucceed(in: List[Future[BelleValue]]): Future[BelleValue] = {
        val p = Promise[BelleValue]()
        // first to succeed completes promise `p`
        in.foreach(_.onComplete({
          case Success(v: BelleProvable) => p.trySuccess(v)
          case Success(_: BelleProofSearchControl) => // option just did not work out
          case Success(ex: BelleThrowable) => p.tryFailure(ex) // option had a critical exception: propagate
          case Failure(ex: java.util.concurrent.ExecutionException) => ex.getCause match {
              case _: BelleProofSearchControl => // concurrent option just did not work out
              case e: Throwable => p.tryFailure(e) // concurrent option had a critical exception: propagate
            }
          case Failure(_: CancellationException) => // option was cancelled from outside
          case Failure(ex) => p.tryFailure(ex) // propagate all other exceptions
        }))
        // if all fail then complete with the @todo aggregated failure
        Future
          .sequence(in)
          .foreach({
            case v if v.forall(_.isInstanceOf[BelleThrowable]) => p.tryFailure(v.head.asInstanceOf[BelleThrowable])
            case _ => false
          })
        p.future
      }

      // @note new internal interpreters because otherwise apply will notify listeners, which currently assume sequential tactic execution
      val interpreters = exprs.map(e => e -> ConcurrentInterpreter())
      val cancellables = interpreters.map({ case (e, i) => Cancellable(i(e, v)) })
      println("Waiting for first one to succeed: " + expr.prettyString)
      val result = Await.result(firstToSucceed(cancellables.map(_.future)), Duration.Inf)
      cancellables.foreach(_.cancel())
      interpreters.foreach(_._2.kill())
      println("Parallel done: " + expr.prettyString + "\n  with result: " + result.prettyString)
      result

    case ChooseSome(options, e) =>
      val opts = options()
      runExpr(ParallelTactic(opts.toList.map(e(_))), v)

    // @todo duplicate with LazySequentialInterpreter
    case BranchTactic(children) => v match {
        case BelleProvable(p, lbl) =>
          val defs = p.defs
          if (children.length != p.subgoals.length) throw new IllFormedTacticApplicationException(
            "<(e)(v) is only defined when len(e) = len(v), but " + children.length + "!=" + p.subgoals.length +
              " subgoals (v)\n" + p.subgoals.map(_.prettyString).mkString("\n===================\n")
          ).inContext(expr, "")
          // Compute the results of piecewise applications of children to provable subgoals.
          val results: Seq[BelleProvable] = children
            .zip(p.subgoals)
            .zipWithIndex
            .map({ case ((e_i, s_i), i) =>
              val ithResult =
                try {
                  apply(e_i, BelleProvable(ProvableSig.startProof(s_i, defs), lbl.getOrElse(Nil).lift(i).map(_ :: Nil)))
                } catch {
                  case e: BelleThrowable => throw e.inContext(
                      BranchTactic(children.map(c => if (c != e_i) c else e.context)),
                      "Failed on branch " + e_i,
                    )
                }
              ithResult match {
                case b: BelleProvable => b
                case _ => throw new BelleUnexpectedProofStateError(
                    "Each piecewise application in a branching tactic should result in a provable.",
                    p.underlyingProvable,
                  ).inContext(expr, "")
              }
            })

          combineBranchResults(results, p)
        case _ => throw new IllFormedTacticApplicationException(
            "Cannot perform branching on a goal that is not a BelleValue of type Provable."
          ).inContext(expr, "")
      }

    case _ => super.runExpr(expr, v)
  }

}

/** Sequential interpreter that runs parallel tactics as alternatives sequentially. */
abstract class SequentialInterpreter(
    override val listeners: scala.collection.immutable.Seq[IOListener],
    override val throwWithDebugInfo: Boolean = false,
) extends BelleBaseInterpreter(listeners, throwWithDebugInfo) with Logging {

  override def runExpr(expr: BelleExpr, v: BelleValue): BelleValue = expr match {
    case ParallelTactic(expr) => runExpr(EitherTactic(expr), v)
    case ChooseSome(options, e) =>
      val opts = options()
      var errors = ""
      var result: Option[BelleValue] = None
      while (result.isEmpty && !isDead && opts.hasNext) {
        val o = opts.next()
        logger.debug("ChooseSome: try " + o)
        val someResult: Option[BelleValue] =
          try { Some(apply(e(o), v)) }
          catch { case err: BelleProofSearchControl => errors += "in " + o + " " + err + "\n"; None }
        logger.debug("ChooseSome: try " + o + " got " + someResult)
        (someResult, e) match {
          case (Some(p: BelleProvable), _) => result = Some(p)
          case (Some(p), _: PartialTactic) => result = Some(p)
          case (Some(_), _) => errors += "option " + o + " " + new IllFormedTacticApplicationException(
              "Tactics must close their proof unless declared as partial. Use \"t partial\" instead of \"t\"."
            ).inContext(ChooseSome(options, e), "Failed option in ChooseSome: " + o) +
              "\n" // throw new BelleThrowable("Non-partials must close proof.").inContext(ChooseSome(options, e), "Failed option in ChooseSome: " + o)
          case (None, _) => // option o had an error, so consider next option
        }
      }
      result match {
        case Some(r) => r
        case None =>
          throw new BelleNoProgress(
            "ChooseSome did not succeed with any of its options"
          ) // .inContext(ChooseSome(options, e), "Failed all options in ChooseSome: " + opts.toList + "\n" + errors)
      }
    case _ => super.runExpr(expr, v)
  }

}

/** Sequential interpreter that explores branching tactics exhaustively, regardless of failure of some. */
case class ExhaustiveSequentialInterpreter(
    override val listeners: scala.collection.immutable.Seq[IOListener] = scala.collection.immutable.Seq(),
    override val throwWithDebugInfo: Boolean = false,
) extends SequentialInterpreter(listeners, throwWithDebugInfo) {

  override def runExpr(expr: BelleExpr, v: BelleValue): BelleValue = expr match {
    case BranchTactic(children) => v match {
        case BelleProvable(p, lbl) =>
          val defs = p.defs
          if (children.length != p.subgoals.length) throw new IllFormedTacticApplicationException(
            "<(e)(v) is only defined when len(e) = len(v), but " + children.length + "!=" + p.subgoals.length +
              " subgoals (v)\n" + p.subgoals.map(_.prettyString).mkString("\n===================\n")
          ).inContext(expr, "")
          // Compute the results of piecewise applications of children to provable subgoals.
          val results: Seq[Either[BelleValue, BelleThrowable]] = children
            .zip(p.subgoals)
            .zipWithIndex
            .map({ case ((e_i, s_i), i) =>
              try {
                Left(
                  apply(e_i, BelleProvable(ProvableSig.startProof(s_i, defs), lbl.getOrElse(Nil).lift(i).map(_ :: Nil)))
                )
              } catch {
                case e: BelleThrowable => Right(e.inContext(
                    BranchTactic(children.map(c => if (c != e_i) c else e.context)),
                    "Failed on branch " + e_i,
                  ))
              }
            })

          val errors = results.collect({ case Right(r) => r })
          // Critical if there is at least one critical
          if (errors.exists(_.isInstanceOf[BelleCriticalException]))
            throw errors.reduce[BelleThrowable](new CompoundCriticalException(_, _))
          else if (errors.nonEmpty)
            // Otherwise, non-critical exception
            // todo: add case for user input exception?
            throw errors.reduce[BelleThrowable](new CompoundProofSearchException(_, _))

          combineBranchResults(results.collect({ case Left(l) => l }), p)
        case _ => throw new IllFormedTacticApplicationException(
            "Cannot perform branching on a goal that is not a BelleValue of type Provable."
          ) // .inContext(expr, "")
      }
    case _ => super.runExpr(expr, v)
  }

}

/** Sequential interpreter that stops exploring branching on the first failing branch. */
case class LazySequentialInterpreter(
    override val listeners: scala.collection.immutable.Seq[IOListener] = scala.collection.immutable.Seq(),
    override val throwWithDebugInfo: Boolean = false,
) extends SequentialInterpreter(listeners, throwWithDebugInfo) {
  override def runExpr(expr: BelleExpr, v: BelleValue): BelleValue = expr match {
    case BranchTactic(children) => v match {
        case BelleProvable(p, lbl) =>
          if (children.length != p.subgoals.length) throw new IllFormedTacticApplicationException(
            "<(e)(v) is only defined when len(e) = len(v), but " + children.length + "!=" + p.subgoals.length +
              " subgoals (v)\n" + p.subgoals.map(_.prettyString).mkString("\n===================\n")
          ).inContext(expr, "")
          // Compute the results of piecewise applications of children to provable subgoals.
          val results: Seq[BelleProvable] = children
            .zipWithIndex
            .map({ case (e_i, i) =>
              val ithResult =
                try { apply(e_i, BelleProvable(p.sub(i), lbl.getOrElse(Nil).lift(i).map(_ :: Nil))) }
                catch {
                  case e: BelleThrowable => throw e.inContext(
                      BranchTactic(children.map(c => if (c != e_i) c else e.context)),
                      "Failed on branch " + e_i,
                    )
                }
              ithResult match {
                case b: BelleProvable => b
                case _ => throw new BelleUnexpectedProofStateError(
                    "Each piecewise application in a branching tactic should result in a provable.",
                    p.underlyingProvable,
                  ).inContext(expr, "")
              }
            })
          combineBranchResults(results, p)
        case _ => throw new IllFormedTacticApplicationException(
            "Cannot perform branching on a goal that is not a BelleValue of type Provable."
          ).inContext(expr, "")
      }
    case _ => super.runExpr(expr, v)
  }
}
