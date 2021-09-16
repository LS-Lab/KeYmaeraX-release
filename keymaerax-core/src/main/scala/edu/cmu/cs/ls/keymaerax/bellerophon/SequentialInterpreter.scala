/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.bellerophon

import java.util.concurrent.CancellationException
import edu.cmu.cs.ls.keymaerax.Logging
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.Generator.Generator
import edu.cmu.cs.ls.keymaerax.btactics.{Ax, ConfigurableGenerator, FixedGenerator, InvariantGenerator, TacticFactory, TactixInit, TactixLibrary}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.{PosInExpr, Position, RenUSubst, UnificationMatch}
import edu.cmu.cs.ls.keymaerax.parser.Declaration
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig

import scala.annotation.tailrec
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.{Await, Future, Promise}
import scala.concurrent.duration.Duration
import scala.util.{Failure, Success, Try}
import scala.util.control.Breaks._

/**
 * Sequential interpreter for Bellerophon tactic expressions.
  *
  * @param listeners Pre- and pos-processing hooks for step-wise tactic execution.
 * @author Nathan Fulton
 * @author Andre Platzer
 */
abstract class BelleBaseInterpreter(val listeners: scala.collection.immutable.Seq[IOListener], val throwWithDebugInfo: Boolean = false)
  extends Interpreter with Logging {
  var isDead: Boolean = false

  override def start(): Unit = isDead = false

  override def apply(expr: BelleExpr, v: BelleValue): BelleValue = {
    if (Thread.currentThread().isInterrupted || isDead) {
      //ToolProvider.tools().foreach(_.cancel()) //@todo breaks TimeoutAlternatives+Mathematica
      //@note end executing the interpreter when its thread gets interrupted
      throw new BelleAbort("Killed", "Execution stopped by killing the interpreter or interrupting the interpreter thread")
    }
    listeners.foreach(_.begin(v, expr))
    try {
      val exprResult = runExpr(expr, v)
      // preserve delayed substitutions
      val result = v match {
        case p: BelleDelayedSubstProvable => exprResult match {
          case fp: BelleDelayedSubstProvable =>
            assert(p.parent.isEmpty || p.parent == fp.parent)
            new BelleDelayedSubstProvable(fp.p, fp.label, p.defs, p.subst ++ fp.subst, p.parent)
          case fp: BelleProvable => new BelleDelayedSubstProvable(fp.p, fp.label, p.defs, p.subst, p.parent)
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
      } catch {
        case ex: Throwable => ex.initCause(e)
      }
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
      if (p.subgoals.size > labels.size) {
        Some(labels ++ List.fill(p.subgoals.size - labels.size)(labels.last))
      } else if (p.subgoals.size < labels.size) {
        Some(labels.dropRight(labels.size - p.subgoals.size))
      } else Some(labels)
  }

  /** Compares provables ignoring labels. */
  private def progress(prev: BelleValue, curr: BelleValue): Boolean = (prev, curr) match {
    case (BelleProvable(pPrev, _, _), BelleProvable(pCurr, _, _)) => pCurr != pPrev
    case _ => curr != prev
  }

  /** Returns the result of running tactic `expr` on value `v`. */
  protected def runExpr(expr: BelleExpr, v: BelleValue): BelleValue = expr match {
    case builtIn: BuiltInTactic => v match {
      case BelleProvable(pr, lbl, defs) => try {
        val result = builtIn.execute(pr)
        //@todo builtIn tactic UnifyUSCalculus.US performs uniform substitutions that may need to be communicated
        // to the outside world but are not accessible here
        BelleProvable(result, adjustLabels(result, lbl), defs)
      } catch {
        case e: BelleThrowable if throwWithDebugInfo => throw e.inContext(BelleDot, pr.prettyString)
      }
      case _ => throw new IllFormedTacticApplicationException(s"Attempted to apply a built-in tactic to a value that is not a Provable: ${v.getClass.getName}") //.inContext(BelleDot, "")
    }

    case SeqTactic(left, right) => left match {
      //@todo on ExpandDef: postpone right until after let
      //          case ExpandDef(DefExpression(Equal(FuncOf(name, arg), t))) =>
      //            val dotArg = if (arg.sort == Unit) Nothing else DotTerm()
      //            apply(Let(FuncOf(name, dotArg), t.replaceFree(arg, DotTerm()), right), v)
      //          case ExpandDef(DefExpression(Equiv(p@PredOf(name, arg), q))) =>
      //            val dotArg = if (arg.sort == Unit) Nothing else DotTerm()
      //            apply(Let(PredOf(name, dotArg), q.replaceFree(arg, DotTerm()), right), v)
      case _ =>
        val leftResult = try {
          apply(left, v)
        } catch {
          case e: BelleThrowable if throwWithDebugInfo => throw e.inContext(SeqTactic(e.context, right), "Failed left-hand side of &: " + left)
        }

        try {
          apply(right, leftResult)
        } catch {
          case e: BelleThrowable if throwWithDebugInfo => throw e.inContext(SeqTactic(e.context, right), "Failed right-hand side of &: " + right)
        }
    }

    case EitherTactic(left, right) => try {
      val leftResult = apply(left, v)
      if (!progress(v, leftResult)) {
        throw new BelleNoProgress("No progress of 'l' in 'l | r' " + expr)
      } else {
        leftResult
      }
    } catch {
      case eleft: BelleProofSearchControl =>
        try {
          apply(right, v)
        } catch {
          case eright: BelleThrowable if throwWithDebugInfo => throw eright.inContext(EitherTactic(eleft.context, eright.context),
                      "Failed: both left-hand side and right-hand side " + expr)
        }
    }

    case SaturateTactic(child) =>
      var prev: BelleValue = null
      var result: BelleValue = v

      breakable { do {
        prev = result
        try {
          result = apply(child, result)
          result match {
            case BelleProvable(pr, _, _) if pr.isProved => break
            case _ => // continue
          }
        } catch {
          case _: BelleProofSearchControl => /*@note child no longer applicable */ result = prev
        }
      } while (progress(prev, result)) }
      result

    case RepeatTactic(child, times) =>
      var result = v
      for (i <- 1 to times) try {
        result = apply(child, result)
      } catch {
        case e: BelleThrowable if throwWithDebugInfo => throw e.inContext(RepeatTactic(e.context, times),
                  "Failed while repating tactic " + i + "th iterate of " + times + ": " + child)
        case e: BelleThrowable => throw new IllFormedTacticApplicationException("RepeatTactic failed on repetition " + i, e)
      }
      result

    case CaseTactic(children) => v match {
      case BelleProvable(p, Some(labels), _) =>
        if (p.subgoals.size != labels.size) throw new BelleUnexpectedProofStateError("Number of labels does not match number of subgoals, got\nlabels  " + labels.map(_.prettyString).mkString("\n  ") + "\nfor " + p.prettyString, p.underlyingProvable)
        if (children.size != labels.size) throw new IllFormedTacticApplicationException("Number of cases does not match number of subgoals, got\ncases\n  " + children.map(_._1.prettyString).mkString("\n  ") + "\nfor\n  " + labels.map(_.prettyString).mkString("\n  "))
        def getBranchTactic(l: BelleLabel): BelleExpr = children.filter(c => l.endsWith(c._1)).toList match {
          case c :: Nil => c._2
          case Nil => throw new IllFormedTacticApplicationException("No case for branch " + l.prettyString)
          case c => throw new IllFormedTacticApplicationException("Multiple labels apply to branch " + l.prettyString + "; please disambiguate cases " + c.map(_._1.prettyString).mkString("::"))
        }
        apply(BranchTactic(labels.map(getBranchTactic)), v)
      case _ => throw new IllFormedTacticApplicationException("Case tactic applied on a proof state without labels")
    }

    case _: BuiltInPositionTactic | _:BuiltInLeftTactic | _:BuiltInRightTactic | _:CoreLeftTactic | _:CoreRightTactic | _:BuiltInTwoPositionTactic | _:DependentPositionTactic =>
      throw new IllFormedTacticApplicationException(s"Need to apply position tactic at a position before executing it: $expr(???)").inContext(expr, "")

    case AppliedPositionTactic(positionTactic, pos) => v match {
      case BelleProvable(pr, lbl, defs) => try {
        val result = positionTactic.apply(pos).computeResult(pr)
        BelleProvable(result, adjustLabels(result, lbl), defs)
      } catch {
        case e: BelleThrowable if throwWithDebugInfo => throw e.inContext(positionTactic + " at " + pos, pr.prettyString)
      }
    }

    case positionTactic@AppliedBuiltinTwoPositionTactic(_, posOne, posTwo) => v match {
      case BelleProvable(pr, lbl, defs) => try {
        val result = positionTactic.computeResult(pr)
        BelleProvable(result, adjustLabels(result, lbl), defs)
      } catch {
        case e: BelleThrowable if throwWithDebugInfo => throw e.inContext(positionTactic + " at " + posOne + ", " + posTwo, pr.prettyString)
      }
    }

    case d: DependentTactic => try {
      val valueDependentTactic = d.computeExpr(v)
      apply(valueDependentTactic, v)
    } catch {
      case e: BelleThrowable => if (throwWithDebugInfo) throw e.inContext(d, v.prettyString) else throw e
      case e: Throwable =>
        val prefix = if (!d.isInternal) "Unable to execute tactic '" + d.name + "', cause: " else ""
        throw new IllFormedTacticApplicationException(prefix + e.getMessage, e).inContext(d, "")
    }

    case subst: InputTactic if subst.name == "US" =>
      val substs = collection.immutable.Seq(subst.inputs.head.asInstanceOf[List[SubstitutionPair]].map(sp => sp.what -> sp.repl):_*)
      apply(subst.computeExpr(), v) match {
        case p: BelleDelayedSubstProvable => new BelleDelayedSubstProvable(p.p, p.label, p.defs, p.subst ++ RenUSubst(substs).usubst, p.parent)
        case p: BelleProvable => new BelleDelayedSubstProvable(p.p, p.label, p.defs, RenUSubst(substs).usubst, None)
        case v => v
      }

    case it: InputTactic => try {
      apply(it.computeExpr(), v)
    } catch {
      case e: BelleThrowable => if (throwWithDebugInfo) throw e.inContext(it, v.prettyString) else throw e
      case e: Throwable => throw new IllFormedTacticApplicationException("Unable to create input tactic '" + it.name + "', cause: " + e.getMessage, e).inContext(it, "")
    }

    case pt@PartialTactic(child, None) => try {
      apply(child, v)
    } catch {
      case e: BelleThrowable if throwWithDebugInfo => throw e.inContext(pt, "Tactic declared as partial failed to run: " + child)
    }

    case pt@PartialTactic(child, Some(label)) => try {
      apply(child, v) match {
        case BelleProvable(pr, Some(labels), defs) => BelleProvable(pr, Some(labels.map(_.append(label))), defs)
        case BelleProvable(pr, None, defs) => BelleProvable(pr, Some(label :: Nil), defs)
        case _ => throw new IllFormedTacticApplicationException(s"Attempted to give a label to a value that is not a Provable: ${v.getClass.getName}").inContext(BelleDot, "")
      }
    } catch {
      case e: BelleThrowable if throwWithDebugInfo => throw e.inContext(pt, "Tactic declared as partial failed to run: " + child)
    }

    case OnAll(e) =>
      val provable = v match {
        case BelleProvable(p, _, _) => p
        case _ => throw new IllFormedTacticApplicationException("Cannot attempt OnAll with a non-Provable value.").inContext(expr, "")
      }
      //@todo actually it would be nice to throw without wrapping inside an extra BranchTactic context
      try {
        apply(BranchTactic(Seq.tabulate(provable.subgoals.length)(_ => e)), v)
      } catch {
        case e: BelleThrowable if throwWithDebugInfo => throw e.inContext(OnAll(e.context), "")
      }

    case LabelBranch(label) => v match {
      case BelleProvable(pr, Some(labels), defs) => BelleProvable(pr, adjustLabels(pr, Some(labels.map(_.append(label)))), defs)
      case BelleProvable(pr, None, defs) =>
        if (label == BelleStartTxLabel || label == BelleRollbackTxLabel) BelleProvable(pr, adjustLabels(pr, Some(BelleLabelTx(BelleStartTxLabel, None) :: Nil)), defs)
        else BelleProvable(pr, adjustLabels(pr, Some(label :: Nil)), defs)
      case _ => throw new IllFormedTacticApplicationException(s"Attempted to give a label to a value that is not a Provable: ${v.getClass.getName}").inContext(BelleDot, "")
    }

    case DefTactic(_, _) => v //@note noop, but included for serialization purposes

    case Expand(n, s) => v match {
      case BelleProvable(_, _, defs) =>
        val subst = defs.substs.find(_.what match {
          case FuncOf(fn, _) => fn == n
          case PredOf(fn, _) => fn == n
          case PredicationalOf(fn, _) => fn == n
          case fn => fn == n
        }) match {
          case Some(pd) => s match {
            case None => USubst(List(pd))
            case Some(sd) =>
              if (pd.repl == sd.repl) USubst(List(pd))
              else throw new IllFormedTacticApplicationException("Expand " + n.prettyString + " substitutions disagree: " + sd.repl.prettyString + " != " + pd.repl.prettyString)
          }
          case None => s match {
            case Some(sd) => USubst(List(sd))
            case None => throw new IllFormedTacticApplicationException("Unknown symbol " + n.prettyString + ": neither file definitions nor proof definitions provide information how to expand")
          }
        }
        TactixInit.invSupplier = substGenerator(TactixLibrary.invSupplier, List(subst))
        apply(TactixLibrary.US(subst), v) match {
          case p: BelleDelayedSubstProvable => new BelleDelayedSubstProvable(p.p, p.label, p.defs, p.subst ++ subst, p.parent)
          case p: BelleProvable => new BelleDelayedSubstProvable(p.p, p.label, p.defs, subst, None)
          case v => v
        }
      case _ => throw new IllFormedTacticApplicationException("Attempted to expand a definition on a Non-Provable")
    }

    case ExpandAll(defs) => v match {
      case BelleProvable(_, _, proofdefs) =>
        val substs =
          if (defs.nonEmpty) {
            val diff = defs.filterNot({ case SubstitutionPair(what, repl) => proofdefs.substs.find(_.what == what).forall(_.repl == repl) })
            if (diff.isEmpty) defs.map(s => USubst(List(s)))
            else throw new IllFormedTacticApplicationException("ExpandAll substitutions disagree")
          } else proofdefs.substs.map(s => USubst(List(s)))
        if (substs.nonEmpty) {
          TactixInit.invSupplier = substGenerator(TactixLibrary.invSupplier, substs)
          val result = apply(substs.map(TactixLibrary.US).reduceOption[BelleExpr](_ & _).getOrElse(TactixLibrary.skip), v)
          result match {
            case p: BelleDelayedSubstProvable => new BelleDelayedSubstProvable(p.p, p.label, p.defs, p.subst ++ substs.reduceRight(_ ++ _), p.parent)
            case p: BelleProvable => new BelleDelayedSubstProvable(p.p, p.label, p.defs, substs.reduceRight(_ ++ _), None)
            case v => v
          }
        } else v
      case _ => throw new IllFormedTacticApplicationException("Attempted to expand a definition on a Non-Provable")
    }

    case ApplyDefTactic(DefTactic(_, t)) => apply(t, v)
    case named: NamedTactic => apply(named.tactic, v)

    case Let(abbr, value, inner) =>
      val (provable, lbl, defs) = v match {
        case BelleProvable(p, l, defs) => (p, l, defs)
        case _ => throw new IllFormedTacticApplicationException("Cannot attempt Let with a non-Provable value.").inContext(expr, "")
      }
      if (provable.subgoals.length != 1)
        throw new IllFormedTacticApplicationException("Let of multiple goals is not currently supported.").inContext(expr, "")

      val subst = (abbr, value) match {
        case (FuncOf(name, arg), t: Term) =>
          val dotArg = if (arg.sort == Unit) Nothing else arg.sort.toDots(0)._1
          SubstitutionPair(FuncOf(name, dotArg), t.replaceFree(arg, dotArg))
        case (PredOf(name, arg), f: Formula) =>
          val dotArg = if (arg.sort == Unit) Nothing else arg.sort.toDots(0)._1
          SubstitutionPair(PredOf(name, dotArg), f.replaceFree(arg, dotArg))
      }

      //@todo sometimes may want to offer some unification for: let j(x)=x^2>0 in tactic for sequent mentioning both x^2>0 and (x+y)^2>0 so j(x) and j(x+y).
      val us: USubst = USubst(subst :: Nil)
      val in: ProvableSig = try {
        ProvableSig.startProof(provable.subgoals.head.replaceAll(value, abbr))
      } catch {
        case e: Throwable => throw new IllFormedTacticApplicationException("Unable to start inner proof in let: " + e.getMessage, e)
      }
      logger.debug("INFO: " + expr + " considers\n" + in + "\nfor outer\n" + provable)
      //assert(us(in.conclusion) == provable.subgoals.head, "backsubstitution will ultimately succeed from\n" + in + "\nvia " + us + " to outer\n" + provable)
      apply(inner, BelleProvable(in, lbl, defs)) match {
        case p: BelleDelayedSubstProvable =>
          try {
            val sub = p.p(us)
            //@note inner may have expanded multiple levels of definitions at once; collect which ones
            // (favor over unification, which would flatten all definitions into a single substitution)
            @tailrec
            def collectSubst(goal: ProvableSig, sub: ProvableSig, subst: USubst): USubst = {
              if (goal.subgoals.head == sub.conclusion) subst
              else {
                val goalSym = StaticSemantics.symbols(goal.subgoals.head)
                val subSym = StaticSemantics.symbols(sub.conclusion)
                val diff = (goalSym -- subSym) ++ (subSym -- goalSym)
                val addSubst = USubst(p.defs.substs.filter(s => diff.intersect(StaticSemantics.symbols(s.what)).nonEmpty))
                collectSubst(goal(addSubst), sub(addSubst), subst ++ addSubst)
              }
            }
            val addSubst = collectSubst(provable, sub, USubst(List.empty))
            val substGoal = exhaustiveSubst(provable, addSubst)
            val substSub = exhaustiveSubst(sub, addSubst)
            new BelleDelayedSubstProvable(substGoal(substSub, 0), p.label, p.defs, p.subst ++ addSubst, p.parent)
          } catch {
            case _: SubstitutionClashException =>
              // happens on Let(v()=v, t) if t did not (yet) finish the proof, e.g., dIRule. postpone until subgoals are proved
              new BelleDelayedSubstProvable(p.p, p.label, p.defs, p.subst ++ us, p.parent)
          }
        case BelleProvable(derivation, resultLbl, resultDefs) =>
          try {
            BelleProvable(provable(derivation(us), 0), resultLbl, resultDefs)
          } catch {
            case _: SubstitutionClashException =>
              // happens on Let(v()=v, t) if t did not (yet) finish the proof, e.g., dIRule. postpone until subgoals are proved
              new BelleDelayedSubstProvable(derivation, resultLbl, resultDefs, us, Some(provable, 0))
          }
        case e => throw new IllFormedTacticApplicationException("Let expected a successful sub-derivation producing a BelleProvable, but got " + e)
      }


    case LetInspect(abbr, instantiator, inner) =>
      val (provable, lbl, defs) = v match {
        case BelleProvable(p, l, defs) => (p,l, defs)
        case _ => throw new IllFormedTacticApplicationException("Cannot attempt LetInspect with a non-Provable value.").inContext(expr, "")
      }
      if (provable.subgoals.length != 1)
        throw new IllFormedTacticApplicationException("LetInspect of multiple goals is not currently supported.").inContext(expr, "")

      val in: ProvableSig = ProvableSig.startProof(provable.subgoals.head)
      apply(inner, BelleProvable(in, lbl, defs)) match {
        case BelleProvable(derivation, resultLbl, resultDefs) =>
          try {
            val value: Expression = instantiator(derivation)
            val us: USubst = USubst(SubstitutionPair(abbr, value) :: Nil)
            val backsubst: ProvableSig = derivation(us)
            BelleProvable(provable(backsubst, 0), resultLbl, resultDefs)
          } catch {
            case e: BelleThrowable => throw e.inContext(expr, "LetInspect backsubstitution failed")
            case e: ProverException => throw new IllFormedTacticApplicationException("LetInspect backsubstitution failed", e).inContext(expr.toString, "LetInspect backsubstitution failed")
          }
        case e => throw new IllFormedTacticApplicationException("LetInspect expected successful sub-derivation, but got " + e)
      }


    case SearchAndRescueAgain(abbr, common, instantiator, continuation) =>
      val (provable, lbl, defs) = v match {
        case BelleProvable(p, l, defs) => (p, l, defs)
        case _ => throw new IllFormedTacticApplicationException("Cannot attempt SearchAndRescueAgain with a non-Provable value.").inContext(expr, "")
      }
      if (provable.subgoals.length != 1)
        throw new IllFormedTacticApplicationException("SearchAndRescueAgain of multiple goals is not currently supported.").inContext(expr, "")

      val in: ProvableSig = ProvableSig.startProof(provable.subgoals.head)
      apply(common, BelleProvable(in, lbl, defs)) match {
        case BelleProvable(commonDerivation, lbl2, defs2) =>
          var lastProblem: ProverException = NoProverException
          while (!isDead) {
            val values = instantiator(commonDerivation, lastProblem)
            try {
              val us: USubst = USubst(abbr.zip(values).map({ case (what, repl) => what ~>> repl }))
              val backsubst: ProvableSig = commonDerivation(us)
              val remaining: BelleProvable = BelleProvable(provable(backsubst, 0), lbl2, defs2)
              apply(continuation, remaining) match {
                // return upon success of tactic
                case pr: BelleProvable =>
                  println("SearchAndRescueAgain committed " + us)
                  return pr
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
        case e => throw new IllFormedTacticApplicationException("SearchAndRescueAgain expected sub-derivation after running common")
      }


    case t@USubstPatternTactic(children) =>
      val provable = v match {
        case BelleProvable(p, _, _) => p
        case _ => throw new IllFormedTacticApplicationException("Cannot attempt US unification with a non-Provable value.").inContext(expr, "")
      }

      if (provable.subgoals.length != 1)
        throw new IllFormedTacticApplicationException("Unification of multi-sequent patterns is not currently supported.").inContext(expr, "")

      //@todo loop through all using the first one whose unificatoin and tactic application ends up being successful as opposed to committing to first unifiable case.
      //Attempt to find a child that unifies with the input.
      val unifications = children.map({ case (ty, expr) =>
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

      apply(unification._2(unification._1.asInstanceOf[RenUSubst]), v)

    //@todo this seems wrongly scoped, so AppliedDependentTwoPositionTactic and USubstPatternTactic are dead code
    case AppliedDependentTwoPositionTactic(t, p1, p2) =>
      val provable = v match {
        case BelleProvable(p, _, _) => p
        case _ => throw new IllFormedTacticApplicationException("two position tactics can only be run on Provables.")
      }
      apply(t.computeExpr(p1, p2).computeExpr(provable), v)

    case TryCatch(t, catchClazz, doCatch, doFinally) =>
      @tailrec
      def matchingCause(ex: Throwable): Option[Throwable] = {
        if (ex == null) None
        else if (catchClazz.isAssignableFrom(ex.getClass)) Some(ex)
        else matchingCause(ex.getCause)
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
          case Some(cause) =>
            Try(apply(doCatch(catchClazz.cast(cause)), v)) match {
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
      case bp@BelleProvable(p, labels, defs) =>
        def keepPos(seq: Sequent, pos: Position): Boolean = es.contains(seq(pos.top)) || (t match {
          case d: AppliedDependentPositionTactic => d.locator.toPosition(seq).contains(pos)
          case d: AppliedPositionTactic => d.locator.toPosition(seq).contains(pos)
          case d: AppliedBuiltinTwoPositionTactic => d.posOne == pos || d.posTwo == pos
          case d: AppliedDependentPositionTacticWithAppliedInput => d.locator.toPosition(seq).contains(pos)
          case _ => false
        })

        def abbrv(f: Formula, i: Int, name: String): (PredOf, Option[SubstitutionPair]) = {
          val fv = StaticSemantics.freeVars(f).toSet.toList
          val dots = fv.zipWithIndex.map({ case (v, i) => (v, DotTerm(Real, Some(i))) })
          val arg = dots.map(_._1).reduceRightOption(Pair).getOrElse(Nothing)
          val dotsArg = dots.map(_._2).reduceRightOption(Pair).getOrElse(Nothing)
          val fDots = dots.foldRight(f)({ case ((what, repl), f) => Box(Assign(what, repl), f) })
          val fn = Function(name, Some(i), arg.sort, Bool, interpreted=false)
          (PredOf(fn, arg), Some(SubstitutionPair(PredOf(fn, dotsArg), fDots)))
        }

        val filteredGoals = p.subgoals.map(s => {
          val antes = s.ante.zipWithIndex.map({ case (f, i) =>
            if (keepPos(s, AntePos(i))) (f, None)
            else abbrv(f, i, "p_")
          })
          val succs = s.succ.zipWithIndex.map({ case (f, i) =>
            if (keepPos(s, SuccPos(i))) (f, None)
            else abbrv(f, i, "q_")
          })

          (ProvableSig.startProof(Sequent(antes.map(_._1), succs.map(_._1))),
            USubst(antes.flatMap(_._2) ++ succs.flatMap(_._2)))
        })

        def backAssign(substs: Seq[SubstitutionPair]): BelleExpr = substs.map(s => s.what match {
          case PredOf(Function(fn, Some(_), _, _, _), arg) =>
            //@note positions are not stable, can't rely on p-index/q-index to refer to the right formula
            TacticFactory.anon ((seq: Sequent) => {
              if (fn == "p_") {
                val i = seq.ante.indexWhere(fml => UnificationMatch.unifiable(s.repl, fml).nonEmpty)
                TactixLibrary.assignb(AntePos(i))*StaticSemantics.symbols(arg).size
              } else if (fn == "q_") {
                val i = seq.succ.indexWhere(fml => UnificationMatch.unifiable(s.repl, fml).nonEmpty)
                TactixLibrary.assignb(SuccPos(i))*StaticSemantics.symbols(arg).size
              } else throw new BelleCriticalException("Implementation error in Using: expected abbreviated p_ or q_") {}
            })
          case _ => throw new BelleCriticalException("Implementation error in Using: expected abbreviated p_ or q_") {}
        }).reduceRightOption[BelleExpr](_ & _).getOrElse(TactixLibrary.skip)

        def selfAssignFor(p: ProvableSig, substs: Seq[SubstitutionPair]): ProvableSig = substs.foldRight(p)({ case (s, pr) => s.what match {
          case PredOf(Function(fn, Some(i), _, _, _), arg) =>
            if (fn == "p_") {
              List.fill(StaticSemantics.symbols(arg).size)(TactixLibrary.useFor(Ax.selfassignb)(AntePos(i))).foldRight(pr)({ case (t, p) => t(p) })
            } else if (fn == "q_") {
              List.fill(StaticSemantics.symbols(arg).size)(TactixLibrary.useFor(Ax.selfassignb)(SuccPos(i))).foldRight(pr)({ case (t, p) => t(p) })
            } else throw new BelleCriticalException("Implementation error in Using: expected abbreviated p_ or q_") {}
          case _ => throw new BelleCriticalException("Implementation error in Using: expected abbreviated p_ or q_") {}
        }})

        val goalResults = filteredGoals.map({ case (p, s) =>
          val tr = apply(t, BelleProvable(p, labels, defs)) match {
            case BelleProvable(rp, rl, rdefs) => BelleProvable(selfAssignFor(rp(s), s.subsDefsInput), rl, rdefs)
            case r => r
          }
          apply(OnAll(backAssign(s.subsDefsInput)), tr)
        })

        goalResults.zipWithIndex.reverse.foldLeft(bp)({ case (BelleProvable(p, l, d), (BelleProvable(sp, sl, sd), i)) =>
          BelleProvable(p(sp, i),
            l match {
              case Some(labels) => Some(labels.patch(i, Nil, 1) ++ sl.getOrElse(Nil))
              case None => sl match {
                case Some(labels) => Some(p.subgoals.indices.toList.map(i => BelleTopLevelLabel(i.toString)).patch(i, Nil, 1) ++ labels)
                case None => None
              }
            },
            d++sd)
        })
    }

  }

  /** Maps sequents to BelleProvables. */
  protected def bval(s: Sequent, lbl: Option[List[BelleLabel]], defs: Declaration) = BelleProvable(ProvableSig.startProof(s), lbl, defs)

  /** Applies substitutions `substs` to the products of `generator` and returns a new generator that includes both
    * original and substituted products */
  private def substGenerator[A](generator: Generator[A], substs: List[USubst]): Generator[A] = {
    generator match {
      case c: ConfigurableGenerator[(Formula, Option[InvariantGenerator.ProofHint])] =>
        new ConfigurableGenerator(c.products ++ c.products.map(p =>
          substs.foldRight[(Expression, Seq[(Formula, Option[InvariantGenerator.ProofHint])])](p)({ case (s, p) => s(p._1) -> p._2.map({ case (f: Formula, h) => s(f) -> h })}))).asInstanceOf[Generator[A]]
      case c: FixedGenerator[(Formula, Option[InvariantGenerator.ProofHint])] =>
        FixedGenerator(c.list ++ c.list.map(p =>
          substs.foldRight[(Formula, Option[InvariantGenerator.ProofHint])](p)({ case (s, p) => s(p._1) -> p._2}))).asInstanceOf[Generator[A]]
      case _ => generator // other generators do not include predefined invariants; they produce their results when asked
    }
  }
}

/** Concurrent interpreter that runs parallel tactics concurrently. */
case class ConcurrentInterpreter(override val listeners: scala.collection.immutable.Seq[IOListener] = Nil,
                                 override val throwWithDebugInfo: Boolean = false)
  extends BelleBaseInterpreter(listeners, throwWithDebugInfo) with Logging {

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
        Future.sequence(in).foreach({
          case v if v.forall(_.isInstanceOf[BelleThrowable]) => p.tryFailure(v.head.asInstanceOf[BelleThrowable])
          case _ => false
        })
        p.future
      }

      //@note new internal interpreters because otherwise apply will notify listeners, which currently assume sequential tactic execution
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

    //@todo duplicate with LazySequentialInterpreter
    case BranchTactic(children) => v match {
      case BelleProvable(p, lbl, defs) =>
        if (children.length != p.subgoals.length)
          throw new IllFormedTacticApplicationException("<(e)(v) is only defined when len(e) = len(v), but " +
            children.length + "!=" + p.subgoals.length + " subgoals (v)\n" +
            p.subgoals.map(_.prettyString).mkString("\n===================\n")).inContext(expr, "")
        //Compute the results of piecewise applications of children to provable subgoals.
        val results: Seq[BelleProvable] = children.zip(p.subgoals).zipWithIndex.map({ case ((e_i, s_i), i) =>
          val ithResult = try {
            apply(e_i, bval(s_i, lbl.getOrElse(Nil).lift(i).map(_ :: Nil), defs))
          } catch {
            case e: BelleThrowable => throw e.inContext(BranchTactic(children.map(c => if (c != e_i) c else e.context)), "Failed on branch " + e_i)
          }
          ithResult match {
            case b: BelleProvable => b
            case _ => throw new BelleUnexpectedProofStateError("Each piecewise application in a branching tactic should result in a provable.", p.underlyingProvable).inContext(expr, "")
          }
        })

        // Compute a single provable that contains the combined effect of all the piecewise computations.
        // The Int is threaded through to keep track of indexes changing, which can occur when a subgoal
        // is replaced with 0 new subgoals (also means: drop labels).
        def createLabels(start: Int, end: Int): List[BelleLabel] = (start until end).map(i => BelleTopLevelLabel(s"$i")).toList

        //@todo preserve labels from parent p (turn new labels into sublabels)
        //@todo combine result definitions?
        val (combinedResult, _, combinedLabels, combinedSubsts) =
          results.foldLeft[(ProvableSig, Int, Option[List[BelleLabel]], USubst)]((p, 0, None, USubst(scala.collection.immutable.Seq.empty)))({
            case ((cp: ProvableSig, cidx: Int, clabels: Option[List[BelleLabel]], csubsts: USubst), subderivation: BelleProvable) =>
              val substs = subderivation match {
                case p: BelleDelayedSubstProvable => csubsts ++ p.subst
                case _ => csubsts
              }
              val (_, combinedProvable, nextIdx) = applySubDerivation(cp, cidx, exhaustiveSubst(subderivation.p, csubsts), substs)
              val combinedLabels: Option[List[BelleLabel]] = (clabels, subderivation.label) match {
                case (Some(origLabels), Some(newLabels)) =>
                  Some(origLabels.patch(cidx, newLabels, 0))
                case (Some(origLabels), None) =>
                  Some(origLabels.patch(cidx, createLabels(origLabels.length, origLabels.length + subderivation.p.subgoals.length), 0))
                case (None, Some(newLabels)) =>
                  Some(createLabels(0, cidx) ++ newLabels)
                case (None, None) => None
              }
              (combinedProvable, nextIdx, combinedLabels, substs)
          })
        //@todo delayed parent?
        if (combinedSubsts.subsDefsInput.isEmpty) BelleProvable(combinedResult, if (combinedLabels.isEmpty) None else combinedLabels, defs)
        else new BelleDelayedSubstProvable(combinedResult, if (combinedLabels.isEmpty) None else combinedLabels, defs, combinedSubsts, None)
      case _ => throw new IllFormedTacticApplicationException("Cannot perform branching on a goal that is not a BelleValue of type Provable.").inContext(expr, "")
    }

    case _ => super.runExpr(expr, v)
  }

}

/** Sequential interpreter that runs parallel tactics as alternatives sequentially. */
abstract class SequentialInterpreter(override val listeners: scala.collection.immutable.Seq[IOListener],
                                     override val throwWithDebugInfo: Boolean = false)
  extends BelleBaseInterpreter(listeners, throwWithDebugInfo) with Logging {

  override def runExpr(expr: BelleExpr, v: BelleValue): BelleValue = expr match {
    case ParallelTactic(expr) => runExpr(expr.reduceRight(EitherTactic), v)
    case ChooseSome(options, e) =>
      val opts = options()
      var errors = ""
      var result: Option[BelleValue] = None
      while (result.isEmpty && !isDead && opts.hasNext) {
        val o = opts.next()
        logger.debug("ChooseSome: try " + o)
        val someResult: Option[BelleValue] = try {
          Some(apply(e(o), v))
        } catch { case err: BelleProofSearchControl => errors += "in " + o + " " + err + "\n"; None }
        logger.debug("ChooseSome: try " + o + " got " + someResult)
        (someResult, e) match {
          case (Some(p: BelleProvable), _) => result = Some(p)
          case (Some(p), _: PartialTactic) => result = Some(p)
          case (Some(_), _) => errors += "option " + o + " " + new IllFormedTacticApplicationException("Tactics must close their proof unless declared as partial. Use \"t partial\" instead of \"t\".").inContext(ChooseSome(options, e), "Failed option in ChooseSome: " + o) + "\n" // throw new BelleThrowable("Non-partials must close proof.").inContext(ChooseSome(options, e), "Failed option in ChooseSome: " + o)
          case (None, _) => // option o had an error, so consider next option
        }
      }
      result match {
        case Some(r) => r
        case None => throw new BelleNoProgress("ChooseSome did not succeed with any of its options") //.inContext(ChooseSome(options, e), "Failed all options in ChooseSome: " + opts.toList + "\n" + errors)
      }
    case _ => super.runExpr(expr, v)
  }

}

/** Sequential interpreter that explores branching tactics exhaustively, regardless of failure of some. */
case class ExhaustiveSequentialInterpreter(override val listeners: scala.collection.immutable.Seq[IOListener] = scala.collection.immutable.Seq(),
                                           override val throwWithDebugInfo: Boolean = false)
  extends SequentialInterpreter(listeners, throwWithDebugInfo) {

  override def runExpr(expr: BelleExpr, v: BelleValue): BelleValue = expr match {
    case BranchTactic(children) => v match {
      case BelleProvable(p, lbl, defs) =>
        if (children.length != p.subgoals.length)
          throw new IllFormedTacticApplicationException("<(e)(v) is only defined when len(e) = len(v), but " +
            children.length + "!=" + p.subgoals.length + " subgoals (v)\n" +
            p.subgoals.map(_.prettyString).mkString("\n===================\n")).inContext(expr, "")
        //Compute the results of piecewise applications of children to provable subgoals.
        val results: Seq[Either[BelleValue, BelleThrowable]] =
          children.zip(p.subgoals).zipWithIndex.map({ case ((e_i, s_i), i) =>
            try {
              Left(apply(e_i, bval(s_i, lbl.getOrElse(Nil).lift(i).map(_ :: Nil), defs)))
            } catch {
              case e: BelleThrowable =>
                Right(e.inContext(BranchTactic(children.map(c => if (c != e_i) c else e.context)), "Failed on branch " + e_i))
            }
          })

        val errors = results.collect({case Right(r) => r})
        // Critical if there is at least one critical
        if (errors.exists(_.isInstanceOf[BelleCriticalException])) throw errors.reduce[BelleThrowable](new CompoundCriticalException(_, _))
        else if (errors.nonEmpty)
          // Otherwise, non-critical exception
          //todo: add case for user input exception?
          throw errors.reduce[BelleThrowable](new CompoundProofSearchException(_, _))

        // Compute a single provable that contains the combined effect of all the piecewise computations.
        // The Int is threaded through to keep track of indexes changing, which can occur when a subgoal
        // is replaced with 0 new subgoals (also means: drop labels).
        def createLabels(parent: Option[BelleLabel], start: Int, end: Int): List[BelleLabel] =
          (start until end).map(i => parent match { case Some(l) => BelleSubLabel(l, s"$i")
          case None => BelleTopLevelLabel(s"$i") }).toList

        //@todo preserve labels from parent p (turn new labels into sublabels)
        //@todo combine result defs?
        val (combinedResult, _, combinedLabels, combinedSubsts) =
          results.collect({case Left(l) => l}).foldLeft[(ProvableSig, Int, Option[List[BelleLabel]], USubst)]((p, 0, None, USubst(scala.collection.immutable.Seq.empty)))({
            case ((cp: ProvableSig, cidx: Int, clabels: Option[List[BelleLabel]], csubsts), subderivation: BelleProvable) =>
              val substs = subderivation match {
                case p: BelleDelayedSubstProvable => csubsts ++ p.subst
                case _ => csubsts
              }
              val (_, combinedProvable, nextIdx) = applySubDerivation(cp, cidx, exhaustiveSubst(subderivation.p, csubsts), substs)
              val combinedLabels: Option[List[BelleLabel]] = (clabels, subderivation.label) match {
                case (Some(origLabels), Some(newLabels)) =>
                  if (newLabels.isEmpty) Some(origLabels)
                  else {
                    val l :: rest = newLabels
                    Some(origLabels.patch(cidx, List(l), 0) ++ rest)
                  }
                case (Some(origLabels), None) =>
                  val labels = createLabels(origLabels.lift(cidx), origLabels.length, origLabels.length + subderivation.p.subgoals.length)
                  if (labels.isEmpty) Some(origLabels)
                  else {
                    val l :: rest = labels
                    Some(origLabels.patch(cidx, List(l), 0) ++ rest)
                  }
                case (None, Some(newLabels)) =>
                  Some(createLabels(None, 0, cidx) ++ newLabels)
                case (None, None) => None
              }
              (combinedProvable, nextIdx, combinedLabels, substs)
          })
        //@todo delayed parent?
        if (combinedSubsts.subsDefsInput.isEmpty) BelleProvable(combinedResult, if (combinedLabels.isEmpty) None else combinedLabels, defs)
        else new BelleDelayedSubstProvable(combinedResult, if (combinedLabels.isEmpty) None else combinedLabels, defs, combinedSubsts, None)
      case _ => throw new IllFormedTacticApplicationException("Cannot perform branching on a goal that is not a BelleValue of type Provable.") //.inContext(expr, "")
    }
    case _ => super.runExpr(expr, v)
  }

}

/** Sequential interpreter that stops exploring branching on the first failing branch. */
case class LazySequentialInterpreter(override val listeners: scala.collection.immutable.Seq[IOListener] = scala.collection.immutable.Seq(),
                                     override val throwWithDebugInfo: Boolean = false) extends SequentialInterpreter(listeners, throwWithDebugInfo) {
  override def runExpr(expr: BelleExpr, v: BelleValue): BelleValue = expr match {
    case BranchTactic(children) => v match {
      case BelleProvable(p, lbl, defs) =>
        if (children.length != p.subgoals.length)
          throw new IllFormedTacticApplicationException("<(e)(v) is only defined when len(e) = len(v), but " +
            children.length + "!=" + p.subgoals.length + " subgoals (v)\n" +
            p.subgoals.map(_.prettyString).mkString("\n===================\n")).inContext(expr, "")
        //Compute the results of piecewise applications of children to provable subgoals.
        val results: Seq[BelleProvable] = children.zip(p.subgoals).zipWithIndex.map({ case ((e_i, s_i), i) =>
          val ithResult = try {
            apply(e_i, bval(s_i, lbl.getOrElse(Nil).lift(i).map(_ :: Nil), defs))
          } catch {
            case e: BelleThrowable => throw e.inContext(BranchTactic(children.map(c => if (c != e_i) c else e.context)), "Failed on branch " + e_i)
          }
          ithResult match {
            case b: BelleProvable => b
            case _ => throw new BelleUnexpectedProofStateError("Each piecewise application in a branching tactic should result in a provable.", p.underlyingProvable).inContext(expr, "")
          }
        })

        // Compute a single provable that contains the combined effect of all the piecewise computations.
        // The Int is threaded through to keep track of indexes changing, which can occur when a subgoal
        // is replaced with 0 new subgoals (also means: drop labels).
        def createLabels(start: Int, end: Int): List[BelleLabel] = (start until end).map(i => BelleTopLevelLabel(s"$i")).toList

        //@todo preserve labels from parent p (turn new labels into sublabels)
        //@todo combine result defs?
        val (combinedResult, _, combinedLabels, combinedSubsts) =
          results.foldLeft[(ProvableSig, Int, Option[List[BelleLabel]], USubst)]((p, 0, None, USubst(scala.collection.immutable.Seq.empty)))({
            case ((cp: ProvableSig, cidx: Int, clabels: Option[List[BelleLabel]], csubsts: USubst), subderivation: BelleProvable) =>
              val substs = subderivation match {
                case p: BelleDelayedSubstProvable => csubsts ++ p.subst
                case _ => csubsts
              }
              val (_, combinedProvable, nextIdx) = applySubDerivation(cp, cidx, exhaustiveSubst(subderivation.p, csubsts), substs)
              //@todo want to keep names of cp abbreviated instead of substituted
              val combinedLabels: Option[List[BelleLabel]] = (clabels, subderivation.label) match {
                case (Some(origLabels), Some(newLabels)) =>
                  if (newLabels.isEmpty) Some(origLabels)
                  else {
                    val l :: rest = newLabels
                    Some(origLabels.patch(cidx, List(l), 0) ++ rest)
                  }
                case (Some(origLabels), None) =>
                  val labels = createLabels(origLabels.length, origLabels.length + subderivation.p.subgoals.length)
                  if (labels.isEmpty) Some(origLabels)
                  else {
                    val l :: rest = labels
                    Some(origLabels.patch(cidx, List(l), 0) ++ rest)
                  }
                case (None, Some(newLabels)) =>
                  Some(createLabels(0, cidx) ++ newLabels)
                case (None, None) => None
              }
              (combinedProvable, nextIdx, combinedLabels, substs)
            })
        //@todo delayed parent?
        if (combinedSubsts.subsDefsInput.isEmpty) BelleProvable(combinedResult, if (combinedLabels.isEmpty) None else combinedLabels, defs)
        else new BelleDelayedSubstProvable(combinedResult, if (combinedLabels.isEmpty) None else combinedLabels, defs, combinedSubsts, None)
      case _ => throw new IllFormedTacticApplicationException("Cannot perform branching on a goal that is not a BelleValue of type Provable.").inContext(expr, "")
    }
    case _ => super.runExpr(expr, v)
  }
}