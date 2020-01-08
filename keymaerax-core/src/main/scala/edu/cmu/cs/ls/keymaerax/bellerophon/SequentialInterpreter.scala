/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.bellerophon

import java.util.concurrent.ExecutionException

import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BellePrettyPrinter
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.Generator.Generator
import edu.cmu.cs.ls.keymaerax.btactics.{ConfigurableGenerator, FixedGenerator, InvariantGenerator, TactixLibrary}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.lemma.LemmaDBFactory
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tools.ToolEvidence
import org.apache.logging.log4j.scala.Logging

import scala.annotation.tailrec
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.{Await, TimeoutException}
import scala.concurrent.duration.{Duration, MILLISECONDS}
import scala.util.control.Breaks._

/**
 * Sequential interpreter for Bellerophon tactic expressions.
  *
  * @param listeners Pre- and pos-processing hooks for step-wise tactic execution.
 * @author Nathan Fulton
 * @author Andre Platzer
 */
abstract class SequentialInterpreter(val listeners: scala.collection.immutable.Seq[IOListener], val throwWithDebugInfo: Boolean = false)
  extends Interpreter with Logging {
  var isDead: Boolean = false

  override def apply(expr: BelleExpr, v: BelleValue): BelleValue = {
    if (Thread.currentThread().isInterrupted || isDead) {
      //@todo kill the running tactic (cancel QE), here or in kill
      //@note end executing the interpreter when its thread gets interrupted
      //@todo throw an error that is easier to identify (for now: irrelevant, since Hydra Future already gone when we throw here)
      throw new BelleThrowable("Execution stopped by killing the interpreter or interrupting the interpreter thread")
    }
    listeners.foreach(_.begin(v, expr))
    try {
      val exprResult = runExpr(expr, v)
      // preserve delayed substitutions
      val result = v match {
        case p: BelleDelayedSubstProvable => exprResult match {
          case fp: BelleDelayedSubstProvable => new BelleDelayedSubstProvable(fp.p, fp.label, p.subst ++ fp.subst)
          case fp: BelleProvable => new BelleDelayedSubstProvable(fp.p, fp.label, p.subst)
          case _ => exprResult
        }
        case _ => exprResult
      }
      listeners.foreach(_.end(v, expr, Left(result)))
      result
    } catch {
      case err: BelleThrowable =>
        listeners.foreach(_.end(v, expr, Right(err)))
        throw err
      case e: StackOverflowError =>
        // unable to recover, listeners are likely corrupted
        logger.fatal("Fatal error: stack overflow, please restart KeYmaera X with increased stack size")
        throw new BelleThrowable("Fatal error: stack overflow, please restart KeYmaera X with increased stack size", e)
      case e: Throwable =>
        val be = new BelleThrowable("Error in sequential interpreter: " + e.getMessage, e)
        listeners.foreach(_.end(v, expr, Right(be)))
        throw be
    }
  }

  override def kill(): Unit = {
    isDead = true
    listeners.foreach(_.kill())
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

  /** Returns the result of running tactic `expr` on value `v`. */
  protected def runExpr(expr: BelleExpr, v: BelleValue): BelleValue = expr match {
    case builtIn: BuiltInTactic => v match {
      case BelleProvable(pr, lbl) => try {
        val result = builtIn.execute(pr)
        //@todo builtIn tactic UnifyUSCalculus.US performs uniform substitutions that may need to be communicated
        // to the outside world but are not accessible here
        BelleProvable(result, adjustLabels(result, lbl))
      } catch {
        case e: BelleThrowable if throwWithDebugInfo => throw e.inContext(BelleDot, pr.prettyString)
      }
      case _ => throw new BelleThrowable(s"Attempted to apply a built-in tactic to a value that is not a Provable: ${v.getClass.getName}") //.inContext(BelleDot, "")
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
      apply(left, v)
    } catch {
      case eleft: BelleThrowable =>
        try {
          apply(right, v)
        } catch {
          case eright: BelleThrowable if throwWithDebugInfo => throw eright.inContext(EitherTactic(eleft.context, eright.context),
                      "Failed: both left-hand side and right-hand side " + expr)
        }
    }

    case BranchTactic(children) => v match {
      case BelleProvable(p, lbl) =>
        if (children.length != p.subgoals.length)
          throw new BelleThrowable("<(e)(v) is only defined when len(e) = len(v), but " +
            children.length + "!=" + p.subgoals.length + " subgoals (v)\n" +
            p.subgoals.map(_.prettyString).mkString("\n===================\n")).inContext(expr, "")
        //Compute the results of piecewise applications of children to provable subgoals.
        val results: Seq[Either[BelleValue, BelleThrowable]] =
          children.zip(p.subgoals).zipWithIndex.map({ case ((e_i, s_i), i) =>
            try {
              Left(apply(e_i, bval(s_i, lbl.getOrElse(Nil).lift(i).map(_ :: Nil))))
            } catch {
              case e: BelleThrowable =>
                Right(e.inContext(BranchTactic(children.map(c => if (c != e_i) c else e.context)), "Failed on branch " + e_i))
            }
          })

        val errors = results.collect({case Right(r) => r})
        if (errors.nonEmpty) throw errors.reduce[BelleThrowable](new CompoundException(_, _))

        // Compute a single provable that contains the combined effect of all the piecewise computations.
        // The Int is threaded through to keep track of indexes changing, which can occur when a subgoal
        // is replaced with 0 new subgoals (also means: drop labels).
        def createLabels(parent: Option[BelleLabel], start: Int, end: Int): List[BelleLabel] =
          (start until end).map(i => parent match { case Some(l) => BelleSubLabel(l, s"$i")
                                                    case None => BelleTopLevelLabel(s"$i") }).toList

        //@todo preserve labels from parent p (turn new labels into sublabels)
        val combinedEffect =
          results.collect({case Left(l) => l}).foldLeft[(ProvableSig, Int, Option[List[BelleLabel]])]((p, 0, None))({
            case ((cp: ProvableSig, cidx: Int, clabels: Option[List[BelleLabel]]), subderivation: BelleProvable) =>
              val (combinedProvable, nextIdx) = replaceConclusion(cp, cidx, subderivation.p, subderivation match {
                case p: BelleDelayedSubstProvable => Some(p.subst)
                case _ => None
              })
              val combinedLabels: Option[List[BelleLabel]] = (clabels, subderivation.label) match {
                case (Some(origLabels), Some(newLabels)) =>
                  Some(origLabels.patch(cidx, newLabels, 0))
                case (Some(origLabels), None) =>
                  Some(origLabels.patch(cidx, createLabels(origLabels.lift(cidx), origLabels.length, origLabels.length + subderivation.p.subgoals.size), 0))
                case (None, Some(newLabels)) =>
                  Some(createLabels(None, 0, cidx) ++ newLabels)
                case (None, None) => None
              }
              (combinedProvable, nextIdx, combinedLabels)
            })
        BelleProvable(combinedEffect._1, if (combinedEffect._3.isEmpty) None else combinedEffect._3)
      case _ => throw new BelleThrowable("Cannot perform branching on a goal that is not a BelleValue of type Provable.") //.inContext(expr, "")
    }

    case AfterTactic(left, right) =>
      val leftResult: Either[BelleValue, BelleValue] = try {
        Left(apply(left, v))
      } catch {
        case eleft: BelleThrowable =>
          try {
            Right(apply(right, new BelleThrowable(eleft.getMessage, eleft.getCause) with BelleValue))
          } catch {
            case eright: BelleThrowable if throwWithDebugInfo => throw eright.inContext(EitherTactic(eleft.context, eright.context),
                          "Failed: both left-hand side and right-hand side " + expr)
          }
      }
      leftResult match {
        case Left(lr: BelleValue) => apply(right, lr)
        case Right(rr: BelleValue) => rr
      }

    case SaturateTactic(child) =>
      var prev: BelleValue = null
      var result: BelleValue = v
      breakable { do {
        prev = result
        try {
          result = apply(child, result)
          result match {
            case BelleProvable(pr, _) if pr.isProved => break
            case _ => // continue
          }
        } catch {
          case e: BelleThrowable => /*@note child no longer applicable */ result = prev
        }
      } while (result != prev) }
      result

    case RepeatTactic(child, times) =>
      var result = v
      for (i <- 1 to times) try {
        result = apply(child, result)
      } catch {
        case e: BelleThrowable if throwWithDebugInfo => throw e.inContext(RepeatTactic(e.context, times),
                  "Failed while repating tactic " + i + "th iterate of " + times + ": " + child)
      }
      result

    case _: BuiltInPositionTactic | _:BuiltInLeftTactic | _:BuiltInRightTactic | _:BuiltInTwoPositionTactic | _:DependentPositionTactic =>
      throw new BelleThrowable(s"Need to apply position tactic at a position before executing it: $expr(???)").inContext(expr, "")

    case AppliedPositionTactic(positionTactic, pos) => v match {
      case BelleProvable(pr, lbl) => try {
        val result = positionTactic.apply(pos).computeResult(pr)
        BelleProvable(result, adjustLabels(result, lbl))
      } catch {
        case e: BelleThrowable if throwWithDebugInfo => throw e.inContext(positionTactic + " at " + pos, pr.prettyString)
      }
    }

    case positionTactic@AppliedBuiltinTwoPositionTactic(_, posOne, posTwo) => v match {
      case BelleProvable(pr, lbl) => try {
        val result = positionTactic.computeResult(pr)
        BelleProvable(result, adjustLabels(result, lbl))
      } catch {
        case e: BelleThrowable if throwWithDebugInfo => throw e.inContext(positionTactic + " at " + posOne + ", " + posTwo, pr.prettyString)
      }
    }

    case d: DependentTactic => try {
      val valueDependentTactic = d.computeExpr(v)
      apply(valueDependentTactic, v)
    } catch {
      case e: BelleFriendlyUserMessage => throw e
      case e: BelleThrowable => throw e //throw e.inContext(d, v.prettyString)
      //@todo unable to create is a serious error in the tactic not just an "oops whatever try something else exception"
      case e: Throwable => throw new BelleThrowable("Unable to create dependent tactic '" + d.name + "', cause: " + e.getMessage, e).inContext(d, "")
    }

    case subst: InputTactic if subst.name == "US" =>
      val substs = collection.immutable.Seq(subst.inputs.map(_.toString.asSubstitutionPair).map(sp => sp.what -> sp.repl):_*)
      apply(subst.computeExpr(), v) match {
        case p: BelleDelayedSubstProvable => new BelleDelayedSubstProvable(p.p, p.label, p.subst ++ RenUSubst(substs).usubst)
        case p: BelleProvable => new BelleDelayedSubstProvable(p.p, p.label, RenUSubst(substs).usubst)
        case v => v
      }

    case it: InputTactic => try {
      apply(it.computeExpr(), v)
    } catch {
      case e: BelleThrowable if throwWithDebugInfo => throw e.inContext(it, v.prettyString)
      case e: BelleThrowable => throw e
      case e: Throwable => throw new BelleThrowable("Unable to create input tactic '" + it.name + "', cause: " + e.getMessage, e).inContext(it, "")
    }

    case PartialTactic(child, None) => try {
      apply(child, v)
    } catch {
      case e: BelleThrowable if throwWithDebugInfo => throw e.inContext(PartialTactic(e.context), "Tactic declared as partial failed to run: " + child)
    }

    case PartialTactic(child, Some(label)) => try {
      apply(child, v) match {
        case BelleProvable(pr, Some(labels)) => BelleProvable(pr, Some(labels.map(_.append(label))))
        case BelleProvable(pr, None) => BelleProvable(pr, Some(label :: Nil))
        case _ => throw new BelleThrowable(s"Attempted to give a label to a value that is not a Provable: ${v.getClass.getName}").inContext(BelleDot, "")
      }
    } catch {
      case e: BelleThrowable if throwWithDebugInfo => throw e.inContext(PartialTactic(e.context), "Tactic declared as partial failed to run: " + child)
    }

    case OnAll(e) =>
      val provable = v match {
        case BelleProvable(p, _) => p
        case _ => throw new BelleThrowable("Cannot attempt OnAll with a non-Provable value.").inContext(expr, "")
      }
      //@todo actually it would be nice to throw without wrapping inside an extra BranchTactic context
      try {
        apply(BranchTactic(Seq.tabulate(provable.subgoals.length)(_ => e)), v)
      } catch {
        case e: BelleThrowable if throwWithDebugInfo => throw e.inContext(OnAll(e.context), "")
      }

    case ChooseSome(options, e) =>
      val opts = options()
      var errors = ""
      var result: Option[BelleValue] = None
      while (result.isEmpty && !isDead && opts.hasNext) {
        val o = opts.next()
        logger.debug("ChooseSome: try " + o)
        val someResult: Option[BelleValue] = try {
          Some(apply(e(o), v))
        } catch { case err: BelleThrowable => errors += "in " + o + " " + err + "\n"; None }
        logger.debug("ChooseSome: try " + o + " got " + someResult)
        (someResult, e) match {
          case (Some(p@BelleProvable(_, _)), _) => result = Some(p)
          case (Some(p), _: PartialTactic) => result = Some(p)
          case (Some(_), _) => errors += "option " + o + " " + new BelleThrowable("Tactics must close their proof unless declared as partial. Use \"t partial\" instead of \"t\".").inContext(ChooseSome(options, e), "Failed option in ChooseSome: " + o) + "\n" // throw new BelleThrowable("Non-partials must close proof.").inContext(ChooseSome(options, e), "Failed option in ChooseSome: " + o)
          case (None, _) => // option o had an error, so consider next option
        }
      }
      result match {
        case Some(r) => r
        case None => throw new BelleThrowable("ChooseSome did not succeed with any of its options") //.inContext(ChooseSome(options, e), "Failed all options in ChooseSome: " + opts.toList + "\n" + errors)
      }

    case TimeoutAlternatives(alternatives, timeout) => alternatives.headOption match {
      case Some(tactic) =>
        val c = Cancellable(apply(tactic, v))
        try {
          Await.result(c.future, Duration(timeout, MILLISECONDS))
        } catch {
          // current alternative failed within timeout, try next
          case ex: ExecutionException => ex.getCause match {
            case _: BelleThrowable => apply(TimeoutAlternatives(alternatives.tail, timeout), v)
            case e => throw e
          }
          case ex: TimeoutException =>
            c.cancel()
            throw new BelleThrowable("Alternative timed out", ex)
        }
      case None => throw new BelleThrowable("Exhausted all timeout alternatives")
    }


    case LabelBranch(label) => v match {
      case BelleProvable(pr, Some(labels)) => BelleProvable(pr, adjustLabels(pr, Some(labels.map(_.append(label)))))
      case BelleProvable(pr, None) => BelleProvable(pr, adjustLabels(pr, Some(label :: Nil)))
      case _ => throw new BelleThrowable(s"Attempted to give a label to a value that is not a Provable: ${v.getClass.getName}").inContext(BelleDot, "")
    }

    case DefTactic(_, _) => v //@note noop, but included for serialization purposes

    case Expand(_, s) =>
      val subst = USubst(s :: Nil)
      TactixLibrary.invGenerator = substGenerator(TactixLibrary.invGenerator, subst :: Nil)
      TactixLibrary.differentialInvGenerator = substGenerator(TactixLibrary.differentialInvGenerator, subst :: Nil)
      apply(TactixLibrary.US(subst), v) match {
        case p: BelleDelayedSubstProvable => new BelleDelayedSubstProvable(p.p, p.label, p.subst ++ subst)
        case p: BelleProvable => new BelleDelayedSubstProvable(p.p, p.label, subst)
        case v => v
      }

    case ExpandAll(defs) =>
      val substs = defs.map(s => USubst(s :: Nil))
      TactixLibrary.invGenerator = substGenerator(TactixLibrary.invGenerator, substs)
      TactixLibrary.differentialInvGenerator = substGenerator(TactixLibrary.differentialInvGenerator, substs)
      apply(defs.map(s => TactixLibrary.US(USubst(s :: Nil))).
        reduceOption[BelleExpr](_ & _).getOrElse(TactixLibrary.skip), v) match {
        case p: BelleDelayedSubstProvable => new BelleDelayedSubstProvable(p.p, p.label, p.subst ++ substs.reduceRight(_++_))
        case p: BelleProvable => new BelleDelayedSubstProvable(p.p, p.label, substs.reduceRight(_++_))
        case v => v
      }

    case ApplyDefTactic(DefTactic(_, t)) => apply(t, v)
    case named: NamedTactic => apply(named.tactic, v)

    case ProveAs(lemmaName, f, e) =>
      val BelleProvable(provable, labels) = v
      assert(provable.subgoals.length == 1)

      val lemma = ProvableSig.startProof(f)

      //Prove the lemma iff it's not already proven.
      if(LemmaDBFactory.lemmaDB.contains(lemmaName)) {
        assert(LemmaDBFactory.lemmaDB.get(lemmaName).head.fact.conclusion == lemma.conclusion)
      }
      else {
        val BelleProvable(result, _) = apply(e, BelleProvable(lemma, labels))
        assert(result.isProved, "Result of proveAs should always be proven.")

        val tacticText: String = try { BellePrettyPrinter(e) } catch { case _: Throwable => "nil" }

        val evidence = ToolEvidence(List(
          "tool" -> "KeYmaera X",
          "model" -> lemma.prettyString,
          "tactic" -> tacticText,
          "proof" -> "" //@todo serialize proof
        )) :: Nil

        //Save the lemma.
        LemmaDBFactory.lemmaDB.add(Lemma(result, Lemma.requiredEvidence(result, evidence), Some(lemmaName)))
      }
      v //nop on the original goal.

    case Let(abbr, value, inner) =>
      val (provable, lbl) = v match {
        case BelleProvable(p, l) => (p, l)
        case _ => throw new BelleThrowable("Cannot attempt Let with a non-Provable value.").inContext(expr, "")
      }
      if (provable.subgoals.length != 1)
        throw new BelleThrowable("Let of multiple goals is not currently supported.").inContext(expr, "")

      val subst = (abbr, value) match {
        case (FuncOf(name, arg), t: Term) =>
          val dotArg = if (arg.sort == Unit) Nothing else DotTerm()
          SubstitutionPair(FuncOf(name, dotArg), t.replaceFree(arg, DotTerm()))
        case (PredOf(name, arg), f: Formula) =>
          val dotArg = if (arg.sort == Unit) Nothing else DotTerm()
          SubstitutionPair(PredOf(name, dotArg), f.replaceFree(arg, DotTerm()))
      }

      //@todo sometimes may want to offer some unification for: let j(x)=x^2>0 in tactic for sequent mentioning both x^2>0 and (x+y)^2>0 so j(x) and j(x+y).
      val us: USubst = USubst(subst :: Nil)
      val in: ProvableSig = try {
        ProvableSig.startProof(provable.subgoals.head.replaceAll(value, abbr))
      } catch {
        case e: Throwable => throw new BelleThrowable("Unable to start inner proof in let: " + e.getMessage, e)
      }
      logger.debug("INFO: " + expr + " considers\n" + in + "\nfor outer\n" + provable)
      //assert(us(in.conclusion) == provable.subgoals.head, "backsubstitution will ultimately succeed from\n" + in + "\nvia " + us + " to outer\n" + provable)
      apply(inner, BelleProvable(in, lbl)) match {
        case BelleProvable(derivation, resultLbl) =>
          try {
            val backsubst: ProvableSig = derivation(us)
            BelleProvable(provable(backsubst, 0), resultLbl)
          } catch {
            case _: SubstitutionClashException =>
              // proof will not close, but keep without backsubstitution to allow users step into the failed derivation
              BelleProvable(derivation, resultLbl)
          }
        case e => throw new BelleThrowable("Let expected sub-derivation")
      }


    case LetInspect(abbr, instantiator, inner) =>
      val (provable, lbl) = v match {
        case BelleProvable(p, l) => (p,l)
        case _ => throw new BelleThrowable("Cannot attempt LetInspect with a non-Provable value.").inContext(expr, "")
      }
      if (provable.subgoals.length != 1)
        throw new BelleThrowable("LetInspect of multiple goals is not currently supported.").inContext(expr, "")

      val in: ProvableSig = ProvableSig.startProof(provable.subgoals.head)
      apply(inner, BelleProvable(in, lbl)) match {
        case BelleProvable(derivation, resultLbl) =>
          try {
            val value: Expression = instantiator(derivation)
            val us: USubst = USubst(SubstitutionPair(abbr, value) :: Nil)
            val backsubst: ProvableSig = derivation(us)
            BelleProvable(provable(backsubst, 0), resultLbl)
          } catch {
            case e: BelleThrowable => throw e.inContext(expr, "LetInspect backsubstitution failed")
            case e: ProverException => throw new BelleThrowable("LetInspect backsubstitution failed", e).inContext(expr.toString, "LetInspect backsubstitution failed")
          }
        case e: BelleThrowable => throw new BelleThrowable("LetInspect expected sub-derivation", e)
      }


    case SearchAndRescueAgain(abbr, common, instantiator, continuation) =>
      val (provable, lbl) = v match {
        case BelleProvable(p, l) => (p,l)
        case _ => throw new BelleThrowable("Cannot attempt SearchAndRescueAgain with a non-Provable value.").inContext(expr, "")
      }
      if (provable.subgoals.length != 1)
        throw new BelleThrowable("SearchAndRescueAgain of multiple goals is not currently supported.").inContext(expr, "")

      val in: ProvableSig = ProvableSig.startProof(provable.subgoals.head)
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
        case e => throw new BelleThrowable("SearchAndRescueAgain expected sub-derivation after running common")
      }


    case t@USubstPatternTactic(children) =>
      val provable = v match {
        case BelleProvable(p, _) => p
        case _ => throw new BelleThrowable("Cannot attempt US unification with a non-Provable value.").inContext(expr, "")
      }

      if (provable.subgoals.length != 1)
        throw new BelleThrowable("Unification of multi-sequent patterns is not currently supported.").inContext(expr, "")

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
          case _ => throw new BelleThrowable("Cannot unify non-sequent types.").inContext(t, "")
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
        case BelleProvable(p,_) => p
        case _ => throw new BelleThrowable("two position tactics can only be run on Provables.")
      }
      apply(t.computeExpr(p1, p2).computeExpr(provable), v)
  }

  /** Maps sequents to BelleProvables. */
  protected def bval(s: Sequent, lbl: Option[List[BelleLabel]]) = BelleProvable(ProvableSig.startProof(s), lbl)

  /**
    * Replaces the nth subgoal of `original`` with the remaining subgoals of `subderivation`.
    *
    * @param original A Provable whose nth subgoal is equal to the conclusion of `subderivation` (modulo substitution).
    * @param n The numerical index of the subgoal of original to rewrite (Seqs are zero-indexed)
    * @param subderivation The provable to replace the original subgoal.
    * @return A pair of:
    *         * A new provable that is identical to `original`, except that the nth subgoal is replaced with the
    *           remaining subgoals of `subderivation`; and
    *         * The next index for the interpreter to continue, n if `subderivation` is proved (i.e., all later
    *           subgoals move up by 1), or (n+1) if subderivation is not proved.
    */
  protected def replaceConclusion(original: ProvableSig, n: Int, subderivation: ProvableSig, subst: Option[USubst]): (ProvableSig, Int) = {
    assert(original.subgoals.length > n, s"$n is a bad index for Provable with ${original.subgoals.length} subgoals: $original")
    val substituted =
      if (original.subgoals(n) == subderivation.conclusion) original
      else subst.map(exhaustiveSubst(original, _)).getOrElse(original)
    if (substituted.subgoals(n) != subderivation.conclusion)
      throw new BelleThrowable(s"Subgoal #$n of the original provable (${substituted.subgoals(n)}}) should be equal to the conclusion of the subderivation (${subderivation.conclusion}})")
    val newProvable = substituted(subderivation, n)
    val nextIdx = if (subderivation.isProved) n else n + 1
    (newProvable, nextIdx)
  }

  /** Applies substitutions `s` to provable `p` exhaustively. */
  @tailrec
  private def exhaustiveSubst(p: ProvableSig, s: USubst): ProvableSig = {
    val substituted = p(s)
    if (substituted != p) exhaustiveSubst(substituted, s)
    else substituted
  }

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

/** Sequential interpreter that explores branching tactics exhaustively, regardless of failure of some. */
case class ExhaustiveSequentialInterpreter(override val listeners: scala.collection.immutable.Seq[IOListener] = scala.collection.immutable.Seq(),
                                           override val throwWithDebugInfo: Boolean = false)
  extends SequentialInterpreter(listeners, throwWithDebugInfo) { }

/** Sequential interpreter that stops exploring branching on the first failing branch. */
case class LazySequentialInterpreter(override val listeners: scala.collection.immutable.Seq[IOListener] = scala.collection.immutable.Seq(),
                                     override val throwWithDebugInfo: Boolean = false) extends SequentialInterpreter(listeners, throwWithDebugInfo) {
  override def runExpr(expr: BelleExpr, v: BelleValue): BelleValue = expr match {
    case BranchTactic(children) => v match {
      case BelleProvable(p, lbl) =>
        if (children.length != p.subgoals.length)
          throw new BelleThrowable("<(e)(v) is only defined when len(e) = len(v), but " +
            children.length + "!=" + p.subgoals.length + " subgoals (v)\n" +
            p.subgoals.map(_.prettyString).mkString("\n===================\n")).inContext(expr, "")
        //Compute the results of piecewise applications of children to provable subgoals.
        val results: Seq[BelleProvable] = children.zip(p.subgoals).zipWithIndex.map({ case ((e_i, s_i), i) =>
          val ithResult = try {
            apply(e_i, bval(s_i, lbl.getOrElse(Nil).lift(i).map(_ :: Nil)))
          } catch {
            case e: BelleThrowable => throw e.inContext(BranchTactic(children.map(c => if (c != e_i) c else e.context)), "Failed on branch " + e_i)
          }
          ithResult match {
            case b@BelleProvable(_, _) => b
            case _ => throw new BelleThrowable("Each piecewise application in a branching tactic should result in a provable.").inContext(expr, "")
          }
        })

        // Compute a single provable that contains the combined effect of all the piecewise computations.
        // The Int is threaded through to keep track of indexes changing, which can occur when a subgoal
        // is replaced with 0 new subgoals (also means: drop labels).
        def createLabels(start: Int, end: Int): List[BelleLabel] = (start until end).map(i => BelleTopLevelLabel(s"$i")).toList

        //@todo preserve labels from parent p (turn new labels into sublabels)
        val combinedEffect =
          results.foldLeft[(ProvableSig, Int, Option[List[BelleLabel]])]((p, 0, None))({
            case ((cp: ProvableSig, cidx: Int, clabels: Option[List[BelleLabel]]), subderivation: BelleProvable) =>
              val (combinedProvable, nextIdx) = replaceConclusion(cp, cidx, subderivation.p, subderivation match {
                case p: BelleDelayedSubstProvable => Some(p.subst)
                case _ => None
              })
              val combinedLabels: Option[List[BelleLabel]] = (clabels, subderivation.label) match {
                case (Some(origLabels), Some(newLabels)) =>
                  Some(origLabels.patch(cidx, newLabels, 0))
                case (Some(origLabels), None) =>
                  Some(origLabels.patch(cidx, createLabels(origLabels.length, origLabels.length + subderivation.p.subgoals.length), 0))
                case (None, Some(newLabels)) =>
                  Some(createLabels(0, cidx) ++ newLabels)
                case (None, None) => None
              }
              (combinedProvable, nextIdx, combinedLabels)
            })
        BelleProvable(combinedEffect._1, if (combinedEffect._3.isEmpty) None else combinedEffect._3)
      case _ => throw new BelleThrowable("Cannot perform branching on a goal that is not a BelleValue of type Provable.").inContext(expr, "")
    }
    case _ => super.runExpr(expr, v)
  }
}