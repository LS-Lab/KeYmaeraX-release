package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import ProofRuleTactics.requireOneSubgoal
import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.infrastruct.ExpressionTraversal.{ExpressionTraversalFunction, StopTraversal}
import edu.cmu.cs.ls.keymaerax.infrastruct._
import edu.cmu.cs.ls.keymaerax.lemma.{Lemma, LemmaDB, LemmaDBFactory}
import edu.cmu.cs.ls.keymaerax.macros.DerivationInfo
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tools.ToolEvidence
import org.apache.logging.log4j.scala.{Logger, Logging}

import scala.collection.immutable
import scala.collection.mutable.ListBuffer

/**
 * @author Nathan Fulton
 */
object DebuggingTactics {
  //@todo import a debug flag as in Tactics.DEBUG
  private val DEBUG = Configuration(Configuration.Keys.DEBUG) == "true"

  private val logger = Logger(getClass)

  def error(e: Throwable): BuiltInTactic = new BuiltInTactic("Error") with NoOpTactic {
    override def result(provable: ProvableSig): ProvableSig = throw e
  }

  /** Indicates a failed attempt that triggers proof search. */
  def error(s: => String): BuiltInTactic = new BuiltInTactic("Error") with NoOpTactic {
    override def result(provable: ProvableSig): ProvableSig = {
      throw new TacticInapplicableFailure(s + "\n" + provable.underlyingProvable.prettyString)
    }
  }

  def recordQECall(): BuiltInTactic = new BuiltInTactic("recordQECall") with NoOpTactic {
    override def result(provable: ProvableSig): ProvableSig = {
      logger.info(s"QE CALL\n==QE==\n${provable.subgoals(0).prettyString}\n==END_QE==")
      provable
    }
  }

  /** debug is a no-op tactic that prints a message and the current provable, if doPrint (defaults to the system property DEBUG) is true. */
  def debug(message: => String, doPrint: Boolean = DEBUG, printer: ProvableSig => String = _.toString): StringInputTactic =
      new StringInputTactic(if (doPrint) "print" else "debug", message::Nil) with NoOpTactic {
    override def result(provable: ProvableSig): ProvableSig = {
      if (doPrint) logger.info("===== " + message + " ==== " + printer(provable) + " =====")
      provable
    }
  }

  /** print is a no-op tactic that prints a message and the current provable, regardless of DEBUG being true or false */
  def print(message: => String): BuiltInTactic = debug(message, doPrint=true)
  /** printIndexed is a no-op tactic that prints a message and the current provable (verbose sequent with formula indices),
    * regardless of DEBUG being true or false */
  def printIndexed(message: => String): BuiltInTactic = debug(message, doPrint=true, _.prettyString)

  /** debug is a no-op tactic that prints a message and the current provable, if the system property DEBUG is true. */
  def debugAt(message: => String, doPrint: Boolean = DEBUG): BuiltInPositionTactic = new BuiltInPositionTactic("debug") with NoOpTactic {
    override def computeResult(provable: ProvableSig, pos: Position): ProvableSig = {
      if (doPrint) logger.info("===== " + message + " ==== " + "\n\t with formula: " + provable.subgoals.head.at(pos)
        + " at position " + pos + " of first subgoal,"
        + "\n\t entire provable: " + provable + " =====")
      provable
    }
  }

  /**
    * Assert that the assertion holds at a the specified position. Could be a non-top-level position. Analogous to [[debugAt]].
    * @param msg The message to display.
    * @param assertion The assertion.
    */
  def assertAt(msg: Expression => String, assertion: Expression => Boolean, ex: String => Throwable = new TacticAssertionError(_)): BuiltInPositionTactic = new BuiltInPositionTactic("ANON") with NoOpTactic {
    override def computeResult(provable: ProvableSig, pos: Position): ProvableSig = {
      val ctx = provable.subgoals.head.at(pos)
      if (!assertion(ctx._2)) throw ex("Assertion Failed: " + msg(ctx._2) + "\nAt:\n" + ctx)
      provable
    }
  }

  def assertAt(msg: => String, assertion: Expression => Boolean, ex: String => Throwable): BuiltInPositionTactic = assertAt((_: Expression) => msg, assertion, ex)

  /** assert is a no-op tactic that raises an error if the provable is not of the expected size. */
  def assert(anteSize: Int, succSize: Int, msg: => String, ex: String => Throwable): BuiltInTactic = new BuiltInTactic("ANON") with NoOpTactic {
    override def result(provable: ProvableSig): ProvableSig = {
      if (provable.subgoals.size != 1 || provable.subgoals.head.ante.size != anteSize ||
        provable.subgoals.head.succ.size != succSize) {
        throw ex(msg + "\nExpected 1 subgoal with: " + anteSize + " antecedent and " + succSize + " succedent formulas,\n\t but got " +
          provable.subgoals.size + " subgoals (head subgoal with: " + provable.subgoals.head.ante.size + "antecedent and " +
          provable.subgoals.head.succ.size + " succedent formulas)")
      }
      provable
    }
  }
  /** assert is a no-op tactic that raises a tactic assertion error if the provable is not of the expected size. */
  def assert(anteSize: Int, succSize: Int, msg: => String = ""): BuiltInTactic = assert(anteSize, succSize, msg, new TacticAssertionError(_))

  //@todo rename to something else otherwise scala assert no longer works!
  /** assert is a no-op tactic that raises an error if the provable has not the expected formula at the specified position. */
  def assert(fml: Formula, message: => String, ex: String => Throwable): DependentPositionWithAppliedInputTactic = {
    import TacticFactory._
    //@todo serialize exception
    ("assert" byWithInputs (fml :: message :: Nil, (pos: Position, seq: Sequent) => {
      (new BuiltInPositionTactic("ANON") {
        override def computeResult(provable: ProvableSig, pos: Position): ProvableSig = {
          if (provable.subgoals.size != 1 || provable.subgoals.head.at(pos)._2 != fml) {
            throw ex(message + "\nExpected 1 subgoal with " + fml + " at position " + pos + ",\n\t but got " +
              provable.subgoals.size + " subgoals (head subgoal with " + provable.subgoals.head.sub(pos) + " at position " + pos + ")")
          }
          provable
        }
      })(pos)
    })) :: NoOpTactic
  }
  /** assert is a no-op tactic that raises a tactic assertion error if the provable has not the expected formula at the specified position. */
  def assert(fml: Formula, message: => String): DependentPositionWithAppliedInputTactic = assert(fml, message, new TacticAssertionError(_))

  /** assert is a no-op tactic that raises an error if the provable does not satisfy a condition on the sole subgoal. */
  def assert(cond: Sequent=>Boolean, message: => String, ex: String => Throwable): BuiltInTactic = new BuiltInTactic("ANON") with NoOpTactic {
    override def result(provable: ProvableSig): ProvableSig = {
      if (provable.subgoals.size != 1 || !cond(provable.subgoals.head)) {
        throw ex(message + "\nExpected 1 subgoal matching a condition but got " +
          (if (provable.subgoals.size != 1) provable.subgoals.size + " subgoals"
           else provable.subgoals.head.prettyString))
      }
      provable
    }
  }
  /** assert is a no-op tactic that raises a tactic assertion error if the provable does not satisfy a condition on the sole subgoal. */
  def assert(cond: Sequent=>Boolean, message: => String): BuiltInTactic = assert(cond, message, new TacticAssertionError(_))

  /** assertOnAll is a no-op tactic that raises an error the provable does not satisfy a condition on all subgoals. */
  def assertOnAll(cond: Sequent=>Boolean, message: => String, ex: String => Throwable = new TacticAssertionError(_)): BuiltInTactic = new BuiltInTactic("ANON") with NoOpTactic {
    override def result(provable: ProvableSig): ProvableSig = {
      if (!provable.subgoals.forall(cond(_))) {
        throw ex(message + "\nExpected all subgoals match condition " + cond + ",\n\t but " +
          provable.subgoals.filter(!cond(_)).mkString("\n") + " do not match")
      }
      provable
    }
  }

  /** asserts that the provable has `provableSize` many subgoals. */
  def assertProvableSize(provableSize: Int, ex: String => Throwable = new TacticAssertionError(_)): BuiltInTactic = new BuiltInTactic(s"assertProvableSize($provableSize)") with NoOpTactic {
    override def result(provable: ProvableSig): ProvableSig = {
      if (provable.subgoals.length != provableSize)
        throw ex(s"assertProvableSize failed: Expected to have $provableSize open goals but found an open goal with ${provable.subgoals.size}")
      provable
    }
  }

  /** assert is a no-op tactic that raises an error if the provable does not satisfy a condition at position pos. */
  def assert(cond: (Sequent,Position)=>Boolean, message: => String, ex: String => Throwable): BuiltInPositionTactic = new BuiltInPositionTactic("ANON") with NoOpTactic {
    override def computeResult(provable: ProvableSig, pos: Position): ProvableSig = {
      if (provable.subgoals.size != 1) {
        throw ex(message + "\nExpected 1 subgoal matching a condition at position " + pos + " but got " +
          provable.subgoals.size + " subgoals")
      } else if (!cond(provable.subgoals.head, pos)) {
        throw ex(message + "\nAn (internal) check failed at the subgoal formula " + provable.subgoals.head.at(pos)._2)
      }
      provable
    }
  }
  /** assert is a no-op tactic that raises a tactic assertion error if the provable does not satisfy a condition at position pos. */
  def assert(cond: (Sequent,Position)=>Boolean, message: => String): BuiltInPositionTactic = assert(cond, message, new TacticAssertionError(_))

  /** assertE is a no-op tactic that raises an error if the provable has not the expected expression at the specified position. */
  def assertE(expected: => Expression, message: => String, ex: String => Throwable): DependentPositionWithAppliedInputTactic = {
    import TacticFactory._
    //@todo serialize exception
    ("assert" byWithInputs (expected :: message :: Nil, (pos: Position, seq: Sequent) => {
      (new BuiltInPositionTactic("ANON") {
        override def computeResult(provable: ProvableSig, pos: Position): ProvableSig = {
          if (provable.subgoals.size != 1 || provable.subgoals.head.at(pos)._2 != expected) {
            throw ex(message + "\nExpected 1 subgoal with " + expected + " at position " + pos + ",\n\t but got " +
              provable.subgoals.size + " subgoals (head subgoal with " + provable.subgoals.head.at(pos) + " at position " + pos + ")")
          }
          provable
        }
    })(pos)
  })) :: NoOpTactic
  }
  /** assertE is a no-op tactic that raises a tactic assertion error if the provable has not the expected expression at the specified position. */
  def assertE(expected: => Expression, message: => String): DependentPositionWithAppliedInputTactic = assertE(expected, message, new TacticAssertionError(_))

  /** @see [[TactixLibrary.done]] */
  lazy val done: BelleExpr = done()
  def done(msg: String = "", storeLemma: Option[String] = None): BelleExpr = new StringInputTactic("done",
      if (msg.nonEmpty && storeLemma.isDefined) msg::storeLemma.get::Nil
      else if (msg.nonEmpty) msg::Nil
      else Nil) {
    override def result(provable: ProvableSig): ProvableSig = {
      if (provable.isProved) {
        print(msg + {if (msg.nonEmpty) ": " else ""} + "checked done")
        if (storeLemma.isDefined) LemmaDBFactory.lemmaDB.add(Lemma(provable, Lemma.requiredEvidence(provable), storeLemma))
        provable
      } else throw BelleUnfinished(msg, provable.underlyingProvable)
    }
  }

  /** Placeholder for a tactic string that is not executed. */
  def pending(tactic: String): BelleExpr = new StringInputTactic("pending",
      // escape " but avoid double-escape
      tactic.replaceAllLiterally("\"", "\\\"").replaceAllLiterally("\\\\\"", "\\\"") :: Nil) {
    override def result(provable: ProvableSig): ProvableSig = provable
  }
}

case class Case(fml: Formula, simplify: Boolean = true) {
  def prettyString: String = s"Case '${fml.prettyString}'"
}

/**
 * @author Nathan Fulton
 */
object Idioms {
  import TacticFactory._

  lazy val nil: BelleExpr = new BuiltInTactic("nil") with NoOpTactic {
    override def result(provable: ProvableSig): ProvableSig = provable
  }
  /** no-op nil */
  lazy val ident: BelleExpr = nil

  /** Optional tactic */
  def ?(t: BelleExpr): BelleExpr = t | nil

  /** Execute ts by branch order. */
  def <(t: BelleExpr*): BelleExpr = BranchTactic(t)

  /** Execute different tactics depending on branch label, fall back to branch order if branches come without labels.
    * <((lbl1,t1), (lbl2,t2)) uses tactic t1 on branch labelled lbl1 and uses t2 on lbl2.
    * @see [[BelleLabels]]
    */
  def <(s1: (BelleLabel, BelleExpr), spec: (BelleLabel, BelleExpr)*): BelleExpr = new LabelledGoalsDependentTactic("onBranch") {
    override def computeExpr(provable: ProvableSig, labels: List[BelleLabel]): BelleExpr = {
      val labelledTactics = (s1 +: spec).toMap
      Idioms.<(labels.map(l => labelledTactics(l)):_*)
    }
    override def computeExpr(provable: ProvableSig): BelleExpr = {
      logger.debug("No branch labels, executing by branch order")
      Idioms.<((s1 +: spec).map(_._2):_*)
    }
  }

  /* branch by case distinction
  *  cases must be exhaustive (or easily proved to be exhaustive in context)
  *  otherwise, the exhaustiveness case is left open
  * */
  def cases(exhaustive: BelleExpr = TactixLibrary.master())(c1: (Case, BelleExpr), cs: (Case, BelleExpr)*): BelleExpr = {
    val cases = c1 +: cs
    val caseFml = cases.map({ case (Case(fml, _), _) => fml }).reduceRight(Or)

    //@todo simplify with only the case formula as simplification 'context' (adapt simplifier)
    val simplify = (fml: Formula) => SimplifierV2.simpTac//(Some(scala.collection.immutable.IndexedSeq(fml)))
    val simplifyAllButCase = (fml: Formula) => "ANON" by {(seq: Sequent) =>
      (0 until seq.ante.length-1).map(i => simplify(fml)(AntePosition.base0(i))).reduceOption[BelleExpr](_&_).getOrElse(ident) &
      seq.succ.indices.map(i => simplify(fml)(SuccPosition.base0(i))).reduceOption[BelleExpr](_&_).getOrElse(ident)
    }

    val caseTactics = cases.map({ case (Case(fml, doSimp), t) =>
      (if (doSimp) simplifyAllButCase(fml) & SaturateTactic(TactixLibrary.hideL('L, True) | TactixLibrary.hideR('R, False)) else ident) & t}).
      reduceRight[BelleExpr]({ case (t1, t2) => TactixLibrary.orL('Llast) & Idioms.<(t1, t2)})

    TactixLibrary.cut(caseFml) & Idioms.<(
      /*use*/ caseTactics,
      // cases might be exhaustive in itself (e.g., x>=0|x<0), or exhaustive per facts from antecedent (x=0|x>0 from x>=0)
      /*show*/
        TactixLibrary.cohideR('Rlast) & exhaustive & TactixLibrary.done |
        TactixLibrary.cohideOnlyR('Rlast) & exhaustive & TactixLibrary.done | exhaustive & TactixLibrary.done | ident
    )
  }
  def cases(c1: (Case, BelleExpr), cs: (Case, BelleExpr)*): BelleExpr = cases()(c1, cs:_*)

  /** Proves by lemma, if lemma `lemmaName` exists, else by tactic `t` and stores the proof found by `t` as lemma `lemmaName`.
    * Must be used on a provable with exactly 1 subgoal (e.g., as created in a Case).
    * Lemma lookup can be disabled with `doLemmaLookup` (lemma lookup enabled by default).
    */
  def rememberAs(lemmaName: String, t: BelleExpr)(implicit lemmaDB: LemmaDB, lookupRememberedLemmas: Boolean = true): BelleExpr =
      new BuiltInTactic("RememberAs") {
    override def result(provable: ProvableSig): ProvableSig = {
      if (provable.subgoals.size > 1) throw new BelleAbort("Too many subgoals", "RememberAs requires exactly 1 subgoal, but got " + provable.subgoals)
      val tactic =
        if (lookupRememberedLemmas && lemmaDB.contains(lemmaName)) TactixLibrary.by(lemmaDB.get(lemmaName).get)
        else t & rememberAs(lemmaName)
      provable(TactixLibrary.proveBy(provable.subgoals.head, tactic), 0)
    }
  }

  /** Stores a lemma `lemmaName` if the current provable is proved. */
  def rememberAs(lemmaName: String)(implicit lemmaDB: LemmaDB): BelleExpr = new BuiltInTactic("RememberProof") with NoOpTactic {
    override def result(provable: ProvableSig): ProvableSig = {
      if (provable.isProved) {
        val evidence = ToolEvidence(immutable.List("input" -> provable.conclusion.prettyString, "output" -> "true")) :: Nil
        lemmaDB.add(new Lemma(provable, evidence, Some(lemmaName)))
      }
      provable
    }
  }

  /** Repeats t while condition at position is true. */
  def repeatWhile(condition: Expression => Boolean)(t: BelleExpr): DependentPositionTactic = "loopwhile" by {(pos: Position) =>
    SaturateTactic(DebuggingTactics.assertAt((_: Expression) => "Stopping loop", condition, new TacticInapplicableFailure(_))(pos) & t)
  }

  /** Executes t if condition is true. */
  def doIf(condition: ProvableSig => Boolean)(t: => BelleExpr): DependentTactic = doIfElse(condition)(t, nil)

  /** Executes t if condition is true and f otherwise. */
  def doIfElse(condition: ProvableSig => Boolean)(t: => BelleExpr, f: => BelleExpr): DependentTactic = new DependentTactic("ANON") {
    override def computeExpr(provable: ProvableSig): BelleExpr = {
      if (condition(provable)) t
      else f
    }
  }

  /** must(t) runs tactic `t` but only if `t` actually changed the goal. */
  def must(t: BelleExpr): BelleExpr = new DependentTactic("ANON") {
    override def computeExpr(before: ProvableSig): BelleExpr = t & new BuiltInTactic(name) {
      override def result(after: ProvableSig): ProvableSig = {
        if (before == after) throw new BelleNoProgress("Tactic " + t + " did not result in mandatory change")
        after
      }
    }
  }

  def atSubgoal(subgoalIdx: Int, t: BelleExpr): DependentTactic = new DependentTactic(s"AtSubgoal($subgoalIdx, ${t.toString})") {
    override def computeExpr(v: BelleValue): BelleExpr = v match {
      case BelleProvable(provable, _) =>
        BranchTactic(Seq.tabulate(provable.subgoals.length)(i => if(i == subgoalIdx) t else ident))
      case _ => throw new IllFormedTacticApplicationException("Cannot perform AtSubgoal on a non-Provable value.")
    }
  }

  /** Gives a name to a tactic to a definable tactic. */
  def NamedTactic(name: String, tactic: => BelleExpr): DependentTactic = new DependentTactic(name) {
    override def computeExpr(v: BelleValue): BelleExpr = tactic
  }

  /**
   * shift(shift, t) does t shifted from position p to shift(p)
   */
  def shift(shift: PosInExpr=>PosInExpr, t: DependentPositionTactic): DependentPositionTactic = "ANON" by ((pos: Position, _: Sequent) =>
    t(pos.navigate(shift(pos.inExpr))))
  /**
   * shift(child, t) does t to positions shifted by child
   */
  def shift(child: PosInExpr, t: DependentPositionTactic): DependentPositionTactic = shift(p => p ++ child, t)

  /** Map sub-positions of `pos` to Ts that fit to the expressions at those sub-positions per `trafo`. */
  def mapSubpositions[T](pos: Position, sequent: Sequent, trafo: (Expression, Position) => Option[T]): List[T] = {
    val result: ListBuffer[T] = ListBuffer()

    def mapTerm(p: PosInExpr, t: Term) = trafo(t, pos ++ p) match {
      case Some(tt) => tt +=: result; Left(None)
      case None => Left(None)
    }

    def mapFormula(p: PosInExpr, e: Formula) = trafo(e, pos ++ p) match {
      case Some(tt) => tt +=: result; Left(None)
      case None => Left(None)
    }

    //@note traverse expression, collect Ts in `result` as side effect
    sequent.sub(pos) match {
      case Some(f: Formula) =>
        ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
          override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = mapFormula(p, e)
          override def preT(p: PosInExpr, t: Term): Either[Option[StopTraversal], Term] = mapTerm(p, t)
        }, f)
      case Some(t: Term) =>
        ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
          override def preT(p: PosInExpr, t: Term): Either[Option[StopTraversal], Term] = mapTerm(p, t)
        }, t)
      case _ =>
    }

    result.toList
  }

  /** Search for formula `f` in the sequent and apply tactic `t` at subposition `in` of the found position. */
  def searchApplyIn(f: Formula, t: DependentPositionTactic, in: PosInExpr): DependentTactic = "ANON" by ((seq: Sequent) => {
    //@todo Extend position locators to sub-positions, e.g., 'L.1.0.1, 'Llast.1.1
    val subPos: Position = {
      val ante = seq.ante.indexOf(f)
      if (ante >= 0) AntePosition.base0(ante, in)
      else {
        val succ = seq.succ.indexOf(f)
        if (succ >= 0) SuccPosition.base0(succ, in)
        else throw new TacticInapplicableFailure("Cannot find formula " + f.prettyString + " in sequent " + seq.prettyString)
      }
    }
    t(subPos)
  })
}

/** Creates tactic objects */
object TacticFactory {

  /**
   * Creates named dependent tactics.
   * @example {{{
   *  "[:=] assign" by (pos => useAt(Ax.assignbAxiom)(pos))
   * }}}
   * @param name The tactic name.
    *             Use the special name "ANON" to indicate that this is an anonymous inner tactic that needs no storage.
   */
  implicit class TacticForNameFactory(val name: String) extends Logging {
    if (name == "") throw new InternalError("Don't use empty name, use ANON for anonymous inner tactics")
    /*if (false)*/ {
      try {
        if (name != "ANON" && DerivationInfo.ofCodeName(name).codeName.toLowerCase() != name.toLowerCase())
          logger.warn("WARNING: codeName should be changed to a consistent name: " + name + " vs. " + DerivationInfo.ofCodeName(name).codeName)
      } catch {
        case ex: IllegalArgumentException => logger.warn("WARNING: codeName not found: " + name, ex)
      }
    }

    /** Creates a named tactic */
    def by(t: BelleExpr): BelleExpr = NamedTactic(name, t)

    def byTactic(t: ((ProvableSig, Position, Position) => BelleExpr)) = new DependentTwoPositionTactic(name) {
      override def computeExpr(p1: Position, p2: Position): DependentTactic = new DependentTactic("") {
        override def computeExpr(p: ProvableSig) = t(p, p1, p2)
      }
    }

    /** Creates a dependent position tactic without inspecting the formula at that position */
    //@todo why does this have to have a DependentPositionTactic instead of a PositionalTactic?
    def by(t: (Position => BelleExpr)): DependentPositionTactic = new DependentPositionTactic(name) {
      override def factory(pos: Position): DependentTactic = new DependentTactic(name) {
        override def computeExpr(provable: ProvableSig): BelleExpr = t(pos)
      }
    }

    /** Creates a dependent position tactic while inspecting the sequent/formula at that position */
    def by(t: ((Position, Sequent) => BelleExpr)): DependentPositionTactic = new DependentPositionTactic(name) {
      override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
        override def computeExpr(sequent: Sequent): BelleExpr = {
          require(pos.isIndexDefined(sequent), "Cannot apply at undefined position " + pos + " in sequent " + sequent)
          t(pos, sequent)
        }
      }
    }

    /** A position tactic with multiple inputs. */
    def byWithInputs(inputs: Seq[Any], t: ((Position, Sequent) => BelleExpr)): DependentPositionWithAppliedInputTactic = new DependentPositionWithAppliedInputTactic(name, inputs) {
      override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
        override def computeExpr(sequent: Sequent): BelleExpr = {
          require(pos.isIndexDefined(sequent), "Cannot apply at undefined position " + pos + " in sequent " + sequent)
          t(pos, sequent)
        }
      }
    }

    /** A position tactic with multiple inputs. */
    def byWithInputs(inputs: Seq[Any], t: (Position => BelleExpr)): DependentPositionWithAppliedInputTactic = new DependentPositionWithAppliedInputTactic(name, inputs) {
      override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
        override def computeExpr(sequent: Sequent): BelleExpr = {
          require(pos.isIndexDefined(sequent), "Cannot apply at undefined position " + pos + " in sequent " + sequent)
          t(pos)
        }
      }
    }

    /** A named tactic with multiple inputs. */
    def byWithInputs(inputs: Seq[Any], t: => BelleExpr): InputTactic = new InputTactic(name, inputs) {
      override def computeExpr(): BelleExpr = t
    }

    /** A position tactic with a single input. */
    def byWithInput(input: Any, t: ((Position, Sequent) => BelleExpr)): DependentPositionWithAppliedInputTactic =
      byWithInputs(input :: Nil, t)

    /** A named tactic with a single input. */
    def byWithInput(input: Any, t: => BelleExpr): InputTactic = byWithInputs(input :: Nil, t)

    /** Creates a dependent tactic, which can inspect the sole sequent */
    def by(t: Sequent => BelleExpr): DependentTactic = new SingleGoalDependentTactic(name) {
      override def computeExpr(sequent: Sequent): BelleExpr = t(sequent)
    }
    def byWithInputs(input: Seq[Any], t: Sequent => BelleExpr): InputTactic = byWithInput(input, new SingleGoalDependentTactic(name) {
      override def computeExpr(sequent: Sequent): BelleExpr = t(sequent)
    })


    /** Creates a BuiltInRightTactic from a function turning provables and succedent positions into new provables.
      * @example {{{
      *         "andR" by((pr,pos)=> pr(AndRight(pos.top),0))
      *         }}}
      */
    def by(t: (ProvableSig, SuccPosition) => ProvableSig): BuiltInRightTactic = new BuiltInRightTactic(name) {
      @inline override def computeResult(provable: ProvableSig, pos: SuccPosition): ProvableSig = {
        requireOneSubgoal(provable, name)
        t(provable, pos)
      }
    }

    /** Creates a CoreRightTactic from a function turning provables and succedent positions into new provables.
      * Unlike [[by]], the coreby will augment MatchErrors from the kernel into readable error messages.
      * @example {{{
      *         "andR" coreby((pr,pos)=> pr(AndRight(pos.top),0))
      *         }}}
      * @see [[Rule]]
      * @see [[TacticInapplicableFailure]]
      */
    def coreby(t: (ProvableSig, SuccPosition) => ProvableSig): CoreRightTactic = new CoreRightTactic(name) {
      /** @throws TacticInapplicableFailure if this tactic is not applicable at the indicated position `pos` in `provable` */
      @inline override def computeCoreResult(provable: ProvableSig, pos: SuccPosition): ProvableSig = {
        requireOneSubgoal(provable, name)
        t(provable, pos)
      }
    }

    /** Creates a CoreRightTactic with applied inputs from a function turning provables and succedent positions into new provables.
     * Unlike [[by]], the coreby will augment MatchErrors from the kernel into readable error messages.
     * @example {{{
     *         "andR" coreby((pr,pos)=> pr(AndRight(pos.top),0))
     *         }}}
     * @see [[Rule]]
     * @see [[TacticInapplicableFailure]]
     */
    def corebyWithInputsR(inputs: Seq[Any], t: (ProvableSig, SuccPosition) => ProvableSig): DependentPositionWithAppliedInputTactic =
      byWithInputs(inputs, (pos: Position, _: Sequent) => {
        new BuiltInTactic(name) {
          override def result(provable: ProvableSig): ProvableSig = {
            t(provable, pos.checkSucc)
          }
        }
      })

    /** Creates a CoreLeftTactic with applied inputs from a function turning provables and antecedent positions into new provables.
     * Unlike [[by]], the coreby will augment MatchErrors from the kernel into readable error messages.
     * @example {{{
     *         "andL" coreby((pr,pos)=> pr(AndLeft(pos.top),0))
     *         }}}
     * @see [[Rule]]
     * @see [[TacticInapplicableFailure]]
     */
    def corebyWithInputsL(inputs: Seq[Any], t: (ProvableSig, AntePosition) => ProvableSig): DependentPositionWithAppliedInputTactic =
      byWithInputs(inputs, (pos: Position, _: Sequent) => {
        new BuiltInTactic(name) {
          override def result(provable: ProvableSig): ProvableSig = {
            t(provable, pos.checkAnte)
          }
        }
      })

    /** Creates a BuiltInLeftTactic from a function turning provables and antecedent positions into new provables.
      * @example {{{
      *         "andL" by((pr,pos)=> pr(AndLeft(pos.top),0))
      *         }}}
      */
    def by(t: (ProvableSig, AntePosition) => ProvableSig): BuiltInLeftTactic = new BuiltInLeftTactic(name) {
      @inline override def computeResult(provable: ProvableSig, pos: AntePosition): ProvableSig = {
        requireOneSubgoal(provable, name)
        t(provable, pos)
      }
    }

    /** Creates a BuiltInLeftTactic from a function turning provables and antecedent positions into new provables.
      * Unlike [[by]], the coreby will augment MatchErrors from the kernel into readable error messages.
      * @example {{{
      *         "andL" coreby((pr,pos)=> pr(AndLeft(pos.top),0))
      *         }}}
      * @see [[Rule]]
      * @see [[TacticInapplicableFailure]]
      */
    def coreby(t: (ProvableSig, AntePosition) => ProvableSig): CoreLeftTactic = new CoreLeftTactic(name) {
      /** @throws TacticInapplicableFailure if this tactic is not applicable at the indicated position `pos` in `provable` */
      @inline override def computeCoreResult(provable: ProvableSig, pos: AntePosition): ProvableSig = {
        requireOneSubgoal(provable, name)
        t(provable, pos)
      }
    }

    /** Creates a BuiltInTwoPositionTactic from a function turning provables and two positions into new provables.
      * @example {{{
      *         "andL" by((pr,pos)=> pr(AndLeft(pos.top),0))
      *         }}}
      */
    def by(t: (ProvableSig, Position, Position) => ProvableSig): BuiltInTwoPositionTactic = new BuiltInTwoPositionTactic(name) {
      @inline override def computeResult(provable: ProvableSig, pos1: Position, pos2: Position): ProvableSig = {
        requireOneSubgoal(provable, name)
        t(provable, pos1, pos2)
      }
    }
  }

  // augment anonymous tactics
  def anon(t: BelleExpr): BelleExpr = "ANON" by t
  def anon(t: ((ProvableSig, AntePosition) => ProvableSig)): BuiltInLeftTactic = "ANON" by t
  def anon(t: ((ProvableSig, SuccPosition) => ProvableSig)): BuiltInRightTactic = "ANON" by t
  def anon(t: ((ProvableSig, Position, Position) => ProvableSig)): BuiltInTwoPositionTactic = "ANON" by t
  def anon(t: ((Position, Sequent) => BelleExpr)): DependentPositionTactic = "ANON" by t
  def anon(t: (Position => BelleExpr)): DependentPositionTactic = "ANON" by t
  def anon(t: (Sequent => BelleExpr)): DependentTactic = "ANON" by t
  def coreanon(t: (ProvableSig, AntePosition) => ProvableSig): CoreLeftTactic = "ANON" coreby t
  def coreanon(t: (ProvableSig, SuccPosition) => ProvableSig): CoreRightTactic = "ANON" coreby t
  /* Function [[inputanon]]  should never be executed. Write these in @Tactic tactics and @Tactic
   * will transform them to the correct byWithInputs */
  def inputanon(t: Sequent => BelleExpr): InputTactic = "ANON" byWithInputs(Nil, t)
  def inputanon(t: (Position => BelleExpr)): DependentPositionWithAppliedInputTactic = "ANON" byWithInputs(Nil, t)
  def inputanon(t: ((Position, Sequent) => BelleExpr)): DependentPositionWithAppliedInputTactic = "ANON" byWithInputs(Nil, t)
  def inputanonR(t: ((ProvableSig, SuccPosition) => ProvableSig)): DependentPositionWithAppliedInputTactic = "ANON" corebyWithInputsR(Nil:Seq[Any], t)
  def inputanonL(t: ((ProvableSig, AntePosition) => ProvableSig)): DependentPositionWithAppliedInputTactic = "ANON" corebyWithInputsL(Nil:Seq[Any], t)
  def inputanon(t: => BelleExpr): InputTactic = "ANON" byWithInputs( Nil, t)
}

/**
 * @author Nathan Fulton
 */
//object Legacy {
//  /** The default mechanism for initializing KeYmaeraScheduler, Mathematica, and Z3 that are used in the legacy tactics.
//    * @note This may interfere in unexpected ways with sequential tactics.
//    */
//  def defaultInitialization(mathematicaConfig:  Map[String,String]) = {
//    Tactics.KeYmaeraScheduler = new Interpreter(KeYmaera)
//    Tactics.MathematicaScheduler = new Interpreter(new Mathematica)
//
//    Tactics.KeYmaeraScheduler.init(Map())
//    Tactics.Z3Scheduler.init
//    Tactics.MathematicaScheduler.init(mathematicaConfig)
//  }

//  def defaultDeinitialization = {
//    if (Tactics.KeYmaeraScheduler != null) {
//      Tactics.KeYmaeraScheduler.shutdown()
//      Tactics.KeYmaeraScheduler = null
//    }
//    if (Tactics.MathematicaScheduler != null) {
//      Tactics.MathematicaScheduler.shutdown()
//      Tactics.MathematicaScheduler = null
//    }
//    if(Tactics.Z3Scheduler != null) {
//      Tactics.Z3Scheduler = null
//    }
//  }
//
//  def initializedScheduledTactic(mathematicaConfig : Map[String,String], tactic: keymaerax.tactics.Tactics.Tactic) = {
//    defaultInitialization(mathematicaConfig)
//    scheduledTactic(tactic)
//  }
//
//  def scheduledTactic(tactic : keymaerax.tactics.Tactics.Tactic) = new BuiltInTactic(s"Scheduled(${tactic.name})") {
//    //@see [[Legacy.defaultInitialization]]
//    if(!Tactics.KeYmaeraScheduler.isInitialized)
//      throw new BelleThrowable("Need to initialize KeYmaera scheduler and possibly also the Mathematica scheduler before running a Legacy.ScheduledTactic.")
//
//    override def result(provable: Provable): Provable = {
//      //@todo don't know if we can create a proof node from a provable.
//      if(provable.subgoals.length != 1) throw new Exception("Cannot run scheduled tactic on something with more than one subgoal.")
//
//      val node = new keymaerax.tactics.RootNode(provable.subgoals.head)
//
//      Tactics.KeYmaeraScheduler.dispatch(new TacticWrapper(tactic, node))
//
//      node.provableWitness
//    }
//  }
//}