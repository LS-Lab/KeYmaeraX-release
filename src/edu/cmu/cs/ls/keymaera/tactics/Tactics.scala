/**
 * *****************************************************************************
 * Copyright (c) 2014 Jan-David Quesel.
 *
 * Contributors:
 *     Jan-David Quesel - initial API and implementation
 * ****************************************************************************
 */
package edu.cmu.cs.ls.keymaera.tactics

import scala.Option.option2Iterable
import edu.cmu.cs.ls.keymaera.core.{Program, Rule, Term, ProofNode}

/**
 * @author jdq
 *
 */
object Tactics {
  trait Timeout;
  val timeout = new Timeout {};

  // implicit conversions
  //implicit def immutableList2OptionList[T](l: ImmutableList[T]): Option[List[T]] = if (l.isEmpty) None else Some(l)

  //implicit def immutableList2List[T](l: ImmutableList[T]): List[T] = (for (i <- l.iterator) yield i).toList

  implicit def ogl2Left(l: Option[Seq[ProofNode]]): Either[Option[Seq[ProofNode]], Timeout] = Left(l)

  implicit def timeout2Right(l: Timeout): Either[Option[Seq[ProofNode]], Timeout] = Right(l)

  implicit def elgt2eolgt(l: Either[Seq[ProofNode], Timeout]): Either[Option[Seq[ProofNode]], Timeout] = l match {
    case Left(x) => Left(Some(x))
    case Right(x) => Right(x)
  }

  implicit def tactic2lazy(t: Tactic): () => Tactic = () => t

  def listOfLefts[A, B](l: Seq[Either[A, B]]): Seq[A] = l collect { case Left(x: A) => x }

  type RuleNumberLimit = Option[Int]

  type TimeLimit = Option[Long]

  class Limit(rl: RuleNumberLimit, tl: TimeLimit) {
    var rulesApplied = 0
    val initialTime = System.currentTimeMillis
    def limitHit: Boolean = (rl match {
      case Some(i) => i > rulesApplied
      case None => false
    }) || (tl match {
      case Some(i) => (System.currentTimeMillis - initialTime > i * 1000)
      case None => false
    })
    def timeLeft: TimeLimit = tl match {
      case None => None
      case Some(i) => Some(System.currentTimeMillis - initialTime)
    }
    def ++ : Unit = rulesApplied += 1
  }

  trait TacticConstructor {
    def getTactic: Tactic;
    def getName: String;
  }

  // A tactic is a script that applies specific rules to a goal
  // it can be built up using the usual constructs like sequential composition,
  // choice, repetition and other helper functions for conditional execution.
  // Further there are methods for generating terms/programelements that will be used
  // to instantiate schema variables in the rules.
  abstract class Tactic(name: String)
    extends ((ProofNode, Limit) => Either[Option[Seq[ProofNode]], Timeout]) {
    // repeat tactic until a fixed point is reached
    def * : Tactic = repeatT(this)
    // apply the first tactic applicable
    def |(o: () => Tactic): Tactic = eitherT(this, o)
    // t1 ~ t2 = (t1 & t2) | t2
    def ~(o: () => Tactic): Tactic = composeBothT(this, o)
    // execute this tactic and the given tactics on the resulting branches
    def &(o: (() => Tactic)*): Tactic = composeT(this, o: _*)
    // create an or-branch for each given tactic
    def <(tcts: (() => Tactic)*) = branchT((() => this) :: tcts.toList: _*)
    override def toString: String = name
  }

  def repeatT(t: Tactic): Tactic = new Tactic("repeat " + t.toString) {
    def apply(g: ProofNode, l: Limit): Either[Option[Seq[ProofNode]], Timeout] = {
      val app = (x: ProofNode) => apply(x, l)
      t(g, l) match {
        case x @ Right(_) => x // timeout
        // case branch closed
        case Left(None) => None
        // case a single goal, check if something changed
        // if we reached a fixed point, return
        case Left(Some(List(ng))) if (ng == g) => Some(List(g))
        // changed goals
        case Left(Some(goals)) =>
          val result = goals.map(app)
          if (result.contains(Right(timeout))) Right(timeout)
          else {
            val res = listOfLefts(result).flatten.flatten
            if (res.isEmpty) None else Some(res)
          }
      }
    }
  }

  /**
   * Apply t1 and if it changed something apply t2 afterwards
   */
  // execute tactic t on the current goal, for ts = (t1,t2,t3): execute t1 on the first goal, t2 on the second, and t3 on the rest
  def composeT(t: Tactic, ts: (() => Tactic)*): Tactic = new Tactic("compose " +
    t.toString + " -> " + ts.toString) {
    def apply(p: ProofNode, l: Limit): Either[Option[Seq[ProofNode]], Timeout] = {
      // create a stream that contains the elements of the given sequence and repeats the last one infinitly often
      def stutter[A](idx: Int, lst: Seq[A]): Stream[A] = Stream.cons(lst(idx), stutter(math.min(idx + 1, lst.length), lst))
      t(p, l) match {
        // timeout
        case x @ Right(_) => x
        // case branch closed
        case x @ Left(None) => x
        // the first tactic could not be applied, therefore stop here
        case r @ Left(Some(Seq(ng))) if (ng == p) => r
        // case goals returned, execute t1 on the first one and t2 on tail.head and t3 on the rest
        case Left(Some(goals)) =>
          // apply ts.head to the first goal, ts.tail.head to the second and so on.
          // Apply ts.last to the remainder of the goals
          val result = stutter(0, ts).zip(goals).map(x => x._1()(x._2, l)).take(math.min(ts.length, goals.length)).toList
          if (result.contains(Right(timeout))) Right(timeout)
          else {
            val res = listOfLefts(result).flatten.flatten
            if (res.isEmpty) Left(None) else Some(res)
          }
      }
    }
  }

  def composeBothT(t1: Tactic, t2: () => Tactic): Tactic = (t1 & t2) | t2

  /**
   * Try to apply t1 and if it is not applicable try t2
   */
  def eitherT(t1: Tactic, t2: () => Tactic) = new Tactic("either " + t1 + " or " + t2) {
    def apply(g: ProofNode, l: Limit): Either[Option[Seq[ProofNode]], Timeout] = {
      // apply t1
      t1(g, l) match {
        // case branch closed
        case Left(None) => None
        // case a single goal, check if something changed
        // if nothing changed try t2
        case Left(Some(List(ng))) if (ng == g) => t2()(g, l)
        // something was changed by t1 or we have a timeout
        case a => a
      }
    }
  }

  // spawn one or-branch per given tactic and persue the tactic on the respective branch
  def branchT(tcts: (() => Tactic)*): Tactic = new Tactic("branch") {
    def apply(p: ProofNode, l: Limit): Either[Option[Seq[ProofNode]], Timeout] = ???/*{
      if (g.node.isClosed) return None
      val gs = g.apply(new BuiltInRuleApp(new OrBranchRule(tcts.size),
        new PosInOccurrence(g.node.sequent.iterator.next, PosInTerm.TOP_LEVEL, false),
        Constraint.TOP)).reverse
      val branches = gs.toArray(new Array[Goal](gs.size))
      assert(branches.size == tcts.size)
      val res = for (i <- 0 until tcts.size)
        yield tcts(i)()(branches(i), s, am.clone(branches(i)), l) match {
        case Left(Some(goals)) => goals
        case Left(None) => return None // one of the Or-Branches is already closed
        // if there was a timeout we ignore the result
      }
      if (res.size > 0) Some(res.toList.flatten) else None
    }*/
  }

  def NilT: Tactic = new Tactic("Nil") {
    def apply(g: ProofNode, l: Limit): Either[Option[Seq[ProofNode]], Timeout] = {
      Some(List(g))
    }
  }

  def ifT(cond: ProofNode => Boolean, t: Tactic): Tactic = ifElseT(cond, t, NilT)

  def ifElseT(cond: ProofNode => Boolean, t: Tactic, ot: Tactic): Tactic = new Tactic("conditional " + t + " else " + ot) {
    def apply(g: ProofNode, l: Limit): Either[Option[Seq[ProofNode]], Timeout] = {
      if (cond(g)) t(g, l) else ot(g, l)
    }
  }


  /*
  def testT3: Tactic = (testT2 < (testT2 ~ cutT((_, _) => Some(Left(TermBuilder.DF.tt))))) ~ dlstrategy

  def testT: Tactic = dlstrategy

  //def testT: Tactic = TacticLoader.loadTactic(new File("/tmp/Test.scala")).getTactic

  def testTp: Tactic = ((testT2 | tryheuristicT("alpha") | tryheuristicT("simplify_prog") | tryheuristicT("diff_solve"))*) ~ tryruleT(ReduceRule.INSTANCE.name.toString)

  def testT2: Tactic = (tryruleT("modality_split_right") | tryruleT("eliminate_variable_decl") | tryruleT(UpdateSimplificationRule.INSTANCE.name.toString))*

  def dlstrategy: Tactic = (((tryheuristicT("closure", "concrete",
      "alpha", "simplify_prog", "simplify", "diff_solve", "delta", "beta")) | loopInvT | loopTry)*) ~
    eliminateUniversalQuantifiersT
  //tryruleT(ReduceRule.INSTANCE.name.toString)

  def dlstrategyOrg: Tactic = (((tryruleT(UpdateSimplificationRule.INSTANCE.name.toString)
    | tryheuristicT("closure", "concrete",
      "alpha", "simplify_prog", "simplify", "delta", "beta") | diffSolveT) | loopInvT)*) ~
    eliminateUniversalQuantifiersT

  def eliminateUniversalQuantifiersT = tryruleT(MergeSequentRule.name.toString) ~ tryruleT(QuantifyAllSkolemSymbolsRule.name.toString) ~ tryruleT("reduce_form_right") ~ tryruleT("close_by_true")

  def run(t: Tactic, g: Goal, s: Services) = t(g, s, new DLRuleAppManager, new Limit(None, None))

  def run(t: Tactic, goals: ImmutableList[Goal], s: Services) =
    for (g <- immutableList2List(goals))
      t(g, s, new DLRuleAppManager, new Limit(None, None))

  def timeoutT(t: Tactic, rl: RuleNumberLimit, tl: TimeLimit): Tactic = new Tactic("timeout " + t) {
    def apply(g: Goal, s: Services, am: AppManager, u: Limit): Either[Option[List[Goal]], Timeout] = t(g, s, am, new Limit(rl, tl))
  }
  */


  def cutT(g: ((Rule, ProofNode) => Option[Either[Term, Program]])): Tactic = ???

  // interface for generating instances
  type Generator[T] = ((Rule, ProofNode, String) => Option[T])

  // creates a new branch and evaluates t, then evaluates t on the other branch
  // this assumes that t has a state that changes during each execution and will
  // eventually halt
  def branchRepeatT(t: Tactic): Tactic = branchT(t, () => branchRepeatT(t))

  def isApplicableRule(r: String, g: ProofNode): Boolean = ???

  def isApplicableHeuristics(h: String, g: ProofNode): Boolean = ???

  // check whether the given rule r is applicable on the current goal and if it is
  // apply the given tactic t
  def ifApplicableRuleT(r: String, t: Tactic): Tactic = ifT(isApplicableRule(r, _), t)

  // check whether some rule in the given heuristic group h is applicable on
  // the current goal and if it is apply the given tactic t
  def ifApplicableHeuristicsT(h: String, t: Tactic): Tactic = ifT(isApplicableHeuristics(h, _), t)

  def withMathematicaQE(t: Tactic): Tactic = useQEMethod("Mathematica", t)

  def withRedlogQE(t: Tactic): Tactic = useQEMethod("Reduce", t)

  def withSMTQE(t: Tactic): Tactic = useQEMethod("SMT", t)

  // use a specific method for QE in the sub tactic
  // FIXME: this can cause issues with stoppen as the MathSolverManger does not know about this
  // FIXME: this needs to be saved along with the proof!
  def useQEMethod(qe: String, t: Tactic): Tactic = new Tactic("QE= " + qe + " in " + t) {
    def apply(g: ProofNode, l: Limit): Either[Option[Seq[ProofNode]], Timeout] = ???
  }

}

