/**
 * *****************************************************************************
 * Copyright (c) 2014 Jan-David Quesel, Marcus Völp
 *
 * Contributors:
 *     Jan-David Quesel - initial API and implementation
 *     Marcus Völp      - parallel execution framework
 * ****************************************************************************
 */
package edu.cmu.cs.ls.keymaera.tactics

//import scala.Option.option2Iterable
import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.core.Tool
//import scala.Left
//import scala.Right
//import scala.Some
import scala.Unit
import scala.math.Ordered
import scala.collection.mutable.SynchronizedQueue
import scala.annotation.elidable
import scala.annotation.elidable._

val KeYmaeraScheduler = new Scheduler(Seq.fill(Config.maxCPUs)(KeYmaera))


/**
 * @author jdq
 *
 */
/*
object Tactics {

//  trait Timeout;
//  val timeout = new Timeout {};

  // implicit conversions
  //implicit def immutableList2OptionList[T](l: ImmutableList[T]): Option[List[T]] = if (l.isEmpty) None else Some(l)

  //implicit def immutableList2List[T](l: ImmutableList[T]): List[T] = (for (i <- l.iterator) yield i).toList

//  implicit def ogl2Left(l: Option[Seq[ProofNode]]): Either[Option[Seq[ProofNode]], Timeout] = Left(l)

//  implicit def timeout2Right(l: Timeout): Either[Option[Seq[ProofNode]], Timeout] = Right(l)

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
  abstract class Tactic(val name: String, val root : ProofNode) {
    var result : Seq[ProofNode]

/*    extends ((ProofNode, Limit) => Either[Option[Seq[ProofNode]], Timeout]) { */

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

    def apply(tool : Tool) {}
  

//  abstract class PositionTactic(val name: String) extends (Position => Tactic) {
//    def applies(s: Sequent, p: Position): Boolean
//  }

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
      println("Applying " + name)
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
  //def ifT(cond: Sequent => Boolean, t: Tactic): Tactic = ifElseT(cond, t, NilT)

  def ifElseT(cond: ProofNode => Boolean, t: Tactic, ot: Tactic): Tactic = new Tactic("conditional " + t + " else " + ot) {
    def apply(g: ProofNode, l: Limit): Either[Option[Seq[ProofNode]], Timeout] = {
      if (cond(g)) t(g, l) else ot(g, l)
    }
  }
  //def ifElseT(cond: Sequent => Boolean, t: Tactic, ot: Tactic): Tactic = ifElseT(((p: ProofNode) => cond(p.sequent)), t, ot)


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

  // interface for generating instances
  type Generator[T] = ((Rule, ProofNode, String) => Option[T])

  // creates a new branch and evaluates t, then evaluates t on the other branch
  // this assumes that t has a state that changes during each execution and will
  // eventually halt
  def branchRepeatT(t: Tactic): Tactic = branchT(t, () => branchRepeatT(t))


  /*********************************************
   * Basic Tactics
   ********************************************
   */

  def findPosAnte(posT: PositionTactic): Tactic = new Tactic("FindPos (" + posT.name + ")") {
    def apply(p: ProofNode, l: Limit): Either[Option[Seq[ProofNode]], Timeout] = {
      for(i <- 0 until p.sequent.ante.length) {
        val pos = new Position(true, i)
        if(posT.applies(p.sequent, pos)) return posT(pos)(p, l)
      }
      Some(Seq(p))
    }
  }

  def findPosSucc(posT: PositionTactic): Tactic = new Tactic("FindPos (" + posT.name + ")") {
    def apply(p: ProofNode, l: Limit): Either[Option[Seq[ProofNode]], Timeout] = {
      for(i <- 0 until p.sequent.succ.length) {
        val pos = new Position(false, i)
        if(posT.applies(p.sequent, pos)) return posT(pos)(p, l)
      }
      Some(Seq(p))
    }
  }

  def AndLeftT: PositionTactic = new PositionTactic ("AndLeft") {
    def applies(s: Sequent, p: Position) = if(p.isAnte) s.ante(p.index) match {
      case And(_, _) => true
      case _ => false
    } else false

    def apply(pos: Position): Tactic = new Tactic("AndLeft") {
      def apply(p: ProofNode, l: Limit): Either[Option[Seq[ProofNode]], Timeout] = applies(p.sequent, pos) match {
        case true => Some(p.apply(AndLeft(pos)))
        case false => Left(Some(Seq(p)))
      }
    }
  }

  def AndLeftFindT: Tactic = findPosAnte(AndLeftT)

  def AndRightT: PositionTactic = new PositionTactic ("AndRight") {
    def applies(s: Sequent, p: Position) = if(!p.isAnte) s.succ(p.index) match {
      case And(_, _) => true
      case _ => false
    } else false

    def apply(pos: Position): Tactic = new Tactic("AndRight") {
      def apply(p: ProofNode, l: Limit): Either[Option[Seq[ProofNode]], Timeout] = applies(p.sequent, pos) match {
        case true => Some(p.apply(AndRight(pos)))
        case false => Left(Some(Seq(p)))
      }
    }
  }

  def AndRightFindT: Tactic = findPosSucc(AndRightT)

  def OrLeftT: PositionTactic = new PositionTactic ("OrLeft") {
    def applies(s: Sequent, p: Position) = if(p.isAnte) s.ante(p.index) match {
      case Or(_, _) => true
      case _ => false
    } else false

    def apply(pos: Position): Tactic = new Tactic("OrLeft") {
      def apply(p: ProofNode, l: Limit): Either[Option[Seq[ProofNode]], Timeout] = applies(p.sequent, pos) match {
        case true => Some(p.apply(OrLeft(pos)))
        case false => Left(Some(Seq(p)))
      }
    }
  }

  def OrLeftFindT: Tactic = findPosAnte(OrLeftT)

  def OrRightT: PositionTactic = new PositionTactic ("OrRight") {
    def applies(s: Sequent, p: Position) = if(!p.isAnte) s.succ(p.index) match {
      case Or(_, _) => true
      case _ => false
    } else false

    def apply(pos: Position): Tactic = new Tactic("OrRight") {
      def apply(p: ProofNode, l: Limit): Either[Option[Seq[ProofNode]], Timeout] = applies(p.sequent, pos) match {
        case true => Some(p.apply(OrRight(pos)))
        case false => Left(Some(Seq(p)))
      }
    }
  }

  def OrRightFindT: Tactic = findPosSucc(OrRightT)

  def ImplyLeftT: PositionTactic = new PositionTactic ("ImplyLeft") {
    def applies(s: Sequent, p: Position) = if(p.isAnte) s.ante(p.index) match {
      case Imply(_, _) => true
      case _ => false
    } else false

    def apply(pos: Position): Tactic = new Tactic("ImplyLeft") {
      def apply(p: ProofNode, l: Limit): Either[Option[Seq[ProofNode]], Timeout] = applies(p.sequent, pos) match {
        case true => Some(p.apply(ImplyLeft(pos)))
        case false => Left(Some(Seq(p)))
      }
    }
  }

  def ImplyLeftFindT: Tactic = findPosAnte(ImplyLeftT)

  def ImplyRightT: PositionTactic = new PositionTactic ("ImplyRight") {
    def applies(s: Sequent, p: Position) = if(!p.isAnte) s.succ(p.index) match {
      case Imply(_, _) => true
      case _ => false
    } else false

    def apply(pos: Position): Tactic = new Tactic("ImplyRight") {
      def apply(p: ProofNode, l: Limit): Either[Option[Seq[ProofNode]], Timeout] = applies(p.sequent, pos) match {
        case true => Some(p.apply(ImplyRight(pos)))
        case false => Left(Some(Seq(p)))
      }
    }
  }

  def ImplyRightFindT: Tactic = findPosSucc(ImplyRightT)

  def NotLeftT: PositionTactic = new PositionTactic ("NotLeft") {
    def applies(s: Sequent, p: Position) = if(p.isAnte) s.ante(p.index) match {
      case Not(_) => true
      case _ => false
    } else false

    def apply(pos: Position): Tactic = new Tactic("NotLeft") {
      def apply(p: ProofNode, l: Limit): Either[Option[Seq[ProofNode]], Timeout] = applies(p.sequent, pos) match {
        case true => Some(p.apply(NotLeft(pos)))
        case false => Left(Some(Seq(p)))
      }
    }
  }

  def NotLeftFindT: Tactic = findPosAnte(NotLeftT)

  def NotRightT: PositionTactic = new PositionTactic ("NotRight") {
    def applies(s: Sequent, p: Position) = if(!p.isAnte) s.succ(p.index) match {
      case Not(_) => true
      case _ => false
    } else false

    def apply(pos: Position): Tactic = new Tactic("NotRight") {
      def apply(p: ProofNode, l: Limit): Either[Option[Seq[ProofNode]], Timeout] = applies(p.sequent, pos) match {
        case true => Some(p.apply(NotRight(pos)))
        case false => Left(Some(Seq(p)))
      }
    }
  }

  def NotRightFindT: Tactic = findPosSucc(NotRightT)

  def AxiomCloseT: Tactic = new Tactic("AxiomClose") {
    def apply(p: ProofNode, l: Limit): Either[Option[Seq[ProofNode]], Timeout] = findPositions(p.sequent) match {
      case Some((a, b)) => Some(p.apply(AxiomClose(a)(b)))
      case None => Left(Some(Seq(p)))
    }
    def findPositions(s: Sequent): Option[(Position,Position)] = {
      for(f <- s.ante; g <- s.succ)
        if(f == g) return Some((new Position(true, s.ante.indexOf(f)), new Position(false, s.succ.indexOf(g))))
      None
    }
  }

  def hideT: PositionTactic = new PositionTactic("Hide") {
    def applies(s: Sequent, p: Position) = true
    def apply(pos: Position): Tactic = new Tactic("Hide") {
      def apply(p: ProofNode, l: Limit): Either[Option[Seq[ProofNode]], Timeout] =
      if(pos.isDefined(p.sequent))
        Some(if(pos.isAnte) p(HideLeft(pos)) else p(HideRight(pos)))
      else
        Some(Seq(p))
    }
  }

  def cutT(g: (ProofNode => Option[Formula])): Tactic = new Tactic("Cut") {
    def apply(p: ProofNode, l: Limit): Either[Option[Seq[ProofNode]], Timeout] = g(p) match {
      case Some(t) => Some(p(Cut(t)))
      case _ => Some(Seq(p))
    }
  }

  def cutT(f: Formula): Tactic = cutT((x:ProofNode) => Some(f))

  def axiomT(id: String): Tactic = new Tactic("Axiom " + id) {
    def apply(p: ProofNode, l: Limit): Either[Option[Seq[ProofNode]], Timeout] = Axiom.axioms.get(id) match {
      case Some(_) => Some(p(Axiom(id)))
      case _ => Some(Seq(p))
    }
  }

  def uniformSubstT(subst: Substitution, delta: (Map[Formula, Formula])) = new Tactic("Uniform Substitution") {
    def apply(p: ProofNode, l: Limit): Either[Option[Seq[ProofNode]], Timeout] = {
      val ante = for(f <- p.sequent.ante) yield delta.get(f) match { case Some(frm) => frm case _ => f}
      val succ = for(f <- p.sequent.succ) yield delta.get(f) match { case Some(frm) => frm case _ => f}
      Some(p(UniformSubstition(subst, Sequent(p.sequent.pref, ante, succ))))
    }

  }

}
*/

object Tactics {

  sealed abstract class TacticResult
    case object Success       extends TacticResult
    case object Failed        extends TacticResult
    case object LimitExceeded extends TacticResult
    case object Unfinished    extends TacticResult


  class Limits(val parent   : Option[Limit],
               var timeout  : Option[Int],
               var branches : Option[Int],
               var rules    : Option[Int]) {


    private def check(opt : Option[Int]) : Boolean =
      opt match
        Some(value) => value > 0
        None    => true

    private def updateLocal(opt : Option[Int], value : Int) =
      opt match
        case Some(old_val) => opt = Some(old_val - value)
        case None =>

    def check() : Boolean = check(timeout) & check(branches) & check(rules)

    def update(t : Int, b : Int, r : Int) : Boolean =
      @synchronized(this) {
        update(timeout, t)
        update(branches, b)
        update(rules, r)
        parent match
          case Some(p) => p.updateRecursive(t, b, r) & check()
          case None    => check()
      }

    def time(fn : () => (Int, Int)) : (Int, Int, Int) {
      start = System.currentTimeMillis
      res = fn()
      return System.currentTimeMillis - start, res
    }

  }


  abstract class Tactic(val name : String) extends Ordered[Tactic] {

    var scheduler : Scheduler = KeYmaeraScheduler

    var limits : Limits

//    var listeners : SynchronizedQueue[TacticsListener] = new SynchronizedQueue()
//    var result    : Seq[ProofNode] = Nil
//    var status    : TacticResult   = Unfinished
//    var root      : ProofNode

    var continuation : (TacticResult, Seq[ProofNode]) => Unit

    override def toString: String = name

    def applicable(node : ProofNode) : Boolean
    def apply  (tool : Tool, node : ProofNode)

    val priority : Int = 10

    def dispatch(node : ProofNode) = scheduler.dispatch(new TacticWrapper(this, node))

    /**
     * Convenience wrappers
     */
  /*
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
  */
  }

  /**
   * do nothing
   */
  def NilT = new Tactic("Nil") {
    def applicable(node : ProofNode) = true
    def apply(tool : Tool, node : ProofNode) = {
      continuation(Success, new Seq(root))
    }
  }

  def onSuccess(t : Tactic)(status : TacticResult, result : Seq[ProofNode]) =
    if (status = Success) result.foreach((n : ProofNode) => t.dispatch(n))

  def unconditionally(t : Tactic)(status : TacticResult, result : Seq[ProofNode]) =
    result.forearch(n : ProofNode => t.dispatch(n))

  def onChange(n : ProofNode, t : Tactic)(status : TacticResult, result : Seq[ProofNode]) =
    if (Seq(n) != result) result.foreach(n : ProofNode => t.dispatch(n))

  def onNoChange(n : ProofNode, t : Tactic)(status : TacticResult, result : Seq[ProofNode]) =
    if (Seq(n) = result) t.dispatch(n)

  def SeqT(left : Tactic, right : Tactic) = new Tactic("Seq(" + left.name + "," + right.name + ")") {
    def applicable(node : ProofNode) = left.applicable(node)

    def apply(tool : Tool, node : ProofNode) = {
      right.continuation = continuation
      left.continuation = onSuccess(right)
      left.dispatch(node)
    }
  }

  def EitherT(left : Tactic, right : Tactic) =
    new Tactic("Seq(" + left.name + "," + right.name + ")") {
      def applicable(node : ProofNode) = left.applicable(node)

      def apply(tool : Tool, node : ProofNode) = {
        right.continuation = continuation
        left.continuation = onNoChange(right)
        left.dispatch(node)
      }
  }

  def WeakSeqT(left : Tactic, right : Tactic) =
    new Tactic("WeakSeq(" + left.name + "," + right.name + ")") {
      def applicable(node : ProofNode) = left.applicable(node)

      def apply(tool : Tool, node : ProofNode) = {
        right.continuation = continuation
        left.continuation  = unconditionally(right)
        left.dispatch(node)
      }
  }

  def ifElseT(cond : ProofNode => Boolean, thenT : Tactic, elseT : Tactic) =
    new Tactic("Conditional " + thenT + " else " elseT) {
      def applicable(node : ProofNode) = true

      def apply(tool : Tool, node : ProofNode) = {
        if (cond(node)) {
           thenT.continuation = continuation
           thenT.dispatch(node)
        } else {
           elseT.continuation = continuation
           elseT.dispatch(node)
        }
      }
  }

  def ifT(cond : ProofNode => Boolean, thenT : Tactic) = ifElseT(cond, thenT,

  // def branchT(tcts: (() => Tactic)*): Tactic = new Tactic("branch")
  // def branchRepeatT(t: Tactic): Tactic = branchT(t, () => branchRepeatT(t))
  // def repeatT(t: Tactic): Tactic = 


  /********************************************************************************
   * Rule application
   ********************************************************************************
   */

  /**
   * Apply rule
   */
  abstract class ApplyRule(val rule : Rule) extends Tactic("Apply rule " + rule) {
    def apply(tool : Tool, node : ProofNode) = {
      if (applicable(node)) {
        continuation(Success, node(rule))
      } else {
        continuation(Failed,  Seq(node))
      }
    }
  }

  /**
   * Apply position rule
   */
  abstract class ApplyPositionRule(val rule : PositionRule, val pos : Position)
                                            extends Tactic("Apply rule " + rule) {

    def apply(tool : Tool, node : ProofNode) = {
      if (applicable(node)) {
        continuation(Success, node(rule, pos))
      } else {
        continuation(Failed,  Seq(node))
      }
    }
  }

  /**
   * Apply position rule
   */
  abstract class ApplyAssumptionRule(val rule : AssumptionRule,
                                     val aPos : Position, val pos : Position)
                                            extends Tactic("Apply rule " + rule) {

    def apply(tool : Tool, node : ProofNode) = {
      if (applicable(node)) {
        continuation(Success, node(rule, aPos, pos))
      } else {
        continuation(Failed,  Seq(node))
      }
    }
  }

}
