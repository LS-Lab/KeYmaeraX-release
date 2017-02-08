package edu.cmu.cs.ls.keymaerax.btactics.cexsearch

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleProvable, SequentialInterpreter}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._

import scala.collection.immutable

/**
  * Given two propositions pre,post and a hybrid program prog, search for a counterexample to pre -> [prog]post.
  * We maintain the invariant that pre is program-free, but post is allowed to have the form [prog'] Q'.
  * Created by bbohrer on 4/24/16.
  */
object ProgramSearchNode {
  def apply(fml:Formula)(implicit qeTool:QETool):ProgramSearchNode = {
    fml match {
      case (Imply(pre, Box(prog, post))) => ProgramSearchNode(pre,prog,post)
      case (Imply(a, Imply(b, c))) => apply(Imply(And(a,b), c))
      case _ => throw new IllegalArgumentException("ProgramSearchNode expects formula of shape P -> [a] Q")
    }
  }
}

case class ProgramSearchNode (pre: Formula, prog: Program, post: Formula)(implicit qeTool: QETool) extends SearchNode {

  /* We are at a goal state if there is a counterexample to pre -> [prog] post that we can find without any more
  * search, which is to say there are no programs left. Since our representation requires that we always have some "program",
  * we represent "no program" as the no-op program ?True. Note that the postcondition is allowed to contain programs,
  * so we are not done unless the postcondition is also free of programs.
  *
  * If we are at a goal state, this returns the actual counterexample that we found, otherwise it returns None to indicate
  * absence of a counterexample
  * */
  def goal = (prog, post) match {
    case (_, Box(_,_)) => None
    case (Test(True), _) =>
      /* Stupid hack - QE fails on formulas that contain no variables, so change P to (x = x) -> P for fresh x, which
       * is equivalent
       */
      val fml = Imply(pre, post)
      val freshVar = UniqueVariable.make
      val hackFml = Imply(Equal(freshVar, freshVar), fml)
      TactixLibrary.findCounterExample(hackFml) match {
        case Some(cex) => Some(ConcreteState(cex.asInstanceOf[Map[NamedSymbol,Term]]))
        case None => None
       }

    case _ => None
  }

  /* Returns a sequence of search states reachable by running this program for one step. The search need not be complete
  * but should be sound, meaning that a counterexample for any child formula constitutes a counterexample for the parent. */
  def children = {
    val kids =
    prog match {
      case Test(True) =>
        post match {
          case Box(a, newPost) => List(ProgramSearchNode(pre, a, newPost))
          case _ => Nil
        }
      case Test(fml) => List(ProgramSearchNode(And(pre, fml), Test(True), post))
      case Assign(x, e) =>
        val vars = StaticSemantics.boundVars(post)
        /* P -> [x := e] Q goes to P & x' = e -> [?true] {x|->x'}Q for fresh x' */
        if (vars.contains(x)) {
          val xPrime = UniqueVariable.make
          val newPost = URename(x, xPrime)(post)
          List(ProgramSearchNode(And(pre, Equal(xPrime, e)), Test(True), newPost))
        } else {
          /* P -> [x := e] Q goes to P -> [?true] {x |-> e} Q */
          val newPost = post.replaceAll(x, e)
          List(ProgramSearchNode(pre, Test(True), newPost))
        }
      /* Differential Symbols are no longer a separate case.
        case Assign(DifferentialSymbol(x), e) =>

        val vars = StaticSemantics.boundVars(post)
        /* P -> [x := e] Q goes to P & x' = e -> [?true] {x|->x'}Q for fresh x' */
        if (vars.contains(DifferentialSymbol(x))) {
          val xPrime = UniqueVariable.make
          val newPost = URename(x, xPrime)(post)
          List(ProgramSearchNode(And(pre, Equal(xPrime, e)), Test(True), newPost))
        } else {
          /* P -> [x := e] Q goes to P -> [?true] {x |-> e} Q */
          val newPost = post.replaceAll(DifferentialSymbol(x), e)
          List(ProgramSearchNode(pre, Test(True), newPost))
        }*/
      case AssignAny(x) => List(ProgramSearchNode(pre, Test(True), Forall(immutable.Seq(x), post)))
      case Compose(a, b) => List(ProgramSearchNode(pre, a, Box(b, post)))
      case Choice(a, b) => List(ProgramSearchNode(pre, a, post), ProgramSearchNode(pre, b, post))
      case Loop(a) => List(ProgramSearchNode(pre, Test(True), post), ProgramSearchNode(pre, a, Box(Loop(a), post)))
      case ODESystem(ode, constraint) => ???
      case _: AtomicODE => ???
      case _: DifferentialProduct => ???
      case _: Dual => throw new IllegalArgumentException("Hybrid games not supported")
      /* This should really never come up during execution, but if it does, since this means "I can be any program"
      * it means we could make the state whatever we want, which simply means the precondition goes out the window
      * and the precondition needs to hold in every possible state */
      case ProgramConst (_) | DifferentialProgramConst(_, _) => List(ProgramSearchNode(True, Test(True), post))

    }
    kids.toSet
  }

  /* Heuristic value for this search state. Should be admissible and all that good stuff. Let's pick a heuristic that
  * looks at both how expensive a state is to evaluate and how likely it is to be a counterexample. In particular, since
  * deciding first-order logic formulas is O(2^(2^n)) in number of variables, we should work that into our cost for
  * leaves. */
  def value:Float = 0

}
