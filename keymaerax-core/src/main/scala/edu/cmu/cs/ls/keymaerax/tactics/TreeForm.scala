package edu.cmu.cs.ls.keymaerax.tactics

import edu.cmu.cs.ls.keymaerax.core._

import scala.collection.mutable

/**
 * Represent terms as recursive lists of logical symbols. This simplified structure is useful for certain analyses that
 * treat all the operators in a relatively uniform way. This representation flattens the term's structure as much as
 * possible (e.g. turning a+(b+c) into (a+b+c)), to make analyses that consider the depth of a term more meaningful.
 * Created by bbohrer on 10/23/15.
 */
object TreeForm {
  sealed case class TermSymbol () {}
  final case class Var(name: String) extends TermSymbol
  final case class DiffVar(name: String) extends TermSymbol
  final case class Func(name:String) extends TermSymbol
  final case class Operator(name:String, arity: Option[Int]) extends TermSymbol {}
  final case class Constant(value:Number) extends TermSymbol {}

  object Tree {
    def binaryTree (t: Term): Tree = {
      t match {
        case Plus (t1, t2) => Tree(Operator("+", Some(2)), List(binaryTree(t1), binaryTree(t2)))
        case Times (t1, t2) => Tree(Operator("*", Some(2)), List(binaryTree(t1), binaryTree(t2)))
        case Divide (t1, t2) => Tree(Operator("/", Some(2)), List(binaryTree(t1), binaryTree(t2)))
        case Power (t1, t2) => Tree(Operator("^", Some(2)), List(binaryTree(t1), binaryTree(t2)))
        case Minus (t1, t2) => Tree(Operator("-", Some(2)), List(binaryTree(t1), binaryTree(t2)))
        case Neg (t1) => Tree(Operator("-", Some(2)), List(Tree(Constant(Number(0)), List()), binaryTree(t1)))
        case Differential(t1) => Tree(Operator("'", Some(1)), List(binaryTree(t1)))
        case Variable (name, _, _) => Tree(Var(name), List())
        case DifferentialSymbol (v, _) => Tree(DiffVar(v.name), List())
        case FuncOf(Function(f, _, _), x) => Tree(Func(f), List(binaryTree(x)))
      }
    }
  }

  final case class Tree (sym: TermSymbol, args: List[Tree]) {
    def this (t: Term) { this (Tree.binaryTree(t).simplify)}

    def size: Int = args.foldLeft(1){case (acc, t) => acc + t.size}

    private def expand(name:String, l:List[Tree]): List[Tree] =
      l.flatMap({case Tree(Operator(name2), lst) => if (name.equals(name2)) lst else Nil})

    private def fixedPoint(l:List[Tree], f:List[Tree] => List[Tree]): List[Tree] = {
      val l2 = f(l)
      if (l.length == l2.length) l
      else fixedPoint(l2, f)
    }

    /**
     * Works best if the input is an output of Tree.binaryTree
     * @return A Tree where as many n-ary operators as possible have been recovered from their binary equivalents
     */
    private def simplify:Tree =
      this match {
        case Tree(Operator("+", _), lst) =>
          val expanded = fixedPoint(lst, {case l => expand("+", l)})
          Tree(Operator("+", Some(expanded.length)), expanded.map({case t => t.simplify}))
        case Tree(Operator("*", _), lst) =>
          val expanded = fixedPoint(lst, {case l => expand("*", l)})
          Tree(Operator("*", Some(expanded.length)), expanded.map({case t => t.simplify}))
        case Tree(Operator("-", Some(n1)), (Tree(Operator("-",Some(n2)), l1))::l2) =>
          Tree(Operator("-", Some(n1+n2-1)), l1 ++ l2).simplify
        case Tree(Operator("-", Some(n)), hd::tl) =>
          val positive = hd::tl.flatMap({case Tree(Operator("-", _), hd1::_) => List(hd1) case _ => Nil})
          val negative = tl.flatMap({case Tree(Operator("-", _), _::tl1) => tl1 case _ => Nil})
          Tree(Operator("-", Some(n)), Tree(Operator("+", Some(positive.length)), positive)::negative).simplify
        case Tree(Operator("/", Some(n1)), (Tree(Operator("/",Some(n2)), l1))::l2) =>
          Tree(Operator("/", Some(n1+n2-1)), l1 ++ l2).simplify
        case Tree(Operator("/", Some(n)), hd::tl) =>
          val mult = hd::tl.flatMap({case Tree(Operator("/", _), hd1::_) => List(hd1) case _ => Nil})
          val div = tl.flatMap({case Tree(Operator("/", _), _::tl1)=> tl1 case _ => Nil})
          Tree(Operator("/", Some(n)), Tree(Operator("*", Some(mult.length)), mult)::div)
        case Tree(Operator("^", Some(n1)), l) =>
          l.last match {
            case Tree(Operator("^", Some(n2)), l2) => Tree(Operator("^", Some(n1+n2-1)), l.take(l.length-1) ++ l2).simplify
            case _ => Tree(Operator("^", Some(n1)), l.map({case t => t.simplify}))
          }
        case Tree(hd, l) => Tree(hd, l.map({case t => t.simplify}))
      }

  def iterDepth(depth: Int, f: (Int, Tree) => Unit): Unit = {
    f(depth, this)
    this match {
      case Tree(_, l) => l.foldLeft(())({case ((), t) => iterDepth(depth + 1, f)})
    }
  }

  def iterDepth(f: (Int, Tree) => Unit): Unit = iterDepth(0, f)
  }

  case class Stat (count: Int, depthWeighted: Int, sizeWeighted: Int) {
    def this (l : List[Tree], depth: Int) = this (1, depth, l.foldLeft(1)({case (acc, t) => acc + t.size}))
    def add (l: List[Tree], depth: Int): Stat =
      Stat(1 + count, depth + depthWeighted, l.foldLeft(sizeWeighted)({case (acc, t) => acc + t.size}))
  }

  case class Stats (t : Term) {
    val asTree = new Tree(t)
    // Operators can appear with multiple arities. As a result, we may want to query both the stats for a particular
    // arity and the aggregate stats for an operator across all arities.
    val operatorTotals = new mutable.HashMap[String, Stat] {}
    val counts = new mutable.HashMap[TermSymbol, Stat] {}
    asTree.iterDepth({case (depth, Tree(sym, l)) =>
      counts.find({case (sym2, _) => sym.equals(sym2)}) match {
        case None => counts.+((sym, new Stat(l, depth)))
        case Some((_, stat)) => counts.+((sym, stat.add(l, depth)))
      }
      sym match {
        case Operator(name, _) =>
          operatorTotals.find({case (name2, _) => name == name2}) match {
            case Some((_, stat)) => operatorTotals.+((name, stat.add(l, depth)))
            case None => operatorTotals.+((name, new Stat (l, depth)))
          }
        case _ => ()
      }
    })
  }

  class StatOrdering (ord: Ordering[Stats]) extends Ordering[Term]{
    def compare (x: Term, y: Term): Int = ord.compare(Stats(x), Stats(y))
  }

  def weightOrdering (f : Stats => Int): Ordering[Term] = {
    new StatOrdering(new Ordering[Stats] {def compare (x: Stats, y: Stats) = f(x).compare(f(y))})
  }

  /** Knuth-Bendix orderings assign a constant weight to each symbol and then
    * weigh the terms based on the sum of all the symbols within.
    * Weights for operators without an arity specified apply to all arities for that operator.
    * @see Knuth, D. E., Bendix, P. B.Simple word problems in universal algebras. */
  class KnuthBendixOrdering (weighting: List[(TermSymbol, Int)]) extends Ordering[Term]{
    def compare (x: Term, y: Term): Int = {
      val (xStats, yStats) = (Stats(x), Stats(y))
      weighting.foldLeft(0)({ case (cmp, (sym, weight)) =>
        if (cmp != 0) cmp
        else {
          def compareOpt(x: Option[Stat], y: Option[Stat]): Int =
            (x, y) match {
              case (None, None) => 0
              case (Some(_), None) => 1
              case (None, Some(_)) => -1
              case (Some(Stat(count1, _, _)), Some(Stat(count2, _, _))) => count1.compare(count2)
            }
          sym match {
            // Get aggregate stats for this operator across all arities
            case Operator(name, None) =>
              compareOpt(xStats.operatorTotals.get(name), yStats.operatorTotals.get(name))
            case _ => compareOpt(xStats.counts.get(sym), yStats.counts.get(sym))
          }
        }
      })
    }
  }

  /** @todo implement: variation on Knuth-Bendix ordering where weights depend on the depth of a constructor within a term*/
  class DepthKBOrdering (weighting: List[(String, Int)], depthFactor: Int => Int) {

  }
}
