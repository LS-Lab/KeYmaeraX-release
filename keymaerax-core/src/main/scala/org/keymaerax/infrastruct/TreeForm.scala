/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.infrastruct

import org.keymaerax.core._

import scala.annotation.nowarn
import scala.collection.mutable

/**
 * Represent terms as recursive lists of logical symbols. This simplified structure is useful for certain analyses that
 * treat all the operators in a relatively uniform way. This representation flattens the term's structure as much as
 * possible (e.g. turning a+(b+c) into (a+b+c)), to make analyses that consider the depth of a term more meaningful.
 *
 * Created by bbohrer on 10/23/15.
 */
object TreeForm {
  sealed trait TermSymbol {}
  final case class Var(name: String) extends TermSymbol
  final case class DiffVar(name: String) extends TermSymbol
  final case class Func(name: String) extends TermSymbol
  final case class Operator(name: String, arity: Option[Int]) extends TermSymbol {}
  final case class Constant(value: Number) extends TermSymbol {}

  object Tree {
    @nowarn("msg=match may not be exhaustive")
    def binaryTree(t: Term): Tree = {
      t match {
        case Plus(t1, t2) => Tree(Operator("+", Some(2)), List(binaryTree(t1), binaryTree(t2)))
        case Times(t1, t2) => Tree(Operator("*", Some(2)), List(binaryTree(t1), binaryTree(t2)))
        case Divide(t1, t2) => Tree(Operator("/", Some(2)), List(binaryTree(t1), binaryTree(t2)))
        case Power(t1, t2) => Tree(Operator("^", Some(2)), List(binaryTree(t1), binaryTree(t2)))
        case Minus(t1, t2) => Tree(Operator("-", Some(2)), List(binaryTree(t1), binaryTree(t2)))
        case Neg(t1) => Tree(Operator("-", Some(2)), List(Tree(Constant(Number(0)), List()), binaryTree(t1)))
        case Differential(t1) => Tree(Operator("'", Some(1)), List(binaryTree(t1)))
        // @todo this looses the index
        case BaseVariable(name, _, _) => Tree(Var(name), List())
        // @todo this looses the index
        case DifferentialSymbol(v) => Tree(DiffVar(v.name), List())
        // @todo this looses the index and interpretedness
        case FuncOf(Function(f, _, _, _, _), x) => Tree(Func(f), List(binaryTree(x)))
        case n @ Number(_) => Tree(Constant(n), List())
      }
    }
  }

  final case class Tree(sym: TermSymbol, args: List[Tree]) {
    def this(t: Tree) = { this(t.sym, t.args) }

    def this(t: Term) = { this(Tree.binaryTree(t).simplify) }

    def size: Int = args.foldLeft(1) { case (acc, t) => acc + t.size }

    private def expand(name: String, l: List[Tree]): List[Tree] = l.flatMap({
      case Tree(Operator(name2, _), lst) => if (name.equals(name2)) lst else Nil
      case x => List(x)
    })

    private def fixedPoint(l: List[Tree], f: List[Tree] => List[Tree]): List[Tree] = {
      val l2 = f(l)
      if (l.length == l2.length) l else fixedPoint(l2, f)
    }

    /**
     * Works best if the input is an output of Tree.binaryTree
     * @return
     *   A Tree where as many n-ary operators as possible have been recovered from their binary equivalents
     */
    private def simplify: Tree = this match {
      case Tree(Operator("+", _), lst) =>
        val expanded = fixedPoint(lst, { case l => expand("+", l) })
        Tree(Operator("+", Some(expanded.length)), expanded.map({ case t => t.simplify }))
      case Tree(Operator("*", _), lst) =>
        val expanded = fixedPoint(lst, { case l => expand("*", l) })
        Tree(Operator("*", Some(expanded.length)), expanded.map({ case t => t.simplify }))
      case Tree(Operator("-", Some(n1)), (Tree(Operator("-", Some(n2)), l1)) :: l2) =>
        Tree(Operator("-", Some(n1 + n2 - 1)), l1 ++ l2).simplify
      case Tree(Operator("-", Some(n)), hd :: tl) =>
        val positives = tl.flatMap({
          case Tree(Operator("-", _), hd1 :: _) => List(hd1)
          case _ => Nil
        })
        val allNegative = tl.flatMap({
          case Tree(Operator("-", _), _ :: tl1) => tl1
          case _ => Nil
        })
        val simplePositives = positives.map({ case x => x.simplify })
        val allPositives = Tree(Operator("+", Some(1 + positives.length)), hd :: simplePositives)
        val negative = allNegative.map({ case x => x.simplify })
        Tree(Operator("-", Some(n)), allPositives :: negative)
      case Tree(Operator("/", Some(n1)), (Tree(Operator("/", Some(n2)), l1)) :: l2) =>
        Tree(Operator("/", Some(n1 + n2 - 1)), l1 ++ l2).simplify
      case Tree(Operator("/", Some(n)), hd :: tl) =>
        val mult = hd :: tl.flatMap({
          case Tree(Operator("/", _), hd1 :: _) => List(hd1)
          case _ => Nil
        })
        val div = tl.flatMap({
          case Tree(Operator("/", _), _ :: tl1) => tl1
          case _ => Nil
        })
        Tree(Operator("/", Some(n)), Tree(Operator("*", Some(mult.length)), mult) :: div)
      case Tree(Operator("^", Some(n1)), l) => l.last match {
          case Tree(Operator("^", Some(n2)), l2) =>
            Tree(Operator("^", Some(n1 + n2 - 1)), l.take(l.length - 1) ++ l2).simplify
          case _ => Tree(Operator("^", Some(n1)), l.map({ case t => t.simplify }))
        }
      case Tree(hd, l) => Tree(hd, l.map({ case t => t.simplify }))
    }

    def iterDepth(depth: Int, f: (Int, Tree) => Unit): Unit = {
      f(depth, this)
      this match { case Tree(_, l) => l.foldLeft(())({ case ((), t) => t.iterDepth(depth + 1, f) }) }
    }

    def iterDepth(f: (Int, Tree) => Unit): Unit = iterDepth(0, f)
  }

  object Stat {
    object countOrdering extends Ordering[Stat] {
      def compare(x: Stat, y: Stat): Int = x.count.compare(y.count)
    }
    object depthOrdering extends Ordering[Stat] {
      def compare(x: Stat, y: Stat): Int = x.depthWeighted.compare(y.depthWeighted)
    }
    object sizeOrdering extends Ordering[Stat] {
      def compare(x: Stat, y: Stat): Int = x.sizeWeighted.compare(y.sizeWeighted)
    }
  }

  case class Stat(count: Int, depthWeighted: Int, sizeWeighted: Int) {
    def this(l: List[Tree], depth: Int, size: Int) = this(1, depth, size)
    def add(other: Stat) =
      Stat(count + other.count, depthWeighted + other.depthWeighted, sizeWeighted + other.sizeWeighted)
    def add(l: List[Tree], depth: Int, size: Int): Stat = Stat(1 + count, depth + depthWeighted, size + sizeWeighted)
  }

  /** A Stats accumulates data about a term that can be used to implement a variety of useful orderings. */
  case class Stats(t: Term, depthFactor: Int => Int = { case i => 1 }, sizeFactor: Int => Int = { case i => 1 }) {
    val asTree = new Tree(t)
    // Operators can appear with multiple arities. As a result, we may want to query both the stats for a particular
    // arity and the aggregate stats for an operator across all arities. We provide this ability by storing the aggregate
    // stats for an operator "op" under Operator("op", None) and the individual stats for each arity i under
    // Operator("op", Some(i))
    val counts = new mutable.HashMap[TermSymbol, Stat]()
    asTree.iterDepth((depth, tree) => {
      val Tree(sym, l) = tree
      counts.find({ case (sym2, _) => sym.equals(sym2) }) match {
        case None => counts.put(sym, new Stat(l, depthFactor(depth), sizeFactor(Tree(sym, l).size)))
        case Some((_, stat)) => counts.put(sym, stat.add(l, depthFactor(depth), sizeFactor(Tree(sym, l).size)))
      }
      sym match {
        case Operator(name, Some(_)) => counts.find({
            case (Operator(name2, None), _) => name == name2
            case _ => false
          }) match {
            case Some((_, stat)) =>
              counts.put(Operator(name, None), stat.add(l, depthFactor(depth), sizeFactor(Tree(sym, l).size)))
            case None =>
              counts.put(Operator(name, None), new Stat(l, depthFactor(depth), sizeFactor(Tree(sym, l).size)))
          }
        case _ => ()
      }
    })

    def combine: Stat = counts.foldLeft(Stat(0, 0, 0))({ case (acc, (_key, stat)) => acc.add(stat) })
  }

  class StatOrdering(ord: Ordering[Stats]) extends Ordering[Term] {
    def compare(x: Term, y: Term): Int = ord.compare(Stats(x), Stats(y))
  }

  def weightOrdering(f: Stats => Int): Ordering[Term] = {
    new StatOrdering(new Ordering[Stats] {
      def compare(x: Stats, y: Stats) = f(x).compare(f(y))
    })
  }

  private def id(i: Int): Int = i

  /**
   * Knuth-Bendix orderings assign a constant weight to each symbol and then weigh the terms based on the sum of all the
   * symbols within and compare by the weight. Weights for operators without an arity specified apply to all arities for
   * that operator.
   * @see
   *   Knuth, D. E., Bendix, P. B.Simple word problems in universal algebras.
   */
  class KnuthBendixOrdering(weighting: List[(TermSymbol, Int)]) extends Ordering[Term] {
    def compare(x: Term, y: Term): Int = { new GenericKBOrdering(weighting, id, id, Stat.countOrdering).compare(x, y) }
  }

  /**
   * Variant of Knuth-Bendix ordering where the weight of every occurrence of a symbol is multiplied by its depth in the
   * formula, which has the affect of penalizing values at the leaves of a term.
   */
  class DepthKBOrdering(weighting: List[(TermSymbol, Int)]) extends Ordering[Term] {
    def compare(x: Term, y: Term): Int = { new GenericKBOrdering(weighting, id, id, Stat.depthOrdering).compare(x, y) }
  }

  /**
   * Variant of Knuth-Bendix ordering where the weight of every occurrence of a symbol is multiplied by the size of the
   * subterm starting at that symbol. This has the effect of penalizing large terms over small terms with the same root
   * symbol.
   */
  class SizeKBOrdering(weighting: List[(TermSymbol, Int)]) extends Ordering[Term] {
    def compare(x: Term, y: Term): Int = { new GenericKBOrdering(weighting, id, id, Stat.sizeOrdering).compare(x, y) }
  }

  /**
   * Generalization of Knuth-Bendix ordering that allows arbitrary comparisons on the Stat's computed for the terms and
   * tweaking the depth/size by replacing each depth with depthFactor(depth) and each size with sizeFactor(size)
   */
  class GenericKBOrdering(
      weighting: List[(TermSymbol, Int)],
      depthFactor: Int => Int,
      sizeFactor: Int => Int,
      cmpStat: Ordering[Stat],
  ) extends Ordering[Term] {
    def compare(x: Term, y: Term): Int = {
      val (xStats, yStats) = (new Stats(x, depthFactor, sizeFactor), new Stats(y, depthFactor, sizeFactor))
      cmpStat.compare(xStats.combine, yStats.combine)
    }
  }

  // @todo This would probably be faster with a map instead of a set
  type Multiset[A] = Set[(A, Int)]

  def multiset[A](l: List[A]): Multiset[A] = {
    l.foldLeft(Set.empty[(A, Int)])({ case (ms, t) =>
      ms.find({ case (t2, n) => t2 == t }) match {
        case None => ms.+((t, 1))
        case Some(old @ (t2, n)) => ms.-(old).+((t2, n + 1))
      }
    })
  }

  def subtract[A](x: Multiset[A], y: Multiset[A]): Multiset[A] = {
    x.flatMap({ case (t1, n1) =>
      y.find({ case (t2, n2) => t1 == t2 }) match {
        case None => Set.empty
        case Some((t2, n2)) => if (n1 > n2) Set.empty.+((t1, n1 - n2)) else Set.empty
      }
    })
  }

  def toSet[A](x: Multiset[A]): Set[A] = { x.map({ case (t, n) => t }) }

  /**
   * Recursive path orderings are one general way to extend orderings on logical symbols to orderings on terms. They
   * obey some of the intuition one might want from a term ordering. For example, if the most complex symbol in t1 is
   * more complex than the most complex symbol of t2, then t1 > t2.
   * @see
   *   Nachum Dershowitz. Orderings for Term-Rewriting Systems. Theoretical Computer Science, 1982.
   */
  class RecursivePathOrdering(ord: Ordering[TermSymbol]) extends Ordering[Term] {
    object TreeOrdering extends Ordering[Tree] {
      def compare(x: Tree, y: Tree): Int = (x, y) match {
        case (Tree(f, s), Tree(g, t)) =>
          val cmp = ord.compare(f, g)
          if (cmp == 0) {
            // @note This relies on the fact that the Ordering type represents total orderings, and that an RPO is
            // a total ordering when ord is a total Ordering. This definition only agrees with Dershowitz's definition
            // if the RPO is a total ordering (we use this definition instead of his because it is faster to compute).
            val (s1, s2) = (multiset(s), multiset(t))
            val (m, n) = (toSet(subtract(s1, s2)), toSet(subtract(s2, s1)))
            compare(m.max(TreeOrdering), n.max(TreeOrdering))
          } else if (cmp > 0) { if (t.forall({ case ti => compare(x, ti) > 0 })) 1 else -1 }
          else { if (s.forall({ case si => compare(y, si) > 0 })) -1 else 1 }
      }
    }

    def compare(x: Term, y: Term): Int = TreeOrdering.compare(new Tree(x), new Tree(y))
  }

  /**
   * Given a list of symbols, and two terms x and y, a LexicographicSymbolOrdering counts the number of occurrences of
   * each symbol in x and y, and considers x > y if x has more occurrences of the first symbol for which they differ.
   */
  class LexicographicSymbolOrdering(ord: List[TermSymbol]) extends Ordering[Term] {
    object Ordering extends Ordering[Stats] {
      def getCount(stat: Stats, sym: TermSymbol): Int = {
        stat.counts.get(sym) match {
          case None => 0
          case Some(Stat(n, _, _)) => n
        }
      }

      def compare(x: Stats, y: Stats): Int = {
        ord.foldLeft(0) { case (cmp, sym) => if (cmp != 0) cmp else getCount(x, sym).compare(getCount(y, sym)) }
      }
    }

    def compare(x: Term, y: Term): Int = new StatOrdering(Ordering).compare(x, y)
  }

  /**
   * General lexicographic ordering: given a list of orderings, tries each ordering in turn until some ordering declares
   * the terms to be unequal. For performance reasons, it may be preferable to reimplement this logic for each
   * lexicographic ordering of interest, but this class is useful for quickly writing experiments.
   */
  class LexicographicOrdering(ord: List[Ordering[Term]]) extends Ordering[Term] {
    def compare(x: Term, y: Term): Int = {
      ord.foldLeft(0)({ case (acc, cmp) => if (acc != 0) acc else cmp.compare(x, y) })
    }
  }
}
