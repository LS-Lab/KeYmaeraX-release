/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.parser

import scala.annotation.tailrec

/**
 * Stack with top on the right. For example the stack `Bottom :+ a3 :+ a2 +: a1` has element a1 on the top, then a2 as
 * the top of the tail.
 * @author
 *   nfulton
 * @author
 *   Andre Platzer
 */
sealed trait Stack[+A] {

  /** Top element of this stack or error if empty. */
  def top: A

  /** Tail of this stack, i.e. all but top element, or error if empty. */
  def tail: Stack[A]

  /** S:+b result of pushing b on top of the stack S. */
  def :+[B >: A](push: B): Stack[B] = new :+(this, push)

  /** S++T result of pushing the whole stack T as is on top of the stack S. */
  def ++[B >: A](pushStack: Stack[B]): Stack[B] = pushStack match {
    case Bottom => this
    case tail :+ top => new :+(this ++ tail, top)
  }

  /** Select all elements except the top n elements of this stack, or empty if there are not that many. */
  def drop(n: Int): Stack[A]

  /** Select only the top n elements of this stack, or less if there are not that many. */
  def take(n: Int): Stack[A]

  /** Whether this stack is empty */
  def isEmpty: Boolean

  /** Number of elements on this stack */
  def length: Int = this match {
    case Bottom => 0
    case tail :+ top => 1 + tail.length
  }

  /** Fold the elements of this stack by f starting with z at the Bottom. */
  def fold[B](z: B)(f: (B, A) => B): B = this match {
    case Bottom => z
    case tail :+ top => f(tail.fold(z)(f), top)
  }

  /** Find the top-most element satisfying p, if any */
  def find(p: (A) => Boolean): Option[A] = if (isEmpty) None else if (p(top)) Some(top) else tail.find(p)

  override def toString: String = fold("")((s, e) => s + " :+ " + e)

  /** Convert stack A,B,C where top = A to the list A :: B :: C :: Nil */
  def toList: List[A] = fold[List[A]](Nil)((list, next) => next +: list)

  /**
   * Splits the stack at first occurrence of an element next s.t. p(next) = true; p is placed in the later stack.
   * @example
   *   (A B C D E).split(C) = ( (A,B), (C, D, E) )
   */
  def split[B >: A](p: B => Boolean) = fold[(Stack[B], Stack[B])]((Bottom, Bottom))((stacks, next) => {
    if (!stacks._2.isEmpty || p(next))
      (
        stacks._1,
        stacks._2 :+ next,
      ) // if the first item satisfying p has already been found then continue on with the second stack.
    else (stacks._1 :+ next, stacks._2) // Otherwise continue with the first stack.
  })
}

/** A stack tail :+ top with top on the top of tail */
case class :+[A](tail: Stack[A], top: A) extends Stack[A] {
  def isEmpty = false
  def drop(n: Int) = { require(n >= 0); if (n == 0) this else tail.drop(n - 1) }
  def take(n: Int) = { require(n >= 0); if (n == 0) Bottom else tail.take(n - 1) :+ top }
  // def find(p: (A) => Boolean): Option[A] = if (p(top)) Some(top) else tail.find(p)
}

/** The empty stack bottom */
object Bottom extends Stack[Nothing] {
  def top = throw new UnsupportedOperationException("Empty stack has no top")
  def tail = throw new UnsupportedOperationException("Empty stack has no tail")
  def isEmpty = true
  def drop(n: Int) = { require(n >= 0); this }
  def take(n: Int) = { require(n >= 0); this }
  // def find[A>:Nothing](p: (A) => Boolean): Option[A] = None
}
