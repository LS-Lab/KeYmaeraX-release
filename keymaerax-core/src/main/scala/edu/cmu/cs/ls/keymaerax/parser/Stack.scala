package edu.cmu.cs.ls.keymaerax.parser

import scala.annotation.tailrec


/**
 * Stack with top on the right.
 * For example the stack Bottom :+ a3 :+ a2 +: a1 has element a1 on the top, then a2 as the top of the tail.
 * @author nfulton
 * @author aplatzer
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

  override def toString: String = fold("")((s, e) => s + " :+ " + e)
}

case class :+[B](tail: Stack[B], top: B) extends Stack[B] {
  def isEmpty = false
  def drop(n: Int) = {require(n>=0); if (n==0) this else tail.drop(n-1)}
}

object Bottom extends Stack[Nothing] {
  def top = throw new UnsupportedOperationException("Empty stack has no top")
  def tail = throw new UnsupportedOperationException("Empty stack has no tail")
  def isEmpty = true
  def drop(n: Int) = this
}


