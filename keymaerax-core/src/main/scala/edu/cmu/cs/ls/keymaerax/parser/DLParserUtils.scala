package edu.cmu.cs.ls.keymaerax.parser

import fastparse.{P, Pass}

import scala.annotation.tailrec

object DLParserUtils {
  /** Like the .rep parser combinator, but with an accumulator term */
  def repFold[A](init: A)(parser: A => P[A])
                         (implicit whitespace: P[_] => P[Unit], ctx: P[Any]): P[A] =
    (parser(init) ~ Pass).flatMap(acc => repFold(acc)(parser)) |
      Pass(init)

  /** For each a in as (in order), runs f a and accumulates the result */
  def mapJoin[A, B](as: Seq[A])(f: A => P[B])(sep: => P[Unit])
                     (implicit whitespace: P[_] => P[Unit], ctx: P[Any]): P[Seq[B]] =
    as.toList match {
      case Nil => Pass(Nil)
      case hd::tl => f(hd).flatMap(hd => mapJoinIter(tl)(f)(sep)(Seq(hd)))
    }

  private def mapJoinIter[A,B](as: List[A])(f: A => P[B])(sep: => P[Unit])(acc: Seq[B])
                              (implicit whitespace: P[_] => P[Unit], ctx: P[Any]): P[Seq[B]] =
    as match {
      case Nil => Pass(acc)
      case hd::tl => (sep ~ f(hd)).flatMap(hd => mapJoinIter(tl)(f)(sep)(acc :+ hd))
    }
}
