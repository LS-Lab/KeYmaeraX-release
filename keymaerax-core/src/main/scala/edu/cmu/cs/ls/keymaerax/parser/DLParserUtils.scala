package edu.cmu.cs.ls.keymaerax.parser

import fastparse.{Fail, Index, P, ParsingRun, Pass}

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

  /** Runs p, and returns the return value from p in addition to the parsed input substring */
  def captureWithValue[A](p: => P[A])(implicit whitespace: P[_] => P[Unit], ctx: P[Any]): P[(A, String)] = {

    val start = ctx.index
    p match { case lhs =>
      if (!lhs.isSuccess) lhs.asInstanceOf[ParsingRun[(A,String)]]
      else {
        val end = ctx.index
        val this2 = lhs.asInstanceOf[ParsingRun[(A,String)]]
        this2.successValue = (lhs.successValue, ctx.input.slice(start, end))
        this2
      }
    }
  }

  /** Like .filter, but accepting a more descriptive failure message */
  def filterWithMsg[A](p: => P[A])(f: A => Boolean)(errMsg: => String)
                      (implicit whitespace: P[_] => P[Unit], ctx: P[Any]): P[A] = {
    val startIndex = ctx.index

    val res = p

    val res2 =
      if (!res.isSuccess) ctx
      else if (f(ctx.successValue.asInstanceOf[A])) ctx
      else {
        if (ctx.verboseFailures) ctx.setMsg(startIndex, () => errMsg)
        ctx.freshFailure(startIndex)
      }

    res2.asInstanceOf[P[A]]
  }
}
