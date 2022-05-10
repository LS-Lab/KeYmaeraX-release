package edu.cmu.cs.ls.keymaerax.parser

import fastparse.{P, Pass}

object DLParserUtils {
  def repFold[A](init: A)(parser: A => P[A])
                         (implicit whitespace: P[_] => P[Unit], ctx: P[Any]): P[A] =
    (parser(init) ~ Pass).flatMap(acc => repFold(acc)(parser)) |
      Pass(init)

}
