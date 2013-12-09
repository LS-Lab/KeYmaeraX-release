package edu.cmu.cs.ls.keymaera.parser

import scala.util.parsing.combinator._
import scala.util.parsing.combinator.lexical._
import scala.util.parsing.combinator.syntactical._

class KeYmaeraParser extends StdTokenParsers {
  type Tokens = StdLexical
  val lexical = new StdLexical
  lexical.delimiters ++= List("\\functions", "{", "}", "(", ")", "+", "-", "*", "/")

  def infile = functions

  def functions = "\\functions" ~ "{" ~> repsep(funcdef, ";") <~ "}"

  def funcdef = ident ~ ident ~ "(" ~ repsep(ident, ",") ~ ")" ^^ {
    case rsort ~ name ~ _ ~ argsorts ~ _ => (rsort, name, argsorts)
  }

  def parse(in: String) = {
    val l = new lexical.Scanner(in)
    infile(l)
  }

}

// vim: set ts=4 sw=4 et:
