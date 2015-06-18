package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.core.Formula
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXLexer.TokenStream

/**
 * Created by nfulton on 6/11/15.
 */
object KeYmaeraXAxiomParser extends (String => List[(String, Formula)]) {
  /**
   * @todo sort hcecking.
   * @param s The contents of the axiom file.
   * @return A list of named axioms occurring in the file.
   */
  def apply(s: String) : List[(String, Formula)] = {
    val tokens = KeYmaeraXLexer.inMode(s, AxiomFileMode())
    println("Tokens are: " + tokens)
    val (decls, axiomTokens) = KeYmaeraXDeclarationsParser(tokens)
    println(decls)
    parseAxioms(axiomTokens)
  }


  /**
   * Very simple -- just read until AXIOM_END.
   * @param input Token string for the axiom file.
   * @return A list of axiom names and the associated formulas.
   */
  def parseAxioms(input: TokenStream): List[(String, Formula)] = {
    require(input.endsWith(List(Token(EOF))), "token streams have to end in " + EOF)
    require(input.head.tok.equals(AXIOM_BEGIN), "expected ALP file to begin with Axion block but found " + input.head)
    val (nextAxiom, nextFormula, remainder) = parseNextAxiom(input)
    if(remainder.length == 1 && remainder.head.tok.equals(EOF))
      List((nextAxiom, nextFormula))
    else
      (nextAxiom, nextFormula) +: parseAxioms(remainder)
  }

  def parseNextAxiom(input: TokenStream): (String, Formula, TokenStream) = {
    require(input.head.tok.equals(AXIOM_BEGIN), "expected ALP file to begin with Axion block.")
    require(input.tail.head.tok.isInstanceOf[AXIOM_NAME])

    val name = input.tail.head match {
      case Token(AXIOM_NAME(x),_) => x
      case _ => throw new Exception("Require should have failed.")
    }
    //Find the End. token and exclude it.
    val (axiomTokens, remainderTokens) =
      input.tail.tail.span(x => !x.tok.equals(END_BLOCK)) //1st element is AXIOM_BEGIN, 2nd is AXIOM_NAME.

    val axiom = KeYmaeraXParser.parse(axiomTokens :+ Token(EOF, UnknownLocation)) match {
      case axiomAsFormula : Formula => axiomAsFormula
      case _ => throw new Exception("Parsed a non-formula in an Axiom context.")
    }

    (name, axiom, remainderTokens.tail)
  }

}
