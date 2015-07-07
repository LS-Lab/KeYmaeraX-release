package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.core.Formula
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXLexer.TokenStream

/**
 * Created by smitsch on 7/03/15.
 * @author Stefan Mitsch
 */
object KeYmaeraXLemmaParser extends (String => (String, Formula, (String, String))) {
  private type Lemma = (String, Formula, (String, String))

  /**
   * @todo sort hcecking.
   * @param s The contents of the lemma file.
   * @return A list of named lemmas, each with tool evidence (tool input/output) occurring in the file.
   */
  def apply(s: String) : Lemma = {
    val tokens = KeYmaeraXLexer.inMode(s, LemmaFileMode())
    println("Tokens are: " + tokens)
    val (decls, lemmaTokens) = KeYmaeraXDeclarationsParser(tokens)
    println(decls)
    parseLemma(lemmaTokens)
  }


  /**
   * Very simple -- just read until LEMMA_END.
   * @param input Token string for the lemma file.
   * @return A lemma (name, associated formula and evidence).
   */
  def parseLemma(input: TokenStream): Lemma = {
    require(input.endsWith(List(Token(EOF))), "token streams have to end in " + EOF)
    require(input.head.tok.equals(LEMMA_BEGIN), "expected ALP file to begin with Lemma block but found " + input.head)
    val (nextLemma, nextFormula, nextEvidence, remainder) = parseNextLemma(input)
    if(remainder.length == 1 && remainder.head.tok.equals(EOF))
      (nextLemma, nextFormula, nextEvidence)
    else
      throw new IllegalArgumentException("Expected only one lemma")
  }

  def parseNextLemma(input: TokenStream): (String, Formula, (String, String), TokenStream) = {
    require(input.head.tok.equals(LEMMA_BEGIN), "expected ALP file to begin with Lemma block.")
    require(input.tail.head.tok.isInstanceOf[LEMMA_AXIOM_NAME], "expected ALP block to have a string as a name")

    val name = input.tail.head match {
      case Token(LEMMA_AXIOM_NAME(x),_) => x
      case _ => throw new AssertionError("Require should have failed.")
    }
    //Find the End. token and exclude it.
    val (lemmaTokens, remainderTokens) =
      input.tail.tail.span(x => !x.tok.equals(END_BLOCK)) //1st element is LEMMA_BEGIN, 2nd is LEMMA_NAME.

    val lemma = KeYmaeraXParser.formulaTokenParser(lemmaTokens :+ Token(EOF, UnknownLocation))

    val (toolInput, toolOutput, remainder) = parseEvidence(remainderTokens.tail)

    (name, lemma, (toolInput, toolOutput), remainder)
  }

  /**
   * Very simple -- just read until TOOL_END.
   * @param input Token string for the lemma file.
   * @return A list of evidence (tool input/output).
   */
  def parseEvidence(input: TokenStream): (String, String, TokenStream) = {
    require(input.endsWith(List(Token(EOF))), "token streams have to end in " + EOF)
    require(input.head.tok.equals(TOOL_BEGIN), "expected Tool block but found " + input.head)
    val (nextInput, nextOutput, remainder) = parseNextEvidence(input)
    if(remainder.length == 1 && remainder.head.tok.equals(EOF))
      (nextInput, nextOutput, remainder)
    else
      throw new IllegalArgumentException("Expected only one tool evidence")
  }

  def parseNextEvidence(input: TokenStream): (String, String, TokenStream) = {
    require(input.head.tok.equals(TOOL_BEGIN), "expected to begin with Tool block.")

    //Find the End. token and exclude it.
    val (toolTokens, remainderTokens) =
      input.tail.tail.span(x => !x.tok.equals(END_BLOCK)) //1st element is TOOL_BEGIN, 2nd is "input".

    val (toolInput, toolOutput) = parseToolInputOutput(toolTokens)

    (toolInput, toolOutput, remainderTokens.tail)
  }

  def parseToolInputOutput(input: TokenStream): (String, String) = {
    require(input.head.tok.equals(TOOL_INPUT), "expected to begin with input.")
    require(input.tail.head.tok match { case TOOL_IO(_) => true case _ => false }, "expected actual input.")
    require(input.tail.tail.head.tok.equals(TOOL_OUTPUT), "expected to follow with output.")
    require(input.tail.tail.tail.head.tok match { case TOOL_IO(_) => true case _ => false }, "expected actual output.")

    val toolInput = input.tail.head match {
      case Token(TOOL_IO(x),_) => x
      case _ => throw new AssertionError("Require should have failed.")
    }

    val toolOutput = input.tail.tail.tail.head match {
      case Token(TOOL_IO(x),_) => x
      case _ => throw new AssertionError("Require should have failed.")
    }

    (toolInput, toolOutput)
  }

}
