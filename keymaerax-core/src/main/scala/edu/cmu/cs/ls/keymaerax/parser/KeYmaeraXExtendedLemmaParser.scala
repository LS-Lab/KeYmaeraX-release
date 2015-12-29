/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.core.{Sequent, Evidence}
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXLexer.TokenStream
import edu.cmu.cs.ls.keymaerax.tools.ToolEvidence

/**
  * Created by smitsch on 7/03/15.
  * Modified by nfulton on 12/16/15 -- Lemmas are now more general.
  * @author Stefan Mitsch
  * @author Nathan Fulton
  */
object KeYmaeraXExtendedLemmaParser extends (String => (Option[String], List[Sequent], Evidence)) {
  /** the lemma name, the lemma conclusion, and the supporting evidence */
  private type Lemma = (Option[String], List[Sequent], Evidence)

  private val DEBUG = System.getProperty("DEBUG", "false")=="true"

  /**
    * @todo sort hcecking.
    * @param input The contents of the lemma file.
    * @return A list of named lemmas, each with tool evidence (tool input/output) occurring in the file.
    */
  def apply(input: String) : Lemma = try {
    val tokens = KeYmaeraXLexer.inMode(input, LemmaFileMode())
    if (DEBUG) println("Tokens are: " + tokens)
    val (decls, lemmaTokens) = KeYmaeraXDeclarationsParser(tokens)
    if (DEBUG) println("Declarations: " + decls)
    parseLemma(lemmaTokens)
  } catch {
    case e: ParseException => throw e.inContext("input:  " + input)
    case e: IllegalArgumentException => throw new ParseException(e.toString, UnknownLocation, "\ninput:  " + input, e)
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

  def parseNextLemma(input: TokenStream): (Option[String], List[Sequent], Evidence, TokenStream) = {
    require(input.head.tok.equals(LEMMA_BEGIN), "expected ALP file to begin with Lemma block.")
    require(input.tail.head.tok.isInstanceOf[LEMMA_AXIOM_NAME], "expected ALP block to have a string as a name")

    val name = input.tail.head match {
      case Token(LEMMA_AXIOM_NAME(x),_) if x != "" => Some(x)
      case Token(LEMMA_AXIOM_NAME(x),_) if x == "" => None
      case _ => throw new AssertionError("Require should have failed.")
    }

    //Find the End. token and exclude it.
    val (lemmaTokens, remainderTokens) =
      input.tail.tail.span(x => !x.tok.equals(END_BLOCK)) //1st element is LEMMA_BEGIN, 2nd is LEMMA_NAME.

    //Separate the lemma into subgoals.
    val sequentTokens = splitAtTerminal(SEQUENT_BEGIN, lemmaTokens)
    val sequents = sequentTokens.map(sequentTokenParser)
    assert(sequents.nonEmpty, "Lemma should at least have a conclusion.")

    val (evidence, remainder) = parseEvidence(remainderTokens.tail)

    (name, sequents, evidence, remainder)
  }

  private def splitAtTerminal(splitTerminal: Terminal, tokens: TokenStream): List[TokenStream] =
    splitAt[Token]((t: Token) => !t.tok.equals(splitTerminal), tokens).filter(_.nonEmpty)

  /** Splits a list at each point where p is true and throws out the fence posts. */
  private def splitAt[T](p: T => Boolean, ts: List[T], pre: List[List[T]] = List()) : List[List[T]] = {
    val (l, r) = ts.span(p)
    if(r.nonEmpty) splitAt(p, r.tail, pre :+ l)
    else pre :+ l
  }

  private def sequentTokenParser(ts: TokenStream): Sequent = {
    require(ts.map(_.tok).contains(TURNSTILE))

    val (anteToks, succToksWithTurnstile) = ts.span(!_.tok.equals(TURNSTILE))
    val succToks = succToksWithTurnstile.tail

    val anteParts = splitAtTerminal(FORMULA_BEGIN, anteToks)
    val antes = anteParts.map(x => KeYmaeraXParser.formulaTokenParser(x :+ Token(EOF)))

    val succParts = splitAtTerminal(FORMULA_BEGIN, succToks)
    val succs = succParts.map(x => KeYmaeraXParser.formulaTokenParser(x :+ Token(EOF)))

    new Sequent(Nil, antes.toIndexedSeq, succs.toIndexedSeq)
  }

  /**
    * Very simple -- just read until TOOL_END.
    * @param input Token string for the lemma file.
    * @return A list of evidence (tool input/output).
    */
  def parseEvidence(input: TokenStream): (Evidence, TokenStream) = {
    require(input.endsWith(List(Token(EOF))), "token streams have to end in " + EOF)
    require(input.head.tok.equals(TOOL_BEGIN), "expected Tool block but found " + input.head)
    val (evidence, remainder) = parseNextEvidence(input)
    if(remainder.length == 1 && remainder.head.tok.equals(EOF))
      (evidence, remainder)
    else
      throw new IllegalArgumentException("Expected only one tool evidence")
  }

  def parseNextEvidence(input: TokenStream): (Evidence, TokenStream) = {
    require(input.head.tok.equals(TOOL_BEGIN), "expected to begin with Tool block.")

    //Find the End. token and exclude it.
    val (toolTokens, remainderTokens) =
      input.tail.tail.span(x => !x.tok.equals(END_BLOCK)) //1st element is TOOL_BEGIN, 2nd is a tool evidence key.

    val evidence = parseToolEvidenceLines(toolTokens)

    (ToolEvidence(evidence), remainderTokens.tail)
  }

  def parseToolEvidenceLines(input: TokenStream): Map[String, String] = {
    require(input.head.tok match { case IDENT(_, _) => true case _ => false }, "expected to begin with key.")
    require(input.tail.head.tok match { case TOOL_VALUE(_) => true case _ => false }, "expected actual value.")

    var evidence = Map[String, String]()
    var line = input

    while (line.nonEmpty &&
      (line.head.tok match { case IDENT(_, _) => true case _ => false }) &&
      (line.tail.head.tok match { case TOOL_VALUE(_) => true case _ => false })) {
      val key = line.head match {
        case Token(IDENT(x, None),_) => x
        case Token(IDENT(x, Some(i)),_) => x + "_" + i
        case _ => throw new AssertionError("Require should have failed.")
      }

      val value = line.tail.head match {
        case Token(TOOL_VALUE(x),_) => x
        case _ => throw new AssertionError("Require should have failed.")
      }

      evidence = evidence + (key -> value)
      line = line.tail.tail
    }

    evidence
  }

}
