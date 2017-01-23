/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.core.{Evidence, Sequent}
import edu.cmu.cs.ls.keymaerax.parser
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXLexer.TokenStream
import edu.cmu.cs.ls.keymaerax.tools.{HashEvidence, ToolEvidence}

import scala.collection.immutable

/**
  * Lemma format is as follows:
  * {{{
  *   Sequent.
  *     Formula: <<formula>>
  *     ...
  *     ==>
  *     Formula: <<formula>>
  *     ...
  *   Sequent.
  *     ...
  *   End.
  *   Tool.
  *     <<key>> """"<<value>>""""
  *     ...
  *   End.
  * }}}
  * Created by smitsch on 7/03/15.
  * Modified by nfulton on 12/16/15 -- Lemmas are now more general.
  * @author Stefan Mitsch
  * @author Nathan Fulton
  */
object KeYmaeraXExtendedLemmaParser extends (String => (Option[String], immutable.List[Sequent], immutable.List[Evidence])) {
  /** the lemma name, the lemma conclusion, and the supporting evidence */
  private type Lemma = (Option[String], List[Sequent], List[Evidence])

  private val DEBUG = System.getProperty("DEBUG", "false")=="true"

  /**
    * @todo sort hcecking.
    * @param inputWithPossibleBOM The contents of the lemma file.
    * @return A list of named lemmas, each with tool evidence (tool input/output) occurring in the file.
    */
  def apply(inputWithPossibleBOM: String) : Lemma = try {
    val input = parser.ParserHelper.removeBOM(inputWithPossibleBOM)

    val tokens = KeYmaeraXLexer.inMode(input, LemmaFileMode)
    if (DEBUG) println("Tokens are: " + tokens)
    val (decls, lemmaTokens) = KeYmaeraXDeclarationsParser(tokens)
    if (DEBUG) println("Declarations: " + decls)
    parseLemma(lemmaTokens)
  } catch {
    case e: ParseException => throw e.inContext("input:  " + inputWithPossibleBOM)
    case e: IllegalArgumentException => throw ParseException("Illegal argument", e).inInput(inputWithPossibleBOM)
  }


  /**
    * Very simple -- just read until LEMMA_END.
    * @param input Token string for the lemma file.
    * @return A lemma (name, associated formula and evidence).
    */
  def parseLemma(input: TokenStream): Lemma = {
    require(input.last.tok == EOF, "token streams have to end in " + EOF)
    require(input.head.tok.equals(LEMMA_BEGIN), "expected ALP file to begin with Lemma block but found " + input.head)
    val (nextLemma, nextFormula, nextEvidence, remainder) = parseNextLemma(input)
    if(remainder.length == 1 && remainder.head.tok.equals(EOF))
      (nextLemma, nextFormula, nextEvidence)
    else
      throw new IllegalArgumentException("Expected only one lemma")
  }

  def parseNextLemma(input: TokenStream): (Option[String], List[Sequent], List[Evidence], TokenStream) = {
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

    val (allEvidence, remainder) = parseAllEvidence(remainderTokens.tail)

    (name, sequents, allEvidence, remainder)
  }

  private def splitAtTerminal(splitTerminal: Terminal, tokens: TokenStream): List[TokenStream] =
    splitAt[Token]((t: Token) => !t.tok.equals(splitTerminal), tokens).filter(_.nonEmpty)

  /** Splits a list at each point where p is true and throws out the fence posts. */
  private def splitAt[T](p: T => Boolean, ts: List[T], pre: List[List[T]] = List()) : List[List[T]] = {
    val (l, r) = ts.span(p)
    if(r.nonEmpty) splitAt(p, r.tail, pre :+ l)
    else pre :+ l
  }

  //@todo performance bottleneck
  private def sequentTokenParser(ts: TokenStream): Sequent = {
    require(ts.map(_.tok).contains(TURNSTILE))

    val (anteToks, succToksWithTurnstile) = ts.span(!_.tok.equals(TURNSTILE))
    val succToks = succToksWithTurnstile.tail

    val anteParts = splitAtTerminal(FORMULA_BEGIN, anteToks)
    val antes = anteParts.map(x => KeYmaeraXParser.formulaTokenParser(x :+ Token(EOF)))

    val succParts = splitAtTerminal(FORMULA_BEGIN, succToks)
    val succs = succParts.map(x => KeYmaeraXParser.formulaTokenParser(x :+ Token(EOF)))

    new Sequent(antes.toIndexedSeq, succs.toIndexedSeq)
  }

  /**
    * Very simple -- just read until TOOL_END.
    * @param input Token string for the lemma file.
    * @return A list of evidence (tool input/output).
    */
  def parseAllEvidence(input: TokenStream, prevEvidence: List[Evidence] = Nil): (List[Evidence], TokenStream) = {
    require(input.last.tok == EOF, "token streams have to end in " + EOF)
    val (evidence, remainder) = parseNextEvidence(input)
    (evidence, remainder)
    if(remainder.length == 1 && remainder.head.tok.equals(EOF))
      (prevEvidence :+ evidence, remainder)
    else
      parseAllEvidence(remainder, prevEvidence :+ evidence)
  }

  def parseNextEvidence(input: TokenStream): (Evidence, TokenStream) = {
    val beginEvidenceTokens = Set(TOOL_BEGIN, HASH_BEGIN)
    require(beginEvidenceTokens.contains(input.head.tok), s"expected to find a begin evidence block but found ${input.head.tok}")

    //Find the End. token and exclude it.
    val (toolTokens, remainderTokens) =
      input.tail.tail.span(x => !x.tok.equals(END_BLOCK)) //1st element is TOOL_BEGIN, 2nd is a tool evidence key.

    val evidenceLines = parseEvidenceLines(toolTokens)

    val evidence = input.head.tok match {
      case TOOL_BEGIN => ToolEvidence(evidenceLines)
      case HASH_BEGIN => {
        assert(evidenceLines.head._1 == "hash")
        HashEvidence(evidenceLines.head._2)
      }
    }

    (evidence, remainderTokens.tail)
  }

  def parseEvidenceLines(input: TokenStream): immutable.List[(String, String)] = {
    require(input.head.tok match { case IDENT(_, _) => true case _ => false }, "expected to begin with key.")
    require(input.tail.head.tok match { case TOOL_VALUE(_) => true case _ => false }, "expected actual value.")

    var evidence = immutable.List[(String, String)]()
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

      evidence = evidence :+ (key -> value)
      line = line.tail.tail
    }

    evidence
  }

}
