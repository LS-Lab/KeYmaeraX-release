/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

/**
 * Differential Dynamic Logic lexer for concrete KeYmaera X notation.
  *
  * @author Andre Platzer
 * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981, 2015."
 */
package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.Logging

import scala.annotation.tailrec
import scala.collection.immutable._
import scala.util.matching.Regex

/**
 * LexerModes corresponds to file types.
 */
sealed abstract class LexerMode
object ExpressionMode extends LexerMode
object AxiomFileMode extends LexerMode
object ProblemFileMode extends LexerMode
object LemmaFileMode extends LexerMode
object StoredProvableMode extends LexerMode

/**
 * Lexer for KeYmaera X turns string into list of tokens.
  *
  * @author Andre Platzer
 * @author nfulton
 */
object KeYmaeraXLexer extends (String => List[Token]) with Logging {
  /** Lexer's token stream with first token at head. */
  type TokenStream = List[Token]

  private val whitespace = """^(\s+)""".r
  private val newline = """(?s)(^\n)""".r //@todo use something more portable.
  private val comment = """(?s)(^/\*[\s\S]*?\*/)""".r

  /** Normalize all new lines in input to a s*/
  def normalizeNewlines(input: String): String = input.replace("\r\n", "\n").replace("\r", "\n").replaceAll(" *\n", "\n")
  /**
   * The lexer has multiple modes for the different sorts of files that are supported by KeYmaeraX.
   * The lexer will disallow non-expression symbols from occuring when the lexer is in expression mode.
   * This also ensures that reserved symbols are never used as function names.
    *
    * @param input The string to lex.
   * @param mode The lexer mode.
   * @return A stream of symbols corresponding to input.
   */
  //@todo performance bottleneck
  def inMode(input: String, mode: LexerMode): KeYmaeraXLexer.TokenStream = {
    val correctedInput = normalizeNewlines(input)
    logger.debug("LEX: " + correctedInput)
    val output = lex(correctedInput, SuffixRegion(1,1), mode)
    require(!output.exists(x => x.tok == ANYTHING), "output should not contain ??")
    require(output.last.tok.equals(EOF), "Expected EOF but found " + output.last.tok)
    output
  }

  def apply(input: String): KeYmaeraXLexer.TokenStream = inMode(input, ExpressionMode)

  /**
   * The lexer.
    *
    * @todo optimize
   * @param input The input to lex.
   * @param inputLocation The position of the input (e.g., wrt a source file).
   * @param mode The mode of the lexer.
   * @return A token stream.
   */
  private def lex(input: String, inputLocation:Location, mode: LexerMode): TokenStream = {
    var remaining: String = input
    var loc: Location = inputLocation
    val output: scala.collection.mutable.ListBuffer[Token] = scala.collection.mutable.ListBuffer.empty
    while (remaining.trim.nonEmpty) {
      findNextToken(remaining, loc, mode) match {
        case Some((nextInput, token, nextLoc)) =>
          output.append(token)
          remaining = nextInput
          loc = nextLoc
        case None =>
          //note: This case can happen if the input is e.g. only a comment or only whitespace.
          remaining = ""
      }
    }
    output.append(Token(EOF, loc))
    replaceAnything(output).toList
  }

  /** Replace all instances of LPAREN,ANYTHING,RPAREN with LBANANA,RBANANA. */
  @tailrec
  private def replaceAnything(output: scala.collection.mutable.ListBuffer[Token]): scala.collection.mutable.ListBuffer[Token] = {
    output.find(x => x.tok == ANYTHING) match {
      case None => output
      case Some(anyTok) =>
        val pos = output.indexOf(anyTok)
        replaceAnything(output.patch(pos-1, Token(LBANANA, anyTok.loc) :: Token(RBANANA, anyTok.loc) :: Nil, 3))
    }
  }

  /**
    *
    * @param cols Number of columns to move cursor.
    * @param terminal terminal to generate a token for.
    * @param location Current location.
    * @return Return value of findNextToken
    */
  private def consumeColumns(s: String, cols: Int, terminal: Terminal, location: Location) : Option[(String, Token, Location)] = {
    assert(cols > 0, "Cannot move cursor less than 1 columns.")
    Some((
      s.substring(cols),
      Token(terminal, spanningRegion(location, cols-1)),
      suffixOf(location, cols)))
  }

  private def consumeTerminalLength(s: String, terminal: Terminal, location: Location): Option[(String, Token, Location)] =
    consumeColumns(s, terminal.img.length, terminal, location)

  private def consumeUnicodeTerminalLength(s: String, terminal: Terminal, location: Location, replacementTerminal: Terminal): Option[(String, Token, Location)] = {
    consumeColumns(s, terminal.img.length, terminal, location).map({ case (st, t, l) => (st, Token(replacementTerminal, t.loc), l) })
  }

  private val lexers: Seq[(Regex, (String, Location, LexerMode, String) => Either[(String, Location, LexerMode),Option[(String, Token, Location)]])] = Seq(
    //update location if we encounter whitespace/comments.
    comment -> ((s: String, loc: Location, mode: LexerMode, theComment: String) => {
      val comment = s.substring(0, theComment.length)
      val lastLineCol = (comment: StringOps).linesIterator.toList.last.length //column of last line.
      val lineCount = (comment: StringOps).linesIterator.length
      Left((s.substring(theComment.length), loc match {
        case UnknownLocation       => UnknownLocation
        case Region(sl, _, el, ec) => Region(sl + lineCount - 1, lastLineCol, el, ec)
        case SuffixRegion(sl, sc)  => SuffixRegion(sl + lineCount - 1, sc + theComment.length)
      }, mode)) }),
    newline -> ((s: String, loc: Location, mode: LexerMode, _) =>
      Left((s.tail, loc match {
        case UnknownLocation       => UnknownLocation
        case Region(sl, _, el, ec) => Region(sl+1,1,el,ec)
        case SuffixRegion(sl, _)   => SuffixRegion(sl+1, 1)
      }, mode))),
    whitespace -> ((s: String, loc: Location, mode: LexerMode, spaces: String) =>
      Left((s.substring(spaces.length), loc match {
        case UnknownLocation        => UnknownLocation
        case Region(sl, sc, el, ec) => Region(sl, sc+spaces.length, el, ec)
        case SuffixRegion(sl, sc)   => SuffixRegion(sl, sc+ spaces.length)
      }, mode))),
    //Lemma file cases
    LEMMA_BEGIN.startPattern -> ((s: String, loc: Location, mode: LexerMode, _) => mode match {
      case LemmaFileMode => Right(consumeTerminalLength(s, LEMMA_BEGIN, loc))
      case ProblemFileMode => Right(consumeColumns(s, LEMMA_BEGIN.img.length, ARCHIVE_ENTRY_BEGIN("Lemma"), loc))
      case _ => throw new Exception("Encountered ``Lemma`` in non-lemma lexing mode.")
    }),
    TOOL_BEGIN.startPattern -> ((s: String, loc: Location, mode: LexerMode, _) => mode match {
      case LemmaFileMode => Right(consumeTerminalLength(s, TOOL_BEGIN, loc))
      case _ => throw new Exception("Encountered ``Tool`` in non-lemma lexing mode.")
    }),
    SEQUENT_BEGIN.startPattern -> ((s: String, loc: Location, mode: LexerMode, _) => mode match {
      case LemmaFileMode => Right(consumeTerminalLength(s, SEQUENT_BEGIN, loc))
      case _ => throw new Exception("Encountered ``Sequent`` in a non-lemma file.")
    }),
    TURNSTILE.startPattern -> ((s: String, loc: Location, mode: LexerMode, _) => mode match {
      case LemmaFileMode | StoredProvableMode => Right(consumeTerminalLength(s, TURNSTILE, loc))
      case _ => throw new Exception("Encountered a turnstile symbol ==> in a non-lemma file or non-storedprovable input")
    }),
    FORMULA_BEGIN.startPattern -> ((s: String, loc: Location, mode: LexerMode, _) => mode match {
      case LemmaFileMode => Right(consumeTerminalLength(s, FORMULA_BEGIN, loc))
      case _ => throw new Exception("Encountered a formula begin symbol (Formula:) in a non-lemma file.")
    }),
    DOT.startPattern -> ((s: String, loc: Location, _: LexerMode, dot: String) => { val (_, idx) = splitName(dot); Right(consumeTerminalLength(s, DOT(idx), loc)) }),
    // File cases
    PERIOD.startPattern -> ((s: String, loc: Location, _: LexerMode, _) => Right(consumeTerminalLength(s, PERIOD, loc))), //swapOutFor(consumeTerminalLength(PERIOD, loc), DOT)
    ARCHIVE_ENTRY_BEGIN.startPattern -> ((s: String, loc: Location, mode: LexerMode, kind: String) => mode match {
      case ProblemFileMode => Right(consumeColumns(s, kind.length, ARCHIVE_ENTRY_BEGIN(kind), loc))
      case LemmaFileMode if kind == "Lemma" => Right(consumeTerminalLength(s, LEMMA_BEGIN, loc))
      case _ => throw new Exception("Encountered ``" + ARCHIVE_ENTRY_BEGIN(kind).img + "`` in non-problem file lexing mode.")
    }),
    FUNCTIONS_BLOCK.startPattern -> ((s: String, loc: Location, mode: LexerMode, _) => mode match {
      case AxiomFileMode | ProblemFileMode | LemmaFileMode => Right(consumeTerminalLength(s, FUNCTIONS_BLOCK, loc))
      case _ => throw new Exception("Functions. should only occur when processing files.")
    }),
    DEFINITIONS_BLOCK.startPattern -> ((s: String, loc: Location, mode: LexerMode, _) => mode match {
      case AxiomFileMode | ProblemFileMode | LemmaFileMode => Right(consumeTerminalLength(s, DEFINITIONS_BLOCK, loc))
      case _ => throw new Exception("Definitions. should only occur when processing files.")
    }),
    PROGRAM_VARIABLES_BLOCK.startPattern -> ((s: String, loc: Location, mode: LexerMode, _) => mode match {
      case AxiomFileMode | ProblemFileMode | LemmaFileMode => Right(consumeTerminalLength(s, PROGRAM_VARIABLES_BLOCK, loc))
      case _ => throw new Exception("ProgramVariables. should only occur when processing files.")
    }),
    VARIABLES_BLOCK.startPattern -> ((s: String, loc: Location, mode: LexerMode, _) => mode match {
      case AxiomFileMode | ProblemFileMode | LemmaFileMode => Right(consumeTerminalLength(s, VARIABLES_BLOCK, loc))
      case _ => throw new Exception("Variables. should only occur when processing files.")
    }),
    IMPLICIT.startPattern -> ((s: String, loc: Location, mode: LexerMode, _) => mode match {
      case AxiomFileMode | ProblemFileMode | LemmaFileMode => Right(consumeTerminalLength(s, IMPLICIT, loc))
      case _ => throw new Exception("IMPLICIT symbol declaration should only occur when processing files.")
    }),
    BOOL.startPattern -> ((s: String, loc: Location, mode: LexerMode, _) => mode match {
      case AxiomFileMode | ProblemFileMode | LemmaFileMode => Right(consumeTerminalLength(s, BOOL, loc))
      case _ => throw new Exception("Bool symbol declaration should only occur when processing files.")
    }),
    REAL.startPattern -> ((s: String, loc: Location, mode: LexerMode, _) => mode match {
      case AxiomFileMode | ProblemFileMode | LemmaFileMode => Right(consumeTerminalLength(s,REAL, loc))
      case _ => throw new Exception("Real symbol declaration should only occur when processing files.")
    }),
    TERM.startPattern -> ((s: String, loc: Location, mode: LexerMode, _) => mode match {
      case AxiomFileMode | ProblemFileMode | LemmaFileMode => Right(consumeTerminalLength(s, TERM, loc))
      case _ => throw new Exception("Term symbol declaration should only occur when processing files.")
    }),
    PROGRAM.startPattern -> ((s: String, loc: Location, mode: LexerMode, _) => mode match {
      case AxiomFileMode | ProblemFileMode | LemmaFileMode => Right(consumeTerminalLength(s, PROGRAM, loc))
      case _ => throw new Exception("Program symbol declaration should only occur when processing files.")
    }),
    CP.startPattern -> ((s: String, loc: Location, mode: LexerMode, _) => mode match {
      case AxiomFileMode | ProblemFileMode | LemmaFileMode => Right(consumeTerminalLength(s, CP, loc))
      case _ => throw new Exception("CP symbol declaration should only occur when processing files.")
    }),
    MFORMULA.startPattern -> ((s: String, loc: Location, mode: LexerMode, _) => mode match {
      case AxiomFileMode | ProblemFileMode | LemmaFileMode => Right(consumeTerminalLength(s, MFORMULA, loc))
      case _ => throw new Exception("MFORMULA symbol declaration should only occur when processing files.")
    }),
    //.kyx file cases
    PROBLEM_BLOCK.startPattern -> ((s: String, loc: Location, mode: LexerMode, _) => mode match {
      case AxiomFileMode | ProblemFileMode => Right(consumeTerminalLength(s, PROBLEM_BLOCK, loc))
      case _ => throw new Exception("Problem./End. sections should only occur when processing .kyx files.")
    }),
    TACTIC_BLOCK.startPattern -> ((s: String, loc: Location, mode: LexerMode, _) => mode match {
      case AxiomFileMode | ProblemFileMode => Right(consumeTerminalLength(s, TACTIC_BLOCK, loc))
      case _ => throw new Exception("Tactic./End. sections should only occur when processing .kyx files.")
    }),
    BACKTICK.startPattern -> ((s: String, loc: Location, mode: LexerMode, _) => mode match {
      case ProblemFileMode => Right(consumeTerminalLength(s, BACKTICK, loc))
      case _ => throw new Exception("Backtick ` should only occur when processing .kyx files.")
    }),
    SHARED_DEFINITIONS_BEGIN.startPattern -> ((s: String, loc: Location, mode: LexerMode, _) => mode match {
      case ProblemFileMode => Right(consumeTerminalLength(s, SHARED_DEFINITIONS_BEGIN, loc))
      case _ => throw new Exception("SharedDefinitions./End. sections should only occur when processing .kyx files.")
    }),
    //Lemma file cases (2)
    TOOL_VALUE_PAT.startPattern -> ((s: String, loc: Location, mode: LexerMode, str: String) => mode match { //@note must be before DOUBLE_QUOTES_STRING
      case LemmaFileMode =>
        // also try stripping spaces around value (are not present up to and including 4.9.3, so may alter old evidence
        // content that had explicit spaces; recover from it in [[ToolEvidence.equals]])
        Right(consumeColumns(s, str.length, TOOL_VALUE(str.stripPrefix("\"\"\"\"").stripSuffix("\"\"\"\"").stripPrefix(" ").stripSuffix(" ")), loc))
      case _ => throw new Exception("Encountered delimited string in non-lemma lexing mode.")
    }),
    //Axiom file cases
    AXIOM_BEGIN.startPattern -> ((s: String, loc: Location, mode: LexerMode, _) => mode match {
      case AxiomFileMode => Right(consumeTerminalLength(s, AXIOM_BEGIN, loc))
      case _ => throw new Exception("Encountered ``Axiom.`` in non-axiom lexing mode.")
    }),
    END_BLOCK.startPattern -> ((s: String, loc: Location, mode: LexerMode, _) => mode match {
      case AxiomFileMode | ProblemFileMode | LemmaFileMode => Right(consumeTerminalLength(s, END_BLOCK, loc))
      case _ => throw new Exception("Encountered ``Axiom.`` in non-axiom lexing mode.")
    }),
    DOUBLE_QUOTES_STRING_PAT.startPattern -> ((s: String, loc: Location, mode: LexerMode, str: String) => mode match {
      case AxiomFileMode | LemmaFileMode | ProblemFileMode =>
        val terminal = DOUBLE_QUOTES_STRING(str.stripPrefix("\"").stripSuffix("\""))
        val n = str.count(_ == '\n')
        val c = if (n>0) str.length - str.lastIndexOf('\n') else loc.begin.column + str.length
        val strLoc = Region(loc.begin.line, loc.begin.column, loc.begin.line + n, c) // endcolumn with \n character
        Right(Some((
          s.substring(str.length),
          Token(terminal, Region(loc.begin.line, loc.begin.column, loc.begin.line + n, c-1)), // without \n character
          SuffixRegion(strLoc.end.line, strLoc.end.column))))
      case _ => throw new Exception("Encountered delimited string in non-axiom lexing mode.")
    }),
    //These have to come before LBOX,RBOX because otherwise <= becopmes LDIA, EQUALS
    GREATEREQ.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeTerminalLength(s, GREATEREQ, loc))),
    GREATEREQ_UNICODE.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeUnicodeTerminalLength(s, GREATEREQ_UNICODE, loc, GREATEREQ))),
    LESSEQ.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeTerminalLength(s, LESSEQ, loc))),
    LESSEQ_UNICODE.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeUnicodeTerminalLength(s, LESSEQ_UNICODE, loc, LESSEQ))),
    NOTEQ.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeTerminalLength(s, NOTEQ, loc))),

    LBANANA.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeTerminalLength(s, LBANANA, loc))),
    RBANANA.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeTerminalLength(s, RBANANA, loc))),
    LPAREN.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeTerminalLength(s, LPAREN, loc))),
    RPAREN.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeTerminalLength(s, RPAREN, loc))),
    LBOX.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeTerminalLength(s, LBOX, loc))),
    RBOX.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeTerminalLength(s, RBOX, loc))),
    LBARB.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeTerminalLength(s, LBARB, loc))),
    RBARB.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeTerminalLength(s, RBARB, loc))),
    LDDIA.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeTerminalLength(s, LDDIA, loc))),
    RDDIA.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeTerminalLength(s, RDDIA, loc))),
    LBRACE.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeTerminalLength(s, LBRACE, loc))),
    RBRACE.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeTerminalLength(s, RBRACE, loc))),

    COMMA.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeTerminalLength(s, COMMA, loc))),
    //
    IF.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeTerminalLength(s, IF, loc))),
    ELSE.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeTerminalLength(s, ELSE, loc))),
    //This has to come before PLUS because otherwise ++ because PLUS,PLUS instead of CHOICE.
    CHOICE.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeTerminalLength(s, CHOICE, loc))),
    //This has to come before MINUS because otherwise -- because MINUS,MINUS instead of DCHOICE.
    DCHOICE.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeTerminalLength(s, DCHOICE, loc))),
    DSTAR.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeTerminalLength(s, DSTAR, loc))),
    //@note must be before POWER
    DUAL.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeTerminalLength(s, DUAL, loc))),
    //
    PRIME.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeTerminalLength(s, PRIME, loc))),
    SLASH.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeTerminalLength(s, SLASH, loc))),
    POWER.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeTerminalLength(s, POWER, loc))),
    STAR.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeTerminalLength(s, STAR, loc))),
    PLUS.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeTerminalLength(s, PLUS, loc))),
    //
    AMP.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeTerminalLength(s, AMP, loc))),
    AND_UNICODE.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeUnicodeTerminalLength(s, AND_UNICODE, loc, AMP))),
    NOT.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeTerminalLength(s, NOT, loc))),
    OR.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeTerminalLength(s, OR, loc))),
    OR_UNICODE.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeUnicodeTerminalLength(s, OR_UNICODE, loc, OR))),
    EQUIV.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeTerminalLength(s, EQUIV, loc))),
    EQUIV_UNICODE.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeUnicodeTerminalLength(s, EQUIV_UNICODE, loc, EQUIV))),
    IMPLY.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeTerminalLength(s, IMPLY, loc))),
    IMPLY_UNICODE.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeUnicodeTerminalLength(s, IMPLY_UNICODE, loc, IMPLY))),
    REVIMPLY.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeTerminalLength(s, REVIMPLY, loc))),
    REVIMPLY_UNICODE.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeUnicodeTerminalLength(s, REVIMPLY_UNICODE, loc, REVIMPLY))),
    //
    FORALL.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeTerminalLength(s, FORALL, loc))),
    FORALL_UNICODE.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeUnicodeTerminalLength(s, FORALL_UNICODE, loc, FORALL))),
    EXISTS.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeTerminalLength(s, EXISTS, loc))),
    EXISTS_UNICODE.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeUnicodeTerminalLength(s, EXISTS_UNICODE, loc, EXISTS))),
    //
    EQ.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeTerminalLength(s, EQ, loc))),
    UNEQUAL_UNICODE.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeUnicodeTerminalLength(s, UNEQUAL_UNICODE, loc, NOTEQ))),
    TRUE.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeTerminalLength(s, TRUE, loc))),
    FALSE.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeTerminalLength(s, FALSE, loc))),
    //
    ANYTHING.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeTerminalLength(s, ANYTHING, loc))), //@note this token is stripped out and replaced with (! !) in [[fin`dNextToken]].
    //
    ASSIGNANY.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeTerminalLength(s, ASSIGNANY, loc))),
    ASSIGN.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeTerminalLength(s, ASSIGN, loc))),
    TEST.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeTerminalLength(s, TEST, loc))),
    SEMI.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeTerminalLength(s, SEMI, loc))),
    //
    PLACE.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeTerminalLength(s, PLACE, loc))),
    PSEUDO.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeTerminalLength(s, PSEUDO, loc))),
    //
    INVARIANT.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeTerminalLength(s, INVARIANT, loc))),
    VARIANT.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeTerminalLength(s, VARIANT, loc))),
    //
    FORMULA_SEPARATOR.startPattern -> ((s: String, loc: Location, mode, _) => mode match {
      case LemmaFileMode | StoredProvableMode => Right(consumeTerminalLength(s, FORMULA_SEPARATOR, loc))
      case _ => throw new Exception("Encountered a formula separator symbol " + FORMULA_SEPARATOR.img + " in a non-storedprovable input")
    }),
    FROM.startPattern -> ((s: String, loc: Location, mode, _) => mode match {
      case LemmaFileMode | StoredProvableMode => Right(consumeTerminalLength(s, FROM, loc))
      case _ => throw new Exception("Encountered a " + FROM.img + " symbol in a non-storedprovable input")
    }),
    QED.startPattern -> ((s: String, loc: Location, mode, _) => mode match {
      case LemmaFileMode | StoredProvableMode => Right(consumeTerminalLength(s, QED, loc))
      case _ => throw new Exception("Encountered a " + QED.img + " symbol in a non-storedprovable input")
    }),
    //
    IDENT.startPattern -> ((s: String, loc: Location, _, name: String) => {
      val (n, idx) = splitName(name)
      Right(consumeTerminalLength(s, IDENT(n, idx), loc))
    }),
    NUMBER.startPattern -> ((s: String, loc: Location, _, n: String) => Right(consumeTerminalLength(s, NUMBER(n), loc))),
    //@NOTE Minus has to come after number so that -9 is lexed as Number(-9) instead of as Minus::Number(9).
    //@NOTE Yet NUMBER has been demoted not to feature - signs, so it has become irrelevant for now.
    MINUS.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeTerminalLength(s, MINUS, loc))),
    //
    LDIA.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeTerminalLength(s, LDIA, loc))),
    RDIA.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeTerminalLength(s, RDIA, loc))),
    //
    PRG_DEF.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeTerminalLength(s, PRG_DEF, loc))),
    COLON.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeTerminalLength(s, COLON, loc))),
    //
    EXERCISE_PLACEHOLDER.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeTerminalLength(s, EXERCISE_PLACEHOLDER, loc))),
    //
    TILDE.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeTerminalLength(s, TILDE, loc))),
    BACKSLASH.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeTerminalLength(s, BACKSLASH, loc))),
    QUOTATION_MARK.startPattern -> ((s: String, loc: Location, _, _) => Right(consumeTerminalLength(s, QUOTATION_MARK, loc)))
  )

  /**
   * Finds the next token in a string.
    *
    * @todo Untested correctness condition: If a token's regex pattern contains another's, then the more restrictive token is processed first in the massive if/else.
    * @param s The string to process.
   * @param loc The location of s.
   * @param mode The mode of the lexer.
   * @return A triple containing:
   *          _1: the next token,
   *          _2: the portion of the string following the next token,
   *          _3: The location of the beginning of the next string.
   */
  private def findNextToken(s: String, loc: Location, mode: LexerMode): Option[(String, Token, Location)] = {
    var next: Either[(String, Location, LexerMode), Option[(String, Token, Location)]] = Left(s, loc, mode)
    while (next.isLeft) {
      val (cs, cloc, cmode) = next.left.toOption.get
      if (cs.isEmpty) next = Right(None)
      else {
        val lexPrefix = lexers.view.map({ case (r, lexer) => r.findPrefixOf(cs).map(lexer(cs, cloc, cmode, _)) }).find(_.isDefined).flatten
        lexPrefix match {
          case Some(Left(lexed)) => next = Left(lexed._1, lexed._2, lexed._3)
          case Some(Right(lexed)) => next = Right(lexed)
          case None => throw LexException(
            s"${loc.begin} Lexer does not recognize input at $loc in `\n" +
              s.substring(0, Math.min(50, s.length)) +
              // getNumericValue returns more reliable result than toInt but is not supported in Scala.js
              s"\n` beginning with character `${s(0)}`=${s(0).toInt}",
            loc,
            s"${s(0)}...",
          ).inInput(s)
        }
      }
    }
    next.toOption.get
  }

  /**
   * Returns the region containing everything between the starting position of the current location
   * location and the indicated offset of from the starting positiong of the current location,
   * inclusive.
    *
    * @param location Current location
   * @param endColOffset Column offset of the region
   * @return The region spanning from the start of ``location" to the offset from the start of ``location".
   */
  private def spanningRegion(location: Location, endColOffset: Int) =
    location match {
      case UnknownLocation      => UnknownLocation
      case Region(sl, sc, _, _) => Region(sl, sc, sl, sc + endColOffset)
      case SuffixRegion(sl, sc) => Region(sl, sc, sl, sc + endColOffset)
    }

  /**
   *
   * @param location Current location
   * @param colOffset Number of columns to chop off from the starting position of location.
   * @return A region containing all of location except the indicated columns in the initial row.
   *         I.e., the colOffset-suffix of location.
   */
  private def suffixOf(location: Location, colOffset: Int) : Location =
    location match {
      case UnknownLocation        => UnknownLocation
      case Region(sl, sc, el, ec) => Region(sl, sc + colOffset, el, ec)
      case SuffixRegion(sl, sc)   => SuffixRegion(sl, sc + colOffset)
    }

  private def splitName(s : String) : (String, Option[Int]) =
    if(s.contains("_") && !s.endsWith("_")) {
      // a_b_2 ==> "a_b", 2
      val (namePart, idxPart) = {
        val finalUnderscoreIdx = s.lastIndexOf("_")
        ( s.substring(0, finalUnderscoreIdx),
          s.substring(finalUnderscoreIdx + 1, s.length) )
      }

      val idx = Some(Integer.parseInt(idxPart))

      (namePart, idx)
    } else (s, None)
}
