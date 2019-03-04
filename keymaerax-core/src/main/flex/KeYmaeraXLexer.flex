/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*
* Modified for DARPA and AFRL under Contract No. FA8750-18-C-0092
* by Aleksey Nogin <anogin@hrl.com>
* Copyright (C) HRL Laboratories, LLC 2019
* Direct further inquiries to legal@hrl.com
* Distribution Statement "A": Approved for Public Release, Distribution Unlimited
*/

/**
 * Differential Dynamic Logic lexer for concrete KeYmaera X notation.
 *
 * @author Andre Platzer
 * @author Aleksey Nogin
 * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981, 2015."
 */
package edu.cmu.cs.ls.keymaerax.parser

import org.apache.logging.log4j.scala.Logging

import java.io.StringReader

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

/**
 * Terminal symbols of the differential dynamic logic grammar.
 *
 * @author Andre Platzer
 */
sealed abstract class Terminal(val img: String) {
  override def toString: String = getClass.getSimpleName// + "\"" + img + "\""
  /** Human-readable description followed by internal info */
  def description: String = img + " (" + toString + ")"
}
private abstract class OPERATOR(val opcode: String) extends Terminal(opcode) {
  //final def opcode: String = img
  override def toString: String = getClass.getSimpleName //+ "\"" + img + "\""
}
private case class IDENT(name: String, index: Option[Int] = None) extends Terminal(name + (index match {case Some(x) => "_"+x.toString case None => ""})) {
  override def toString: String = "ID(\"" + (index match {
    case None => name
    case Some(idx) => name + "," + idx
  }) + "\")"
}
private case class NUMBER(value: String) extends Terminal(value) {
  override def toString: String = "NUM(" + value + ")"
}

/**
 * End Of Stream
 */
object EOF extends Terminal("<EOF>")

private object LPAREN  extends Terminal("(")
private object RPAREN  extends Terminal(")")
private object LBANANA  extends Terminal("(|")
private object RBANANA  extends Terminal("|)")
private object LBRACE  extends Terminal("{")
private object RBRACE  extends Terminal("}")
private object LBARB   extends Terminal("{|")
private object RBARB   extends Terminal("|}")
private object LBOX    extends Terminal("[")
private object RBOX    extends Terminal("]")
private object LDIA    extends OPERATOR("<") //@todo really operator or better not?
private object RDIA    extends OPERATOR(">")

private object PRG_DEF  extends OPERATOR("::=")

private object COMMA   extends OPERATOR(",")
private object COLON   extends OPERATOR(":")

private object PRIME   extends OPERATOR("'")
private object POWER   extends OPERATOR("^")
private object STAR    extends OPERATOR("*")
private object SLASH   extends OPERATOR("/")
private object PLUS    extends OPERATOR("+")
private object MINUS   extends OPERATOR("-")

private object NOT     extends OPERATOR("!")
private object AMP     extends OPERATOR("&")
private object OR      extends OPERATOR("|")
private object EQUIV   extends OPERATOR("<->")
private object EQUIV_UNICODE extends OPERATOR("↔")
private object IMPLY   extends OPERATOR("->")
private object IMPLY_UNICODE extends OPERATOR("→")

//@todo maybe could change to <-- to disambiguate poor lexer's x<-7 REVIMPLY from LDIA MINUS
private object REVIMPLY extends OPERATOR("<-")
private object REVIMPLY_UNICODE extends OPERATOR("←")

private object FORALL  extends OPERATOR("\\forall")
private object EXISTS  extends OPERATOR("\\exists")

private object EQ      extends OPERATOR("=")
private object NOTEQ   extends OPERATOR("!=")
private object GREATEREQ extends OPERATOR(">=")
private object LESSEQ  extends OPERATOR("<=")

//Unicode versions of operators:
private object LESSEQ_UNICODE extends OPERATOR("≤")
private object GREATEREQ_UNICODE extends OPERATOR("≥")
private object AND_UNICODE extends OPERATOR("∧")
private object OR_UNICODE extends OPERATOR("∨")
private object UNEQUAL_UNICODE extends OPERATOR("≠")
private object FORALL_UNICODE extends OPERATOR("∀")
private object EXISTS_UNICODE extends OPERATOR("∃")

private object TRUE    extends OPERATOR("true")
private object FALSE   extends OPERATOR("false")

//@todo should probably also allow := *
private object ASSIGNANY extends OPERATOR(":=*")
private object ASSIGN  extends OPERATOR(":=")
private object TEST    extends OPERATOR("?")
private object IF extends OPERATOR("if")
private object ELSE extends OPERATOR("else")
private object SEMI    extends OPERATOR(";")
private object CHOICE  extends OPERATOR("++")
//@todo simplify lexer by using silly ^@ notation rather than ^d for now. @ for adversary isn't too bad to remember but doesn't look as good as ^d.
private object DUAL    extends OPERATOR("^@")

/*@TODO
private object DCHOICE  extends OPERATOR("--") {
  override def regexp = """--""".r
}
*/

// pseudos: could probably demote so that some are not OPERATOR
private object NOTHING extends Terminal("")

private case class DOT(index: Option[Int] = None) extends Terminal("•" + (index match {case Some(x) => "_"+x case None => ""})) {
  override def toString: String = "DOT(\"" + (index match {
    case None => ""
    case Some(idx) => idx
  }) + "\")"
}

private object PLACE   extends OPERATOR("⎵") //("_")
private object ANYTHING extends OPERATOR("??")
private object PSEUDO  extends Terminal("<pseudo>")

private object EXERCISE_PLACEHOLDER extends Terminal("__________")

// @annotations

private object INVARIANT extends Terminal("@invariant")

// axiom and problem file

private object AXIOM_BEGIN extends Terminal("Axiom")
private object END_BLOCK extends Terminal("End")
private case class DOUBLE_QUOTES_STRING(var s: String) extends Terminal("<string>")
private object PERIOD extends Terminal(".")
private object FUNCTIONS_BLOCK extends Terminal("Functions")
private object DEFINITIONS_BLOCK extends Terminal("Definitions")
private object PROGRAM_VARIABLES_BLOCK extends Terminal("ProgramVariables")
private object VARIABLES_BLOCK extends Terminal("Variables") //used in axioms file...
private object PROBLEM_BLOCK extends Terminal("Problem")
private object TACTIC_BLOCK extends Terminal("Tactic")
//@todo the following R, B, T, P etc should be lexed as identifiers. Adapt code to make them disappear.
//@todo the following should all be removed or at most used as val REAL = Terminal("R")
private object REAL extends Terminal("$$$R")
private object BOOL extends Terminal("$$$B")
//Is there any reason we parse a bunch of stuff just to throw it away? Are these suppose to be in our sort heirarchy...?
private object TERM extends Terminal("$$$T")
private object PROGRAM extends Terminal("$$$P")
private object CP extends Terminal("$$$CP")
private object MFORMULA extends Terminal("$$F")

///////////
// Section: Terminal signals for extended lemma files.
///////////
private object SEQUENT_BEGIN extends Terminal("Sequent")
private object TURNSTILE extends Terminal("==>")
private object FORMULA_BEGIN extends Terminal("Formula")

///////////
// Section: Terminal signals for tool files.
///////////
private object LEMMA_BEGIN extends Terminal("Lemma")
private object TOOL_BEGIN extends Terminal("Tool")
private object HASH_BEGIN extends Terminal("Hash")
private case class TOOL_VALUE(var s: String) extends Terminal("<string>")

private object SHARED_DEFINITIONS_BEGIN extends Terminal("SharedDefinitions")

private case class ARCHIVE_ENTRY_BEGIN(name: String) extends Terminal("ArchiveEntry|Lemma|Theorem|Exercise") {
  override def toString: String = name
}

///////////
// Section: Terminal signals for tactics.
///////////
private object BACKTICK extends Terminal("`")

private sealed trait LexError {
  self: Throwable =>
  val err_loc: Location
  val s : String
}

object KeYmaeraXLexer {
  /** Lexer's token stream with first token at head. */
  type TokenStream = List[Token]

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
  def inMode(input: String, mode: LexerMode): KeYmaeraXLexer.TokenStream = {
    val correctedInput = normalizeNewlines(input)
    // @todo: not sure how to get the next line to compile correctly
    // logger.debug("LEX: " + correctedInput)
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
    // Rumor is, this newline is needed to avoid JFlex issue where we can't match EOF with lookahead
    val reader = new StringReader(input + "\n")
    // We are creating a fresh one, rather than retaining and reusing to make things thread-safe
    // Not sure whether it matters, but seems better to be on the safe side
    val flex = new KeYmaeraXLexer(reader)
    flex.mode = mode
    flex.loc = inputLocation
    var output: scala.collection.mutable.ListBuffer[Token] = scala.collection.mutable.ListBuffer.empty
    try {
      var currentToken = flex.yylex()
      while (currentToken != null) {
        output.append(currentToken)
        currentToken = flex.yylex()
      }
    } catch {
      case ex: Throwable with LexError =>
        ex.err_loc match {
          case UnknownLocation => throw LexException("Lexer does not recognize input beginning with character `" + ex.s(0) + "`=" + ex.s(0).toInt, ex.err_loc).inInput(ex.s)
          case _ =>
            val line = input.lines.drop(ex.err_loc.line-inputLocation.line).next
            val col = if (inputLocation.line < ex.err_loc.line) ex.err_loc.column - 1 else ex.err_loc.column - inputLocation.column
            throw LexException(ex.err_loc.begin + " Lexer does not recognize input at " + ex.err_loc + " in:\n" + line +"\n" + (" " * col) + "^\nbeginning with character `" + line(col) + "`=" + line(col).toInt, ex.err_loc).inInput(line.substring(col))
        }
    }
    replaceAnything(output).to
  }

  /** Replace all instances of LPAREN,ANYTHING,RPAREN with LBANANA,RBANANA. */
  // @todo Aleksey Nogin: this functions looks weird and inefficient. Does not actually check
  //       whether the tokens before and after ANYTHING are LPAREN/RPAREN...
  private def replaceAnything(output: scala.collection.mutable.ListBuffer[Token]): scala.collection.mutable.ListBuffer[Token] = {
    output.find(x => x.tok == ANYTHING) match {
      case None => output
      case Some(anyTok) =>
        val pos = output.indexOf(anyTok)
        replaceAnything(output.patch(pos-1, Token(LBANANA, anyTok.loc) :: Token(RBANANA, anyTok.loc) :: Nil, 3))
    }
  }

}

%%

%class KeYmaeraXLexer
%unicode
%type Token
%extends Logging
%scanerror Exception
%apiprivate

// We use our own character counting:
// - automated line/column counting is not yet implemented correctly in jflex-scala
//   (see https://github.com/strubell/jflex-scala/issues/1)
// - Flex documentation suggests that it is the way to go for performance reasons
//   (https://jflex.de/manual.html - "Avoid line and column counting")
//%line
//%column
//%char

%{
  private def tok(term: Terminal) : Token = {
    val cols = yylength()
    val token = Token(term, spanningRegion(loc, cols-1))
    loc = suffixOf(loc, cols)
    return token
  }

  private var mode : LexerMode = ExpressionMode

  private var loc : Location = UnknownLocation

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
      case UnknownLocation        => UnknownLocation
      case Region(sl, sc, el, ec) => Region(sl, sc, sl, sc + endColOffset)
      case SuffixRegion(sl, sc)   => Region(sl, sc, sl, sc + endColOffset)
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

%}

//@note Pattern is more permissive than NamedSymbol's since Lexer's IDENT will include the index, so xy_95 is acceptable.
IDENT = [a-zA-Z][a-zA-Z0-9]*\_?\_?[0-9]*

//@NOTE Minus sign artificially excluded from the number to make sure x-5 lexes as IDENT("x"),MINUS,NUMBER("5") not as IDENT("x"),NUMBER("-5")
NUMBER = [0-9]+\.?[0-9]*

DOUBLE_QUOTES_STRING = \" ~ \"

DOT=("•"(\_[0-9]+)?) | (\.\_[0-9]+)

// values are nested into quadruple ", because they can contain single, double, or triple " themselves (arbitrary Scala code)
TOOL_VALUE = \"{4} ~ \"{4}

// The full set of options is "ArchiveEntry" | "Theorem" | "Exercise" | "Lemma".
// but we omit "Lemma" to avoid conflict with LEMMA_BEGIN and instead have a
// special case in the rule for LEMMA_BEGIN
ARCHIVE_ENTRY_BEGIN = "ArchiveEntry" | "Theorem" | "Exercise"
LEMMA_BEGIN = "Lemma"

WHITESPACE = \s+
COMMENT = "/*" ~ "*/"

%%

{COMMENT} | {WHITESPACE} { // WHITESPACE includes newlines
  val str = yytext()
  val lineCount = str.count(c => c=='\n') + 1
  val lastLineCol = if (lineCount > 1) yylength() - str.lastIndexOf("\n") - 1 else yylength()
  loc = loc match {
    case UnknownLocation => UnknownLocation
    case Region(sl, sc, el, ec) => Region(sl + lineCount - 1, if (lineCount > 1) lastLineCol+1 else sc + lastLineCol, el, ec)
    case SuffixRegion(sl, sc) => SuffixRegion(sl + lineCount - 1, if (lineCount > 1) lastLineCol+1 else sc + lastLineCol)
  }
  null
}

//Lemma file cases
{LEMMA_BEGIN} {
  mode match {
    case LemmaFileMode => tok(LEMMA_BEGIN)
    case ProblemFileMode => tok(ARCHIVE_ENTRY_BEGIN("Lemma"))
    case _ => throw new Exception("Encountered ``Lemma`` in non-lemma lexing mode.")
  }
}
"Tool" {
  mode match {
    case LemmaFileMode => tok(TOOL_BEGIN)
    case _ => throw new Exception("Encountered ``Tool`` in non-lemma lexing mode.")
  }
}
"Hash" {
  mode match {
    case LemmaFileMode => tok(HASH_BEGIN)
    case _ => throw new Exception("Encountered ``Hash`` in non-lemma lexing mode.")
  }
}
"Sequent" {
  mode match {
    case LemmaFileMode => tok(SEQUENT_BEGIN)
    case _ => throw new Exception("Encountered ``Sequent`` in a non-lemma file.")
  }
}
"==>" {
  mode match {
    case LemmaFileMode => tok(TURNSTILE)
    case _ => throw new Exception("Encountered a turnstile symbol ==> in a non-lemma file.")
  }
}
"Formula" {
  mode match {
    case LemmaFileMode => tok(FORMULA_BEGIN)
    case _ => throw new Exception("Encountered a formula begin symbol (Formula:) in a non-lemma file.")
  }
}

{DOT} {val (_, idx) = splitName(yytext()); tok(DOT(idx))}

// File cases
"." { tok (PERIOD) }
/*mode match {
   case AxiomFileMode | ProblemFileMode | LemmaFileMode => tok(PERIOD)
   case _ => throw new Exception("Periods should only occur when processing files.")
}*/

{ARCHIVE_ENTRY_BEGIN} {
  val kind = yytext()
  mode match {
    case ProblemFileMode => tok(ARCHIVE_ENTRY_BEGIN(kind))
    case _ => throw new Exception("Encountered ``" + ARCHIVE_ENTRY_BEGIN(kind).img + "`` in non-problem file lexing mode.")
  }
}

//not totally necessary -- you'll still get the right behavior because . matches \. But also allows stuff like Functions: which maybe isn't terrible.
//"Functions\."
"Functions" {
  mode match {
    case AxiomFileMode | ProblemFileMode | LemmaFileMode => tok(FUNCTIONS_BLOCK)
    case _ => throw new Exception("Functions. should only occur when processing files.")
  }
}
"Definitions" {
  mode match {
    case AxiomFileMode | ProblemFileMode | LemmaFileMode => tok(DEFINITIONS_BLOCK)
    case _ => throw new Exception("Definitions. should only occur when processing files.")
  }
}
"ProgramVariables" {
  mode match {
    case AxiomFileMode | ProblemFileMode | LemmaFileMode => tok(PROGRAM_VARIABLES_BLOCK)
    case _ => throw new Exception("ProgramVariables. should only occur when processing files.")
  }
}
"Variables" {
  mode match {
    case AxiomFileMode | ProblemFileMode | LemmaFileMode => tok(VARIABLES_BLOCK)
    case _ => throw new Exception("Variables. should only occur when processing files.")
  }
}
"$$$B" {
  mode match {
    case AxiomFileMode | ProblemFileMode | LemmaFileMode => tok(BOOL)
    case _ => throw new Exception("Bool symbol declaration should only occur when processing files.")
  }
}
"$$$R" {
  mode match {
    case AxiomFileMode | ProblemFileMode | LemmaFileMode => tok(REAL)
    case _ => throw new Exception("Real symbol declaration should only occur when processing files.")
  }
}
"$$$T" {
  mode match {
    case AxiomFileMode | ProblemFileMode | LemmaFileMode => tok(TERM)
    case _ => throw new Exception("Term symbol declaration should only occur when processing files.")
  }
}
"$$$P" {
  mode match {
    case AxiomFileMode | ProblemFileMode | LemmaFileMode => tok(PROGRAM)
    case _ => throw new Exception("Program symbol declaration should only occur when processing files.")
  }
}
"$$$CP" {
  mode match {
    case AxiomFileMode | ProblemFileMode | LemmaFileMode => tok(CP)
    case _ => throw new Exception("CP symbol declaration should only occur when processing files.")
  }
}
"$$F" {
  mode match {
    case AxiomFileMode | ProblemFileMode | LemmaFileMode => tok(MFORMULA)
    case _ => throw new Exception("MFORMULA symbol declaration should only occur when processing files.")
  }
}
//.kyx file cases
"Problem" {
  mode match {
    case AxiomFileMode | ProblemFileMode => tok(PROBLEM_BLOCK)
    case _ => throw new Exception("Problem./End. sections should only occur when processing .kyx files.")
  }
}
"Tactic" {
  mode match {
    case AxiomFileMode | ProblemFileMode => tok(TACTIC_BLOCK)
    case _ => throw new Exception("Tactic./End. sections should only occur when processing .kyx files.")
  }
}
"`" {
  mode match {
    case ProblemFileMode => tok(BACKTICK)
    case _ => throw new Exception("Backtick ` should only occur when processing .kyx files.")
  }
}
"SharedDefinitions" {
  mode match {
    case ProblemFileMode => tok(SHARED_DEFINITIONS_BEGIN)
    case _ => throw new Exception("SharedDefinitions./End. sections should only occur when processing .kyx files.")
  }
}
//Lemma file cases (2)
{TOOL_VALUE} {
  mode match {
    case LemmaFileMode =>
      //A tool value looks like """"blah"""" but we only want blah
      tok(TOOL_VALUE(yytext().slice(4,yylength()-4)))
    case _ => throw new Exception("Encountered delimited string in non-lemma lexing mode.")
  }
}
//Axiom file cases
"Axiom" {
  mode match {
    case AxiomFileMode => tok(AXIOM_BEGIN)
    case _ => throw new Exception("Encountered ``Axiom.`` in non-axiom lexing mode.")
  }
}
"End" {
  mode match {
    case AxiomFileMode | ProblemFileMode | LemmaFileMode => tok(END_BLOCK)
    case _ => throw new Exception("Encountered ``Axiom.`` in non-axiom lexing mode.")
  }
}

{DOUBLE_QUOTES_STRING} {
  mode match {
    case AxiomFileMode | LemmaFileMode | ProblemFileMode =>
      tok(DOUBLE_QUOTES_STRING(yytext().slice(1,yylength()-1)))
    case _ => throw new Exception("Encountered delimited string in non-axiom lexing mode.")
  }
}

">=" {tok(GREATEREQ)}
"≥" {tok(GREATEREQ_UNICODE)}
"<=" {tok(LESSEQ)}
"≤" {tok(LESSEQ_UNICODE)}
"!=" {tok(NOTEQ)}

"(|" {tok(LBANANA)}
"|)" {tok(RBANANA)}
"(" {tok(LPAREN)}
")" {tok(RPAREN)}
"[" {tok(LBOX)}
"]" {tok(RBOX)}
"{|" {tok(LBARB)}
"|}" {tok(RBARB)}
"{" {tok(LBRACE)}
"}" {tok(RBRACE)}

"," {tok(COMMA)}

"if" {tok(IF)}
"else" {tok(ELSE)}
"++" {tok(CHOICE)}
// @TODO "--" {tok(DCHOICE)}
"^@" {tok(DUAL)}

"'" {tok(PRIME)}
"/" {tok(SLASH)}
"^" {tok(POWER)}
"*" {tok(STAR)}
"+" {tok(PLUS)}

"&" {tok(AMP)}
"∧" {tok(AND_UNICODE)}
"!" {tok(NOT)}
"|" {tok(OR)}
"∨" {tok(OR_UNICODE)}
"<->" {tok(EQUIV)}
"↔" {tok(EQUIV_UNICODE)}
"->" {tok(IMPLY)}
"→" {tok(IMPLY_UNICODE)}
"<-" {tok(REVIMPLY)}
"←" {tok(REVIMPLY_UNICODE)}

"\\forall" {tok(FORALL)}
"∀" {tok(FORALL_UNICODE)}
"\\exists" {tok(EXISTS)}
"∃" {tok(EXISTS_UNICODE)}

"=" {tok(EQ)}
"≠" {tok(UNEQUAL_UNICODE)}
"true" {tok(TRUE)}
"false" {tok(FALSE)}

"??" {tok(ANYTHING)} //@note this token is stripped out and replaced with (! !) in [[lex]].

":=*" {tok(ASSIGNANY)}
":=" {tok(ASSIGN)}
"?" {tok(TEST)}
";" {tok(SEMI)}

"⎵" {tok(PLACE)}
"<pseudo>" {tok(PSEUDO)}

"@invariant" {tok(INVARIANT)}

{IDENT} {
  val (s, idx) = splitName(yytext())
  tok(IDENT(s, idx))
}

{NUMBER} {tok(NUMBER(yytext()))}

"-" {tok(MINUS)}

"<" {tok(LDIA)}
">" {tok(RDIA)}

"::=" {tok(PRG_DEF)}
":" {tok(COLON)}

"__________" {tok(EXERCISE_PLACEHOLDER)}

/* error fallback */
[^] {
  throw new Exception() with LexError {
    override val err_loc = loc
    override val s = yytext()
  }
}

<<EOF>> { tok(EOF) }
