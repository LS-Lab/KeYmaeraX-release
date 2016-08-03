/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
/**
 * Differential Dynamic Logic lexer for concrete KeYmaera X notation.
  *
  * @author Andre Platzer
 * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981, 2015."
 */
package edu.cmu.cs.ls.keymaerax.parser

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

/**
 * Terminal symbols of the differential dynamic logic grammar.
  *
  * @author Andre Platzer
 */
sealed abstract class Terminal(val img: String) {
  override def toString = getClass.getSimpleName// + "\"" + img + "\""
  /**
   * @return The regex that identifies this token.
   */
  def regexp : scala.util.matching.Regex = img.r

  val startPattern: Regex = ("^" + regexp.pattern.pattern + "[\\s\\S]*").r
}
private abstract class OPERATOR(val opcode: String) extends Terminal(opcode) {
  //final def opcode: String = img
  override def toString = getClass.getSimpleName //+ "\"" + img + "\""
}
private case class IDENT(name: String, index: Option[Int] = None) extends Terminal(name + (index match {case Some(x) => "_"+x.toString case None => ""})) {
  override def toString = "ID(\"" + (index match {
    case None => name
    case Some(idx) => name + "," + idx
  }) + "\")"
  override def regexp = IDENT.regexp
}
private object IDENT {
  //@note Pattern is more permissive than NamedSymbol's since Lexer's IDENT will include the index, so xy_95 is acceptable.
  def regexp = """([a-zA-Z][a-zA-Z0-9]*\_?\_?[0-9]*)""".r
  val startPattern: Regex = ("^" + regexp.pattern.pattern + "[\\s\\S]*").r
}
private case class NUMBER(value: String) extends Terminal(value) {
  override def toString = "NUM(" + value + ")"
  override def regexp = NUMBER.regexp
}
private object NUMBER {
  //A bit weird, but this gives the entire number in a single group.
  //def regexp = """(-?[0-9]+\.?[0-9]*)""".r
  //@NOTE Minus sign artificially excluded from the number to make sure x-5 lexes as IDENT("x"),MINUS,NUMBER("5") not as IDENT("x"),NUMBER("-5")
  def regexp = """([0-9]+\.?[0-9]*)""".r
  val startPattern: Regex = ("^" + regexp.pattern.pattern + "[\\s\\S]*").r
}

/**
 * End Of Stream
 */
object EOF extends Terminal("<EOF>") {
  override def regexp = "$^".r //none.
}

private object LPAREN  extends Terminal("(") {
  override def regexp = """\(""".r
}
private object RPAREN  extends Terminal(")") {
  override def regexp = """\)""".r
}
private object LBANANA  extends Terminal("(|") {
  override def regexp = """\(\|""".r
}
private object RBANANA  extends Terminal("|)") {
  override def regexp = """\|\)""".r
}
private object LBRACE  extends Terminal("{") {
  override def regexp = """\{""".r
}
private object RBRACE  extends Terminal("}") {
  override def regexp = """\}""".r
}
private object LBOX    extends Terminal("[") {
  override def regexp = """\[""".r
}
private object RBOX    extends Terminal("]") {
  override def regexp = """\]""".r
}
private object LDIA    extends OPERATOR("<") {
  override def regexp = """\<""".r
}//@todo really operator or better not?
private object RDIA    extends OPERATOR(">") {
  override def regexp = """\>""".r
}

private object COMMA   extends OPERATOR(",")

private object PRIME   extends OPERATOR("'")
private object POWER   extends OPERATOR("^") {
  override def regexp = """\^""".r
}
private object STAR    extends OPERATOR("*") {
  override def regexp = """\*""".r
}
private object SLASH   extends OPERATOR("/")
private object PLUS    extends OPERATOR("+") {
  override def regexp = """\+""".r
}
private object MINUS   extends OPERATOR("-")

private object NOT     extends OPERATOR("!") {
  override def regexp = """\!""".r
}
private object AMP     extends OPERATOR("&")
private object OR      extends OPERATOR("|") {
  override def regexp = """\|""".r
}
private object EQUIV   extends OPERATOR("<->")
private object IMPLY   extends OPERATOR("->")
//@todo maybe could change to <-- to disambiguate poor lexer's x<-7 REVIMPLY from LDIA MINUS
private object REVIMPLY extends OPERATOR("<-")

private object FORALL  extends OPERATOR("\\forall") {
  override def regexp = """\\forall""".r
}
private object EXISTS  extends OPERATOR("\\exists") {
  override def regexp = """\\exists""".r
}

private object EQ      extends OPERATOR("=")
private object NOTEQ   extends OPERATOR("!=") {
  override def regexp = """\!=""".r
}
private object GREATEREQ extends OPERATOR(">=")
private object LESSEQ  extends OPERATOR("<=")

private object TRUE    extends OPERATOR("true")
private object FALSE   extends OPERATOR("false")

//@todo should probably also allow := *
private object ASSIGNANY extends OPERATOR(":=*") {
  override def regexp = """:=\*""".r
}
private object ASSIGN  extends OPERATOR(":=")
private object TEST    extends OPERATOR("?") {
  override def regexp = """\?""".r
}
private object SEMI    extends OPERATOR(";")
private object CHOICE  extends OPERATOR("++") {
  override def regexp = """\+\+""".r
}
//@todo simplify lexer by using silly ^@ notation rather than ^d for now. @ for adversary isn't too bad to remember but doesn't look as good as ^d.
private object DUAL    extends OPERATOR("^@") {
  override def regexp = """\^\@""".r
}

/*@TODO
private object DCHOICE  extends OPERATOR("--") {
  override def regexp = """--""".r
}
*/

// pseudos: could probably demote so that some are not OPERATOR
private object NOTHING extends Terminal("")
private object DOT     extends OPERATOR("•") //(".")
private object PLACE   extends OPERATOR("⎵") //("_")
private object ANYTHING extends OPERATOR("??") {
  override def regexp = """\?\?""".r
}
private object PSEUDO  extends Terminal("<pseudo>")


// @annotations

private object INVARIANT extends Terminal("@invariant") {
  override def regexp = """\@invariant""".r
}


// axiom and problem file

private object AXIOM_BEGIN extends Terminal("Axiom") {
  override def regexp = """Axiom""".r
}
private object END_BLOCK extends Terminal("End.")
private case class LEMMA_AXIOM_NAME(var s: String) extends Terminal("<string>") {
  override def regexp = LEMMA_AXIOM_NAME_PAT.regexp
}
private object LEMMA_AXIOM_NAME_PAT {
  def regexp = """\"(.*)\"\.""".r
  val startPattern: Regex = ("^" + regexp.pattern.pattern + "[\\s\\S]*").r
}
private object PERIOD extends Terminal(".") {
  override def regexp = "\\.".r
}
private object FUNCTIONS_BLOCK extends Terminal("Functions.") {
  //not totally necessary -- you'll still get the right behavior because . matches \. But also allows stuff like Functions: which maybe isn't terrible.
//  override def regexp = """Functions\.""".r
}
private object PROGRAM_VARIABLES_BLOCK extends Terminal("ProgramVariables.")
private object VARIABLES_BLOCK extends Terminal("Variables.") //used in axioms file...
private object PROBLEM_BLOCK extends Terminal("Problem.")
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
private object SEQUENT_BEGIN extends Terminal("Sequent.")  {
  override def regexp = """Sequent\.""".r
}
private object TURNSTILE extends Terminal("==>") {
  override def regexp = """==>""".r
}
private object FORMULA_BEGIN extends Terminal("Formula:") {
  override def regexp = """Formula:""".r
}

///////////
// Section: Terminal signals for tool files.
///////////
private object LEMMA_BEGIN extends Terminal("Lemma") {
  override def regexp = """Lemma""".r
}
private object TOOL_BEGIN extends Terminal("Tool") {
  override def regexp = """Tool""".r
}
private object HASH_BEGIN extends Terminal("Hash") {
  override def regexp = """Hash""".r
}
private case class TOOL_VALUE(var s: String) extends Terminal("<string>") {
  override def regexp = TOOL_VALUE_PAT.regexp
}
private object TOOL_VALUE_PAT {
  // values are nested into quadruple ", because they can contain single, double, or triple " themselves (arbitrary Scala code)
  def regexp = "\"{4}(([^\"]|\"(?!\"\"\")|\"\"(?!\"\")|\"\"\"(?!\"))*)\"{4}".r
//  def regexp = "\"([^\"]*)\"".r
  val startPattern: Regex = ("^" + regexp.pattern.pattern + "[\\s\\S]*").r
}

/**
 * Lexer for KeYmaera X turns string into list of tokens.
  *
  * @author Andre Platzer
 * @author nfulton
 */
object KeYmaeraXLexer extends ((String) => List[Token]) {

  /** Lexer's token stream with first token at head. */
  type TokenStream = List[Token]

  private val DEBUG = System.getProperty("DEBUG", "false")=="true"


  /** Normalize all new lines in input to a s*/
  def normalizeNewlines(input: String): String = input.replace("\r\n", "\n").replace("\r", "\n")
  /**
   * The lexer has multiple modes for the different sorts of files that are supported by KeYmaeraX.
   * The lexer will disallow non-expression symbols from occuring when the lexer is in expression mode.
   * This also ensures that reserved symbols are never used as function names.
    *
    * @param input The string to lex.
   * @param mode The lexer mode.
   * @return A stream of symbols corresponding to input.
   */
  def inMode(input: String, mode: LexerMode) = {
    val correctedInput = normalizeNewlines(input)
    if (DEBUG) println("LEX: " + correctedInput)
    val output = lex(correctedInput, SuffixRegion(1,1), mode)
    require(output.last.tok.equals(EOF), "Expected EOF but found " + output.last.tok)
    output
  }

  def apply(input: String) = inMode(input, ExpressionMode)

  /**
   * The lexer.
    *
    * @todo optimize
   * @param input The input to lex.
   * @param inputLocation The position of the input (e.g., wrt a source file).
   * @param mode The mode of the lexer.
   * @return A token stream.
   */
//  //@todo //@tailrec
//  private def lex(input: String, inputLocation:Location, mode: LexerMode): TokenStream =
//    if(input.trim.length == 0) {
//      List(Token(EOF))
//    }
//    else {
//      findNextToken(input, inputLocation, mode) match {
//        case Some((nextInput, token, nextLoc)) =>
//          //if (DEBUG) print(token)
//          token +: lex(nextInput, nextLoc, mode)
//        case None => List(Token(EOF)) //note: This case can happen if the input is e.g. only a comment or only whitespace.
//      }
//    }

  private def lex(input: String, inputLocation:Location, mode: LexerMode): TokenStream = {
    var remaining: String = input
    var loc: Location = inputLocation
    val output: scala.collection.mutable.ListBuffer[Token] = scala.collection.mutable.ListBuffer.empty
    while (!remaining.isEmpty) {
      findNextToken(remaining, loc, mode) match {
        case Some((nextInput, token, nextLoc)) =>
          //if (DEBUG) print(token)
          output.append(token)
          remaining = nextInput
          loc = nextLoc
        case None => //note: This case can happen if the input is e.g. only a comment or only whitespace.
          output.append(Token(EOF, loc))
          return output.to
      }
    }
    output.append(Token(EOF, loc))
    output.to
  }

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
  @tailrec
  private def findNextToken(s: String, loc: Location, mode: LexerMode): Option[(String, Token, Location)] = {
    val whitespace = """^(\s+)[\s\S]*""".r
    val newline = """(?s)(^\n)[\s\S]*""".r //@todo use something more portable.
    val comment = """(?s)(^/\*[\s\S]*?\*/)[\s\S]*""".r

    /**
     *
     * @param cols Number of columns to move cursor.
     * @param terminal terminal to generate a token for.
     * @param location Current location.
     * @return Return value of findNextToken
     */
    def consumeColumns(cols: Int, terminal: Terminal, location: Location) = {
      assert(cols > 0, "Cannot move cursor less than 1 columns.")
      Some((
        s.substring(cols),
        Token(terminal, spanningRegion(loc, cols-1)),
        suffixOf(loc, cols)))
    }

    def consumeTerminalLength(terminal: Terminal, location: Location) =
      consumeColumns(terminal.img.length, terminal, location)

    s match {
      //update location if we encounter whitespace/comments.
      case comment(theComment) => {
        val comment = s.substring(0, theComment.length)
        val lastLineCol = comment.lines.toList.last.length //column of last line.
        val lineCount = comment.lines.length
        findNextToken(s.substring(theComment.length), loc match {
          case UnknownLocation => UnknownLocation
          case Region(sl, sc, el, ec) => Region(sl + lineCount - 1, lastLineCol, el, ec)
          case SuffixRegion(sl, sc) => SuffixRegion(sl + lineCount - 1, theComment.length)
        }, mode)
      }

      case newline(_*) =>
        findNextToken(s.tail, loc match {
          case UnknownLocation     => UnknownLocation
          case Region(sl,sc,el,ec) => Region(sl+1,1,el,ec)
          case SuffixRegion(sl,sc) => SuffixRegion(sl+1, 1)
        }, mode)

      case whitespace(spaces) =>
        findNextToken(s.substring(spaces.length), loc match {
          case UnknownLocation => UnknownLocation
          case Region(sl,sc,el,ec) => Region(sl, sc+spaces.length, el, ec)
          case SuffixRegion(sl,sc) => SuffixRegion(sl, sc+ spaces.length)
        }, mode)

      //Lemma file cases
      case LEMMA_BEGIN.startPattern(_*) => mode match {
        case LemmaFileMode => consumeTerminalLength(LEMMA_BEGIN, loc)
        case _ => throw new Exception("Encountered ``Lemma`` in non-lemma lexing mode.")
      }
      case TOOL_BEGIN.startPattern(_*) => mode match {
        case LemmaFileMode => consumeTerminalLength(TOOL_BEGIN, loc)
        case _ => throw new Exception("Encountered ``Tool`` in non-lemma lexing mode.")
      }
      case HASH_BEGIN.startPattern(_*) => mode match {
        case LemmaFileMode => consumeTerminalLength(HASH_BEGIN, loc)
        case _ => throw new Exception("Encountered ``Tool`` in non-lemma lexing mode.")
      }
      case SEQUENT_BEGIN.startPattern(_*) => mode match {
        case LemmaFileMode => consumeTerminalLength(SEQUENT_BEGIN, loc)
        case _ => throw new Exception("Encountered ``Sequent`` in a non-lemma file.")
      }
      case TURNSTILE.startPattern(_*) => mode match {
        case LemmaFileMode => consumeTerminalLength(TURNSTILE, loc)
        case _ => throw new Exception("Encountered a turnstile symbol ==> in a non-lemma file.")
      }
      case FORMULA_BEGIN.startPattern(_*) => mode match {
        case LemmaFileMode => consumeTerminalLength(FORMULA_BEGIN, loc)
        case _ => throw new Exception("Encountered a formula begin symbol (Formula:) in a non-lemma file.")
      }

      // File cases
      case PERIOD.startPattern(_*) => consumeTerminalLength(PERIOD, loc)
        /*mode match {
        case AxiomFileMode | ProblemFileMode | LemmaFileMode => consumeTerminalLength(PERIOD, loc)
        case _ => throw new Exception("Periods should only occur when processing files.")
      }*/
      case FUNCTIONS_BLOCK.startPattern(_*) => mode match {
        case AxiomFileMode | ProblemFileMode | LemmaFileMode => consumeTerminalLength(FUNCTIONS_BLOCK, loc)
        case _ => throw new Exception("Functions. should only occur when processing files.")
      }
      case PROGRAM_VARIABLES_BLOCK.startPattern(_*) => mode match {
        case AxiomFileMode | ProblemFileMode | LemmaFileMode => consumeTerminalLength(PROGRAM_VARIABLES_BLOCK, loc)
        case _ => throw new Exception("ProgramVariables. should only occur when processing files.")
      }
      case VARIABLES_BLOCK.startPattern(_*) => mode match {
        case AxiomFileMode | ProblemFileMode | LemmaFileMode => consumeTerminalLength(VARIABLES_BLOCK, loc)
        case _ => throw new Exception("Variables. should only occur when processing files.")
      }
      case BOOL.startPattern(_*) => mode match {
        case AxiomFileMode | ProblemFileMode | LemmaFileMode => consumeTerminalLength(BOOL, loc)
        case _ => throw new Exception("Bool symbol declaration should only occur when processing files.")
      }
      case REAL.startPattern(_*) => mode match {
        case AxiomFileMode | ProblemFileMode | LemmaFileMode => consumeTerminalLength(REAL, loc)
        case _ => throw new Exception("Real symbol declaration should only occur when processing files.")
      }
      case TERM.startPattern(_*) => mode match {
        case AxiomFileMode | ProblemFileMode | LemmaFileMode => consumeTerminalLength(TERM, loc)
        case _ => throw new Exception("Term symbol declaration should only occur when processing files.")
      }
      case PROGRAM.startPattern(_*) => mode match {
        case AxiomFileMode | ProblemFileMode | LemmaFileMode => consumeTerminalLength(PROGRAM, loc)
        case _ => throw new Exception("Program symbol declaration should only occur when processing files.")
      }
      case CP.startPattern(_*) => mode match {
        case AxiomFileMode | ProblemFileMode | LemmaFileMode => consumeTerminalLength(CP, loc)
        case _ => throw new Exception("CP symbol declaration should only occur when processing files.")
      }
      case MFORMULA.startPattern(_*) => mode match {
        case AxiomFileMode | ProblemFileMode | LemmaFileMode => consumeTerminalLength(MFORMULA, loc)
        case _ => throw new Exception("MFORMULA symbol declaration should only occur when processing files.")
      }
      //.kyx file cases
      case PROBLEM_BLOCK.startPattern(_*) => mode match {
        case AxiomFileMode | ProblemFileMode => consumeTerminalLength(PROBLEM_BLOCK, loc)
        case _ => throw new Exception("Problem./End. sections should only occur when processing .kyx files.")
      }
      //Axiom file cases
      case AXIOM_BEGIN.startPattern(_*) => mode match {
        case AxiomFileMode => consumeTerminalLength(AXIOM_BEGIN, loc)
        case _ => throw new Exception("Encountered ``Axiom.`` in non-axiom lexing mode.")
      }
      case END_BLOCK.startPattern(_*) => mode match {
        case AxiomFileMode | ProblemFileMode | LemmaFileMode => consumeTerminalLength(END_BLOCK, loc)
        case _ => throw new Exception("Encountered ``Axiom.`` in non-axiom lexing mode.")
      }
      case LEMMA_AXIOM_NAME_PAT.startPattern(str) => mode match {
        case AxiomFileMode | LemmaFileMode =>
          //An axiom name looks like "blah". but only blah gets grouped, so there are three
          // extra characters to account for.
          consumeColumns(str.length + 3, LEMMA_AXIOM_NAME(str), loc)
        case _ => throw new Exception("Encountered delimited string in non-axiom lexing mode.")
      }
      //Lemma file cases (2)
      case TOOL_VALUE_PAT.startPattern(str, _) => mode match {
        case LemmaFileMode =>
          //A tool value looks like """"blah"""" but only blah gets grouped, so there are eight
          // extra characters to account for.
          consumeColumns(str.length + 8, TOOL_VALUE(str), loc)
        case _ => throw new Exception("Encountered delimited string in non-lemma lexing mode.")
      }

      //These have to come before LBOX,RBOX because otherwise <= becopmes LDIA, EQUALS
      case GREATEREQ.startPattern(_*) => consumeTerminalLength(GREATEREQ, loc)
      case LESSEQ.startPattern(_*) => consumeTerminalLength(LESSEQ, loc)
      case NOTEQ.startPattern(_*) => consumeTerminalLength(NOTEQ, loc)

      case LBANANA.startPattern(_*) => consumeTerminalLength(LBANANA, loc)
      case RBANANA.startPattern(_*) => consumeTerminalLength(RBANANA, loc)
      case LPAREN.startPattern(_*) => consumeTerminalLength(LPAREN, loc)
      case RPAREN.startPattern(_*) => consumeTerminalLength(RPAREN, loc)
      case LBOX.startPattern(_*) => consumeTerminalLength(LBOX, loc)
      case RBOX.startPattern(_*) => consumeTerminalLength(RBOX, loc)
      case LBRACE.startPattern(_*) => consumeTerminalLength(LBRACE, loc)
      case RBRACE.startPattern(_*) => consumeTerminalLength(RBRACE, loc)

      case COMMA.startPattern(_*) => consumeTerminalLength(COMMA, loc)

      //This has to come before PLUS because otherwise ++ because PLUS,PLUS instead of CHOICE.
      case CHOICE.startPattern(_*) => consumeTerminalLength(CHOICE, loc)
      //This has to come before MINUS because otherwise -- because MINUS,MINUS instead of DCHOICE.
      //@TODO case DCHOICE.startPattern(_*) => consumeTerminalLength(DCHOICE, loc)
      //@note must be before POWER
      case DUAL.startPattern(_*) => consumeTerminalLength(DUAL, loc)

      case PRIME.startPattern(_*) => consumeTerminalLength(PRIME, loc)
      case SLASH.startPattern(_*) => consumeTerminalLength(SLASH, loc)
      case POWER.startPattern(_*) => consumeTerminalLength(POWER, loc)
      case STAR.startPattern(_*) => consumeTerminalLength(STAR, loc)
      case PLUS.startPattern(_*) => consumeTerminalLength(PLUS, loc)


      case AMP.startPattern(_*) => consumeTerminalLength(AMP, loc)
      case NOT.startPattern(_*) => consumeTerminalLength(NOT, loc)
      case OR.startPattern(_*) => consumeTerminalLength(OR, loc)
      case EQUIV.startPattern(_*) => consumeTerminalLength(EQUIV, loc)
      case IMPLY.startPattern(_*) => consumeTerminalLength(IMPLY, loc)
      case REVIMPLY.startPattern(_*) => consumeTerminalLength(REVIMPLY, loc)

      case FORALL.startPattern(_*) => consumeTerminalLength(FORALL, loc)
      case EXISTS.startPattern(_*) => consumeTerminalLength(EXISTS, loc)

      case EQ.startPattern(_*) => consumeTerminalLength(EQ, loc)
      case TRUE.startPattern(_*) => consumeTerminalLength(TRUE, loc)
      case FALSE.startPattern(_*) => consumeTerminalLength(FALSE, loc)

      case ANYTHING.startPattern(_*) => consumeTerminalLength(ANYTHING, loc)

      case ASSIGNANY.startPattern(_*) => consumeTerminalLength(ASSIGNANY, loc)
      case ASSIGN.startPattern(_*) => consumeTerminalLength(ASSIGN, loc)
      case TEST.startPattern(_*) => consumeTerminalLength(TEST, loc)
      case SEMI.startPattern(_*) => consumeTerminalLength(SEMI, loc)


      case DOT.startPattern(_*) => consumeTerminalLength(DOT, loc)
      case PLACE.startPattern(_*) => consumeTerminalLength(PLACE, loc)
      case PSEUDO.startPattern(_*) => consumeTerminalLength(PSEUDO, loc)

      case INVARIANT.startPattern(_*) => consumeTerminalLength(INVARIANT, loc)

      case IDENT.startPattern(name) => {
        val (s, idx) = splitName(name)
        consumeTerminalLength(IDENT(s, idx), loc)
      }
      case NUMBER.startPattern(n) => consumeTerminalLength(NUMBER(n), loc)
      //@NOTE Minus has to come after number so that -9 is lexed as Number(-9) instead of as Minus::Number(9).
      //@NOTE Yet NUMBER has been demoted not to feature - signs, so it has become irrelevant for now.
      case MINUS.startPattern(_*) => consumeTerminalLength(MINUS, loc)

      case LDIA.startPattern(_*) => consumeTerminalLength(LDIA, loc)
      case RDIA.startPattern(_*) => consumeTerminalLength(RDIA, loc)

      case _ if s.isEmpty => None
        //@todo should be LexException inheriting
      case _ => throw LexException(loc.begin + " Lexer does not recognize input at " + loc + " in `\n" + s +"\n` beginning with character `" + s(0) + "`=" + s(0).getNumericValue, loc).inInput(s)
    }
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
}
