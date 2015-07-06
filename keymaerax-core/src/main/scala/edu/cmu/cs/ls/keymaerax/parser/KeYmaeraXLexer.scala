/**
 * Differential Dynamic Logic lexer for concrete KeYmaera X notation.
 * @author aplatzer
 * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981, 2015."
 */
package edu.cmu.cs.ls.keymaerax.parser

import scala.collection.immutable._
import scala.util.matching.Regex


sealed abstract class LexerMode
case class ExpressionMode() extends LexerMode
case class AxiomFileMode() extends LexerMode
case class ProblemFileMode() extends LexerMode

/**
 * Terminal symbols of the differential dynamic logic grammar.
 * @author aplatzer
 */
sealed abstract class Terminal(val img: String) {
  override def toString = getClass.getSimpleName// + "\"" + img + "\""
  /**
   * @return The regex that identifies this token.
   */
  def regexp : scala.util.matching.Regex = img.r

  val startPattern: Regex = ("^" + regexp.pattern.pattern + "[\\s\\S]*").r
}
abstract class OPERATOR(val opcode: String) extends Terminal(opcode) {
  //final def opcode: String = img
  override def toString = getClass.getSimpleName //+ "\"" + img + "\""
}
case class IDENT(name: String) extends Terminal(name) {
  override def toString = "ID(\"" + name + "\")"
  override def regexp = IDENT.regexp
}
object IDENT {
  def regexp = """([a-zA-Z][a-zA-Z0-9\_]*)""".r
  val startPattern: Regex = ("^" + regexp.pattern.pattern + "[\\s\\S]*").r
}
case class NUMBER(value: String) extends Terminal(value) {
  override def toString = "NUM(" + value + ")"
  override def regexp = NUMBER.regexp
}
object NUMBER {
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

object LPAREN  extends Terminal("(") {
  override def regexp = """\(""".r
}
object RPAREN  extends Terminal(")") {
  override def regexp = """\)""".r
}
object LBRACE  extends Terminal("{") {
  override def regexp = """\{""".r
}
object RBRACE  extends Terminal("}") {
  override def regexp = """\}""".r
}
object LBOX    extends Terminal("[") {
  override def regexp = """\[""".r
}
object RBOX    extends Terminal("]") {
  override def regexp = """\]""".r
}
object LDIA    extends OPERATOR("<") {
  override def regexp = """\<""".r
}//@todo really operator or better not?
object RDIA    extends OPERATOR(">") {
  override def regexp = """\>""".r
}

object COMMA   extends OPERATOR(",")

object PRIME   extends OPERATOR("'")
object POWER   extends OPERATOR("^") {
  override def regexp = """\^""".r
}
object STAR    extends OPERATOR("*") {
  override def regexp = """\*""".r
}
object SLASH   extends OPERATOR("/")
object PLUS    extends OPERATOR("+") {
  override def regexp = """\+""".r
}
object MINUS   extends OPERATOR("-")

object NOT     extends OPERATOR("!") {
  override def regexp = """\!""".r
}
object AMP     extends OPERATOR("&")
object OR      extends OPERATOR("|") {
  override def regexp = """\|""".r
}
object EQUIV   extends OPERATOR("<->")
object IMPLY   extends OPERATOR("->")
//@todo maybe could change to <-- to disambiguate poor lexer's x<-7 REVIMPLY from LDIA MINUS
object REVIMPLY extends OPERATOR("<-")

object FORALL  extends OPERATOR("\\forall") {
  override def regexp = """\\forall""".r
}
object EXISTS  extends OPERATOR("\\exists") {
  override def regexp = """\\exists""".r
}

object EQ      extends OPERATOR("=")
object NOTEQ   extends OPERATOR("!=") {
  override def regexp = """\!=""".r
}
object GREATEREQ extends OPERATOR(">=")
object LESSEQ  extends OPERATOR("<=")

object TRUE    extends OPERATOR("true")
object FALSE   extends OPERATOR("false")

object ASSIGNANY extends OPERATOR(":=*") {
  override def regexp = """:=\*""".r
}
object ASSIGN  extends OPERATOR(":=")
object TEST    extends OPERATOR("?") {
  override def regexp = """\?""".r
}
object SEMI    extends OPERATOR(";")
object CHOICE  extends OPERATOR("++") {
  override def regexp = """\+\+""".r
}

/*@TODO
object DCHOICE  extends OPERATOR("--") {
  override def regexp = """--""".r
}
*/

// pseudos: could probably demote so that some are not OPERATOR
object NOTHING extends Terminal("")
object DOT     extends OPERATOR("•") //(".")
object PLACE   extends OPERATOR("⎵") //("_")
object ANYTHING extends OPERATOR("??") {
  override def regexp = """\?\?""".r
}
object PSEUDO  extends Terminal("<pseudo>")

object AXIOM_BEGIN extends Terminal("Axiom") {
  override def regexp = """Axiom""".r
}
object END_BLOCK extends Terminal("End.")
case class AXIOM_NAME(var s: String) extends Terminal("<string>") {
  override def regexp = AXIOM_NAME_PAT.regexp
}
object AXIOM_NAME_PAT {
  def regexp = """\"(.*)\"\.""".r
  val startPattern: Regex = ("^" + regexp.pattern.pattern + "[\\s\\S]*").r
}
object PERIOD extends Terminal(".") {
  override def regexp = "\\.".r
}
object FUNCTIONS_BLOCK extends Terminal("Functions.")
object PROGRAM_VARIABLES_BLOCK extends Terminal("ProgramVariables.")
object VARIABLES_BLOCK extends Terminal("Variables.") //used in axioms file...
object PROBLEM_BLOCK extends Terminal("Problem.")
//@todo the following R, B, T, P etc should be lexed as identifiers. Adapt code to make them disappear.
object REAL extends Terminal("$$$R")
object BOOL extends Terminal("$$$B")
//Is there any reason we parse a bunch of stuff just to throw it away? Are these suppose to be in our sort heirarchy...?
object TERM extends Terminal("$$$T")
object PROGRAM extends Terminal("$$$P")
object CP extends Terminal("$$$CP")
object MFORMULA extends Terminal("$$F")

/**
 * The location where a Terminal is located in an input stream.
 */
sealed abstract class Location
object UnknownLocation extends Location {
  override def toString = "<somewhere>"
}
case class Region(line: Int, column: Int, endLine: Int, endColumn: Int) extends Location {
  require(line <= endLine || (line == endLine && column <= endColumn),
    "A region cannot start after it ends.")
  override def toString = line + ":" + column + (if (column!=endColumn || line!=endLine) " to " + endLine + ":" + endColumn else "")
}
/**
 * Like a region, but extends until the end of the input.
 * @param line The starting line.
 * @param column The ending line.
 */
case class SuffixRegion(line: Int, column: Int) extends Location {
  override def toString = line + ":" + column + " to " + EOF
}

/**
 * Created by aplatzer on 6/8/15.
 * @author aplatzer
 * @author nfulton
 */
object KeYmaeraXLexer extends ((String) => List[Token]) {

  /** Lexer's token stream with first token at head. */
  type TokenStream = List[Token]

  /**
   * The lexer has multiple modes for the different sorts of files that are supported by KeYmaeraX.
   * The lexer will disallow non-expression symbols from occuring when the lexer is in expression mode.
   * This also ensures that reserved symbols are never used as function names.
   * @param input The string to lex.
   * @param mode The lexer mode.
   * @return A stream of symbols corresponding to input.
   */
  def inMode(input: String, mode: LexerMode) = {
    val output = lex(input, SuffixRegion(1,1), mode)
    require(output.last.tok.equals(EOF), "Expected EOF but found " + output.last.tok)
    output
  }

  def apply(input: String) = inMode(input, ExpressionMode())

  /**
   * The lexer.
   * @todo optimize
   * @param input The input to lex.
   * @param inputLocation The position of the input (e.g., wrt a source file).
   * @param mode The mode of the lexer.
   * @return A token stream.
   */
  private def lex(input: String, inputLocation:Location, mode: LexerMode): TokenStream =
    if(input.trim.length == 0) {
      List(Token(EOF))
    }
    else {
      findNextToken(input, inputLocation, AxiomFileMode()) match {
        case Some((nextInput, token, nextLoc)) => token +: lex(nextInput, nextLoc, mode)
        case None => List(Token(EOF)) //note: This case can happen if the input is e.g. only a comment or only whitespace.
      }
    }

  /**
   * Finds the next token in a string.
   * @todo Untested correctness condition: If a token's regex pattern contains another's, then the more restrictive token is processed first in the massive if/else.
   *
   * @param s The string to process.
   * @param loc The location of s.
   * @param mode The mode of the lexer.
   * @return A triple containing:
   *          _1: the next token,
   *          _2: the portion of the string following the next token,
   *          _3: The location of the beginning of the next string.
   */
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
        val lastLineCol = s.lines.toList.last.length //column of last line.
        val lineCount = s.lines.length
        findNextToken(s.substring(theComment.length), loc match {
          case UnknownLocation => UnknownLocation
          case Region(sl, sc, el, ec) => Region(sl + lineCount, lastLineCol, el, ec)
          case SuffixRegion(sl, sc) => SuffixRegion(sl + lineCount, theComment.length)
        }, mode)
      }

      case whitespace(spaces) =>
        findNextToken(s.substring(spaces.length), loc match {
          case UnknownLocation => UnknownLocation
          case Region(sl,sc,el,ec) => Region(sl, sc+spaces.length, el, ec)
          case SuffixRegion(sl,sc) => SuffixRegion(sl, sc+ spaces.length)
        }, mode)

      case newline(_*) =>
        findNextToken(s.tail, loc match {
          case UnknownLocation     => UnknownLocation
          case Region(sl,sc,el,ec) => Region(sl+1,1,el,ec)
          case SuffixRegion(sl,sc) => SuffixRegion(sl+1, 1)
        }, mode)

      // File cases
      case PERIOD.startPattern(_*) => mode match {
        case AxiomFileMode() | ProblemFileMode() => consumeTerminalLength(PERIOD, loc)
        case _ => throw new Exception("Periods should only occur when processing files.")
      }
      case FUNCTIONS_BLOCK.startPattern(_*) => mode match {
        case AxiomFileMode() | ProblemFileMode() => consumeTerminalLength(FUNCTIONS_BLOCK, loc)
        case _ => throw new Exception("Functions. should only occur when processing files.")
      }
      case PROGRAM_VARIABLES_BLOCK.startPattern(_*) => mode match {
        case AxiomFileMode() | ProblemFileMode() => consumeTerminalLength(PROGRAM_VARIABLES_BLOCK, loc)
        case _ => throw new Exception("ProgramVariables. should only occur when processing files.")
      }
      case VARIABLES_BLOCK.startPattern(_*) => mode match {
        case AxiomFileMode() | ProblemFileMode() => consumeTerminalLength(VARIABLES_BLOCK, loc)
        case _ => throw new Exception("Variables. should only occur when processing files.")
      }
      case BOOL.startPattern(_*) => mode match {
        case AxiomFileMode() | ProblemFileMode() => consumeTerminalLength(BOOL, loc)
        case _ => throw new Exception("Bool symbol declaration should only occur when processing files.")
      }
      case REAL.startPattern(_*) => mode match {
        case AxiomFileMode() | ProblemFileMode() => consumeTerminalLength(REAL, loc)
        case _ => throw new Exception("Real symbol declaration should only occur when processing files.")
      }
      case TERM.startPattern(_*) => mode match {
        case AxiomFileMode() | ProblemFileMode() => consumeTerminalLength(TERM, loc)
        case _ => throw new Exception("Term symbol declaration should only occur when processing files.")
      }
      case PROGRAM.startPattern(_*) => mode match {
        case AxiomFileMode() | ProblemFileMode() => consumeTerminalLength(PROGRAM, loc)
        case _ => throw new Exception("Program symbol declaration should only occur when processing files.")
      }
      case CP.startPattern(_*) => mode match {
        case AxiomFileMode() | ProblemFileMode() => consumeTerminalLength(CP, loc)
        case _ => throw new Exception("CP symbol declaration should only occur when processing files.")
      }
      case MFORMULA.startPattern(_*) => mode match {
        case AxiomFileMode() | ProblemFileMode() => consumeTerminalLength(MFORMULA, loc)
        case _ => throw new Exception("MFORMULA symbol declaration should only occur when processing files.")
      }
      //.kyx file cases
      case PROBLEM_BLOCK.startPattern(_*) => mode match {
        case AxiomFileMode() | ProblemFileMode() => consumeTerminalLength(PROBLEM_BLOCK, loc)
        case _ => throw new Exception("Problem./End. sections should only occur when processing .kyx files.")
      }
      //Axiom file cases
      case AXIOM_BEGIN.startPattern(_*) => mode match {
        case AxiomFileMode() => consumeTerminalLength(AXIOM_BEGIN, loc)
        case _ => throw new Exception("Encountered ``Axiom.`` in non-axiom lexing mode.")
      }
      case END_BLOCK.startPattern(_*) => mode match {
        case AxiomFileMode() | ProblemFileMode() => consumeTerminalLength(END_BLOCK, loc)
        case _ => throw new Exception("Encountered ``Axiom.`` in non-axiom lexing mode.")
      }
      case AXIOM_NAME_PAT.startPattern(str) => mode match {
        case AxiomFileMode() =>
          //An axiom name looks like "blah". but only blah gets grouped, so there are three
          // extra characters to account for.
          consumeColumns(str.length + 3, AXIOM_NAME(str), loc)
        case _ => throw new Exception("Encountered delimited string in non-axiom lexing mode.")
      }


      //These have to come before LBOX,RBOX because otherwise <= becopmes LDIA, EQUALS
      case GREATEREQ.startPattern(_*) => consumeTerminalLength(GREATEREQ, loc)
      case LESSEQ.startPattern(_*) => consumeTerminalLength(LESSEQ, loc)
      case NOTEQ.startPattern(_*) => consumeTerminalLength(NOTEQ, loc)

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

      case IDENT.startPattern(name) => consumeTerminalLength(IDENT(name), loc)
      case NUMBER.startPattern(n) => consumeTerminalLength(NUMBER(n), loc)
      //Minus has to come after number so that -9 is lexed as Number(-9) instead of as Minus::Number(9).
      case MINUS.startPattern(_*) => consumeTerminalLength(MINUS, loc)

      case LDIA.startPattern(_*) => consumeTerminalLength(LDIA, loc)
      case RDIA.startPattern(_*) => consumeTerminalLength(RDIA, loc)

      case _ if s.isEmpty => None
      case _ => throw new Exception("Lexer did not understand input at " + loc + " in `\n" + s +"\n` First character was `" + s(0) + "`")
    }
  }

  /**
   * Returns the region containing everything between the starting position of the current location
   * location and the indicated offset of from the starting positiong of the current location,
   * inclusive.
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
}
