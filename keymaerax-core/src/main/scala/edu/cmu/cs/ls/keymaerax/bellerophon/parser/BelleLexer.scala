package edu.cmu.cs.ls.keymaerax.bellerophon.parser

import edu.cmu.cs.ls.keymaerax.core.Expression

import edu.cmu.cs.ls.keymaerax.parser._

import scala.collection.immutable.List
import scala.util.matching.Regex

sealed abstract class BelleTerminal(val img: String) {
  assert(img != null)

  override def toString = getClass.getSimpleName// + "\"" + img + "\""
  /**
    * @return The regex that identifies this token.
    */
  def regexp : scala.util.matching.Regex = img.r
  val startPattern: Regex = ("^" + regexp.pattern.pattern + "[\\s\\S]*").r
}

case class IDENT(name: String) extends BelleTerminal(name) {
  assert(name != "US" && name.toLowerCase != "partial")
  override def toString = s"IDENT($name)"
}
object IDENT {
  def regexp = """([a-zA-Z][a-zA-Z0-9]*)""".r
  //"[\\p{Alpha}\\p{Alnum}]*".r
  val startPattern: Regex = ("^" + regexp.pattern.pattern + "[\\s\\S]*").r
}


// Combinator Tokens
object SEQ_COMBINATOR extends BelleTerminal("&") {
  override def regexp = "\\&".r
}

object EITHER_COMBINATOR extends BelleTerminal("|") {
  override def regexp = "\\|".r
}

object BRANCH_COMBINATOR extends BelleTerminal("<")

object KLEENE_STAR extends BelleTerminal("*") {
  override def regexp = "\\*".r
}

object SATURATE extends BelleTerminal("+") {
  override def regexp = "\\+".r
}

object US_MATCH extends BelleTerminal("US")

object RIGHT_ARROW extends BelleTerminal("=>")

// Separation/Grouping Tokens
object OPEN_PAREN extends BelleTerminal("(") {
  override def regexp = "\\(".r
}
object CLOSE_PAREN extends BelleTerminal(")") {
  override def regexp = "\\)".r
}
object COMMA extends BelleTerminal(",")

// Positions
case class ABSOLUTE_POSITION(positionString: String) extends BelleTerminal(positionString) {
  override def regexp = ABSOLUTE_POSITION.regexp
  override val startPattern = ABSOLUTE_POSITION.startPattern
  override def toString = s"ABSOLUTE_POSITION($positionString)"
}
object ABSOLUTE_POSITION {
  def regexp = """(-?\d+(?:\.\d+)*)""".r
  val startPattern: Regex = ("^" + regexp.pattern.pattern + "[\\s\\S]*").r
}
object SEARCH_SUCCEDENT extends BelleTerminal("'R")
object SEARCH_ANTECEDENT extends BelleTerminal("'L")
object SEARCH_EVERYWHERE extends BelleTerminal("'-") {
  override def regexp = "'\\-".r
}

object PARTIAL extends BelleTerminal("partial") {
  override def regexp = "(?i)partial".r // allow case-insensitive use of the work partial.
}

/** A dL expression. We allow both terms and formulas as arguments; e.g. in diffGhost. */
case class EXPRESSION(exprString: String) extends BelleTerminal(exprString) {
  val expression: Expression = {
    assert(exprString.startsWith("{`") && exprString.endsWith("`}"),
      s"EXPRESSION.regexp should ensure delimited expression begin and end with {` `}, but an EXPRESSION was constructed with argument: ${exprString}")

    //Remove delimiters and parse the expression.
    KeYmaeraXParser(exprString.drop(2).dropRight(2))
  }

  override def regexp = EXPRESSION.regexp
  override val startPattern = EXPRESSION.startPattern

  override def toString = s"EXPRESSION($exprString)"

  override def equals(other: Any) = other match {
    case EXPRESSION(str) => str == exprString
    case _ => false
  }
}
object EXPRESSION {
  def regexp = """(\{\`[\p{ASCII}]*\`\})""".r
  val startPattern = ("^" + regexp.pattern.pattern + "[\\s\\S]*").r
}

object EOF extends BelleTerminal("<EOF>") {
  override def regexp = "$^".r //none.
}

/**
  * @author Nathan Fulton
  */
object BelleLexer extends ((String) => List[BelleToken]) {
  type TokenStream = List[BelleToken]

  private val DEBUG = System.getProperty("DEBUG", "false")=="true"

  def apply(s: String) : List[BelleToken] = {
    //Avoids importing a thing with lots of potential name clashes.
    val correctedInput = edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXLexer.normalizeNewlines(s)
    //@todo not sure if this position is Ok. This is what's used in the KeYmaera X lexer.
    val startingLocation = SuffixRegion(1,1)

    if (DEBUG) println("LEX: " + correctedInput)
    lex(s, startingLocation)
  }

  /**
    *
    * @param input The input
    * @param inputLocation The location of this input.
    *                      If this is a recursive call, then inputLocation might not be (0,0).
    */
  private def lex(input: String, inputLocation: Location): TokenStream =
    if(input.trim.length == 0) {
      List(BelleToken(EOF, inputLocation))
    }
    else {
      findNextToken(input, inputLocation) match {
        case Some((nextInput, token, nextLoc)) =>
          //if (DEBUG) print(token)
          token +: lex(nextInput, nextLoc)
        case None => List(BelleToken(EOF, inputLocation)) //note: This case can happen if the input is e.g. only a comment or only whitespace.
      }
    }

  private def findNextToken(input: String, loc: Location): Option[(String, BelleToken, Location)] = {
    /**
      * Helper method for findNextToken
      * @param cols Number of columns to move cursor.
      * @param terminal terminal to generate a token for.
      * @return Return value of findNextToken
      */
    def consumeColumns(cols: Int, terminal: BelleTerminal, loc: Location) = {
      assert(cols > 0, "Cannot move cursor less than 1 columns.")
      Some((
        input.substring(cols),
        BelleToken(terminal, spanningRegion(loc, cols-1)),
        suffixOf(loc, cols)))
    }
    /** Helper method for findNextToken */
    def consumeTerminalLength(terminal: BelleTerminal, location: Location) =
      consumeColumns(terminal.img.length, terminal, location)

    input match {
        //Comments, newlines, and white-space. These are all copied from the KeYmaera X lexer.
      case comment(theComment) =>
        val comment = input.substring(0, theComment.length)
        val lastLineCol = comment.lines.toList.last.length //column of last line.
        val lineCount = comment.lines.length
        findNextToken(input.substring(theComment.length), loc match {
          case UnknownLocation => UnknownLocation
          case Region(sl, sc, el, ec) => Region(sl + lineCount - 1, lastLineCol, el, ec)
          case SuffixRegion(sl, sc) => SuffixRegion(sl + lineCount - 1, theComment.length)
        })

      case newline(_*) =>
        findNextToken(input.tail, loc match {
          case UnknownLocation     => UnknownLocation
          case Region(sl,sc,el,ec) => Region(sl+1,1,el,ec)
          case SuffixRegion(sl,sc) => SuffixRegion(sl+1, 1)
        })

      case whitespace(spaces) =>
        findNextToken(input.substring(spaces.length), loc match {
          case UnknownLocation => UnknownLocation
          case Region(sl,sc,el,ec) => Region(sl, sc+spaces.length, el, ec)
          case SuffixRegion(sl,sc) => SuffixRegion(sl, sc+ spaces.length)
        })

      //Stuff that could be confused as an identifier.
      case US_MATCH.startPattern(_*) => consumeTerminalLength(US_MATCH, loc)
      case PARTIAL.startPattern(_*) => consumeTerminalLength(PARTIAL, loc)

      //build-in tactics.
      case IDENT.startPattern(name) => consumeTerminalLength(IDENT(name), loc)

      //Combinators
      case SEQ_COMBINATOR.startPattern(_*) => consumeTerminalLength(SEQ_COMBINATOR, loc)
      case EITHER_COMBINATOR.startPattern(_*) => consumeTerminalLength(EITHER_COMBINATOR, loc)
      case KLEENE_STAR.startPattern(_*) => consumeTerminalLength(KLEENE_STAR, loc)
      case SATURATE.startPattern(_*) => consumeTerminalLength(SATURATE, loc)
      case BRANCH_COMBINATOR.startPattern(_*) => consumeTerminalLength(BRANCH_COMBINATOR, loc)

      //Positions
      case ABSOLUTE_POSITION.startPattern(positionString) => consumeTerminalLength(ABSOLUTE_POSITION(positionString), loc)
      case SEARCH_SUCCEDENT.startPattern(_*) => consumeTerminalLength(SEARCH_SUCCEDENT, loc)
      case SEARCH_ANTECEDENT.startPattern(_*) => consumeTerminalLength(SEARCH_ANTECEDENT, loc)
      case SEARCH_EVERYWHERE.startPattern(_*) => consumeTerminalLength(SEARCH_EVERYWHERE, loc)

      //Delimited expressions
      case EXPRESSION.startPattern(expressionString) => try {
        //Constructing an EXPRESSION results in an attempt to parse expressionString, which might
        //result in a parse error that should be passed back to the user.
        consumeTerminalLength(EXPRESSION(expressionString), loc)
      } catch {
        case e : Throwable => throw LexException(
          s"Could not parse expression: $expressionString", loc)
      }

      //Misc.
      case OPEN_PAREN.startPattern(_*) => consumeTerminalLength(OPEN_PAREN, loc)
      case CLOSE_PAREN.startPattern(_*) => consumeTerminalLength(CLOSE_PAREN, loc)
      case COMMA.startPattern(_*) => consumeTerminalLength(COMMA, loc)
      case RIGHT_ARROW.startPattern(_*) => consumeTerminalLength(RIGHT_ARROW, loc)

      //Error messages
      case _ => throw LexException(s"Could not lex $input", loc)
    }
  }

  private val whitespace = """^(\s+)[\s\S]*""".r
  //@note Assuming all newlines are just \n is OK because we normalize newlines prior to lexing.
  private val newline = """(?s)(^\n)[\s\S]*""".r
  private val comment = """(?s)(^/\*[\s\S]*?\*/)[\s\S]*""".r

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
