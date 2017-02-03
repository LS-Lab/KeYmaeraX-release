package edu.cmu.cs.ls.keymaerax.bellerophon.parser

import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser.BelleToken
import edu.cmu.cs.ls.keymaerax.parser._

import scala.collection.immutable.List

/**
  * A lexer for the Bellerophon tactics language.
  *
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
      *
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
      case ON_ALL.startPattern(_*) => consumeTerminalLength(ON_ALL, loc)
      case US_MATCH.startPattern(_*) => consumeTerminalLength(US_MATCH, loc)
      case PARTIAL.startPattern(_*) => consumeTerminalLength(PARTIAL, loc)
      case DONE.startPattern(_*) => consumeTerminalLength(DONE, loc)
      case LET.startPattern(_*) => consumeTerminalLength(LET, loc)
      case IN.startPattern(_*) => consumeTerminalLength(IN, loc)

      //build-in tactics.
      case IDENT.startPattern(name) => consumeTerminalLength(IDENT(name), loc)

      case N_TIMES.startPattern(n) => consumeTerminalLength(N_TIMES(Integer.parseInt(n.tail)), loc)

      //Combinators
      case SEQ_COMBINATOR.startPattern(_*) => consumeTerminalLength(SEQ_COMBINATOR, loc)
      case DEPRECATED_SEQ_COMBINATOR.startPattern(_*) => consumeTerminalLength(DEPRECATED_SEQ_COMBINATOR, loc)
      case EITHER_COMBINATOR.startPattern(_*) => consumeTerminalLength(EITHER_COMBINATOR, loc)
      case KLEENE_STAR.startPattern(_*) => consumeTerminalLength(KLEENE_STAR, loc)
      case SATURATE.startPattern(_*) => consumeTerminalLength(SATURATE, loc)
      case BRANCH_COMBINATOR.startPattern(_*) => consumeTerminalLength(BRANCH_COMBINATOR, loc)
      case OPTIONAL.startPattern(_*) => consumeTerminalLength(OPTIONAL, loc)

      //Positions
      case ABSOLUTE_POSITION.startPattern(positionString) => consumeTerminalLength(ABSOLUTE_POSITION(positionString), loc)
      case LAST_SUCCEDENT.startPattern(_*) => consumeTerminalLength(LAST_SUCCEDENT, loc)
      case LAST_ANTECEDENT.startPattern(_*) => consumeTerminalLength(LAST_ANTECEDENT, loc)
      case SEARCH_SUCCEDENT.startPattern(_*) => consumeTerminalLength(SEARCH_SUCCEDENT, loc)
      case SEARCH_ANTECEDENT.startPattern(_*) => consumeTerminalLength(SEARCH_ANTECEDENT, loc)
      case SEARCH_EVERYWHERE.startPattern(_*) => consumeTerminalLength(SEARCH_EVERYWHERE, loc)
      case EXACT_MATCH.startPattern(_*) => consumeTerminalLength(EXACT_MATCH, loc)
      case UNIFIABLE_MATCH.startPattern(_*) => consumeTerminalLength(UNIFIABLE_MATCH, loc)

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


}
