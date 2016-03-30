package edu.cmu.cs.ls.keymaerax.bellerophon.parser

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.Generator
import edu.cmu.cs.ls.keymaerax.core.{Expression, Formula}
import edu.cmu.cs.ls.keymaerax.parser._
import BelleLexer.TokenStream

/**
  * The Bellerophon parser
  *
  * @author Nathan Fulton
  */
object BelleParser extends (String => BelleExpr) {
  private var invariantGenerator : Option[Generator[Formula]] = None
  private val DEBUG = true

  override def apply(s: String) = parseWithInvGen(s, None)

  def parseWithInvGen(s: String, g:Option[Generator[Formula]] = None) = {
    invariantGenerator = g;
    parseTokenStream(BelleLexer(s))
  }

  //region The LL Parser

  private case class ParserState(stack: Stack[BelleItem], input: TokenStream)

  def parseTokenStream(toks: TokenStream): BelleExpr = {
    val result = parseLoop(ParserState(Bottom, toks))
    result.stack match {
      case Bottom :+ BelleAccept(e) => e
      case context :+ (BelleErrorItem(msg,loc,st)) => throw ParseException(msg, loc, "<unknown>", "<unknown>", "", st) //@todo not sure why I need the extra () around ErrorList.
      case _ => throw new AssertionError(s"Parser terminated with unexpected stack ${result.stack}")
    }
  }

  private def parseStep(st: ParserState) : ParserState = {
    val stack : Stack[BelleItem] = st.stack

    stack match {
      case r :+ BelleToken(IDENT(name), identLoc) =>
        if(!isOpenParen(st.input)) ParserState(r :+ ParsedBelleExpr(constructTactic(name, None), identLoc), st.input.tail)
        else {
          val (args, remainder) = parseArgumentList(st.input)

          //Do our best at computing the entire range of positions that is encompassed by the tactic application.
          val endLoc = remainder match {
            case hd :: tl => hd.location
            case _ => st.input.last.location
          }
          val spanLoc = if(endLoc.end.column != -1) identLoc.spanTo(endLoc) else identLoc

          ParserState(r :+ ParsedBelleExpr(constructTactic(name, Some(args)), spanLoc), remainder)
        }

      case r :+ BelleToken(OPEN_PAREN, openParenLoc) :+ expr :+ BelleToken(CLOSE_PAREN, closeParenLoc) =>
        if(isAccepted(expr)) ParserState(r :+ expr, st.input)
        else throw ParseException(s"Expected item surrounded by parentheses to be a parsable expression", closeParenLoc)

      case r :+ ParsedBelleExpr(e, loc) =>
        if(st.input isEmpty) ParserState(r :+ BelleAccept(e), Nil)
        else ParserState(stack :+ st.input.head, st.input.tail)

      case r :+ BelleToken(EOF, eofLoc) =>
        if(st.input isEmpty) ParserState(r, st.input)
        else throw ParseException("Internal parser error: did not expect to find EOF while input stream is unempty.", UnknownLocation)

      case Bottom =>
        if(st.input isEmpty) throw new Exception("Empty inputs are not parsable.")//ParserState(stack :+ FinalItem(), Nil) //Disallow empty inputs.
        else if(isIdent(st.input)) ParserState(stack :+ st.input.head, st.input.tail)
        else if(isOpenParen(st.input)) ParserState(stack :+ st.input.head, st.input.tail)
        else throw ParseException("Bellerophon programs should start with identifiers", st.input.head.location)
    }
  }

  //@tailrec
  private def parseLoop(st: ParserState) : ParserState = {
    if(DEBUG) println(s"Current state: ${st}")

    st.stack match {
      case _ :+ (result : FinalBelleItem) => st
      case _ => parseLoop(parseStep(st))
    }
  }

  //endregion

  //region Recognizers (i.e., predicates over the input stream that determine whether the stream matches some pattern)

  private def isIdent(toks : TokenStream) = toks match {
    case BelleToken(IDENT(_), _) :: _ => true
    case _ => false
  }

  private def isAccepted(item: BelleItem) = item match {
    case accepted : BelleAccept => true
    case _ => false
  }

  private def isOpenParen(toks : TokenStream) = toks match {
    case BelleToken(OPEN_PAREN, _) :: _ => true
    case _ => false
  }

  //endregion

  //region Constructors (i.e., functions that construct [[BelleExpr]]'s from partially parsed inputs.

  /** Constructs a tactic using the reflective expression builder. */
  private def constructTactic(name: String, args : Option[List[TacticArg]]) : BelleExpr = {
    //Turn all expressions into seqs of expressions :-(
    val newArgs = args match {
      case Some(argv) => argv.map(_ match {
        case Left(expression) => Left(Seq(expression))
        case Right(positionLocator) => Right(positionLocator)
      })
      case None => Nil
    }

    try {
      ReflectiveExpressionBuilder(name, newArgs, invariantGenerator)
    }
    catch {
      case e : ReflectiveExpressionBuilderExn => throw new ReflectiveExpressionBuilderExn(e.getMessage + s" Encountered while parsing ${name}")
    }
  }

  //endregion

  //region Ad-hoc Argument List Parser

  private type TacticArg = Either[Expression, PositionLocator]

  /**
    * An ad-hoc parser for argument lists.
    *
    * @param input A TokenStream containing: arg :: "," :: arg :: "," :: arg :: "," :: ... :: ")" :: remainder
    * @return Parsed arguments and the remainder token string.
    */
  private def parseArgumentList(input: TokenStream) : (List[TacticArg], TokenStream) = input match {
    case BelleToken(OPEN_PAREN, oParenLoc) +: rest => {
      val (argList, closeParenAndRemainder) = rest.span(tok => tok.terminal != CLOSE_PAREN)

      //Ensure we actually found a close-paren and then compute the remainder.
      if(closeParenAndRemainder isEmpty)
        throw ParseException("Expected argument list but could not find closing parenthesis.", input.head.location)
      assert(closeParenAndRemainder.head.terminal == CLOSE_PAREN)
      val remainder = closeParenAndRemainder.tail

      //Parse all the arguments.
      val arguments = removeCommas(argList, false).map(parseArgumentToken)

      (arguments, remainder)
    }
  }

  /** Takes a COMMA-delimited list of arguments and extracts only the argument tokens.
    *
    * @see parseArgumentList */
  private def removeCommas(toks: TokenStream, commaExpected: Boolean) : List[BelleToken] = toks match {
    case BelleToken(COMMA, commaPos) :: r =>
      if(commaExpected) removeCommas(r, !commaExpected)
      else throw ParseException(s"Expected argument but found comma.", commaPos)
    case BelleToken(COMMA, commaPos) :: Nil => throw ParseException("Expected argument but found none", commaPos)
    case arg :: r => arg.terminal match {
      case terminal : TACTIC_ARGUMENT => arg +: removeCommas(r, !commaExpected)
      case _ => {
        assert(!isArgument(toks.head), "Inexhautive pattern matching in removeCommas.")
        throw ParseException(s"Expected tactic argument but found ${arg.terminal.img}", arg.location)
      }
    }
    case Nil => Nil
  }

  private def parseArgumentToken(tok : BelleToken) : TacticArg = tok.terminal match {
    case terminal : TACTIC_ARGUMENT => terminal match {
      case ABSOLUTE_POSITION(posString) => Right(parseAbsolutePosition(posString, tok.location))
      case SEARCH_ANTECEDENT            => Right(Find.FindL(0, None)) //@todo 0?
      case SEARCH_SUCCEDENT             => Right(Find.FindR(0, None)) //@todo 0?
      case SEARCH_EVERYWHERE            => throw ParseException("Search Everywhere is not currently supported. Sorry!", tok.location)
      case tok : EXPRESSION       => Left(tok.expression) //@todo allow lists here as well :-(
      case _ => throw ParseException(s"Expected a tactic argument (Belle Expression or position locator) but found ${terminal.img}", tok.location)
    }
  }

  /** Parses a string of the form int.int.int.int to a Bellerophon position.
    * Public because this is a useful utility function.
    * @see [[parseArgumentToken]] */
  def parseAbsolutePosition(s : String, location: Location) : PositionLocator = {
    if(!s.contains(".")) Fixed(Position(parseNonZeroInt(s, location)))
    else {
      val subPositions = s.split('.').map(x => parseNonZeroInt(x, location))
      Fixed(Position(subPositions.head, subPositions.tail.toList))
    }
  }

  /** Parses s to a non-zero integer or else throws a ParseException pointing to location.
    *
    * @see [[parseAbsolutePosition]] */
  private def parseNonZeroInt(s: String, location: Location) =
    try {
      val pos = Integer.parseInt(s)
      if(pos == 0) throw ParseException("0 is not a valid absolute (sub)position -- must be (-inf, -1] \\cup [1, inf)", location)
      else pos
    }
    catch {
      case e : NumberFormatException => throw ParseException("Could not parse absolute position a (sequence of) integer(s)", location)
    }

  /** Argument tokens are positions and escaped expressions. */
  private def isArgument(tok: BelleToken) = tok.terminal match {
    case ABSOLUTE_POSITION(_) => true
    case SEARCH_ANTECEDENT    => true
    case SEARCH_SUCCEDENT     => true
    case SEARCH_EVERYWHERE    => true
    case EXPRESSION(_)        => true
    case _                    => false
  }

  //endregion

  //region Items processed/generated by the Bellerophon Parser

  trait BelleItem
  trait FinalBelleItem
  case class BelleToken(terminal: BelleTerminal, location: Location) extends BelleItem
  case class ParsedBelleExpr(expr: BelleExpr, loc: Location) extends BelleItem
  case class ParsedPosition(pos: Position, loc: Location) extends BelleItem
  case class BelleAccept(e: BelleExpr) extends BelleItem with FinalBelleItem
  case class BelleErrorItem(msg: String, loc: Location, state: String) extends BelleItem with FinalBelleItem

  //endregion
}
