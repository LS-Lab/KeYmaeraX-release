package edu.cmu.cs.ls.keymaerax.bellerophon.parser

import edu.cmu.cs.ls.keymaerax.bellerophon.BelleExpr
import edu.cmu.cs.ls.keymaerax.parser.{Location, Stack}
import BelleLexer.TokenStream
import edu.cmu.cs.ls.keymaerax.tactics.Position


sealed trait Item


/**
  * The Bellerophon parser
  * @author Nathan Fulton
  */
object BelleParser extends (String => BelleExpr) {
case class BelleToken(terminal: BelleTerminal, location: Location) extends Item
case class ParsedExpr(expr: BelleExpr, loc: Location) extends Item
case class ParsedPosition(pos: Position, loc: Location) extends Item

  override def apply(s: String) = parseTokenStream(BelleLexer(s))

  def parseTokenStream(tks: TokenStream): BelleExpr = ???
//    tks match {
//    case BelleToken(IDENT(name), loc) :+ tl =>
//      if(headIsArgList(tl)) ???
//      else ???
//  }


  private def headIsArgList(toks: TokenStream) =
    toks.length >= 1 && toks.head.terminal == OPEN_PAREN && isArgument(toks.tail.head)

  /** Argument tokens are positions and escaped expressions. */
  private def isArgument(tok: BelleToken) = tok.terminal match {
    case ABSOLUTE_POSITION(_) => true
    case SEARCH_ANTECEDENT    => true
    case SEARCH_SUCCEDENT     => true
    case SEARCH_EVERYWHERE    => true
    case EXPRESSION(_)        => true
    case _                    => false
  }




}
