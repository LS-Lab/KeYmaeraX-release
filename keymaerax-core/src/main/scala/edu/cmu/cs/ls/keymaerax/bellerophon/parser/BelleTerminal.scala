package edu.cmu.cs.ls.keymaerax.bellerophon.parser

import edu.cmu.cs.ls.keymaerax.bellerophon.PositionLocator
import edu.cmu.cs.ls.keymaerax.core.{Expression, Formula, Program, SubstitutionPair, Term}
import edu.cmu.cs.ls.keymaerax.infrastruct.{FormulaTools, PosInExpr}
import edu.cmu.cs.ls.keymaerax.parser.{LexException, Parser, UnknownLocation}

import scala.util.matching.Regex

private object PSEUDO  extends BelleTerminal("<pseudo>")

sealed abstract class BelleTerminal(val img: String, val postfix: String = "") {
  assert(img != null)

  override def toString: String = getClass.getSimpleName// + "\"" + img + "\""
  /**
    * @return The regex that identifies this token.
    */
  def regexp: scala.util.matching.Regex = img.r
  val startPattern: Regex = ("^" + regexp.pattern.pattern + postfix).r
}

private case class IDENT(name: String) extends BelleTerminal(name) {
  assert(name != "USMatch" && name.toLowerCase != "partial")
  override def toString = s"IDENT($name)"
}
private object IDENT {
  def regexp: Regex = """([a-zA-Z][a-zA-Z0-9]*)""".r
  //"[\\p{Alpha}\\p{Alnum}]*".r
  val startPattern: Regex = ("^" + regexp.pattern.pattern).r
}


// Combinator Tokens
object SEQ_COMBINATOR extends BelleTerminal(";") {
  override def regexp: Regex = ";".r
}

private object DEPRECATED_SEQ_COMBINATOR extends BelleTerminal("&") {
  override def regexp: Regex = "\\&".r
}

private object EITHER_COMBINATOR extends BelleTerminal("|") {
  override def regexp: Regex = "\\|".r
}

object BRANCH_COMBINATOR extends BelleTerminal("<")

private object ON_ALL extends BelleTerminal("doall")

private object KLEENE_STAR extends BelleTerminal("*") {
  override def regexp: Regex = "\\*".r
}

private object SATURATE extends BelleTerminal("+") {
  override def regexp: Regex = "\\+".r
}

private object OPTIONAL extends BelleTerminal("?") {
  override def regexp: Regex = "\\?".r
}

private case class N_TIMES(n:Int) extends BelleTerminal(s"*$n") {
  assert(n >= 0)
  override def toString = s"NTIMES($n)"
  override def regexp: Regex = s"\\*$n".r
}
private object N_TIMES {
  def regexp: Regex  = """(\*\d+)""".r
  def startPattern: Regex = ("^" + regexp.pattern.pattern).r
}


private object US_MATCH extends BelleTerminal("USMatch")

private object LET extends BelleTerminal("let", "[\\s]")

private object IN extends BelleTerminal("in", "[\\s]")

private object TACTIC extends BelleTerminal("tactic", "[\\s]")

private object AS extends BelleTerminal("as", "[\\s]")

private object EXPAND extends BelleTerminal("expand")

private object EXPANDALLDEFS extends BelleTerminal("expandAllDefs")

private object USING extends BelleTerminal("using")

private object RIGHT_ARROW extends BelleTerminal("=>")

// Separation/Grouping Tokens
private object OPEN_PAREN extends BelleTerminal("(") {
  override def regexp: Regex = "\\(".r
}
private object CLOSE_PAREN extends BelleTerminal(")") {
  override def regexp: Regex = "\\)".r
}
private object COMMA extends BelleTerminal(",")

private object COLON extends BelleTerminal(":")

private trait TACTIC_ARGUMENT

// Positions
private abstract class BASE_POSITION(val positionString: String) extends BelleTerminal(positionString) with TACTIC_ARGUMENT
private case class ABSOLUTE_POSITION(override val positionString: String) extends BASE_POSITION(positionString) {
  override def regexp: Regex = ABSOLUTE_POSITION.regexp
  override val startPattern: Regex = ABSOLUTE_POSITION.startPattern
  override def toString = s"ABSOLUTE_POSITION($positionString)"
}
private object ABSOLUTE_POSITION {
  def regexp: Regex = """(-?\d+(?:\.\d+)*)""".r
  val startPattern: Regex = ("^" + regexp.pattern.pattern).r
}
private case class LAST_SUCCEDENT(override val positionString: String) extends BASE_POSITION(positionString) {
  override def regexp: Regex = LAST_SUCCEDENT.regexp
  override val startPattern: Regex = LAST_SUCCEDENT.startPattern
  override def toString: String = s"LAST_SUCCEDENT($positionString)"
}
private object LAST_SUCCEDENT {
  def regexp: Regex = """('Rlast(?:\.\d+)*)""".r
  val startPattern: Regex = ("^" + regexp.pattern.pattern).r
}
private case class LAST_ANTECEDENT(override val positionString: String) extends BASE_POSITION(positionString) {
  override def regexp: Regex = LAST_ANTECEDENT.regexp
  override val startPattern: Regex = LAST_ANTECEDENT.startPattern
  override def toString: String = s"LAST_ANTECEDENT($positionString)"
}
private object LAST_ANTECEDENT {
  def regexp: Regex = """('Llast(?:\.\d+)*)""".r
  val startPattern: Regex = ("^" + regexp.pattern.pattern).r
}
private case class SEARCH_SUCCEDENT(override val positionString: String) extends BASE_POSITION(positionString) {
  override def regexp: Regex = SEARCH_SUCCEDENT.regexp
  override val startPattern: Regex = SEARCH_SUCCEDENT.startPattern
  override def toString: String = s"SEARCH_SUCCEDENT($positionString)"
}
private object SEARCH_SUCCEDENT {
  def regexp: Regex = """('R(?:\.\d+)*)""".r
  val startPattern: Regex = ("^" + regexp.pattern.pattern).r
}
private case class SEARCH_ANTECEDENT(override val positionString: String) extends BASE_POSITION(positionString) {
  override def regexp: Regex = SEARCH_ANTECEDENT.regexp
  override val startPattern: Regex = SEARCH_ANTECEDENT.startPattern
  override def toString: String = s"SEARCH_ANTECEDENT($positionString)"
}
private object SEARCH_ANTECEDENT {
  def regexp: Regex = """('L(?:\.\d+)*)""".r
  val startPattern: Regex = ("^" + regexp.pattern.pattern).r
}
private case class SEARCH_EVERYWHERE(override val positionString: String) extends BASE_POSITION(positionString) {
  override def regexp: Regex = SEARCH_EVERYWHERE.regexp
  override val startPattern: Regex = SEARCH_EVERYWHERE.startPattern
  override def toString: String = s"SEARCH_EVERYWHERE($positionString)"
}
private object SEARCH_EVERYWHERE {
  def regexp: Regex = """('_(?:\.\d+)*)""".r
  val startPattern: Regex = ("^" + regexp.pattern.pattern).r
}
private object EXACT_MATCH extends BelleTerminal("==") with TACTIC_ARGUMENT
private object UNIFIABLE_MATCH extends BelleTerminal("~=") with TACTIC_ARGUMENT

private object PARTIAL extends BelleTerminal("partial") {
  override def regexp: Regex = "(?i)partial".r // allow case-insensitive use of the word partial.
}

/** A tactic argument expression. We allow strings, terms, and formulas as arguments. */
private abstract class BELLE_EXPRESSION(val exprString: String, val delimiters: (String, String)) extends BelleTerminal(exprString) with TACTIC_ARGUMENT {
  lazy val undelimitedExprString: String = exprString.stripPrefix(delimiters._1).stripSuffix(delimiters._2).
    // un-escape escaped delimiters
    replaceAllLiterally("\\" + delimiters._1, delimiters._1).
    replaceAllLiterally("\\" + delimiters._2, delimiters._2)

  override def regexp: Regex = BELLE_EXPRESSION.regexp
  override val startPattern: Regex = BELLE_EXPRESSION.startPattern

  override def toString = s"EXPRESSION($exprString)"

  override def equals(other: Any): Boolean = other match {
    case be: BELLE_EXPRESSION => be.exprString == exprString
    case _ => false
  }
}

private case class EXPRESSION(override val exprString: String, override val delimiters: (String, String)) extends BELLE_EXPRESSION(exprString, delimiters) {
  /** Parses the `exprString` as dL expression. May throw a parse exception. */
  def expression: Expression = {
    assert(exprString.startsWith(delimiters._1) && exprString.endsWith(delimiters._2),
      s"EXPRESSION.regexp should ensure delimited expression begin and end with $delimiters, but an EXPRESSION was constructed with argument: $exprString")
    Parser.parser(undelimitedExprString)
  }
}

private case class SUBSTITUTION_PAIR(override val exprString: String, override val delimiters: (String, String)) extends BELLE_EXPRESSION(exprString, delimiters) {
  /** Parses the `exprString` as dL substitution pair. May throw a parse exception. */
  def expression: SubstitutionPair = {
    import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
    assert(exprString.startsWith(delimiters._1) && exprString.endsWith(delimiters._2),
      s"EXPRESSION.regexp should ensure delimited expression begin and end with $delimiters, but an EXPRESSION was constructed with argument: $exprString")
    undelimitedExprString.asSubstitutionPair
  }
}

private case class EXPRESSION_SUB(override val exprString: String, override val delimiters: (String, String)) extends BELLE_EXPRESSION(exprString, delimiters) {
  /** Parses the `exprString` as dL expression and sub-position. May throw a parse exception. */
  def expression: (Expression, PosInExpr) = {
    assert(exprString.startsWith(delimiters._1) && exprString.endsWith(delimiters._2),
      s"EXPRESSION.regexp should ensure delimited expression begin and end with $delimiters, but an EXPRESSION was constructed with argument: $exprString")
    val subStart = undelimitedExprString.indexOf('#')+1
    val subEnd = undelimitedExprString.lastIndexOf('#')
    assert(subStart >= 1 && subEnd > subStart, "Non-empty sub-position marker expected")
    val subString = undelimitedExprString.slice(subStart, subEnd)
    val sub = Parser(subString)
    val (expr, inExpr) =
      if (undelimitedExprString.indexOf(subString) != subStart) {
        // marked sub-expression is not leftmost in expr, mark with "hash" placeholders
        val (markedStr, placeholder) = PositionLocator.withMarkers(undelimitedExprString, sub, subStart - 1, subEnd - subStart + 2)
        val expr = Parser(markedStr)
        (Parser(PositionLocator.replaceHashesParenthesized(undelimitedExprString, sub.kind)), FormulaTools.posOf(expr, placeholder))
      } else {
        val expr = Parser(PositionLocator.replaceHashesParenthesized(undelimitedExprString, sub.kind))
        (expr, FormulaTools.posOf(expr, sub))
      }

    (expr, inExpr.getOrElse(throw LexException("Sub-expression " + subString + " does not exist in " + undelimitedExprString, UnknownLocation)))
  }
}

private object BELLE_EXPRESSION {
  def regexp: Regex = """(\{`[\s\S]*?`})|("(?:[^\\"]*(?:\\.)?)*")""".r // allows \" inside "..."
  val startPattern: Regex = ("^" + regexp.pattern.pattern).r

  def apply(exprString: String, delimiters: (String, String)): BELLE_EXPRESSION = {
    //@todo detect strings that are neither substitution pairs nor expressions (for now they're misclassified depending on content)
    if (exprString.contains("~>")) SUBSTITUTION_PAIR(exprString, delimiters)
    else if (exprString.contains("#")) EXPRESSION_SUB(exprString, delimiters)
    else EXPRESSION(exprString, delimiters)
  }
}

object EOF extends BelleTerminal("<EOF>") {
  override def regexp: Regex = "$^".r //none.
}
