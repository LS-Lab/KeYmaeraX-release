/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.parser

import scala.util.matching.Regex

/**
 * Terminal symbols of the differential dynamic logic grammar.
 *
 * @author
 *   Andre Platzer
 */
sealed abstract class Terminal(val img: String) {
  override def toString: String = getClass.getSimpleName

  /** Human-readable description */
  def description: String = img

  /** @return The regex that identifies this token. */
  def regexp: scala.util.matching.Regex = img.r

  val startPattern: Regex = ("^" + regexp.pattern.pattern).r
}
private abstract class OPERATOR(val opcode: String) extends Terminal(opcode) {
  // final def opcode: String = img
  override def toString: String = getClass.getSimpleName // + "\"" + img + "\""
}
private case class IDENT(name: String, index: Option[Int] = None)
    extends Terminal(
      name +
        (index match {
          case Some(x) => "_" + x.toString
          case None => ""
        })
    ) {
  override def toString: String = "ID(\"" +
    (index match {
      case None => name
      case Some(idx) => name + "," + idx
    }) + "\")"
  override def regexp: Regex = IDENT.regexp
}
private object IDENT {
  // @note Pattern is more permissive than NamedSymbol's since Lexer's IDENT will include the index, so xy_95 is acceptable.
  def regexp: Regex = """([a-zA-Z][a-zA-Z0-9]*\_?\_?[0-9]*)""".r
  val startPattern: Regex = ("^" + regexp.pattern.pattern).r
}
private case class NUMBER(value: String) extends Terminal(value) {
  override def toString: String = "NUM(" + value + ")"
  override def regexp: Regex = NUMBER.regexp
}
private object NUMBER {
  // A bit weird, but this gives the entire number in a single group.
  // def regexp = """(-?[0-9]+\.?[0-9]*)""".r
  // @NOTE Minus sign artificially excluded from the number to make sure x-5 lexes as IDENT("x"),MINUS,NUMBER("5") not as IDENT("x"),NUMBER("-5")
  def regexp: Regex = """([0-9]+\.?[0-9]*)""".r
  val startPattern: Regex = ("^" + regexp.pattern.pattern).r
}

/** End Of Stream */
object EOF extends Terminal("<EOF>") {
  override def regexp: Regex = "$^".r // none.
}

private object LPAREN extends Terminal("(") {
  override def regexp: Regex = """\(""".r
}
private object RPAREN extends Terminal(")") {
  override def regexp: Regex = """\)""".r
}
private object LBANANA extends Terminal("(|") {
  override def regexp: Regex = """\(\|""".r
}
private object RBANANA extends Terminal("|)") {
  override def regexp: Regex = """\|\)""".r
}
private object LBRACE extends Terminal("{") {
  override def regexp: Regex = """\{""".r
}
private object RBRACE extends Terminal("}") {
  override def regexp: Regex = """\}""".r
}
private object LBARB extends Terminal("{|") {
  override def regexp: Regex = """\{\|""".r
}
private object RBARB extends Terminal("|}") {
  override def regexp: Regex = """\|\}""".r
}
private object LDDIA extends Terminal("<<") {
  override def regexp: Regex = """\<\<""".r
}
private object RDDIA extends Terminal(">>") {
  override def regexp: Regex = """\>\>""".r
}
private object LBOX extends Terminal("[") {
  override def regexp: Regex = """\[""".r
}
private object RBOX extends Terminal("]") {
  override def regexp: Regex = """\]""".r
}
private object LDIA extends OPERATOR("<") {
  override def regexp: Regex = """\<""".r
} //@todo really operator or better not?
private object RDIA extends OPERATOR(">") {
  override def regexp: Regex = """\>""".r
}

private object PRG_DEF extends OPERATOR("::=")

private object COMMA extends OPERATOR(",")
private object COLON extends OPERATOR(":")

private object PRIME extends OPERATOR("'")
private object POWER extends OPERATOR("^") {
  override def regexp: Regex = """\^""".r
}
private object STAR extends OPERATOR("*") {
  override def regexp: Regex = """\*""".r
}
private object SLASH extends OPERATOR("/")
private object PLUS extends OPERATOR("+") {
  override def regexp: Regex = """\+""".r
}
private object MINUS extends OPERATOR("-")

private object NOT extends OPERATOR("!") {
  override def regexp: Regex = """\!""".r
}
private object AMP extends OPERATOR("&")
private object OR extends OPERATOR("|") {
  override def regexp: Regex = """\|""".r
}
private object EQUIV extends OPERATOR("<->")
private object EQUIV_UNICODE extends OPERATOR("↔")
private object IMPLY extends OPERATOR("->")
private object IMPLY_UNICODE extends OPERATOR("→")

//@todo maybe could change to <-- to disambiguate poor lexer's x<-7 REVIMPLY from LDIA MINUS
private object REVIMPLY extends OPERATOR("<-")
private object REVIMPLY_UNICODE extends OPERATOR("←")

private object FORALL extends OPERATOR("\\forall") {
  override def regexp: Regex = """\\forall """.r
}
private object EXISTS extends OPERATOR("\\exists") {
  override def regexp: Regex = """\\exists """.r
}

private object EQ extends OPERATOR("=")
private object NOTEQ extends OPERATOR("!=") {
  override def regexp: Regex = """\!=""".r
}
private object GREATEREQ extends OPERATOR(">=")
private object LESSEQ extends OPERATOR("<=")

//Unicode versions of operators:
private object LESSEQ_UNICODE extends OPERATOR("≤")
private object GREATEREQ_UNICODE extends OPERATOR("≥")
private object AND_UNICODE extends OPERATOR("∧")
private object OR_UNICODE extends OPERATOR("∨")
private object UNEQUAL_UNICODE extends OPERATOR("≠")
private object FORALL_UNICODE extends OPERATOR("∀")
private object EXISTS_UNICODE extends OPERATOR("∃")

private object TRUE extends OPERATOR("true")
private object FALSE extends OPERATOR("false")

//@todo should probably also allow := *
private object ASSIGNANY extends OPERATOR(":=*") {
  override def regexp: Regex = """:=\*""".r
}
private object ASSIGN extends OPERATOR(":=")
private object TEST extends OPERATOR("?") {
  override def regexp: Regex = """\?""".r
}
private object IF extends OPERATOR("if")
private object ELSE extends OPERATOR("else")
private object SEMI extends OPERATOR(";")
private object CHOICE extends OPERATOR("++") {
  override def regexp: Regex = """\+\+|∪""".r
}
//@todo simplify lexer by using silly ^@ notation rather than ^d for now. @ for adversary isn't too bad to remember but doesn't look as good as ^d.
private object DUAL extends OPERATOR("^@") {
  override def regexp: Regex = """\^\@""".r
}
private object DCHOICE extends OPERATOR("∩") {
  override def regexp: Regex = """∩""".r
}
private object DSTAR extends OPERATOR("×") {
  override def regexp: Regex = """×""".r
}

private object TILDE extends OPERATOR("~")
private object BACKSLASH extends Terminal("\\\\")
private object QUOTATION_MARK extends Terminal("\"")

/** Separates formulas in stored provables. */
private object FORMULA_SEPARATOR extends OPERATOR("::") {
  override def regexp: Regex = """::[^=]""".r // @note disambiguate from ::= [[PRG_DEF]]
}

/** Separates sequents in stored provables. */
private object FROM extends OPERATOR("\\from") {
  override def regexp: Regex = """\\from""".r
}

/** Separates stored provables. */
private object QED extends OPERATOR("\\qed") {
  override def regexp: Regex = """\\qed""".r
}

/*@TODO
private object DCHOICE  extends OPERATOR("--") {
  override def regexp = """--""".r
}
 */

// pseudos: could probably demote so that some are not OPERATOR
private object NOTHING extends Terminal("")

private case class DOT(index: Option[Int] = None)
    extends Terminal(
      "•" +
        (index match {
          case Some(x) => "_" + x
          case None => ""
        })
    ) {
  override def toString: String = "DOT(\"" +
    (index match {
      case None => ""
      case Some(idx) => idx
    }) + "\")"
  override def regexp: Regex = DOT.regexp
}
private object DOT {
  def regexp: Regex = """((?:•(?:\_[0-9]+)?)|(?:\.\_[0-9]+))""".r
  val startPattern: Regex = ("^" + regexp.pattern.pattern).r
}

private object PLACE extends OPERATOR("⎵") //("_")
private object ANYTHING extends OPERATOR("??") {
  override def regexp: Regex = """\?\?""".r
}
private object PSEUDO extends Terminal("<pseudo>")

private object EXERCISE_PLACEHOLDER extends Terminal("__________")

// @annotations

private object INVARIANT extends Terminal("@invariant") {
  override def regexp: Regex = """\@invariant""".r
}

private object VARIANT extends Terminal("@variant") {
  override def regexp: Regex = """\@variant""".r
}

// axiom and problem file

private object AXIOM_BEGIN extends Terminal("Axiom") {
  override def regexp: Regex = """Axiom""".r
}
private object END_BLOCK extends Terminal("End")
private case class DOUBLE_QUOTES_STRING(var s: String) extends Terminal("<string>") {
  override def regexp: Regex = DOUBLE_QUOTES_STRING_PAT.regexp
}
private object DOUBLE_QUOTES_STRING_PAT {
  // everything between "...", allows line breaks, \, and escaped \" as content
  def regexp: Regex = """"(([^\\"]*|\\.)*)"""".r
  val startPattern: Regex = ("^" + regexp.pattern.pattern).r
}
private object PERIOD extends Terminal(".") {
  override def regexp: Regex = "\\.".r
}
private object FUNCTIONS_BLOCK extends Terminal("Functions") {
  // not totally necessary -- you'll still get the right behavior because . matches \. But also allows stuff like Functions: which maybe isn't terrible.
//  override def regexp = """Functions\.""".r
}
private object DEFINITIONS_BLOCK extends Terminal("Definitions")
private object PROGRAM_VARIABLES_BLOCK extends Terminal("ProgramVariables")
private object VARIABLES_BLOCK extends Terminal("Variables") //used in axioms file...
private object PROBLEM_BLOCK extends Terminal("Problem")
private object TACTIC_BLOCK extends Terminal("Tactic")
private object IMPLICIT extends Terminal("implicit")
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
private object SEQUENT_BEGIN extends Terminal("Sequent") {
  override def regexp: Regex = """Sequent""".r
}
private object TURNSTILE extends Terminal("==>") {
  override def regexp: Regex = """==>""".r
}
private object FORMULA_BEGIN extends Terminal("Formula") {
  override def regexp: Regex = """Formula""".r
}

///////////
// Section: Terminal signals for tool files.
///////////
private object LEMMA_BEGIN extends Terminal("Lemma") {
  override def regexp: Regex = """Lemma""".r
}
private object TOOL_BEGIN extends Terminal("Tool") {
  override def regexp: Regex = """Tool""".r
}
private case class TOOL_VALUE(var s: String) extends Terminal("<string>") {
  override def regexp: Regex = TOOL_VALUE_PAT.regexp
}
private object TOOL_VALUE_PAT {
  // values are nested into quadruple " and set apart with spaces (not until 4.9.3, so for backwards-compatibility we do
  // not insist on presence of spaces), because they can contain and end in single, double, or triple " themselves
  def regexp: Regex = "\"{4}([\\s\\S]*?)\"{4}".r
  val startPattern: Regex = ("^" + regexp.pattern.pattern).r
}

private object SHARED_DEFINITIONS_BEGIN extends Terminal("SharedDefinitions") {}

private case class ARCHIVE_ENTRY_BEGIN(name: String) extends Terminal("ArchiveEntry|Lemma|Theorem|Exercise") {
  override def toString: String = name
  override def regexp: Regex = ARCHIVE_ENTRY_BEGIN.regexp
}
private object ARCHIVE_ENTRY_BEGIN {
  def regexp: Regex = "(ArchiveEntry|Lemma|Theorem|Exercise)".r
  val startPattern: Regex = ("^" + regexp.pattern.pattern).r
}

///////////
// Section: Terminal signals for tactics.
///////////
private object BACKTICK extends Terminal("`") {}
