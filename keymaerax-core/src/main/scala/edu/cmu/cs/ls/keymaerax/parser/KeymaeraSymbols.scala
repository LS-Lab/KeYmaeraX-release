/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.parser

/**
 * A list of symbols for Keymaera programs
 */
trait KeYmaeraSymbols {
  //**Terms
  val LEQ:String
  val GEQ:String
  val LT:String
  val GT:String
  val EQ:String
  val MULTIPLY:String
  val PLUS:String
  val MINUS:String
  def divide : (String, String) => String
  val NEGATIVE:String
    
  val OPEN_CBRACKET:String
  val CLOSE_CBRACKET:String
  val COMMA:String

  //**Formulas
  val TRUE:String
  val FALSE:String
  val NEGATE:String
  val AND:String
  val OR:String
  val ARROW:String
  val LARROW:String

  //** Temporal Modealities
  val BOX:String
  val DIA:String
  
  //** Dynamic Modalities
  val BOX_OPEN:String
  val BOX_CLOSE:String
  val DIA_OPEN:String
  val DIA_CLOSE:String
  
  //** Programs
  val ASSIGN :String
  val KSTAR:String
  val CHOICE:String
  val SCOLON:String
  val TEST:String
  val PRIME:String
  val START_INCOMPLETE_SYSTEM: String
  val END_INCOMPLETE_SYSTEM: String
  val CHECKED_EQ : String
    
  val PARALLEL:String
  val SEND:String
  val RECEIVE:String
  
  //Output-only program constructs
  val PCOMP_JOINED:String
  val CURSOR:String
    
  //** Provability relations
  val TUNSTILE:String
  val DTURNSTILE:String
  val EQUIV:String
  val PROGRAM_META:String
  val FORMULA_META:String
  
  //Abbreviations
  def paren(s:String):String
  
  
  val EXP:String
  val NEQ:String
  val PAIR_OPEN:String
  val PAIR_CLOSE:String
  val EXISTS:String
  val FORALL:String
  
  val FUNCTIONS_SECT:String
  val PROBLEM_SECT:String
  val EXTERNAL_FUNCTION : String
  val PVARS_SECT : String
  val START_SECT : String
  val END_SECT : String
  val VARIABLES_SECT : String
}



/**
 * Standard symbol table for the Parser
 */
object ParseSymbols extends KeYmaeraSymbols {
  
  /** Section headers */
  val FUNCTIONS_SECT = "Functions" //RigidVariables
  val PROBLEM_SECT = "Problem" //Assignables
  val VARIABLES_SECT = "Variables"
  val EXTERNAL_FUNCTION = "external"
  val PVARS_SECT = "ProgramVariables" //ProgramVariables
  val START_SECT = "."
  val END_SECT   = "End."

  /** Constants */
  //**Terms
  val LEQ = "<=" //≤
  val GEQ = ">=" //≥
  val LT = "<"
  val GT = ">"
  val EQ = "="
  val MULTIPLY = "*"
  val PLUS = "+"
  val MINUS = "-"
  val DIVIDE = "/" //We still need the symbol here because it's used by the parser.
  override def divide : (String,String) => String = (top:String, bot:String) => top + "/" + bot
  val NEGATIVE = "-"
  val EXP = "^"
  val NEQ = "!="
    
  val OPEN_CBRACKET = "{"
  val CLOSE_CBRACKET = "}"
  val COMMA = ","

  //**Formulas
  val TRUE      = "true"//"⊤"
  val FALSE     = "false"//"⊥"
  val NEGATE    = "!" //¬
  val AND       = "&" //∧
  val OR        = "|" //∨
  val ARROW     = "->" //⊃
  val LARROW    = "<-"

  //** Temporal Modealities
  val BOX    = "[]" //◻
  val DIA    = "<>" //⋄
  
  //** Dynamic Modalities
  val BOX_OPEN  = "["
  val BOX_CLOSE  = "]"
  val DIA_OPEN  = "<" //〈
  val DIA_CLOSE  = ">" //〉
  
  //** Programs
  val ASSIGN = ":="
  val KSTAR    = "*"
  val CHOICE  = "++" //∪
  val SCOLON  = ";"
  val TEST = "?"
  val PRIME = "'" //derivative of
  val START_INCOMPLETE_SYSTEM = "$$"
  val END_INCOMPLETE_SYSTEM = "$$"
  val CHECKED_EQ = "≚"
    
  val PARALLEL    = "||" //∥
  val SEND = "!"
  val RECEIVE = "?"
  
  //Output-only program constructs
  val PCOMP_JOINED = "∦" //for pretty printing.
  val CURSOR = "."
    
  //** Provability relations
  val TUNSTILE  = "⊢"
  val DTURNSTILE= "⊨"
  val EQUIV        = "<->" //"≡"
  val PROGRAM_META = "P"
  val FORMULA_META = "F"

    
  val PAIR_OPEN = "("
  val PAIR_CLOSE = ")"
    
  val EXISTS = "\\exists"
  val FORALL = "\\forall"  
  
  //Abbreviations
  //Parens are always defined in the normal way..
  def paren(s:String) = "(" + s + ")"
}


/**
 * Standard symbol table for the Parser
 */
object HTMLSymbols extends KeYmaeraSymbols {
  
  /** Section headers */
  val FUNCTIONS_SECT = "Functions" //RigidVariables
  val PROBLEM_SECT = "Problem" //Assignables
  val VARIABLES_SECT = "Variables"
  val EXTERNAL_FUNCTION = "external"
  val PVARS_SECT = "ProgramVariables" //ProgramVariables
  val START_SECT = "."
  val END_SECT   = "End."

  /** Constants */
  //**Terms
  val LEQ = "≤"
  val GEQ = "≥"
  val LT = "&lt;"
  val GT = "&gt;"
  val EQ = "="
  val MULTIPLY = "*"
  val PLUS = "+"
  val MINUS = "-"
  val DIVIDE = "/"
  override def divide : (String,String) => String = (top:String, bot:String) => top + "/" + bot
  val NEGATIVE = "-"
  val EXP = "^"
  val NEQ = "!="
    
  val OPEN_CBRACKET = "{"
  val CLOSE_CBRACKET = "}"
  val COMMA = ","

  //**Formulas
  val TRUE      = "⊤"
  val FALSE     = "⊥"
  val NEGATE    = "¬"
  val AND       = "∧"
  val OR        = "∨"
  val ARROW     = "⊃"
  val LARROW    = "<-"

  //** Temporal Modealities
  val BOX    = "◻"
  val DIA    = "⋄"
  
  //** Dynamic Modalities
  val BOX_OPEN  = "["
  val BOX_CLOSE  = "]"
  val DIA_OPEN  = "&lt;"
  val DIA_CLOSE  = "&gt;"
  
  //** Programs
  val ASSIGN = ":="
  val KSTAR    = "*"
  val CHOICE  = "∪"
  val SCOLON  = ";"
  val TEST = "?"
  val PRIME = "'" //derivative of
  //For DI on systems of differential equations.
  val START_INCOMPLETE_SYSTEM = "$$"
  val END_INCOMPLETE_SYSTEM = "$$"
  val CHECKED_EQ = "≚"

  val PARALLEL    = "∥"
  val SEND = "!"
  val RECEIVE = "?"
  
  //Output-only program constructs
  val PCOMP_JOINED = "∦" //for pretty printing.
  val CURSOR = "."
    
  //** Provability relations
  val TUNSTILE  = "⊢"
  val DTURNSTILE= "⊨"
  val EQUIV        = "≡"
  val PROGRAM_META = "P"
  val FORMULA_META = "F"

    
  val PAIR_OPEN = "("
  val PAIR_CLOSE = ")"
    
  val EXISTS = "∃"
  val FORALL = "∀"  
  
  //Abbreviations
  //Parens are always defined in the normal way..
  def paren(s:String) = "(" + s + ")" 
}

/**
 * symbol table for latex user interfaces.
 */
object LaTeXSymbols extends KeYmaeraSymbols {

  /** Section headers */
  val FUNCTIONS_SECT = "Functions" //RigidVariables
  val PROBLEM_SECT = "Problem" //Assignables
  val VARIABLES_SECT = "Variables"
  val EXTERNAL_FUNCTION = "external"
  val PVARS_SECT = "ProgramVariables" //ProgramVariables
  val START_SECT = "."
  val END_SECT   = "End."

  /** Constants */
  //**Terms
  val LEQ = "\\le" //≤
  val GEQ = "\\ge" //≥
  val LT = "<"
  val GT = ">"
  val EQ = "="
  val MULTIPLY = "*"
  val PLUS = "+"
  val MINUS = "-"
  override def divide : (String,String) => String = (top:String, bot:String) => "\\frac{" + top + "}{" + bot + "}"
  val NEGATIVE = "-"
  val EXP = "^" //I think this works out of the box, as long as groupings are also {}-grouped. 
  val NEQ = "\\ne"

  val OPEN_CBRACKET = "\\{"
  val CLOSE_CBRACKET = "\\}"
  val COMMA = ","

  //**Formulas
  val TRUE      = "\\top"//"⊤"
  val FALSE     = "\\bot"//"⊥"
  val NEGATE    = "\\neg" //¬
  val AND       = "\\land" //∧
  val OR        = "\\or" //∨
  val ARROW     = "\\rightarrow" //⊃
  val LARROW    = "\\leftarrow"

  //** Temporal Modealities
  val BOX    = "\\lbox" //◻
  val DIA    = "\\ldia" //⋄

  //** Dynamic Modalities
  val BOX_OPEN  = "["
  val BOX_CLOSE  = "]"
  val DIA_OPEN  = "\\langle" //〈
  val DIA_CLOSE  = "\\rangle" //〉

  //** Programs
  val ASSIGN = ":="
  val KSTAR    = "^*"
  val CHOICE  = "++" //∪
  val SCOLON  = ";"
  val TEST = "?"
  val PRIME = "'" //derivative of
  val START_INCOMPLETE_SYSTEM = "$$"
  val END_INCOMPLETE_SYSTEM = "$$"
  val CHECKED_EQ = "≚"

  val PARALLEL    = "\\|" //∥
  val SEND = "!"
  val RECEIVE = "?"

  //Output-only program constructs
  val PCOMP_JOINED = "\\not \\|" //for pretty printing.
  val CURSOR = "."

  //** Provability relations
  val TUNSTILE  = "⊢"
  val DTURNSTILE= "⊨"
  val EQUIV        = "\\equiv" //"≡"
  val PROGRAM_META = "P"
  val FORMULA_META = "F"


  val PAIR_OPEN = "("
  val PAIR_CLOSE = ")"

  val EXISTS = "\\exists"
  val FORALL = "\\forall"

  //put groupings around pairings so that exponentiation works currently.
  def paren(s:String) = "{(" + s + ")}"
}