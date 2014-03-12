package edu.cmu.cs.ls.keymaera.parser

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
  val DIVIDE:String
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
    
  val PCOMP:String
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
}

/**
 * Standard symbol table for the Parser
 */
object ParseSymbols extends KeYmaeraSymbols {
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
  val DIVIDE = "/"
  val NEGATIVE = "-"
    
  val OPEN_CBRACKET = "{"
  val CLOSE_CBRACKET = "}"
  val COMMA = ","

  //**Formulas
  val TRUE      = "⊤"
  val FALSE     = "⊥"
  val NEGATE    = "!" //¬
  val AND       = "&" //∧
  val OR        = "|" //∨
  val ARROW     = "->" //⊃

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
    
  val PCOMP    = "||" //∥
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
  
  //Abbreviations
  //Parens are always defined in the normal way..
  def paren(s:String) = "(" + s + ")" 
}
