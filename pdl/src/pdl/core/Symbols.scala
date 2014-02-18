package pdl.core

//object Symbols {
//  /** Constants */
//  //**Terms
//  val LEQ = "<="
//  val GEQ = ">="
//  val LT = "<"
//  val GT = ">"
//  val EQ = "="
//  val TIMES = "*"
//  val PLUS = "+"
//  val MINUS = "-"
//  val DIVIDE = "/"
//
//  //**Formulas
//  val TRUE      = "TRUE"
//  val FALSE     = "FALSE"
//  val NEGATE    = "!"
//  val AND       = "&"
//  val OR        = " OR "
//  val ARROW     = "->"
//
//  //** Temporal Modealities
//  val BOX    = "[]"
//  val DIA    = "<>"
//  
//  //** Dynamic Modalities
//  val BOX_OPEN  = "["
//  val BOX_CLOSE  = "]"
//  val DIA_OPEN  = "<"
//  val DIA_CLOSE  = ">"
//  
//  //** Programs
////  val ASSIGN  = ":="
//    val ASSIGN = ":="
//  val KSTAR    = "*"
//  val CHOICE  = "CHOICE"
//  val SCOLON  = ";"
//  val PCOMP    = "||"
//  val PDIFF    = "|/|"
//  
//  //** Provability relations
//  val TUNSTILE  = "|-"
//  val DTURNSTILE= "|="
//  val PROGRAM_META = "P"
//  val FORMULA_META = "F"
//  
//  //Abbreviations
//  //Parens are always defined in the normal way..
//  def paren(s:String) = "(" + s + ")" 
//}


object Symbols {
  /** Constants */
  //**Terms
  val LEQ = "≤"
  val GEQ = "≥"
  val LT = "<"
  val GT = ">"
  val EQ = "="
  val TIMES = "*"
  val PLUS = "+"
  val MINUS = "-"
  val DIVIDE = "/"
    
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

  //** Temporal Modealities
  val BOX    = "◻"
  val DIA    = "⋄"
  
  //** Dynamic Modalities
  val BOX_OPEN  = "["
  val BOX_CLOSE  = "]"
  val DIA_OPEN  = "〈"
  val DIA_CLOSE  = "〉"
  
  //** Programs
//  val ASSIGN  = ":="
    val ASSIGN = ":="
  val KSTAR    = "*"
  val CHOICE  = "∪"
  val SCOLON  = ";"
  val TEST = "?"
  val PRIME = "`" //derivative of
    
  val PCOMP    = "∥"
  val PDIFF    = "∦"
  val PCOMP_JOINED = PDIFF //well...
  val CURSOR = "."
  val SEND = "!"
  val RECEIVE = "?"
  
  //** Provability relations
  val TUNSTILE  = "⊢"
  val DTURNSTILE= "⊨"
  val PROGRAM_META = "P"
  val FORMULA_META = "F"
  
  //Abbreviations
  //Parens are always defined in the normal way..
  def paren(s:String) = "(" + s + ")" 
}