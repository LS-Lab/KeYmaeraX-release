package pdl.core

object Symbols {
  /** Constants */
  //**Terms
  val LEQ = "<=" //≤
  val GEQ = ">=" //≥
  val LT = "<"
  val GT = ">"
  val EQ = "="
  val TIMES = "*"
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