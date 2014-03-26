package edu.cmu.cs.ls.keymaera.parser

import scala.util.parsing.combinator._
import scala.util.parsing.combinator.lexical._
import scala.util.parsing.combinator.syntactical._
import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.core.Add

import scala.util.matching.Regex

import scala.annotation.elidable
import scala.annotation.elidable._


/**
 * The KeYmaera Parser
 * @author Nathan Fulton
 */
class KeYmaeraParser extends RegexParsers with PackratParsers {    
  //////////////////////////////////////////////////////////////////////////////
  // Public-facing interface.
  //////////////////////////////////////////////////////////////////////////////

  def parse(s:String):Expr = {
    val parser = new KeYmaeraParser()
    
    //Parse file.
    val (functions,predicateConstants,variables,problemText) = 
      parser.parseAll(parser.fileParser, s) match {
        case parser.Success(result,next) => result
        case parser.Failure(_,_) => throw new Exception("parse failed.")
        case parser.Error(_,_) => throw new Exception("parse error.")
      }
    
    
    val programs = List[ProgramConstant]() //TODO support these.
    
    //Parse the problem.
    val exprParser = parser.makeExprParser(variables, functions, predicateConstants,programs)
    val parseResult = parser.parseAll(exprParser, problemText) match {
        case parser.Success(result,next) => result
        case parser.Failure(_,_) => throw new Exception("parse failed.")
        case parser.Error(_,_) => throw new Exception("parse error.")
    }
    
    //Ensure that parse( print(parse(problemText)) ) = parse(problemText)
    val printOfParse = KeYmaeraPrettyPrinter.stringify(parseResult)
    checkParser(functions, predicateConstants, variables, programs,parseResult,printOfParse)
    
    parseResult
  }
  
  /**
   * Ensures that parse( print(parse(input)) ) = parse(input)
   */
  @elidable(ASSERTION) 
  def checkParser(functions:List[Function],
    predicateConstants:List[PredicateConstant],
    variables:List[Variable],
    programVariables:List[ProgramConstant],
    parse:Expr,
    printOfParse:String) = 
  {
    val parser = new KeYmaeraParser()
    val exprParser = parser.makeExprParser(variables, functions, predicateConstants,programVariables)
    val printofparseParse = parser.parseAll(exprParser, printOfParse) match {
        case parser.Success(result,next) => result
        case parser.Failure(_,_) => throw new Exception("parse failed.")
        case parser.Error(_,_) => throw new Exception("parse error.")
    }

    require(parse.equals(printofparseParse), "Parse not equals parse(pp(parse(_)))" )
  }
   
  import edu.cmu.cs.ls.keymaera.parser.ParseSymbols._
  
  type Tokens = StdLexical
  
  //////////////////////////////////////////////////////////////////////////////
  // Primitive syntactic constructs
  //////////////////////////////////////////////////////////////////////////////
  
  protected override val whiteSpace = 
    """(\s|(?m)\(\*(\*(?!/)|[^*])*\*\)|/\*(.)*?\*/|\/\*[\w\W\s\S\d\D]+?\*\/)+""".r
  protected val space               = """[\ \t\n]*""".r
  
  /**
   * ``ident" should match function, variable and sort names.
   */
  protected val ident               = """[a-zA-Z][a-zA-Z0-9\_]*""".r
  
  val lexical = new StdLexical
  //TODO should we add the rest of the \\'s to the delimiters list?
  lexical.delimiters ++= List("\\functions", "{", "}", "(", ")", "+", "-", "*", "/")
  
  //////////////////////////////////////////////////////////////////////////////
  // Function Definition Section.
  //////////////////////////////////////////////////////////////////////////////

  /**
   * @returns A list of defined function sorts.
   */
  lazy val functionsP = {
    lazy val pattern = "\\functions" ~ "{" ~ rep1sep(funcdefP, ";") ~ ";".? ~ "}" 
    log(pattern)("Functions section") ^^ {
      case  "\\functions" ~ "{" ~ definitions ~ extraScolon ~ "}" => definitions
    }
  }

  //TODO-nrf throwing away the external annotation. Is this ok?
  lazy val funcdefP = "\\external".?  ~ ident ~ ident ~ ("(" ~ rep1sep(ident, ",") ~ ")").? ^^ {
    case external ~ rsort ~ name ~ tail =>
      tail match {
        case Some(_ ~ argsorts ~ _) => Function(name, None, identsToSorts(argsorts), identToSort(rsort))
        case None =>  PredicateConstant(name)
      }
  }
  
  //////////////////////////////////////////////////////////////////////////////
  // State Variable Definition Section.
  //////////////////////////////////////////////////////////////////////////////

  /**
   * @returns A list of defined program sorts.
   */
  lazy val programVariablesP = {
    lazy val pattern = "\\programVariables" ~ "{" ~ rep1sep(vardefP, ";") ~ ";".? ~ "}"
    
    log(pattern)("\\programVariables section.") ^^ {
      case "\\programVariables" ~ "{" ~ variables ~ extraScolon ~ "}" => variables
    }
  }

  lazy val vardefP = ident ~ ident ^^ {
    //Note: it might be necessary to give these arguments indices.
    case rsort ~ name => Variable(name, None, identToSort(rsort))
  }

  //////////////////////////////////////////////////////////////////////////////
  // Problem Section.
  //////////////////////////////////////////////////////////////////////////////
  lazy val problemP = {
    lazy val pattern = "\\problem" ~ "{" ~> """[\w\W\s\S\d\D]+}""".r 
    log(pattern)("\\problem section (extract a string)") ^^ {
      case programText => programText.substring(0, programText.length()-1) //remove trailig }
    }
  } 
    
  lazy val fileParser = functionsP.? ~ programVariablesP.? ~ problemP ^^ {
    case functionSection ~ programVarsSection ~ problemText => {
      val functions:List[Function] = functionSection match {
        case Some(l) => l.filter(_.isInstanceOf[Function]).map(_.asInstanceOf[Function])
        case None    => List[Function]()
      }
      val predicateConstants:List[PredicateConstant] = functionSection match {
        case Some(l) => l.filter(_.isInstanceOf[PredicateConstant]).map(_.asInstanceOf[PredicateConstant])
        case None    => List[PredicateConstant]()
      }
      val variables:List[Variable] = programVarsSection match {
        case Some(l) => l
        case None    => List[Variable]()
      }
      (functions,predicateConstants,variables,problemText)
    }
  }
 
  /* ***************************************************************************
   * Begin parsing actual programs and formulas.
   * **************************************************************************/
  
  //////////////////////////////////////////////////////////////////////////////
  // Terms.
  //////////////////////////////////////////////////////////////////////////////
  class TermParser(variables:List[Variable], functions:List[Function]) {
    type SubtermParser = PackratParser[Term]
    
    //TODO-nrf Some of these parsers assign sorts somewhat arbitrarily, and I'm
    //not sure about the correct thing to do. see e.g. subtractP.
    lazy val parser = precedence.reduce(_|_)
    
    val precedence : List[SubtermParser] =
      expP ::
      multiplyP ::
      divP ::
      addP ::
      subtractP ::
      negativeP ::
      applyP ::
      termDerivativeP ::
      variableP ::
      numberP   ::
      groupP    ::
      Nil
    
      
    //variable parser
    lazy val variableP:PackratParser[Term] = {
      lazy val pattern = {
        val stringList =  variables.map(Variable.unapply(_) match {
          case Some(t) => t._1
          case None => ???
        })
        if(stringList.isEmpty) { """$^""".r/*match nothing.*/ }
        else new scala.util.matching.Regex( stringList.reduce(_+"|"+_) )
      }
      
      log(pattern)("Variable") ^^ {
        case name => {
          variables.find(Variable.unapply(_) match {
            case Some(p) => p._1.equals(name)
            case None => false
          }) match {
            case Some(p) => p
            case None => 
              throw new Exception("Predicate was mentioned out of context: " + name)
          }
        }
      } 
    }
    
    lazy val termDerivativeP:SubtermParser = {
      lazy val pattern = tighterParsers(precedence, termDerivativeP).reduce(_|_)
      log(pattern ~ PRIME)(PRIME + " parser") ^^ {
        case t ~ PRIME => new Derivative(t.sort, t)
      }
    }
    
    //Compound terms
      
    lazy val multiplyP:SubtermParser = {
      lazy val pattern = leftAssociative(precedence, multiplyP, Some(MULTIPLY))
      log(pattern)("Multiplication") ^^ {
        case left ~ MULTIPLY ~ right => Multiply(left.sort, left,right)
      }
    }
    lazy val divP:SubtermParser = {
      lazy val pattern = leftAssociative(precedence, divP, Some(DIVIDE))
      log(pattern)("Division") ^^ {
        case left ~ DIVIDE ~ right => Divide(left.sort, left,right)
      }
    }
    
    lazy val expP:SubtermParser = {
      lazy val pattern = parser ~ EXP ~ parser //?
      log(pattern)("Exponentiation") ^^ {
        case left ~ EXP ~ right => Exp(left.sort, left,right)
      }
    }
    lazy val addP:SubtermParser = {
      lazy val pattern = leftAssociative(precedence, addP, Some(PLUS))
      log(pattern)("Addition") ^^ {
        case left ~ PLUS ~ right => Add(left.sort, left,right)
      }
    }
    lazy val subtractP:SubtermParser = {
      lazy val pattern = leftAssociative(precedence, subtractP, Some(MINUS))
      log(pattern)("Subtract") ^^ {
        case left ~ MINUS ~ right => Subtract(left.sort, left,right)
      }
    }
    
    //Unary term operators
    
    lazy val negativeP:SubtermParser = {
      lazy val pattern = NEGATIVE ~ asTightAsParsers(precedence, negativeP).reduce(_|_)
      log(pattern)("negate") ^^ {
        case NEGATIVE ~ term => Neg(term.sort, term)
      }
    }
    
    //Function application
    
    lazy val applyP:SubtermParser = {      
      lazy val pattern = ident ~ "(" ~ rep1sep(tighterParsers(precedence,applyP).reduce(_|_), ",") ~ ")"
      
      log(pattern)("Function Application") ^^ {
        case name ~ "(" ~ args ~ ")" => 
          Apply(functionFromName(name, functions), 
              args.reduce( (l,r) => Pair( TupleT(l.sort,r.sort), l, r) ) )
      }
    }

    //Groupings
    
    lazy val groupP:SubtermParser = {
      lazy val pattern = "(" ~ precedence.reduce(_|_) ~ ")"
      log(pattern)("Subterm Grouping") ^^ {
        case "(" ~ p ~ ")" => p
      }
    }
    
    //Numbers
    
    lazy val numberP:SubtermParser = {
      lazy val pattern = """[0-9]+(\.[0-9]+)?""".r
      log(pattern)("NUMBER") ^^ {
        case n => Number(BigDecimal(n))
      }
    }
  }
  
  //////////////////////////////////////////////////////////////////////////////
  // Formulas.
  //////////////////////////////////////////////////////////////////////////////
  class FormulaParser(variables:List[Variable],
      functions:List[Function],
      predicates:List[PredicateConstant],
      programVariables:List[ProgramConstant]) 
  {
    type SubformulaParser = PackratParser[Formula]
    
    lazy val programParser = 
      new ProgramParser(variables,functions,predicates,programVariables).parser
    
    lazy val parser = precedence.reduce(_|_)
    
    val precedence : List[SubformulaParser] =
      implP  ::
      boxP   ::
      diamondP ::
      orP ::
      andP ::
      equivP ::
      equalsP ::
      leP    ::
      geP    ::
      gtP    ::
      ltP    ::  // magic alert: tightestComparisonOperator is the tightest comparison operator.
      notP ::
      formulaDerivativeP ::
      predicateP ::
      trueP ::
      falseP ::
      groupP ::
      Nil
    
      
   lazy val variableP:PackratParser[Term] = {
      lazy val pattern = {
        val stringList =  variables.map(Variable.unapply(_) match {
          case Some(t) => t._1
          case None => ???
        })
        if(stringList.isEmpty) { """$^""".r/*match nothing.*/ }
        else new scala.util.matching.Regex( stringList.reduce(_+"|"+_) )
      }
      
      log(pattern)("Variable") ^^ {
        case name => {
          variables.find(Variable.unapply(_) match {
            case Some(p) => p._1.equals(name)
            case None => false
          }) match {
            case Some(p) => p
            case None => 
              throw new Exception("Predicate was mentioned out of context: " + name)
          }
        }
      } 
    }
      
    val tightestComparisonOperator = ltP
    val tighterThanComparison = tighterParsers(precedence, tightestComparisonOperator).reduce(_|_)
    
    //Modalities
    lazy val boxP : SubformulaParser = {
      lazy val pattern = BOX_OPEN ~ 
    		  			 programParser ~ 
    		  			 BOX_CLOSE ~ 
    		  			 tighterParsers(precedence, boxP).reduce(_|_)
      log(pattern)(BOX_OPEN + PROGRAM_META + BOX_CLOSE + FORMULA_META) ^^ {
        case BOX_OPEN ~ p ~ BOX_CLOSE ~ f => println("here!");BoxModality(p,f)
      }
    }
    
    lazy val diamondP : SubformulaParser = {
      lazy val pattern = DIA_OPEN ~ programParser ~ DIA_CLOSE ~ tighterParsers(precedence, diamondP).reduce(_|_)
      log(pattern)(DIA_OPEN + PROGRAM_META + DIA_CLOSE + FORMULA_META) ^^ {
        case DIA_OPEN ~ p ~ DIA_CLOSE ~ f => DiamondModality(p,f)
      }
    }
    
    //Predicates
    lazy val predicateP:SubformulaParser = {
      lazy val pattern = {
        val stringList =  predicates.map(PredicateConstant.unapply(_) match {
          case Some(t) => t._1
          case None => ???
        })
        if(stringList.isEmpty) { """$^""".r/*match nothing.*/ }
        else new scala.util.matching.Regex( stringList.reduce(_+"|"+_) )
      }
      
      log(pattern)("Predicate") ^^ {
        case name => {
          predicates.find(PredicateConstant.unapply(_) match {
            case Some(p) => p._1.equals(name)
            case None => false
          }) match {
            case Some(p) => p
            case None => 
              throw new Exception("Predicate was mentioned out of context: " + name)
          }
        }
      } 
    }

    //Unary Formulas
    
    lazy val notP:SubformulaParser = {
      lazy val pattern = NEGATE ~ tighterParsers(precedence, notP).reduce(_|_)
      log(pattern)(NEGATE) ^^ {
        case NEGATE ~ f => Not(f.asInstanceOf[Formula])
      }
    }
    
    lazy val formulaDerivativeP:SubformulaParser = {
      log(tighterParsers(precedence, formulaDerivativeP).reduce(_|_) ~ PRIME)("Formula derivative") ^^ {
        case v ~ PRIME => new FormulaDerivative(v)
      }
    }
    
    
    //Binary Formulas
    
    lazy val equivP:SubformulaParser = {
      lazy val pattern = 
        (tighterThanComparison) ~ 
        EQUIV ~
        (tighterThanComparison)
        
      log(pattern)(EQUIV) ^^ {
        case left ~ _ ~ right => Equiv(left,right)
      }
    }
    
    
    lazy val equalsP:SubformulaParser = {
      lazy val pattern = 
        (tighterThanComparison|termParser) ~ 
        EQ ~
        (tighterThanComparison|termParser)
        
      log(pattern)(EQ + " formula parser") ^^ {
        case left ~ _ ~ right => {
          if(left.isInstanceOf[Term] && right.isInstanceOf[Term])
            Equals(right.sort,left.asInstanceOf[Term],right.asInstanceOf[Term])
          else
            ??? //Probably a parse failure.
        }
      }
    }
    
    lazy val implP:SubformulaParser = {
      lazy val pattern = rightAssociative(precedence, implP, Some(ARROW))
      log(pattern)(ARROW) ^^ {
        case left ~ _ ~ right => Imply(left,right)
      }
    }
    
    lazy val andP : SubformulaParser = {
      lazy val pattern = leftAssociative(precedence, andP, Some(AND))
      log(pattern)(AND + " parser") ^^ {
        case left ~ _ ~ right => And(left,right)
      }
    }
    
    lazy val orP : SubformulaParser = {
      lazy val pattern = leftAssociative(precedence, orP, Some(OR))
      log(pattern)(OR + " parser") ^^ {
        case left ~ _ ~ right => Or(left,right)
      }
    }
    //Binary Relations

    lazy val termParser = new TermParser(variables,functions).parser
    
    lazy val leP:SubformulaParser = {
      lazy val pattern = termParser ~ LEQ ~ termParser
      log(pattern)(LEQ) ^^ {
        case left ~ LEQ ~ right =>  
          LessEquals(left.sort,left,right)
      }
    }
    
    lazy val geP:SubformulaParser = {
      lazy val pattern = termParser ~ GEQ ~ termParser
      log(pattern)(GEQ) ^^ {
        case left ~ GEQ ~ right =>  
          GreaterEquals(left.sort,left,right)
      }
    }
    
    lazy val gtP:SubformulaParser = {
      lazy val pattern = termParser ~ GT ~ termParser
      log(pattern)(GT) ^^ {
        case left ~ GT ~ right =>  
          GreaterThan(left.sort,left,right)
      }
    }
    
    lazy val ltP:SubformulaParser = {
      lazy val pattern = termParser ~ LT ~ termParser
      log(pattern)(LT + " parser") ^^ {
        case left ~ LT ~ right =>  
          LessThan(left.sort,left,right)
      }
    }

    lazy val falseP:SubformulaParser = {
      lazy val pattern = FALSE
      log(pattern)("False") ^^ {
        case FALSE => False
      }
    }
    
    lazy val trueP:SubformulaParser = {
      lazy val pattern = TRUE
      log(pattern)("true") ^^ {
        case TRUE => True
      }
    }
    
    lazy val groupP:SubformulaParser = {
      lazy val pattern = "(" ~ precedence.reduce(_|_) ~ ")"
      log(pattern)("Subterm Grouping") ^^ {
        case "(" ~ p ~ ")" => p
      }
    }
  }
  
  //////////////////////////////////////////////////////////////////////////////
  // Programs.
  //////////////////////////////////////////////////////////////////////////////
  class ProgramParser(variables:List[Variable],
      functions:List[Function],
      predicates:List[PredicateConstant],
      programVariables:List[ProgramConstant]) 
  {
    type SubprogramParser = PackratParser[Program]
    
    lazy val parser = precedence.reduce(_|_)
    //TODO do we need to make the program variables into predicates so that they
    //can be assigned to and such? Actually, I think that the stuff in ProgramVariables
    // should all be put into the predicates in the first place because programVariables
    //should only hold variables which hold arbitrary programs.
    lazy val formulaParser = new FormulaParser(variables, functions, predicates,programVariables).parser
    lazy val termParser = new TermParser(variables,functions).parser
    
    val precedence : List[SubprogramParser] =
      choiceP     ::
      sequenceP   ::
      ifThenElseP ::
      ifThenP     ::
      whileP      ::
      closureP    ::
      assignP     ::
      ndassignP   ::
      evolutionP ::
      testP       ::
//      pvarP       ::
      groupP      ::
      Nil

     
    lazy val sequenceP:SubprogramParser = {
      lazy val pattern = rightAssociativeOptional(precedence,sequenceP,Some(SCOLON))
      log(pattern)("program" + SCOLON + "program") ^^ {
        case left ~ SCOLON ~ right => right match {
          case Some(rightDefined) => new Sequence(left,rightDefined)
          case None               => left
        }
      }
    }
    
    lazy val choiceP:SubprogramParser = {
      lazy val pattern = rightAssociative(precedence,choiceP,Some(CHOICE))
      log(pattern)(CHOICE) ^^ {
        case left ~ _ ~ right => new Choice(left,right)
      }
    }
    
    lazy val ifThenP:SubprogramParser = {
      lazy val pattern = "if" ~ ("(" ~> formulaParser <~ ")") ~ "then" ~ parser ~ "fi"
      log(pattern)("if-then") ^^ {
        case "if" ~ f ~ "then" ~ p ~ "fi" => new IfThen(f,p)
      }
    }
    
    lazy val ifThenElseP:SubprogramParser = {
      lazy val pattern =
        "if" ~ ("(" ~> formulaParser <~ ")") ~ "then" ~ 
        parser ~ 
        "else" ~ 
        parser ~
        "fi"
        
      log(pattern)("if-then-else") ^^ {
        case "if" ~ f ~ "then" ~ p1 ~ "else" ~ p2 ~ "fi" => new IfThenElse(f,p1,p2)
      }
    }
    
    lazy val whileP:SubprogramParser = {
      lazy val pattern = "while(" ~ formulaParser ~ ")" ~ parser ~ "end"
      log(pattern)("while") ^^ {
        case "while(" ~ test ~ ")" ~ alpha ~ "end" => new Sequence(
          new Loop( new Sequence( new Test(test), alpha ) ),
          new Test(Not(test))
        )
      }
    }
    
    lazy val closureP:SubprogramParser = {
      lazy val pattern = tighterParsers(precedence, closureP).reduce(_|_) ~ KSTAR
      log(pattern)("*") ^^ {
        case p ~ KSTAR => new Loop(p)
      }
    }
    
    lazy val assignP:SubprogramParser = {
      lazy val pattern = termParser ~ ASSIGN ~ termParser
      log(pattern)("Assignment") ^^ {
        case pvar ~ ASSIGN ~ term => new Assign(pvar, term)
      }
    }
    
    lazy val ndassignP:SubprogramParser = {
      lazy val pattern = termParser ~ ASSIGN ~ KSTAR
      log(pattern)("Non-det assign") ^^ {
        case t ~ ASSIGN ~ KSTAR => new NDetAssign(t)
      }
    }

//   // TODO Per Jan's email, use N.F. constructor if v is a var.
//    lazy val nfEvolutionP:SubprogramParser = {
////      lazy val diffEqP:SubprogramParser = termParser ~ PRIME ~ EQ ~ termParser ^^ {
////        case v ~ PRIME ~ EQ ~ t => ContEvolve(Equals(Real,Derivative(v.sort,v),t))
////      }     
//    }

    lazy val evolutionP:SubprogramParser = {      
      lazy val pattern = (OPEN_CBRACKET ~
                          rep1sep(formulaParser, AND) ~
                          AND.? ~ formulaParser.? ~
                          CLOSE_CBRACKET)
      log(pattern)("Cont Evolution") ^^ {
        case OPEN_CBRACKET ~ des ~ andOption ~ constraintOption ~ CLOSE_CBRACKET => constraintOption match {
          case Some(constraint) => ContEvolve( And(des.reduceRight(And(_,_)) , constraint) )
          case None => ContEvolve( des.reduceRight(And(_,_)) )
        }
      }
    }
    
    lazy val testP:SubprogramParser = {
      lazy val pattern = TEST ~ formulaParser
      log(pattern)(TEST + " parser") ^^ {
        case TEST ~ f => new Test(f)
      }
    }
    
    //this need rewriting, but we dont suppor these at the moment anyway.
//    lazy val pvarP:SubprogramParser = {
//      log(ident)("Program Variable") ^^ {
//        case name => programVariables.find(ProgramConstant.unapply(_) match {
//          case Some(t) => t._1.equals(name)
//          case None    => false
//        }) match {
//          case Some(p ) => p
//          case None     => throw new Exception("Program variable was mentioned but not in context: " + name)
//        }
//      }
//    }
    
    lazy val groupP:SubprogramParser = {
      lazy val pattern = "(" ~ precedence.reduce(_|_) ~ ")"
      log(pattern)("Subterm Grouping") ^^ {
        case "(" ~ p ~ ")" => p
      }
    }
    
  }
  
  /**
   * Gets an expression parser based upon the function and programVariable sections.
   */
  def makeExprParser(variables:List[Variable], functions:List[Function],
      predicates:List[PredicateConstant],programs:List[ProgramConstant]):PackratParser[Expr] =
  {
    
    lazy val formulaParser = new FormulaParser(variables,functions,predicates,programs).parser
    lazy val ret = formulaParser ^^ {
      case e => e
    }
    ret
  }
  
  //////////////////////////////////////////////////////////////////////////////
  // Utility methods for converting strings into relevant portions of the core.
  //////////////////////////////////////////////////////////////////////////////

  /**
   * Maps identifiers for common types to their core representation. Example:
   *   "R" -> Real
   *   "MyOwnSort" -> UserDefinedSort("MyOwnSort")
   */
  def identToSort(ident:String):Sort = ident match {
    case "R" => Real
    case "B" => Bool
    case _   => UserSort(ident)
  }

  /**
   * Maps a list of sort identifiers to the appropriate tuple sort.
   * @see identToSort
   */
  def identsToSorts(idents : List[String]):Sort = {
    val sortList = idents.map(ident => identToSort(ident))
    sortList.reduceRight( (l,r) => TupleT.apply(l, r) )
  }
  
  def projectName(v:Variable):String = Variable.unapply(v) match {
    case Some(t) => t._1
    case None    => ""
  }
  
  //////////////////////////////////////////////////////////////////////////////
  // Utility methods for precedence lists
  //////////////////////////////////////////////////////////////////////////////
  //TODO-nrf clean up this section.
  def tighterParsers[T](precedence:List[PackratParser[T]], parser:PackratParser[T]):List[PackratParser[T]] = 
    precedence.dropWhile(candidate => !candidate.equals(parser)).drop(1)
  
  def asTightAsParsers[T](precedence:List[PackratParser[T]],parser:PackratParser[T]):List[PackratParser[T]] =
    precedence.dropWhile(candidate => !candidate.equals(parser))

  def leftAssociative[T](precedence:List[PackratParser[T]],parser:PackratParser[T],separator:Option[String]) = {
    val tighter = tighterParsers(precedence,parser)
    val asTightAs = asTightAsParsers(precedence, parser)
    
    separator match {
      case Some(s:String)	=> asTightAs.reduce(_|_) ~ s  ~ tighter.reduce(_|_)
      case None				=> asTightAs.reduce(_|_) ~ "" ~ tighter.reduce(_|_)
    }
  }
  
  def rightAssociative[T](precedence:List[PackratParser[T]],parser:PackratParser[T],separator:Option[String]) = {
    val tighter = tighterParsers(precedence,parser)
    val asTightAs = asTightAsParsers(precedence, parser)
    
    separator match {
      case Some(s:String) => tighter.reduce(_|_) ~ s ~ asTightAs.reduce(_|_)
      case None			=> tighter.reduce(_|_) ~ "" ~ asTightAs.reduce(_|_)
    }
  }
  
  def rightAssociativeOptional[T](precedence:List[PackratParser[T]],parser:PackratParser[T],separator:Option[String]) = {
    val tighter = tighterParsers(precedence,parser)
    val asTightAs = asTightAsParsers(precedence, parser)
    
    separator match {
      case Some(s:String) => tighter.reduce(_|_) ~ s ~ asTightAs.reduce(_|_).?
      case None			=> tighter.reduce(_|_) ~ "" ~ asTightAs.reduce(_|_).?
    }
  }
  
  
  //////////////////////////////////////////////////////////////////////////////
  // Misc helper methods
  //////////////////////////////////////////////////////////////////////////////
  
  def functionFromName(name:String, functions:List[Function]) = {
    functions.find(Function.unapply(_) match {
      case Some(f) => f._1.equals(name)
      case None    => false
    }) match {
      case Some(function) => function
      case None           => ??? //create a new function?
    }
  }
  
}

// vim: set ts=4 sw=4 et:
