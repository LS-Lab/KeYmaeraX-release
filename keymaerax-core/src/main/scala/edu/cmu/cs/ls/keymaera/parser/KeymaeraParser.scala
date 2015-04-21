package edu.cmu.cs.ls.keymaera.parser

import edu.cmu.cs.ls.keymaera.tactics.{ProofNode, ConfigurableGenerate}

import scala.util.parsing.combinator._
import scala.util.parsing.combinator.lexical._
import edu.cmu.cs.ls.keymaera.core._
import scala.annotation.elidable
import scala.annotation.elidable._
import scala.util.parsing.input.CharSequenceReader
import edu.cmu.cs.ls.keymaera.core.Term
import java.io.File


/**
 * The KeYmaera Parser
 * @author Nathan Fulton
 * @author Stefan Mitsch
 * TODO:
 *  * cleaner distinction between:
 *  	predicates (boolean-valued, rigid)
 *      rigid variables (currently predicateconstants, but that implies boolean-valued) 
 *      "assignables" (non-rigid, currently called variables)
 *      functions (terms that take arguments
 */
class KeYmaeraParser(enabledLogging: Boolean = false,
                     env: { val generator: ConfigurableGenerate[Formula]} = new { lazy val generator = new ConfigurableGenerate[Formula]()})
  extends RegexParsers with PackratParsers {
  def log[T](p : Parser[T])(name : String) = if(!enabledLogging) p else super.log(p)(name)
  //////////////////////////////////////////////////////////////////////////////
  // Public-facing interface.
  //////////////////////////////////////////////////////////////////////////////

  /**
   * Returns all occurances of variables in s.
   * @param s
   * @return All variables occcuring in s.
   */
  private def allVariableOccurances(s:String) = ident.findAllIn(s).map(s => {
    val varParts = s.split("_")
    if (varParts.length == 1 || (!varParts.last.forall(_.isDigit))) new Variable(s, None, Real)
    else new Variable(varParts.slice(0, varParts.length - 1).mkString("_"), Some(varParts.last.toInt), Real)
  }).toSet.toList

  /**
   *
   * @param s the string to parse into a expr
   * @return The expression.
   */
  def parseBareExpression(s:String) : Option[Expression] = {
    val variables = allVariableOccurances(s)
    // HACK: allow parameterless functions for everything that could be a variable, but exclude builtin functions
    val functions = variables.filter(v => !builtinFunctions.exists(_.name == v.name)).map(v => Function(v.name, v.index, Unit, Real)) ++ builtinFunctions
    val parser = new KeYmaeraParser(false, env)

    val exprParser = parser.makeExprParser(variables, functions, Nil, Nil, Nil)
    parser.parseAll(exprParser, s) match {
      case parser.Success(result, next) => Some(result.asInstanceOf[Expression])
      case f: parser.Failure => throw new IllegalArgumentException(f.toString())
      case e: parser.Error => throw new IllegalArgumentException(e.toString())
      case _ => None //todo actually, pass back an error
    }
  }

  /**
   *
   * @param s the string to parse into a expr
   * @return The expression.
   */
  def parseBareTerm(s:String) : Option[Term] = {
    val variables = allVariableOccurances(s)
    // HACK: allow parameterless functions for everything that could be a variable, but exclude builtin functions
    val functions = variables.filter(v => !builtinFunctions.exists(_.name == v.name)).map(v => Function(v.name, v.index, Unit, Real)) ++ builtinFunctions
    val parser = new KeYmaeraParser(false, env)

    val exprParser = parser.makeTermParser(variables, functions)
    parser.parseAll(exprParser, s) match {
      case parser.Success(result, next) => Some(result.asInstanceOf[Term])
      case _ => None //todo actually, pass back an error
    }
  }

  def parseBareFormula(s : String) : Option[Formula] = {
    try {
      val expr      = this.parseBareExpression(s).get
      val formula   = expr.asInstanceOf[Formula]
      val variables = allVariableOccurances(s)
      Some(Forall(variables, formula))
    }
    catch {
      case e:Exception => None
    }
  }

  def parseBareFormulaUnquantified(s : String) : Formula = {
    parseBareExpression(s).get.asInstanceOf[Formula]
  }

  def runParser(s:String):Expression = {
    val parser = new KeYmaeraParser(enabledLogging, env)

    //Parse file.
    val (functions : List[Function],predicateConstants : List[Function], variables : List[Variable],problemText : String) =
      parser.parseAll(parser.fileParser, s) match {
        case parser.Success(result,next) => result
        case f: parser.Failure => throw new IllegalArgumentException(f.toString())
        case f: parser.Error => throw new IllegalArgumentException(f.toString())
      }


    val programs = List[ProgramConst]() //TODO support these.
    val differentialPrograms = List[DifferentialProgramConst]()
    
    
    /**
     * The failure message for parse failures during problem parsing.
     */
    def failureMessage(result : String, next : parser.Input):String = {
      "Failed to parse problem (line: " + next.pos.line + ", column: " + next.pos.column + ")\n" +
      "Error message: " + result + " in:\n" + next.pos.longString
    }
    
    //Parse the problem.
    val exprParser = parser.makeExprParser(variables, functions ++ builtinFunctions, predicateConstants, programs, differentialPrograms)
    val parseResult : Expression = parser.parseAll(exprParser, problemText) match {
        case parser.Success(result,next) => result.asInstanceOf[Expression]
        case parser.Failure(result,next) => throw new Exception(failureMessage(result,next))
        case parser.Error(result,next) => throw new Exception(failureMessage(result,next))
    }
    
    //Ensure that parse( print(parse(problemText)) ) = parse(problemText)
    val printOfParse = KeYmaeraPrettyPrinter.stringify(parseResult)
    checkParser(functions ++ builtinFunctions, predicateConstants, variables, programs, differentialPrograms, parseResult,printOfParse)
    
    parseResult
  }
  
  
  /**
   * Ensures that parse( print(parse(input)) ) = parse(input)
   */
  @elidable(ASSERTION) 
  def checkParser(functions:List[Function],
    predicateConstants:List[Function],
    variables:List[Variable],
    programVariables:List[ProgramConst],
    DifferentialProgramVariables: List[DifferentialProgramConst],
    parse:Expression,
    printOfParse:String) = 
  {
    /* don't let the checking parser communicate with the objects injected into the real parser */
    val parser = new KeYmaeraParser(enabledLogging, new { val generator = new ConfigurableGenerate[Formula]() } )
    val exprParser = parser.makeExprParser(variables, functions, predicateConstants,programVariables, DifferentialProgramVariables)
    try{
      val printofparseParse = parser.parseAll(exprParser, printOfParse) match {
        case parser.Success(result,next) => result
        case f@parser.Failure(msg,_) => throw new Exception("parse failed: " + f.toString())
        case e@parser.Error(msg,_) => throw new Exception("parse error: " + e.toString())
      }
      require(parse.equals(printofparseParse), "Parse not equals parse(pp(parse(_))): " + parse + " != " + printofparseParse )
    }
    catch {
      case e : Exception => require(requirement = false,
        "Parse of print did not succeed on: " + printOfParse + "\nExpected: " + KeYmaeraPrettyPrinter.stringify(parse) +
        "\n Exception was: " + e)
    }

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
  
  protected val everything = """[\w\W\s\S\d\D\n\r]""".r
  
  protected val notDblQuote = """[^\"]*""".r

  protected val builtinFunctions = Function("Abs", None, Real, Real) :: Nil
  
  val lexical = new StdLexical
  //TODO should we add the rest of the \\'s to the delimiters list?
  lexical.delimiters ++= List("{", "}", "(", ")", "+", "-", "*", "/")
  
  //////////////////////////////////////////////////////////////////////////////
  // Function Definition Section.
  //////////////////////////////////////////////////////////////////////////////

  /**
   * Returns a list of defined function sorts.
   */
  lazy val functionsP = {	
    lazy val pattern = ParseSymbols.FUNCTIONS_SECT ~> START_SECT ~> rep1sep(funcdefP, ".") <~ ".".? <~ END_SECT 
    log(pattern)("Functions section") ^^ {
      case  definitions => definitions
    }
  }

  lazy val funcdefP = ParseSymbols.EXTERNAL_FUNCTION.?  ~ ident ~ ident ~ ("(" ~ repsep(ident, ",") ~ ")").? ^^ {
    case external ~ rsort ~ name ~ tail =>
      tail match {
        case Some(_ ~ argsorts ~ _) => {
          val isExternal = external match {
            case Some(EXTERNAL_FUNCTION) => true
            case Some(_) => throw new Exception("Parser combinator library is buggy...")
            case None    => false
          }
          val result = {
            val (n, idx) = nameAndIndex(name)
            Function(n, idx, identsToSorts(argsorts), identToSort(rsort))
          }
          if(isExternal) {
            throw new UnsupportedOperationException("external functions not yet supported")
            //result.markExternal()
          }
          result
        }
        case None => {
          val (n, idx) = nameAndIndex(name)
          Function(n, idx, Unit, Bool)
        }
      }
  }
  
  //////////////////////////////////////////////////////////////////////////////
  // State Variable Definition Section.
  //////////////////////////////////////////////////////////////////////////////

  /**
   * Returns a list of defined program sorts.
   */
  lazy val programVariablesP = {
    lazy val pattern = PVARS_SECT ~> START_SECT ~> rep1sep(vardefP, ".") <~ ".".? <~ END_SECT
    
    log(pattern)("ProgramVariables section.") ^^ {
      case variables => variables
    }
  }

  lazy val vardefP = ident ~ ident ^^ {
    //Note: it might be necessary to give these arguments indices.
    case rsort ~ name => val (n, i) = nameAndIndex(name); Variable(n, i, identToSort(rsort))
  }

  //////////////////////////////////////////////////////////////////////////////
  // Problem Section.
  //////////////////////////////////////////////////////////////////////////////
  lazy val problemP = {
    lazy val textP = ("""[\w\W\s\S\d\D]+""" + END_SECT).r
  
    lazy val pattern = PROBLEM_SECT ~> "." ~> textP 
    log(pattern)("\\problem section (extract a string)") ^^ {
      case programText => programText.replace(END_SECT, "")
    }
  } 
    
  lazy val fileParser = functionsP.? ~ programVariablesP.? ~ problemP ^^ {
    case functionSection ~ programVarsSection ~ problemText => {
      val functions:List[Function] = functionSection match {
        case Some(l) => l.filter({ case Function(_, _, Unit, Bool) => false case _ => true }).map(_.asInstanceOf[Function])
        case None    => List[Function]()
      }
      
      val predicateConstants:List[Function] = functionSection match {
        case Some(l) => l.filter({ case Function(_, _, Unit, Bool) => true case _ => false }).map(_.asInstanceOf[Function])
        case None    => List[Function]()
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
      addP ::
      subtractP ::
      multiplyP ::
      divP ::
      expP ::
      negativeP ::
      termDerivativeP ::
      applyP ::
      variableP :: //real-valued.
      numberP   ::
      identP :: //variableP should match first.
      groupP    ::
      Nil

    /**
     * Terms containing no derivatives.
     * @todo This does not actually work. All this does is make sure the *top level* parser is not a termDerivative.
     *      But, for instance, -x' is still allowed because the negativeP parser does a "tighterThan" on the original
     *      precedence list. In order to fix this problem, we should make this class parameterized by a precedence list.
     */
    lazy val nonDerivativeTermP =   (precedence diff (termDerivativeP::Nil)).reduce(_|_)

    //non-variable ident parser. TODO-nrf add logging and check anything
    //parsed by identP is always bound.
    lazy val identP : PackratParser[Term] = {
      log(ident)("Arbitrary Identifier") ^^ {
        case id =>
          val (n, idx) = nameAndIndex(id)
          Variable(n, idx, Real)
      }
    }

    //variable parser
    lazy val variableP:PackratParser[Variable] = {
      log(ident)("Variable") ^^ {
        case name => {
          val (n, i) = nameAndIndex(name)
          variables.find(Variable.unapply(_) match {
            case Some((nn, ii, _)) => nn == n && ii == i
            case None => false
          }) match {
            case Some(p) => p
            case None => System.err.println("WARNING: undeclared identifier " + name); Variable(n, i, Real)
          }
        }
      } 
    }
    
    lazy val termDerivativeP:PackratParser[Differential] = {
      lazy val pattern = tighterParsers(precedence, termDerivativeP).reduce(_|_)
      log(pattern ~ PRIME)(PRIME + " parser") ^^ {
        case t ~ PRIME => new Differential(t)
      }
    }
    
    //Compound terms
      
    lazy val multiplyP:SubtermParser = {
      lazy val pattern = leftAssociative(precedence, multiplyP, Some(MULTIPLY))
      log(pattern)("Multiplication") ^^ {
        case left ~ MULTIPLY ~ right => Times(left, right)
      }
    }
    lazy val divP:SubtermParser = {
      lazy val pattern = leftAssociative(precedence, divP, Some(DIVIDE))
      log(pattern)("Division") ^^ {
        case left ~ DIVIDE ~ right => Divide(left, right)
      }
    }
    
    lazy val expP:SubtermParser = {
      lazy val pattern = tighterParsers(precedence,expP).reduce(_|_) ~ EXP ~ numberP
      log(pattern)("Exponentiation") ^^ {
        case left ~ EXP ~ right => Power(left, right)
      }
    }
    lazy val addP:SubtermParser = {
      lazy val pattern = leftAssociative(precedence, addP, Some(PLUS))
      log(pattern)("Addition") ^^ {
        case left ~ PLUS ~ right => Plus(left, right)
      }
    }
    lazy val subtractP:SubtermParser = {
      lazy val pattern = leftAssociative(precedence, subtractP, Some(MINUS))
      log(pattern)("Subtract") ^^ {
        case left ~ MINUS ~ right => Minus(left, right)
      }
    }
    
    //Unary term operators
    
    lazy val negativeP:SubtermParser = {
      lazy val pattern = NEGATIVE ~ asTightAsParsers(precedence, negativeP).reduce(_|_)
      log(pattern)("negate") ^^ {
        case NEGATIVE ~ term => Neg(term)
      }
    }
    
    //Function application
    
    lazy val applyP:SubtermParser = {
      // TODO disallow functions of functions?
      lazy val pattern = ident ~ ("(" ~> ("?" | repsep(precedence.reduce(_|_), ",")) <~ ")")
      
      log(pattern)("Function Application") ^? (
        {case name ~ args if !functions.exists(_.name == name) || functionFromName(name, functions).sort == Real =>
          args match {
            case termArgs: List[Term] =>
              if (termArgs.isEmpty) FuncOf(functionFromName(name.toString, functions), Nothing)
              else FuncOf(functionFromName(name.toString, functions), termArgs.reduce((l,r) => Pair(l, r)))
            case _: String => FuncOf(functionFromName(name.toString, functions), Anything)
          }},
        { case name ~ args => "Can only use identifier of sort Real in function application, but " + name + " has sort " +
                                functionFromName(name.toString, functions).sort})
    }

    //Groupings
    
    lazy val groupP:SubtermParser = {
      lazy val pattern = "(" ~ precedence.reduce(_|_) ~ ")"
      log(pattern)("Subterm Grouping") ^^ {
        case "(" ~ p ~ ")" => p
      }
    }
    
    //Numbers
    
    lazy val numberP:PackratParser[Number] = {
      lazy val pattern = """[0-9]+(\.[0-9]+)?""".r //copied into combinator language parser; if you change, change there as well. @todo Does this allow negatives?!
      log(pattern)("NUMBER") ^^ {
        case n => Number.apply(BigDecimal(n))
      }
    }
  }
  
  //////////////////////////////////////////////////////////////////////////////
  // Formulas.
  //////////////////////////////////////////////////////////////////////////////
  class FormulaParser(variables:List[Variable],
      functions:List[Function],
      predicates:List[Function],
      programVariables:List[ProgramConst],
      DifferentialProgramVariables: List[DifferentialProgramConst])
  {
    type SubformulaParser = PackratParser[Formula]
    
    lazy val programParser = 
      new ProgramParser(variables,functions,predicates,programVariables,DifferentialProgramVariables).parser

    /**
     * @todo Is this unused? If so, why?
     */
    lazy val termParserObj =
      new TermParser(variables, functions)

    lazy val parser = precedence.reduce(_|_)

    /**
     * This is not included in the precedence list, and is merely a helper for parsing NFContEvolve-form diffeq's.
     * @todo this doesn't work because inside the inditividual parser we acutally use the precendence list. We would
     *      have to make the entire parser parameterized by the precedence list...
     */
    lazy val nonDerivativeFormulaP = (precedence diff formulaDerivativeP::Nil).reduce(_|_)

    val precedence : List[SubformulaParser] =
      equivP ::
      implP  ::
      backwardImplP :: //makes writing axioms less painful.
      orP ::
      andP ::
      notP ::
      boxP :: //Magic: keep box before diamond.
      diamondP ::
      forallP :: 
      existsP :: 
      equalsP ::
      notEqualsP ::
      leP    ::
      geP    ::
      gtP    ::
      ltP    ::  
      formulaDerivativeP ::
      applyPredicateP ::
      predicateP ::
      trueP ::
      falseP ::
      groupP ::
      Nil

    lazy val forallP : PackratParser[Formula] = {      
      lazy val pattern = (FORALL ~> rep1sep(ident,",") <~ ".") ~ asTightAsParsers(precedence, boxP).reduce(_|_)
      log(pattern)("Forall") ^^ {
        case idents ~ formula => {
          val boundVariables = idents.map(str => {val (n, i) = nameAndIndex(str); Variable.apply(n, i, Real)}) //TODO?
          new Forall(boundVariables, formula)
        }
      }
    }
    
    lazy val existsP : PackratParser[Formula] = { 
      lazy val fP = 
        asTightAsParsers(precedence, boxP).reduce(_|_)
      lazy val pattern = (EXISTS ~> rep1sep(ident,",") <~ ".") ~ fP
      log(pattern)("Exists") ^^ {
        case idents ~ formula => {
          val boundVariables = idents.map(str => {val (n, i) = nameAndIndex(str); Variable.apply(n, i, Real)}) //TODO?
          new Exists(boundVariables, formula)
        }
      }
    }
    
    
    lazy val variableP:PackratParser[Term] = {
      lazy val pattern = {
        val stringList =  variables.map(Variable.unapply(_) match {
          case Some(t) => t._1
          case None => ???
        })
        if(stringList.isEmpty) { """$^""".r/*match nothing.*/ }
        else new scala.util.matching.Regex( stringList.sortWith(_.length > _.length).reduce(_+"|"+_) )
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
      
    //Modalities
    lazy val boxP : SubformulaParser = {
      lazy val pattern = BOX_OPEN ~ 
    		  			 programParser ~ 
    		  			 BOX_CLOSE ~ 
    		  			 asTightAsParsers(precedence, boxP).reduce(_|_)
      log(pattern)("box: " + BOX_OPEN + PROGRAM_META + BOX_CLOSE + FORMULA_META) ^^ {
        case BOX_OPEN ~ p ~ BOX_CLOSE ~ f => Box(p, f)
      }
    }
    
    lazy val diamondP : SubformulaParser = {
      lazy val pattern = DIA_OPEN ~ 
                         programParser ~ 
                         DIA_CLOSE ~ 
                         asTightAsParsers(precedence, boxP).reduce(_|_)
      log(pattern)("Diamond: " + DIA_OPEN + PROGRAM_META + DIA_CLOSE + FORMULA_META) ^^ {
        case DIA_OPEN ~ p ~ DIA_CLOSE ~ f => Diamond(p, f)
      }
    }

    //Predicate application

    lazy val applyPredicateP:SubformulaParser = {
      lazy val pattern = ident ~ ("(" ~> ("?" | rep1sep(termParser, ",")) <~ ")")

      log(pattern)("Predicate Application") ^? (
        { case name ~ args if !functions.exists(_.name == name) || functionFromName(name, functions).sort == Bool =>
          args match {
            case termArgs: List[Term] =>
              PredOf(functionFromName(name.toString, functions), termArgs.reduce( (l,r) => Pair(l, r) ) )
            case _: String => PredOf(functionFromName(name.toString, functions), Anything)
          }},
        { case name ~ args => "Can only use identifier of sort Bool in predicate application, but " + name + " has sort " +
            functionFromName(name.toString, functions).sort}
      )
    }

    //Predicates
    lazy val predicateP:SubformulaParser = {
      lazy val pattern = {
        val stringList =  predicates.map(Function.unapply(_) match {
          case Some((n, i, _, _)) => n + (i match { case Some(idx) => "_" + idx case None => ""})
          case None => ???
        })
        if(stringList.isEmpty) { """$^""".r/*match nothing.*/ }
        else new scala.util.matching.Regex( stringList.sortWith(_.length > _.length).reduce(_+"|"+_) )
      }

      log(pattern)("Predicate") ^^ {
        case name => {
          val (n, i) = nameAndIndex(name)
          val fn = Function(n, i, Unit, Bool)
          val p = PredOf(fn, Nothing)
          require(predicates.contains(fn), "All predicates have to be declared, but the predicate named ``" + p.prettyString() + "\" was not found in the list of predicates: " + predicates)
          p
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
        case v ~ PRIME => new DifferentialFormula(v)
      }
    }
    
    
    //Binary Formulas
    
    lazy val equivP:SubformulaParser = {
      lazy val pattern = 
        asTightAsParsers(precedence, equivP).reduce(_|_) ~ 
        EQUIV ~
        tighterParsers(precedence, equivP).reduce(_|_)
        
      log(pattern)(EQUIV) ^^ {
        case left ~ _ ~ right => Equiv(left,right)
      }
    }
    
    
    lazy val equalsP:SubformulaParser = {
      lazy val pattern = 
        termParser ~ 
        EQ ~
        termParser 
        
      log(pattern)(EQ + " formula parser (on terms)") ^^ {
        case left ~ _ ~ right => Equal(left, right)
      }
    }
    
    lazy val notEqualsP:SubformulaParser = {
      lazy val pattern = 
        termParser ~ 
        NEQ ~
        termParser 
        
      log(pattern)(NEQ + " formula parser (on terms)") ^^ {
        case left ~ _ ~ right => NotEqual(left, right)
      }
    }
    
    lazy val implP:SubformulaParser = {
      lazy val pattern = rightAssociative(precedence, implP, Some(ARROW))
      log(pattern)(ARROW) ^^ {
        case left ~ _ ~ right => Imply(left, right)
      }
    }
    
    lazy val backwardImplP:SubformulaParser = {
      lazy val pattern = rightAssociative(precedence, backwardImplP, Some(LARROW))
      log(pattern)(ARROW) ^^ {
        case left ~ _ ~ right => Imply(right, left)
      }
    }
    
    lazy val andP : SubformulaParser = {
      lazy val pattern = leftAssociative(precedence, andP, Some(AND))
      log(pattern)(AND + " parser") ^^ {
        case left ~ _ ~ right => And(left, right)
      }
    }
    
    lazy val orP : SubformulaParser = {
      lazy val pattern = leftAssociative(precedence, orP, Some(OR))
      log(pattern)(OR + " parser") ^^ {
        case left ~ OR ~ right => Or(left, right)
      }
    }
    //Binary Relations

    lazy val termParser = new TermParser(variables,functions).parser
    
    lazy val leP:SubformulaParser = {
      lazy val pattern = termParser ~ LEQ ~ termParser
      log(pattern)(LEQ) ^^ {
        case left ~ LEQ ~ right =>  
          LessEqual(left, right)
      }
    }
    
    lazy val geP:SubformulaParser = {
      lazy val pattern = termParser ~ GEQ ~ termParser
      log(pattern)(GEQ) ^^ {
        case left ~ GEQ ~ right =>  
          GreaterEqual(left, right)
      }
    }
    
    lazy val gtP:SubformulaParser = {
      lazy val pattern = termParser ~ GT ~ termParser
      log(pattern)(GT) ^^ {
        case left ~ GT ~ right =>  
          Greater(left, right)
      }
    }
    
    lazy val ltP:SubformulaParser = {
      lazy val pattern = termParser ~ LT ~ termParser
      log(pattern)(LT + " parser") ^^ {
        case left ~ LT ~ right =>  
          Less(left, right)
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
      predicates:List[Function],
      programVariables:List[ProgramConst],
      DifferentialProgramVariables: List[DifferentialProgramConst])
  {
    type SubprogramParser = PackratParser[Program]
    
    //This is not precedence.reduce(_|_) because some things need trailing ;
    //This list should contain precedence in order, with all elements which
    //require a trailing ; removed. These will be captured by sequenceP.
    lazy val parser = choiceP | sequenceP | ifThenElseP | ifThenP | whileP | closureP | groupPseq | groupP

    //@todo do we need to make the program variables into predicates so that they
    //can be assigned to and such? Actually, I think that the stuff in ProgramVariables
    // should all be put into the predicates in the first place because programVariables
    //should only hold variables which hold arbitrary programs.
    val theFormulaParser = new FormulaParser(variables, functions, predicates,programVariables, DifferentialProgramVariables)
    lazy val formulaParser = theFormulaParser.parser

    val theTermParser = new TermParser(variables,functions)
    lazy val termParser = theTermParser.parser
    lazy val variableParser = theTermParser.variableP

    val precedence : List[SubprogramParser] =
      choiceP     ::
      sequenceP   ::
      ifThenElseP ::
      ifThenP     ::
      whileP      ::
      closureP    ::
      assignP     ::
      ndassignP   ::
        diffAssignP ::
      testP       ::
      pvarP       ::
      differentialSystemP ::
      contEvolvePVarP ::
      groupPseq :: groupP      ::
      Nil

    lazy val variableDerivativeP  : PackratParser[DifferentialSymbol] = {
      log(theTermParser.variableP ~ PRIME)(PRIME + " parser") ^^ {
        case t ~ PRIME => new DifferentialSymbol(t)
      }
    }

    private def computeProduct(elements : List[(DifferentialSymbol, Term)]) : DifferentialProgram = {
      if(elements.length == 1) {
        AtomicODE(elements.head._1, elements.head._2)
      }
      else {
        DifferentialProduct(AtomicODE(elements.head._1, elements.head._2), computeProduct(elements.tail))
      }
    }

    lazy val differentialSystemP : PackratParser[DifferentialProgram] = {
      val pattern = rep1sep(variableDerivativeP ~ (EQ ~> theTermParser.parser), COMMA) ~ (AND ~> theFormulaParser.parser).?
      log(pattern)("Differential equation system") ^^ {
        case elements ~ constraint => {
          val diffProgram = computeProduct(elements.map(x => (x._1, x._2)))
          constraint match {
            case Some(c) => ODESystem(diffProgram, c)
            case None => ODESystem(diffProgram, True)
          }
        }
      }
    }

    lazy val pvarP:PackratParser[ProgramConst] = {
      lazy val pattern = {
        val stringList =  programVariables.map(ProgramConst.unapply(_) match {
          case Some(n) => n
          case None => ???
        })
        if(stringList.isEmpty) { """$^""".r/*match nothing.*/ }
        else new scala.util.matching.Regex( stringList.sortWith(_.length > _.length).reduce(_+"|"+_) )
      }
      
      log(pattern)("Program Variable") ^^ {
        case name => {
          val (n, i) = nameAndIndex(name)
          val p = ProgramConst(n)
          require(programVariables.contains(p), "All program constants have to be declared " + p.prettyString() + " not found in " + programVariables)
          p
        }
      } 
    }

    lazy val contEvolvePVarP:PackratParser[DifferentialProgramConst] = {
      lazy val pattern = {
        val stringList =  DifferentialProgramVariables.map(DifferentialProgramConst.unapply(_) match {
          case Some(n) => n
          case None => ???
        })
        if(stringList.isEmpty) { """$^""".r/*match nothing.*/ }
        else new scala.util.matching.Regex( stringList.sortWith(_.length > _.length).reduce(_+"|"+_) )
      }

      log(pattern)("DifferentialProgram Variable") ^^ {
        case name => {
          val (n, i) = nameAndIndex(name)
          val p = DifferentialProgramConst(n)
          require(DifferentialProgramVariables.contains(p), "All program constants have to be declared; '" + p.prettyString() + "' not found in " + programVariables)
          p
        }
      }
    }
    
    lazy val sequenceP:SubprogramParser = {
      lazy val pattern = rightAssociativeOptional(precedence,sequenceP,Some(SCOLON))
      log(pattern)("program" + SCOLON + "program") ^^ {
        case left ~ SCOLON ~ right => right match {
          case Some(r) => new Compose(left, r)
          case None => left
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
        case "if" ~ f ~ "then" ~ p ~ "fi" => new Choice(Compose(Test(f), p), Test(Not(f)))
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
        case "if" ~ f ~ "then" ~ p1 ~ "else" ~ p2 ~ "fi" => new Choice(Compose(Test(f), p1), Compose(Test(Not(f)), p2))
      }
    }
    
    lazy val whileP:SubprogramParser = {
      lazy val pattern = "while(" ~ formulaParser ~ ")" ~ parser ~ "end"
      log(pattern)("while") ^^ {
        case "while(" ~ test ~ ")" ~ alpha ~ "end" => new Compose(
          new Loop( new Compose(new Test(test), alpha ) ),
          new Test(Not(test))
        )
      }
    }
    
    lazy val closureP:SubprogramParser = {
      lazy val pattern = (tighterParsers(precedence, closureP).reduce(_|_) <~ KSTAR) ~ opt("@invariant" ~> "(" ~> formulaParser <~ ")")
      log(pattern)("*") ^^ {
        case p ~ Some(f) => val result = new Loop(p); env.generator.products += result -> f; result
        case p ~ None => new Loop(p)
      }
    }
    
    lazy val assignP:SubprogramParser = {
      lazy val pattern = variableParser ~ ASSIGN ~ termParser
      log(pattern)("Assignment") ^^ {
        case pvar ~ ASSIGN ~ term => new Assign(pvar, term)
      }
    }

    lazy val diffAssignP : SubprogramParser = {
      lazy val pattern = variableDerivativeP ~ (ASSIGN ~> termParser)
      log(pattern)("x' := theta") ^^ {
        case pvar ~ term => new DiffAssign(pvar, term)
      }
    }

    lazy val ndassignP:SubprogramParser = {
      lazy val pattern = variableParser ~ ASSIGN ~ KSTAR
      log(pattern)("Non-det assign") ^^ {
        case t ~ ASSIGN ~ KSTAR => new AssignAny(t)
      }
    }

    lazy val testP:SubprogramParser = {
      lazy val pattern = TEST ~ formulaParser
      log(pattern)(TEST + " parser") ^^ {
        case TEST ~ f => new Test(f)
      }
    }
    
    lazy val groupP:SubprogramParser = {
    lazy val pattern = "{" ~> parser <~ "}"
      log(pattern)("Subprogram Grouping") ^^ {
        case  p => p
      }
    }

    /**
     * So that you can type { a; b; } c as well as {a; b }; c
     */
    lazy val groupPseq:SubprogramParser = {
      lazy val pattern = ("{" ~> parser <~ "}") ~ parser
      log(pattern)("Stermprogram grouping without semicolon") ^^ {
        case p ~ q => Compose(p,q)
      }
    }
    
  }
  
  /**
   * Gets an expression parser based upon the function and programVariable sections.
   */
  def makeExprParser(variables:List[Variable], functions:List[Function],
      predicates:List[Function],programs:List[ProgramConst],differentialPrograms:List[DifferentialProgramConst]):PackratParser[Expression] =
  {
    
    lazy val formulaParser = new FormulaParser(variables,functions,predicates,programs,differentialPrograms).parser
    lazy val ret = formulaParser ^^ {
      case e => e
    }
    ret
  }

  /**
   * Gets a term parser based upon the function and programVariable sections.
   */
  def makeTermParser(variables:List[Variable], functions:List[Function]):PackratParser[Expression] = {
    lazy val termParser = new TermParser(variables,functions).parser
    lazy val ret = termParser ^^ {
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
    case _   => ObjectSort(ident)
  }

  /**
   * Maps a list of sort identifiers to the appropriate tuple sort.
   * @see identToSort
   */
  def identsToSorts(idents : List[String]):Sort = {
    if (idents.isEmpty) {
      Unit
    } else {
      val sortList = idents.map(ident => identToSort(ident))
      sortList.reduceRight((l, r) => Tuple.apply(l, r))
    }
  }
  
  def projectName(v:Variable): Option[(String, Option[Int])] = Variable.unapply(v) match {
    case Some((n, idx, _)) => Some((n, idx))
    case None    => None
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
  /**
   * gets a Function object from the ``functions" list with name ``name"
   */
  def functionFromName(name:String, functions:List[Function]) = {
    val (n, idx) = nameAndIndex(name)
    functions.find(Function.unapply(_) match {
      case Some(f) => f._1.equals(n) && f._2.equals(idx)
      case None    => false
    }) match {
      case Some(function) => function
      case None           => throw new Exception("The function " + name + " is used but not declared.")
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////////
  // KeYmaera Proof files
  // 	ProofFileParser -- Top-level parser for an axiom/lemma/proof file.
  // 	ProofParser 	-- parser for a LISPy proof.
  //////////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////////
  object ProofFileParser {
    /**
     * Type of the Variable Parser
     */
    sealed trait VType
      case class VProgram(variable: ProgramConst) extends VType
      case class VDifferentialProgram(variable: DifferentialProgramConst) extends VType
      case class VFormula(variable: Function) extends VType
      case class VTerm(variable: Variable) extends VType
      case class VFunction(fn: Function) extends VType
    /**
     * Type of the Axiom and Lemma parsers
     */
    type ALPType = PackratParser[List[LoadedKnowledge]]
    
    /**
     * The main parser
     */
    def runParser(in:String) : List[LoadedKnowledge] = {
      //The parse happens in two phases. First, we parse the program and formula
      //variable definitions. Then, we parse the axioms and lemmas.
      
      val inReader = new PackratReader(new CharSequenceReader(in))
      val (programs, differentialPrograms, formulas, terms, funs, nextIn) = parse(firstPassParser, inReader) match {
        case Success(result, next) => (result._1, result._2, result._3, result._4, result._5 ++ builtinFunctions, next)
        case Failure(msg, next)    => 
          throw new Exception("Failed to parse variables section:"  + msg)
        case Error(msg,next)       =>
          throw new Exception("Error while parsing variables section:" + msg)
      }
      
      def posStr(msg:String, next : Input) = {
        "(line: " + next.pos.line + ", column:" + next.pos.column + ")"
      }
      
      val alParser = makeAxiomLemmaParser(programs, differentialPrograms, formulas, terms, funs) //axiomlemmaParser
      val knowledge = parseAll(alParser, nextIn) match {
        case Success(result, next) => result
        case Failure(msg, next)    => 
          throw new Exception("Failed to parse Lemmas & Axioms at " + posStr(msg,next) + ": "  + msg)
        case Error(msg,next)       =>
          throw new Exception("Error while parsing Lemmas & Axioms at " + posStr(msg,next) + ":" + msg)
      }
      knowledge
    }
  
    /**
     * This is the parser for the first pass
     */
    lazy val firstPassParser 
    : PackratParser[(List[ProgramConst], List[DifferentialProgramConst], List[Function], List[Variable], List[Function])] =
    {
      lazy val pattern = variablesP
      log(pattern)("Parsing variable declarations in proof file.") ^^ {
        case vars => {
          val programs = vars collect {
            case VProgram(p) => p
          }
          val differentialPrograms = vars collect {
            case VDifferentialProgram(p) => p
          }
          val formulas = vars collect {
            case VFormula(f) => f
          }
          val terms = vars collect {
            case VTerm(t) => t
          }
          val funs = vars collect {
            case VFunction(f) => f
          }
          (programs, differentialPrograms, formulas, terms, funs)
        }
      }
    }

    /**
     * Maps a string representation of a type and a name to an Expression
     */
    private def makeVariable(ty : String, name : String) : VType = {
      val (n, idx) = nameAndIndex(name)
      ty match {
        case "P" => VProgram(ProgramConst(n))
        case "CP" => VDifferentialProgram(DifferentialProgramConst(n))
        case "F" => VFormula(Function(n, idx, Unit, Bool))
        case "T" => VTerm(Variable(n, idx, Real))
        case _ => throw new Exception("Type " + ty + " is unknown! Expected P (program) or F (formula) or T (term)")
      }
    }

    private def makeFunction(ty : String, name : String, argT: String) : VType = {
      require(argT == "T" | argT == "" | argT == "?", "can only handle parameterless and unary functions")
      val (n, idx) = nameAndIndex(name)
      val domainSort = argT match {
        case "T" => Real
        case "" => Unit
        case "?" => Real
      }
      ty match {
        case "F" => VFunction(Function(n, idx, domainSort, Bool))
        case "T" => VFunction(Function(n, idx, domainSort, Real))
        case _ => throw new Exception("Type " + ty + " is unknown! Expected F (formula) or T (term)")
      }
    }

    /**
     * Parses the Variables section of the file
     */
    lazy val variablesP = {
      //e.g., T x or T f(x:T) or T f(x). In the latter case, x:T implicitly.
      // @todo But currently, T f(x:T  y:T) isn't supported. Use product sorts to implement.
      lazy val variablesP = ident ~ ident ~ ("(" ~> ("?" | repsep(ident ~ (":" ~> ident).?, ",")) <~ ")").? ^^ {
        //if tail is defined then this is a function; else it's a variable.
        case codomainSort ~ name ~ parameters => parameters match {
          case Some(arguments: List[~[String, Option[String]]]) => {
            //@todo support product domains sorts. Also requires modifying makeFunction
            require(arguments.length <= 1, "don't support functions w/ arity > 1")
            if (arguments.length == 0) {
              makeFunction(codomainSort, name, "")
            } else {
              val domainType = arguments.last._2 match {
                case Some(sort) => sort
                case None => codomainSort
              }
              //@todo NRFb4c but then ultimately just ignore that and use "T" like it wants us to...
              //            makeFunction(codomainSort,name,domainType)
              makeFunction(codomainSort, name, "T")
            }
          }
          case Some(wildcard: String) => makeFunction(codomainSort, name, wildcard)
          case None => makeVariable(codomainSort.toString, name.toString)
        }
      }
      lazy val pattern =
        VARIABLES_SECT ~> START_SECT ~> ((repsep(variablesP, """\.""".r) <~ ".".?) <~ END_SECT)
      log(pattern)("Variable declarations") ^^ {
        case  variables => variables
      }
    }

    /**
     * Parses the lemmas/axioms section of the file
     */
    def makeAxiomLemmaParser(
          programs : List[ProgramConst],
          differentialPrograms: List[DifferentialProgramConst],
          formulas : List[Function],
          terms : List[Variable],
          funs: List[Function]) : ALPType  =
    {
      //Names of lemmas and axioms may contain pretty much everything except "
      val alName = notDblQuote
      
      //Create the Formula and Evidence parsers.
      val formulaParser = new FormulaParser(terms,
          funs,
          formulas,
          programs,
          differentialPrograms)
      lazy val formulaP = formulaParser.parser
      
      lazy val evidenceP : PackratParser[Evidence] = EvidenceParser.evidenceParser
      
      lazy val axiomParser : ALPType = {
        lazy val pattern = ("Axiom" ~> "\"" ~> alName) ~ 
                           (("\"" ~ ".") ~> repsep(formulaP, ".") <~ ".".?) <~ "End."

        log(pattern)("Axiom Parser") ^^ {
          case name ~ formulas => formulas.map(f => new LoadedAxiom(name, f))
        }
      } 
      
      /**
       * Each Lemma block may have only one formula
       * The result type is a Parser[List[Formula]] so that lemma and axiom parse
       * results are easy to combine.
       */
      lazy val lemmaParser : ALPType = {
        val pattern = ("Lemma" ~> "\"" ~> alName) ~ 
                      (("\"" ~ ".") ~> formulaP <~ "End.") ~ //only allow a single formula.
                      evidenceP.* 

        log(pattern)("Lemma Parser") ^^ {
          case name ~ formula ~ evidence => List(new LoadedLemma(name, formula, evidence))
        }
      }
        
      (axiomParser | lemmaParser).* ^^ { 
        case kList => 
          if(kList.isEmpty) 
            List() 
          else 
            kList.reduce( (left,right) => left ++ right)
      }
    }
  }
  
  object EvidenceParser {
    lazy val evidenceParser = proofParser | 
                              toolInfoParser | 
                              externalInfoParser
    
    lazy val proofParser = {
      lazy val pattern = "Proof." ~> ProofLanguageParser.proofParser <~ "End."
      log(pattern)("Proof evidence") ^^ {
        case proof => new ProofEvidence(proof)
      }
    }
    
    lazy val toolInfoParser = {
      //Parses a single KVP
      lazy val kvpParser =  {
        lazy val pattern = ident ~ ("\"" ~> notDblQuote <~ "\"")
        log(pattern)("Parsing tool info KVP") ^^ {
          case name ~ value => (name, value)
        }
      }
      
      lazy val pattern = "Tool." ~> kvpParser.* <~ "End." 
      
      log(pattern)("KVPs containing tool info") ^^ {
        case kvps => {
          //Translate a list of KVPs into a map (left = key, right = value).
          val toolInfo =
            kvps.foldLeft(Map[String,String]())( (h,kvp) => h + kvp)
          new ToolEvidence(toolInfo )
        }
      }
    }
    
    lazy val externalInfoParser = {
      lazy val pattern = "External." ~> """.*""".r <~ "End."
      log(pattern)("External Proof") ^^ {
        case file => new ExternalEvidence(new File(file))
      }
    }
  }
  
  /**
   * Parser for LISPy serialized proofs. The target of the parse are the Loaded*
   * types in core/ProofFile.scala.
   * 
   * The Lispy syntax follows:
   * (branch "name"
   *    (rule "name" <ruleInfo>)
   *    ...(more rules)...
   * )
   * ...(more branches)...
   * 
   * where <ruleInfo> is like (identifier "value")
   * The identifier of <ruleInfo> rules determines which subtype of 
   * ``LoadedRuleInfo" in generated. This mapping is defined in 
   * LoadedRuleInfo.fromName. 
   */
  object ProofLanguageParser {
    /**
     * Type of parsers for proof steps.
     */
    type StepParser = PackratParser[ProofNode.ProofStep]
    
    lazy val parserList = 
      branchP ::
      ruleP ::
      ruleInfoP ::
      Nil
      
    lazy val proofParser = log(branchP.*)("Top-level proof tree parser -- searching for a sequence of branches") ^^ {
      case branches => branches
    }
    
    //branch ::= (branch "name" <expr>?)
    lazy val branchP = {
      lazy val pattern = ("(" ~> "branch" ~> "\"" ~> ident <~ "\"") ~ 
                    ruleP.*  <~ ")"
      log(pattern)("Proof branch parser") ^^ {
        case name ~ rules => new LoadedBranch(name, rules)
      }
    }
    
    lazy val ruleP = {
      lazy val pattern = ("(" ~> "rule" ~> "\"" ~> ident <~ "\"") ~
    		  		ruleInfoP.*
      log(pattern)("Proof rule parser") ^^ {
        case name ~ ruleInfo => new LoadedRule(name, ruleInfo)
      }
    }
    
    lazy val ruleInfoP = {
      lazy val pattern = "(" ~> ident ~
                         ("\"" ~> notDblQuote <~ "\"") <~ ")"
      log(pattern)("Rule Information parser") ^^ {
        case name ~ info => EmptyRule().fromName(name, info)
      }
    }
  }

  def nameAndIndex(id: String): (String, Option[Int]) =
    try {
      val i = id.lastIndexOf("_")
      if(i <= 0) {
        (id, None)
      } else {
        val pref = id.substring(0, i)
        val idxCandidate = id.substring(i + 1)
        (pref, Some(Integer.parseInt(idxCandidate)))
      }
    } catch {
      case e: NumberFormatException => (id, None)
    }

}

// vim: set ts=4 sw=4 et:
