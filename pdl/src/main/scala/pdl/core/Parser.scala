package pdl.core

import scala.util.parsing.combinator.RegexParsers
import scala.util.parsing.combinator.PackratParsers
import scala.util.matching.Regex

class UnimplementedExn extends Exception

/**
 * @deprecated Warning: I'm in the process of refactoring how I handle grouping, so this parser isn't working ATM.
 */
object Parser {
  def parse(s:String):Formula = {
    val parser = new Parser()
    parser.parseAll(parser.parser, s) match {
      case parser.Success(result,next) => result
      case parser.Failure(_,_) => throw new Exception("parse failed.")
      case parser.Error(_,_) => throw new Exception("parse errored.")
    }
  }
  
  def parseProgram(s:String):Program = {
    val parser = new Parser()
    parser.parseAll(parser.ProgramParser.parser, s) match {
      case parser.Success(result,next) => result
      case parser.Failure(a,b) => throw new Exception("parse failed." + a.toString() + b.getClass().getName().toString())
      case parser.Error(a,b)   => throw new Exception("parse errored." + a.toString() + b.toString())
    }
  }
  
  def parseSubterm(s:String):Formula = {
    val parser = new Parser()
    parser.parseAll(parser.TermParser.parser, s) match {
      case parser.Success(result,next) => result
      case parser.Failure(a,b) => throw new Exception("parse failed." + a.toString() + b.getClass().getName().toString())
      case parser.Error(a,b)   => throw new Exception("parse errored." + a.toString() + b.toString())
    }
  }
}
class Parser extends RegexParsers with PackratParsers {
  ////////////////////////////////////////////////////////////////////////////
  // LOGGING ON/OFF - comment this line to turn on logging.
  ////////////////////////////////////////////////////////////////////////////
  override def log[T](p: => Parser[T])(name: String): Parser[T] = p

  ////////////////////////////////////////////////////////////////////////////
  // THE MAIN PARSER
  ////////////////////////////////////////////////////////////////////////////
  lazy val parser = FormulaParser.parser //TODO
  
  ////////////////////////////////////////////////////////////////////////////
  // Global stuff regarding grammar
  ////////////////////////////////////////////////////////////////////////////
  protected override val whiteSpace = """(\s|(?m)\(\*(\*(?!/)|[^*])*\*\)|/\*(.)*?\*/)+""".r
  protected val space = """[\ \t\n]*""".r
  protected val identifier = """[a-zA-Z][a-zA-Z0-9\_]*""".r
  
  ////////////////////////////////////////////////////////////////////////////
  // Utility Methods for Precedence Lists
  ////////////////////////////////////////////////////////////////////////////
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
  
  ////////////////////////////////////////////////////////////////////////////
  // Term Parser
  ////////////////////////////////////////////////////////////////////////////
  object TermParser {
    type SubtermParser = PackratParser[Formula] 
    
    lazy val parser = precedence.reduce(_|_)
    
    val precedence : List[SubtermParser] =
      multP ::
      divP ::
      addP ::
      subP ::
      negativeP ::
      FormulaParser.symbolP ::
      FormulaParser.varP ::
      numberP ::
      groupP ::
      Nil
    
    lazy val groupP:SubtermParser = {
      lazy val pattern = "(" ~ precedence.reduce(_|_) ~ ")"
      log(pattern)("Subterm Grouping") ^^ {
        case "(" ~ p ~ ")" => p
      }
    }
    
    lazy val addP:SubtermParser = {
      lazy val pattern = leftAssociative(precedence, addP, Some(Symbols.PLUS))
      log(pattern)(Symbols.PLUS) ^^ {
        case left ~ Symbols.PLUS ~ right => Sum(left,right)
      }
    }
    
    lazy val subP:SubtermParser = {
      lazy val pattern = leftAssociative(precedence, subP, Some(Symbols.MINUS))
      log(pattern)(Symbols.MINUS) ^^ {
        case left ~ Symbols.MINUS ~ right => Difference(left,right)
      }
    }
    
    lazy val multP:SubtermParser = {
      lazy val pattern = leftAssociative(precedence, multP, Some(Symbols.TIMES))
      log(pattern)(Symbols.TIMES) ^^ {
        case left ~ Symbols.TIMES ~ right => Product(left,right)
      }
    }
    
    lazy val divP:SubtermParser = {
      lazy val pattern = leftAssociative(precedence, divP, Some(Symbols.DIVIDE))
      log(pattern)(Symbols.DIVIDE) ^^ {
        case left ~ Symbols.DIVIDE ~ right => Quotient(left,right)
      }
    }
    
    lazy val negativeP:SubtermParser = {
      lazy val pattern = Symbols.NEGATIVE.r ~ precedence.reduce(_|_)
      log(pattern)(Symbols.NEGATIVE + "(negative)") ^^ {
        case Symbols.NEGATIVE ~ term => Negative(term)
      }
    }
    
    lazy val numberP:SubtermParser = {
      lazy val pattern = """[0-9]+(\.[0-9]+)?""".r
      log(pattern)("NUMBER") ^^ {
        case n => Number(n)
      }
    }
  }
  
  ////////////////////////////////////////////////////////////////////////////
  // Formula Parser
  ////////////////////////////////////////////////////////////////////////////
  object FormulaParser {    
    type SubformulaParser = PackratParser[Formula]
    
    lazy val parser = precedence.reduce(_|_)
    
    val precedence : List[SubformulaParser] = 
      boxP ::
      diamondP ::
      implP ::
      andP ::
      orP ::
      eqP ::  
      geqP ::
      leqP ::
      gtP ::
      ltP ::   //MAGIC WARNING. This is the tightestComparisonParser
      termP ::
      groupP ::
      trueP ::
      falseP ::
      Nil
      
      

    
    
    /**
     * This is used by the ParserParser when getting a list of differential equations.
     */
    type SubformulaSetParser = PackratParser[List[Formula]]
    lazy val listOfDerivatives:SubformulaSetParser = {
      lazy val leftOfEqP = derivativeP
      lazy val rightOfEqP = derivativeP | termP | groupP
      
      lazy val patternP = leftOfEqP ~ Symbols.EQ ~ rightOfEqP ^^ {
        case left ~ Symbols.EQ ~ right => Eq(left,right)
      }
      
      lazy val repeatingPatternP:SubformulaSetParser = rep1sep(patternP, Symbols.COMMA)
//      lazy val repeatingPatternP:SubformulaSetParser = (patternP | (patternP ~ Symbols.COMMA ~ repeatingPatternP)) ^^ {
//        case left ~ Symbols.COMMA ~ right => {
//          try {
//            right.asInstanceOf[Set[Formula]].union(Set(left.asInstanceOf[Eq]))
//          }
//          catch {
//            case e:Exception => throw new Exception("Expected set of formuals on the right.")
//          }
//        }
//        case single => single match {
//          case Eq(l,r) => Set[Formula](Eq(l,r))
//          case _ => throw new Exception("Expected to match patternP.")
//        }
//      }
      
      log(repeatingPatternP)("a'=term, b'=term, ..., c'=term")
    }
    
    lazy val groupP:SubformulaParser = {
      lazy val pattern = "(" ~ precedence.reduce(_|_) ~ ")"
      log(pattern)("Formula grouping") ^^ {
        case "(" ~ p ~ ")" => p
      }
    }
    
    lazy val termP : SubformulaParser = TermParser.parser ^^ {
      case term => term
    }
    
    /**
     * For now, we don't allow a < b < c. Therefore, each of the comparison operators
     * fails to parse if this pattern is discovered. To ensure this behavior, we only
     * allow subformulas on either side of a comparison operator to contain something
     * below the last comparison operator.
     */
    lazy val nonComparionParsers = tighterParsers(precedence, tightestComparisonParser).reduce(_|_)
    lazy val tightestComparisonParser:SubformulaParser = ltP
    
    
    lazy val implP:SubformulaParser = {
      lazy val pattern = rightAssociative(precedence, implP, Some(Symbols.ARROW))
      log(pattern)(Symbols.ARROW) ^^ {
        case left ~ _ ~ right => Impl(left,right)
      }
    }     
  
    lazy val andP : SubformulaParser = {
      lazy val pattern = leftAssociative(precedence, andP, Some(Symbols.AND))
      log(pattern)(Symbols.AND) ^^ {
        case left ~ _ ~ right => And(left,right)
      }
    }
    
    lazy val orP : SubformulaParser = {
      lazy val pattern = leftAssociative(precedence, orP, Some(Symbols.OR))
      log(pattern)(Symbols.OR) ^^ {
        case left ~ _ ~ right => Or(left,right)
      }
    }
    
    lazy val boxP : SubformulaParser = {
      lazy val pattern = Symbols.BOX_OPEN ~ ProgramParser.parser ~ Symbols.BOX_CLOSE ~ parser
      log(pattern)(Symbols.BOX_OPEN + Symbols.PROGRAM_META + Symbols.BOX_CLOSE + Symbols.FORMULA_META) ^^ {
        case Symbols.BOX_OPEN ~ p ~ Symbols.BOX_CLOSE ~ f => Box(p,f)
      }
    }
    
    lazy val diamondP : SubformulaParser = {
      lazy val pattern = Symbols.DIA_OPEN ~ ProgramParser.parser ~ Symbols.DIA_CLOSE ~ parser
      log(pattern)(Symbols.DIA_OPEN + Symbols.PROGRAM_META + Symbols.DIA_CLOSE + Symbols.FORMULA_META) ^^ {
        case Symbols.DIA_OPEN ~ p ~ Symbols.DIA_CLOSE ~ f => Diamond(p,f)
      }
    }
    
    lazy val varP : SubformulaParser = {
      lazy val pattern = identifier 
      pattern ^^ {
        case s => FVar(new Var(s))
      }
    }
    
    /**
     * TODO replace identifier with a parameter to the parser.
     */
    lazy val symbolP : SubformulaParser = {
      lazy val pattern = identifier~"("~repsep(parser,Symbols.COMMA)~")" 
      pattern ^^ {
        case name ~ _ ~ args ~ _ => new Symbol(name, args)
      }
    }
     
      
    
    lazy val derivativeP : SubformulaParser = {
      lazy val pattern = asTightAsParsers(ProgramParser.precedence, ProgramParser.pvarP).reduce(_|_) ~ Symbols.PRIME
      log(pattern)(Symbols.PRIME) ^^ {
        case pvar ~ Symbols.PRIME => pvar match {
          case PVar(v) => Derivative(PVar(v))
          case _       => throw new Exception("Expected PVar from the pvarParser, but got a non-pvar.")
        }
      }
    }
    
    lazy val trueP : SubformulaParser = {
      lazy val pattern = Symbols.TRUE.r 
      log(pattern)(Symbols.TRUE) ^^ {
        case _ => True()
      }
    }
    
    lazy val falseP : SubformulaParser = {
      lazy val pattern = Symbols.FALSE.r 
      log(pattern)(Symbols.FALSE) ^^ {
        case _ => False()
      }
    }

    lazy val eqP:SubformulaParser = {
      lazy val pattern = nonComparionParsers ~ Symbols.EQ ~ nonComparionParsers
      log(pattern)(Symbols.EQ) ^^ {
        case left ~ Symbols.EQ ~ right => Eq(left,right)
      }
    }
    
    lazy val geqP:SubformulaParser = {
      lazy val pattern = nonComparionParsers ~ Symbols.GEQ ~ nonComparionParsers
      log(pattern)(Symbols.GEQ) ^^ {
        case left ~ Symbols.GEQ ~ right => Geq(left,right)
      }
    }
    
    lazy val leqP:SubformulaParser = {
      lazy val pattern = nonComparionParsers ~ Symbols.LEQ ~ nonComparionParsers
      log(pattern)(Symbols.LEQ) ^^ {
        case left ~ Symbols.LEQ ~ right => Geq(left,right)
      }
    }
    
    lazy val gtP:SubformulaParser = {
      lazy val pattern = nonComparionParsers ~ Symbols.GT ~ nonComparionParsers
      log(pattern)(Symbols.GT) ^^ {
        case left ~ Symbols.GT ~ right => Gt(left,right)
      }
    }
    
    lazy val ltP:SubformulaParser = {
      lazy val pattern = nonComparionParsers ~ Symbols.LT ~ nonComparionParsers
      log(pattern)(Symbols.LT) ^^ {
        case left ~ Symbols.LT ~ right => Lt(left,right)
      }
    }
    
    lazy val notP:SubformulaParser = {
      lazy val pattern = Symbols.NEGATE ~ parser
      log(pattern)(Symbols.NEGATE) ^^ {
        case Symbols.NEGATE ~ f => Not(f)
      }
    }
    //This is just here as a reminder to add parsing support for new formulas
    private def ignoreMe(f:Formula) = f match {
      case Impl(l:Formula,r:Formula) => false
      case FVar(v:Var) => false
      case And(l:Formula,r:Formula) => false
      case Or(l:Formula,r:Formula) => false
      case True() => false
      case False() => false
      case Box(p:Program,f:Formula) => false
      case Diamond(p:Program,f:Formula) => false
      case Eq(l:Formula,r:Formula) => false
      case Leq(l:Formula,r:Formula) => false
      case Geq(l:Formula,r:Formula) => false
      case Gt(l:Formula,r:Formula) => false
      case Lt(l:Formula,r:Formula) => false
      case Not(f:Formula) => false
      
      
      //Subterms
      case Difference(f:Formula, f2:Formula) => false
      case Number(s:String)                  => false
      case Product(x:Formula, y:Formula)     => false
      case Quotient(x:Formula, y:Formula)    => false
      case Sum(x:Formula, y:Formula)         => false
      case Negative(f:Formula)               => false
      case Symbol(n:String, lf:List[Formula]) => false
      case Derivative(p:Program)             => false
    }
  }
  
  ////////////////////////////////////////////////////////////////////////////
  // Program Parser - used by formula parser.
  ////////////////////////////////////////////////////////////////////////////
  object ProgramParser {
    type SubprogramParser = PackratParser[Program]
    
    lazy val parser = precedence.reduce(_|_)
    
    val precedence : List[SubprogramParser] =
      parallelP ::
      choiceP ::
      sequenceP ::
      ifElseP ::
      ifP ::
      whileP ::
      closureP ::
      assignmentP ::
      nonDetAssignmentP ::
      evolutionP ::
      testP ::
      receiveP ::
      receiveMultipleP ::
      sendP :: 
      pvarP ::
      groupP     ::
      Nil
    
    lazy val ifP:SubprogramParser = {
      lazy val pattern = "if(" ~ FormulaParser.parser ~ ")" ~ space ~ "then" ~ parser ~ "fi"
      log(pattern)("if") ^^ {
        case "if(" ~ cond ~ ")" ~ _ ~ "then" ~ alpha ~ "fi" => 
          Sequence(Test(cond), alpha)
      }
    }
    
    lazy val ifElseP:SubprogramParser = {
      lazy val pattern = "if(" ~ FormulaParser.parser ~ ")" ~ space ~ "then" ~ parser ~ "else" ~ parser ~ "fi"
      log(pattern)("if-else") ^^ {
        case "if(" ~ cond ~ ")" ~ _ ~ "then" ~ alpha ~ "else" ~ beta ~ "fi" =>
          ProgramHelpers.normalize(List(Test(cond), alpha, Test(Not(cond)), beta))
      }
    }
    
    lazy val whileP:SubprogramParser = {
      lazy val pattern = "while(" ~ FormulaParser.parser ~ ")" ~ parser ~ "end"
      log(pattern)("while") ^^ {
        case "while(" ~ test ~ ")" ~ alpha ~ "end" => Sequence(
          STClosure( Sequence( Test(test), alpha ) ),
          Test(Not(test))
        )
      }
    }
    
    lazy val groupP:SubprogramParser = {
      lazy val pattern = "(" ~ precedence.reduce(_|_) ~ ")"
      log(pattern)("Program grouping") ^^ {
        case "(" ~ p ~ ")" => p
      }
    }
    
    /**
     * TDOO should this be an associative parser?
     */
    lazy val parallelP:SubprogramParser = {
      lazy val subPattern = asTightAsParsers(precedence, parallelP).reduce(_|_)
      lazy val pattern = subPattern ~ Symbols.PCOMP ~ subPattern
      log(pattern)(Symbols.PCOMP) ^^ {
        case left ~ Symbols.PCOMP ~ right => Parallel(left,right)
      }
    }
    
    lazy val channelP:PackratParser[Channel] = identifier ^^ {
      case s => new Channel(s)
    }
    
    lazy val receiveP:SubprogramParser = {
      lazy val pattern = channelP ~
                         Symbols.RECEIVE ~
                         pvarP
      log(pattern)(Symbols.RECEIVE + "(" + Symbols.PCOMP + ")") ^^ {
        case c ~ Symbols.RECEIVE ~ variable => Receive(c, Set(variable))
      }
    }
    
    lazy val receiveMultipleP:SubprogramParser = {
      lazy val pattern = channelP ~ 
                         Symbols.RECEIVE ~ 
                         Symbols.OPEN_CBRACKET ~ 
                           rep1sep(pvarP, Symbols.COMMA) ~ 
                         Symbols.CLOSE_CBRACKET
      log(pattern)(Symbols.RECEIVE + "(" + Symbols.PCOMP + ")") ^^ {
        case c ~ Symbols.RECEIVE ~ Symbols.OPEN_CBRACKET ~ variables ~ Symbols.CLOSE_CBRACKET => 
          Receive(c, variables.toSet)
      }
    }
    
    lazy val sendP:SubprogramParser = {
      lazy val pattern = channelP ~
                         Symbols.SEND ~
//                         Symbols.OPEN_CBRACKET ~
//                         rep1sep(pvarP, Symbols.COMMA) ~
//                         Symbols.CLOSE_CBRACKET ~
                         FormulaParser.termP
      
      log(pattern)(Symbols.SEND + "(" + Symbols.PCOMP + ")") ^^ {
        case c ~ Symbols.SEND ~ v => 
          Send(c, v)
      }
    }
    
    lazy val testP:SubprogramParser = {
      lazy val pattern = Symbols.TEST ~ FormulaParser.parser
      log(pattern)(Symbols.TEST) ^^ {
        case Symbols.TEST ~ f => Test(f)
      }
    }
    lazy val choiceP:SubprogramParser = {
      lazy val pattern = rightAssociative(precedence,choiceP,Some(Symbols.CHOICE))
      log(pattern)(Symbols.CHOICE) ^^ {
        case left ~ _ ~ right => Choice(left,right)
      }
    }
    
    lazy val sequenceP:SubprogramParser = {
      lazy val pattern = rightAssociativeOptional(precedence,sequenceP,Some(Symbols.SCOLON))
      log(pattern)("program" + Symbols.SCOLON + "program") ^^ {
        case left ~ Symbols.SCOLON ~ right => right match {
          case Some(rightDefined) => {
            //Make sure that the sequence is placed in normal form.
            left match {
              case Sequence(ll,lr) => Sequence(ll,lr).append(rightDefined)
              case _               => Sequence(left,rightDefined)
            }
          }
          case None               => left
        }
      }
    }

    lazy val assignmentP:SubprogramParser = {
      lazy val pattern = pvarP ~ Symbols.ASSIGN ~ FormulaParser.parser
      log(pattern)(Symbols.ASSIGN) ^^ {
        case variable ~ _ ~ formula => Assignment(variable, formula)
      }
    }
    
    lazy val closureP:SubprogramParser = {
      lazy val pattern = asTightAsParsers(precedence,closureP).reduce(_|_) ~ Symbols.KSTAR
      log(pattern)(Symbols.KSTAR) ^^ {
        case left ~ Symbols.KSTAR => STClosure(left)
      }
    }
    
    lazy val evolutionP:SubprogramParser = {
      lazy val pattern = (Symbols.OPEN_CBRACKET ~
                          FormulaParser.listOfDerivatives ~
                          Symbols.CLOSE_CBRACKET) |
                         (Symbols.OPEN_CBRACKET ~ 
                          FormulaParser.listOfDerivatives ~
                          Symbols.COMMA ~
                          FormulaParser.parser ~
                          Symbols.CLOSE_CBRACKET)
      log(pattern)("Continuous Evolution") ^^ {
        case Symbols.OPEN_CBRACKET ~ list ~ Symbols.CLOSE_CBRACKET => 
          Evolution(list.asInstanceOf[List[Formula]].toSet,True())
        case Symbols.OPEN_CBRACKET ~ list ~ Symbols.COMMA ~ condition ~ Symbols.CLOSE_CBRACKET =>
          Evolution(list.asInstanceOf[List[Formula]].toSet, condition.asInstanceOf[Formula])
      }
    }
    
    lazy val nonDetAssignmentP:SubprogramParser = {
      lazy val pattern = pvarP ~ Symbols.ASSIGN ~ Symbols.KSTAR
      log(pattern)(Symbols.ASSIGN + Symbols.KSTAR) ^^ {
        case v ~ Symbols.ASSIGN ~ Symbols.KSTAR => v match {
          case PVar(v) => NonDetAssignment(PVar(v))
          case _ => throw new Exception("Expected PVar out of pvarP but found Program.")
        }
      }
    }
    
    lazy val pvarP:PackratParser[PVar] = identifier ^^ {
      case s => PVar(new Var(s))
    }
    
    
    /**
     * This is an exhaustive match so that compile-time errors show up in this
     * file whenever Program is extended with a new constructor.
     * This should never be called.
     */
    private def ignoreMe(p:Program) = {p match {
      case Assignment(v:PVar,f:Formula) => false
      case STClosure(p:Program) => false
      case PVar(v:Var) => false
      case Sequence(l:Program,r:Program) => false
      case Choice(l:Program,r:Program) => false
      case Evolution(s:Set[Formula], f:Formula) => false 
      case NonDetAssignment(v:PVar) => false
      case Test(f:Formula) => false
      case Parallel(l:Program, r:Program) => false
      case Receive(c:Channel, sv:Set[PVar]) => false
      case Send(c:Channel, v:Formula) => false
      
      //These are all internal representations and do not need to be parsed:
      case Bottom() => true
      case CursorAfter(_) => true
      case CursorBefore(_) => true
      case Deadlock() => true
      case Epsilon() => true
      case Forward(_,_,_) => true
      case JoinedParallel(_,_) => true
      case Label(_) => true
      case NoCursor(_) => true
      case Remainder(_) => true
    }; throw new Exception("Do not call me!")}
  }
}
