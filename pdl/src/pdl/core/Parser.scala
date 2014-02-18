package core.io

import scala.util.parsing.combinator.RegexParsers
import scala.util.parsing.combinator.PackratParsers
import scala.util.matching.Regex
import core._

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
  protected override val whiteSpace = """(\s|(?m)\(\*(\*(?!/)|[^*])*\*\))+""".r
  protected val identifier = """[a-zA-Z]+[a-zA-Z0-9\_]*""".r
  
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
  
  ////////////////////////////////////////////////////////////////////////////
  // Term Parser
  ////////////////////////////////////////////////////////////////////////////
  object TermParser {
    type SubtermParser = PackratParser[SpecialTerm] 
    
    lazy val parser = precedence.reduce(_|_)
    
    val precedence : List[SubtermParser] =
      multP ::
      divP ::
      addP ::
      subP ::
      numberP ::
      Nil
    
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
        case left ~ Symbols.DIVIDE ~ right => Product(left,right)
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
      ltP ::   //MAGIC WARNING. tightestComparisonParser
      value ::
      Nil
      
    lazy val value:SubformulaParser = log(termP | varP | trueP | falseP | group)("values and groups")
    lazy val group = "(" ~> parser <~ ")"
    
    lazy val termP : SubformulaParser = TermParser.parser ^^ {
      case term => FTerm(term)
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
    
    lazy val varP : SubformulaParser = identifier ^^ {
      case s => FVar(s)
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
    
        
    //This is just here as a reminder to add parsing support for new formulas
    private def ignoreMe(f:Formula) = f match {
      case Impl(l:Formula,r:Formula) => false
      case Not(f:Formula) => false
      case FVar(s:String) => false
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
    }
  }
  
  ////////////////////////////////////////////////////////////////////////////
  // Program Parser - used by formula parser.
  ////////////////////////////////////////////////////////////////////////////
  object ProgramParser {
    type SubprogramParser = PackratParser[Program]
    
    lazy val parser = precedence.reduce(_|_)
    
    val precedence : List[SubprogramParser] = 
      choiceP ::
      sequenceP ::
      assignmentP ::
      closureP ::
      pvarP ::
      Nil
      
    lazy val choiceP:SubprogramParser = {
      lazy val pattern = rightAssociative(precedence,choiceP,Some(Symbols.CHOICE))
      log(pattern)(Symbols.CHOICE) ^^ {
        case left ~ _ ~ right => Choice(left,right)
      }
    }
    
    lazy val sequenceP:SubprogramParser = {
      lazy val pattern = leftAssociative(precedence,sequenceP,Some(Symbols.SCOLON))
      log(pattern)(Symbols.SCOLON) ^^ {
        case left ~ _ ~ right => Sequence(left,right)
      }
    }
    
    lazy val assignmentP:SubprogramParser = {
      lazy val pattern = leftAssociative(precedence,assignmentP,Some(Symbols.ASSIGN))
      log(pattern)(Symbols.ASSIGN) ^^ {
        case left ~ _ ~ right => left match {
          case PVar(s) => Assignment(PVar(s),right)
          case _ => throw new Exception("Assignment to non-programvariable detected!")
        }
      }
    }
    
    lazy val closureP:SubprogramParser = {
      lazy val pattern = asTightAsParsers(precedence,closureP).reduce(_|_) ~ Symbols.KSTAR
      log(pattern)(Symbols.KSTAR) ^^ {
        case left ~ Symbols.KSTAR => STClosure(left)
      }
    }
    
    lazy val pvarP:SubprogramParser = identifier ^^ {
      case s => PVar(s)
    }
    
    
    //This is just here as a reminder to add parsing support for new programs
    private def ignoreMe(p:Program) = p match {
      case Assignment(v:PVar,p:Program) => false
      case STClosure(p:Program) => false
      case PVar(s:String) => false
      case Sequence(l:Program,r:Program) => false
      case Choice(l:Program,r:Program) => false
    }
  }
}