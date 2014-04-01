package edu.cmu.cs.ls.keymaera.parser

import scala.util.parsing.combinator._
import scala.util.parsing.combinator.lexical._
import scala.util.parsing.combinator.syntactical._
import edu.cmu.cs.ls.keymaera.core._
import scala.util.matching.Regex
import scala.annotation.elidable
import scala.annotation.elidable._
import scala.collection.immutable.HashMap


/**
 * Parser for KeYmaera4 lemma and axiom files.
 * @author Nathan Fulton
 */
class ProofFileParser extends RegexParsers with PackratParsers {    
  lazy val metaVariablesP = {
    lazy val pattern = "\\metaVariables" ~ "{" ~ rep1sep(vardefP, ";") ~ ";".? ~ "}"
    
    log(pattern)("\\programVariables section.") ^^ {
      case "\\metaVariables" ~ "{" ~ variables ~ extraScolon ~ "}" => variables
    }
  }

  lazy val vardefP : PackratParser[NamedSymbol] = ident ~ ident ^^ {
    //Note: it might be necessary to give these arguments indices.
    case rsort ~ name => if(rsort.equals("P")) {
      new ProgramConstant(name)
    }
    else {
      new PredicateConstant(name)
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  // Lemmas section.
  //////////////////////////////////////////////////////////////////////////////
  lazy val lemmaP = {
    lazy val pattern = "\\lemmas" ~ "{" ~> """[\w\W\s\S\d\D\n\r]+}""".r 
    log(pattern)("\\lemma section (extract a string)") ^^ {
      case programText => programText.substring(0, programText.length()-1) //remove trailig }
    }
  } 
    
  lazy val fileParser = metaVariablesP.? ~ lemmaP ^^ {
    case variables ~ problemText => {
      val programs:List[ProgramConstant] = variables match {
        case Some(l) => l.filter(_.isInstanceOf[ProgramConstant]).map(_.asInstanceOf[ProgramConstant])
        case None    => List[ProgramConstant]()
      }
      val formulas = variables match {
        case Some(l) => l.filter(_.isInstanceOf[PredicateConstant]).map(_.asInstanceOf[PredicateConstant])
        case None    => List[PredicateConstant]()
      }
      (programs, formulas, problemText)
    }
  }
  
  
  //////////////////////////////////////////////////////////////////////////////
  // Public-facing interface.
  //////////////////////////////////////////////////////////////////////////////
  def parse(s:String):List[LoadedKnowledge] = {
    val parser = new ProofFileParser()
    
    //Parse file.
    val (programs,predicateConstants,lemmasText) = 
      parser.parseAll(parser.fileParser, s) match {
        case parser.Success(result,next) => result
        case parser.Failure(_,_) => throw new Exception("parse failed.")
        case parser.Error(_,_) => throw new Exception("parse error.")
      }
    
    val functions = List[Function]()
    val formulas = List[Variable]()
    
    //Parse the axioms and lemmas.
    val knowledgeParser = parser.makeParser(formulas, functions, predicateConstants,programs)
    val parseResult = parser.parseAll(knowledgeParser, lemmasText) match {
        case parser.Success(result,next) => result
        case parser.Failure(_,_) => throw new Exception("parse failed.")
        case parser.Error(_,_) => throw new Exception("parse error.")
    }
    
    parseResult
  }


  def makeParser(
      variables:List[Variable],
      functions:List[Function],
      predicates : List[PredicateConstant],
      programs : List[ProgramConstant]) : PackratParser[List[LoadedKnowledge]] = 
  {
    def parseFormulatext(text:String) = {
      val kp = (new KeYmaeraParser())
      lazy val formulaParser = new kp.FormulaParser(variables,functions,predicates,programs).parser
      kp.parseAll(formulaParser, text) match {
        case kp.Success(result,next) => result
        case kp.Failure(_,_) => throw new Exception("parse failed.")
        case kp.Error(_,_) => throw new Exception("parse error.")
      }
    }
  
    lazy val evidenceParser : PackratParser[Evidence] = EvidenceParser.parser
    
    lazy val lemmaParser    : PackratParser[LoadedLemma]   = {
      lazy val pattern = "Lemma \"" ~ ident ~ "." ~ """.*""".r ~ "." ~ "End." ~ ("Evidence." ~ evidenceParser ~ "End.").*
      log(pattern)("Lemma statement") ^^ {
        case _ ~ name ~ _ ~ formula ~ _ ~ _ ~ evidence => {
          val evidenceList = evidence.map(ev => ev match {case _ ~ e ~ _ => e})
          new LoadedLemma(name, parseFormulatext(formula), evidenceList)
        }
      }
    }
    
    lazy val axiomParser    : PackratParser[LoadedAxiom] = {
      lazy val pattern = "Axiom" ~ "\"" ~ ident ~ "\"" ~ "." ~ """.*""".r
      log(pattern)("Axiom statement") ^^ {
        case "Axiom" ~ "\"" ~ name ~ "\"" ~ "." ~ formula => 
          new LoadedAxiom(name, parseFormulatext(formula))
      }
    }
    
    (lemmaParser | axiomParser).*
  }
  
  /**
   * Evidence is usually a proof, but might also be:
   *   + a tool used for real arith. quantifier elimination (e.g. Mathematica,
   *   etc.)
   *   + ???
   */
  object EvidenceParser {
    type EvidenceSubparser = PackratParser[Evidence]

    lazy val parser = parsers.reduce(_|_)
    
    lazy val parsers = 
//      proofParser ::
      toolInfoP ::
      Nil
    
    lazy val toolInfoP = {
      lazy val pattern = (ident ~ ":" ~ """.*""".r).*
      log(pattern)("Evidence") ^^ {
        case evidences => {
          val map = new HashMap[String,String]() ++
            evidences.map(e => e match { case name ~ _ ~ value => (name,value) })
          new ToolEvidence(map)
        }
      }
    }
  }

  protected override val whiteSpace = 
    """(\s|(?m)\(\*(\*(?!/)|[^*])*\*\)|/\*(.)*?\*/|\/\*[\w\W\s\S\d\D]+?\*\/)+""".r
  protected val space               = """[\ \t\n]*""".r
  /**
   * ``ident" should match function, variable and sort names.
   */
  protected val ident               = """[a-zA-Z][a-zA-Z0-9\_]*""".r 
}