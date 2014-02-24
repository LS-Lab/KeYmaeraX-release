package pdl.tests

import pdl.core._

object FormulaParserTests {
  import pdl.core.Symbols._
  
  //////////////////////////////////////////////////////////////////////////////
  // Definitions
  //////////////////////////////////////////////////////////////////////////////
  abstract class FormulaParserTest extends TestCase {
    val s : String
    val f : Formula
    
    def result =  Parser.parse(s).equals(f)
    
    def message = {
      val resultStr = try {
        Parser.parse(s).prettyString
      }
      catch {
        case e:Throwable => "Error encountered:" + e.toString()
      } 
      "Expected: " + f.prettyString + "\t" + "Result: " + resultStr
    }
  }
    abstract class TermParserTest extends TestCase {
    val s : String
    val f : Formula
    
    def result =  Parser.parseSubterm(s).equals(f)
    
    def message = {
      val resultStr = try {
        Parser.parseSubterm(s)
      }
      catch {
        case e:Throwable => "Error encountered:" + e.toString()
      } 
      "Expected: " + f.toString + "\t" + "Result: " + resultStr
    }
  }
  
  
  val a = FVar(new Var("a"))
  val b = FVar(new Var("b"))
  val c = FVar(new Var("c"))
  
  //////////////////////////////////////////////////////////////////////////////
  // Terms.
  //////////////////////////////////////////////////////////////////////////////
  object prod extends FormulaParserTest {
    val s = "a+b*c"
    val f = Product(Sum(a,b),c)
  }
  object quot extends FormulaParserTest {
    val s = "a+b/c"
    val f = Quotient(Sum(a,b),c)
  }
  object plusminus extends FormulaParserTest {
    val s = "a+b-c"
    val f = Sum(a, Difference(b,c))
  }
  object fvar1 extends FormulaParserTest {
    val s = "a1"
    val f = FVar(new Var("a1"))
  }
  
  //Negative precedence.
  object neg1 extends FormulaParserTest {
    val s = "-a"
    val f = Negative(a)
  }
  object negGroup extends FormulaParserTest {
    val s = "-(a+b)"
    val f = Negative(Sum(a,b))
  }
  object negTightNegRight extends TermParserTest {
    val s = "a+-b"
    val f = Sum(a,Negative(b))
  }
  object negTightNegLeft extends TermParserTest {
    val s = "-a+b"
    val f = Negative(Sum(a,b))
  }
  object negTightNeg extends TermParserTest {
    val s = "(-(a+b))+c"
    val f = Sum(Negative(Sum(a,b)),c)
  }
  object longVarNegate extends TermParserTest {
    val s = "-abc*c"
    val f = Negative(Product(FVar(new Var("abc")), c))
  }
  
  object symbolTest extends TermParserTest {
    val s = "Sin(x)"
    val f = Symbol("Sin", FVar(new Var("x"))::Nil)
  }
  
  
  
  
  
  //////////////////////////////////////////////////////////////////////////////
  // Run tests
  //////////////////////////////////////////////////////////////////////////////
  def tests = prod             ::
	  		  quot             ::
	  		  plusminus        ::
	  		  fvar1            ::
	  		  neg1             ::
	  		  negGroup         ::
	  		  negTightNegRight ::
	  		  negTightNegLeft  ::
	  		  negTightNeg      ::
	  		  longVarNegate    ::
	  		  symbolTest       ::
	  		  Nil
  
  
  def main(args:Array[String]):Unit = {
    TestHarness.runSuite(tests)
//    negTightNegLeft.runTest
  }
  
}