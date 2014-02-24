package pdl.tests

import pdl.core._

object MultiStageRewriteTests {
  //////////////////////////////////////////////////////////////////////////////
  // Definitions
  //////////////////////////////////////////////////////////////////////////////
  abstract class MultiRewriteTest extends TestCase {
    def s        : String
    def expected : Program
    
    def parsedProgram = Parser.parseProgram(s)
    def rewrittenProgram = PdlRewrite.rewrite(parsedProgram)
    
    def result = rewrittenProgram.equals(expected)
    
    def message = "Expected: " + expected.prettyString + "\tFound: " + rewrittenProgram
  }
  
  def parseOf(program:String) = Parser.parseProgram(program) 
  
  //////////////////////////////////////////////////////////////////////////////
  // Very simple tests
  //////////////////////////////////////////////////////////////////////////////
  object singleVar extends MultiRewriteTest {
    val s = "c!1 || c?x"
    val expected = parseOf("x:=1")
  }
  
  //////////////////////////////////////////////////////////////////////////////
  // Run tests
  //////////////////////////////////////////////////////////////////////////////
  def tests:List[TestCase] = singleVar :: Nil
  
  def main(arg:Array[String]):Unit = {
    TestHarness.runSuite(tests)
  }
}
