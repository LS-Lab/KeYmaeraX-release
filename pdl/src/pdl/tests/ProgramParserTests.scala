package pdl.tests

import pdl.core._

object ProgramParserTests {
  import Symbols._
  
  val pA = PVar(new Var("a"))
  val pB = PVar(new Var("b"))
  val pC = PVar(new Var("c"))
  val fA = FVar(new Var("a"))
  val fB = FVar(new Var("b"))
  
  abstract class ProgramTestCase extends TestCase {
    def program : Program
    def s       : String
    
    override def message = s
    override def result  = testProgram(s,program)
        
    protected def testProgram(s:String, expected:Program) = {
      val parseResult = Parser.parseProgram(s)
      try {
        expected.equals(parseResult.asInstanceOf[Program])
      } catch {
        case e:ClassCastException => false
      }
    }
  
    protected  def testFormula(s:String, expected:Formula) = {
      val parseResult = Parser.parse(s)
      try {
        expected.equals(parseResult.asInstanceOf[Formula])
      } catch {
        case e:ClassCastException => false
      }
    }
  }
  
  object sequence extends ProgramTestCase {
    val s       = "a;b"
    val program = Sequence(pA, pB)
  }
  
  object choice extends ProgramTestCase {
    val s       = "a" + CHOICE + "b"
    val program = Choice(pA,pB) 
  }
  
  object choiceOfSequences extends ProgramTestCase {
    val s       = "a" + SCOLON + "b" + CHOICE + "c"
    val program = Choice(Sequence(pA, pB),pC) 
  }
  
  
  object choiceOfSequences2 extends ProgramTestCase {
    val s       = "(a" + CHOICE + "b)" + SCOLON + "c"
    val program = Sequence(Choice(pA,pB),pC)
  }
  
  object ptest extends ProgramTestCase {
    val s       = TEST + "a" + GT + "b"
    val program = Test(Gt(fA,fB))
  }
  
  object AparallelB extends ProgramTestCase {
    val s       = "a" + PCOMP + "b"
    val program = Parallel(pA, pB)
  }
  
  object receiveABonC extends ProgramTestCase {
    val s       = "c" + RECEIVE + OPEN_CBRACKET + "a" + COMMA + "b" + CLOSE_CBRACKET
    val program = Receive(new Channel("c"), Set(pA,pB))
  }
  
  object sendABonC extends ProgramTestCase {
    val s       = "c" + SEND + OPEN_CBRACKET + "a" + COMMA + "b" + CLOSE_CBRACKET + "1"
    val program = Send(new Channel("c"), Set(pA,pB), Number("1"))
  }
  
  
  def tests = 
            sequence           ::
            choice             ::
            choiceOfSequences  ::
            choiceOfSequences2 ::
            ptest              ::
            AparallelB         ::
            receiveABonC       ::
            sendABonC          ::
            Nil
  
  def main(args:Array[String]):Unit = {
    TestHarness.runSuite(tests)
  }
}