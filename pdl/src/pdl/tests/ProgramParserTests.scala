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
    
    override def message = {
      val resultStr = try {
        Parser.parseProgram(s).prettyString
      } catch {
        case e:Exception => "Failed parse."
      }
      
      val expectedStr = program.prettyString
      
      "Result: " + resultStr + ". Expected: " + expectedStr
    }
    
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

  
  object sequenceIsRightAssoc extends ProgramTestCase {
    val s = "a:=1; b:=2; ?2>1; c:=a+b"
    val program = 
      Sequence( Assignment(pA, Number("1")),
      Sequence( Assignment(pB, Number("2")),
      Sequence( Test(Gt(Number("2"),Number("1"))), 
                Assignment(pC, Sum(pA.toFvar, pB.toFvar))
      )))
  }
  //////////////////////////////////////////////////////////////////////////////
  // Atomics
  //////////////////////////////////////////////////////////////////////////////
  object ptest extends ProgramTestCase {
    val s       = TEST + "a" + GT + "b"
    val program = Test(Gt(fA,fB))
  }
  
  object assign extends ProgramTestCase {
    val s       = "a" + ASSIGN + 2.toString()
    val program = Assignment(pA, Number("2"))
  }
  
  object ndassign extends ProgramTestCase {
    val s       = "a" + ASSIGN + KSTAR
    val program = NonDetAssignment(pA)
  }
  
  //////////////////////////////////////////////////////////////////////////////
  // Parallel stuff
  //////////////////////////////////////////////////////////////////////////////
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
            sequence             ::
            choice               ::
            choiceOfSequences    ::
            choiceOfSequences2   ::
            ptest                ::
            assign               ::
            ndassign             ::
            AparallelB           ::
            receiveABonC         ::
            sendABonC            ::
            sequenceIsRightAssoc ::
            Nil
  
  def main(args:Array[String]):Unit = {
    TestHarness.runSuite(tests)
  }
}