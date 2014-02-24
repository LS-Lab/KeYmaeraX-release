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
      
      val expectedStr = PrettyPrinter.programToString(program)
      
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
  
  ///
  
  abstract class ProgramTryOrDie extends TestCase {
    def s       : String
    
    override def message = {
      val resultStr = try {
        Parser.parseProgram(s).prettyString
      } catch {
        case e:Exception => "Failed parse."
      }
      
      
      "Result: " + resultStr 
    }
    
    override def result  = testProgram(s)
        
    protected def testProgram(s:String) = { 
      try {
        val parseResult = Parser.parseProgram(s)
        true
      } catch {
        case e:ClassCastException => false
      }
    }
  }
  
  ///
  
  object sequence extends ProgramTestCase {
    val s       = "a;b"
    val program = Sequence(pA, pB)
  }
  
  object sequence3 extends ProgramTestCase {
    val s       = "a;b;a"
    val program = Sequence(pA, Sequence(pB, pA))
  }
  
  object sequenceNoEnd extends ProgramTestCase {
    val s       = "a;b;"
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
  
  object receiveAonC extends ProgramTestCase {
    val s       = "c" + RECEIVE + "a" 
    val program = Receive(new Channel("c"), Set(pA))
  }
  
  object receiveABonC extends ProgramTestCase {
    val s       = "c" + RECEIVE + OPEN_CBRACKET + "a" + COMMA + "b" + CLOSE_CBRACKET 
    val program = Receive(new Channel("c"), Set(pA,pB))
  }
  
  
  
  object sendOnC extends ProgramTestCase {
    val s       = "c" + SEND + "1"
    val program = Send(new Channel("c"), Number("1"))
  }
  
  object commentL extends ProgramTestCase {
    val s = "/*this is a comment.*/a:=0"
    val program = Assignment(pA, Number("0"))
  }
  
  object commentR extends ProgramTestCase {
    val s = "a:=0/*this is a comment.*/"
    val program = Assignment(pA, Number("0"))
  }
  
  object comment extends ProgramTestCase {
    val s = "/*this is a comment.*/a:=0;/*this is a comment.*/a:=0"
    val program = Sequence(Assignment(pA, Number("0")),Assignment(pA, Number("0")))
  }
  
  
  /////////////////////////////////////
  // Conditionals
  ////////////////////////////////////
  object iffi extends ProgramTestCase {
    val fx = FVar(new Var("x"))
    val px = PVar(new Var("x"))
    val s = "if(x>1) then x := 1 fi"
    val program = Sequence(Test(Gt(fx,Number("1"))), Assignment(px, Number("1")))
  }
  object ifelse extends ProgramTestCase {
    val fx = FVar(new Var("x"))
    val px = PVar(new Var("x"))
    val s = "if(x>1) then x := 1 else x := 2 fi"
    val program = Sequence(Test(Gt(fx,Number("1"))), 
                  Sequence(Assignment(px, Number("1")),
                  Sequence(Test(Not(Gt(fx,Number("1")))),
                           Assignment(px, Number("2"))
                           )))
  }
  
  
  
  
  /////////////////////////////////////
  // Minimal formula parsing necessary for program parsing to succeed.
  ////////////////////////////////////
  object fgrouping extends TestCase {
    def message = "Formula grouping"
      
    def result = {
      val formula = "(a=1 "+Symbols.OR+" (a=2 "+Symbols.AND+" b>2)) "+Symbols.AND+" c=3"
      val a=FVar(new Var("a"))
      val b=FVar(new Var("b"))
      val c=FVar(new Var("c"))
      val two=Number("2")
      val three=Number("3")
      val expected = And(Or(Eq(a,Number("1")), And(Eq(a,two),Gt(b,two))), Eq(c,three))
      Parser.parse(formula).equals(expected)
    }
  }
  
  
  /////////////////////////////////////
  // Empirical failures
  ////////////////////////////////////
  object domainConstraint1 extends ProgramTestCase {
    val s = "{a'=1, a>1}"
    val a = PVar(new Var("a"))
    val one = Number("1")
    val program = Evolution( Set(Eq(Derivative(a),one)) , Gt(a.toFvar,one) )
  }
  object domainConstraint2 extends ProgramTestCase {
    val s = "{a'=1, b'=2, a>1}"
    val a = PVar(new Var("a"))
    val b = PVar(new Var("b"))
    val one = Number("1")
    val program = Evolution( Set(Eq(Derivative(a),one), Eq(Derivative(b),Number("2"))) , Gt(a.toFvar,one) )
  }
  
  object domainConstraintNeg extends ProgramTestCase {
    val s = "{a'=-1, a>-1}"
    val a = PVar(new Var("a"))
    val one = Negative(Number("1"))
    val program = Evolution( Set(Eq(Derivative(a),one)) , Gt(a.toFvar,one) )
  }
  
  object emp1 extends ProgramTryOrDie {
    val s = "(?step = 1;b2_vel := b1_vel; b1_vel := 0);"
    val program = null
  }
  
  object emp2 extends ProgramTryOrDie {
    val s = "((?step = 1;b2_vel := b1_vel; b1_vel := 0);)*"
    val program = null
  }
  object emp3 extends ProgramTryOrDie {
    val s = "(step := 1;(?step = 1;b2_vel := b1_vel; b1_vel := 0);)*"
    val program = null
  }
  object emp4 extends ProgramTryOrDie {
    val s = "((step := 2; step := 1);(?step = 1;b2_vel := b1_vel; b1_vel := 0))*"
    val program = null
  }
  object emp5 extends ProgramTryOrDie {
    val s = "((step := 2; step := 1);(?step = 1;b2_vel := b1_vel; b1_vel := 0);)*"
    val program = null
  }
  
  object emp6 extends ProgramTestCase {
    val x = PVar(new Var("x"))
    val s="x:=1"
    val program = Assignment(x, Number("1"))
  }
  object emp7 extends ProgramTestCase {
    val s="c!1 || c?x"
    val c = new Channel("c")
    val x = PVar(new Var("x"))
    val program = Parallel(Send(c,Number("1")), Receive(c,Set(x)))
  }
  
  
  
  def tests = 
            sequence             ::
            sequence3            ::
            sequenceNoEnd        ::
            choice               ::
            choiceOfSequences    ::
            choiceOfSequences2   ::
            ptest                ::
            assign               ::
            ndassign             ::
            AparallelB           ::
            receiveAonC          ::
            receiveABonC         ::
            sendOnC              ::
            sequenceIsRightAssoc ::
            commentL             ::
            commentR             ::
            comment              ::
            iffi                 ::
            ifelse               ::
            fgrouping            ::
            domainConstraint1    ::
            domainConstraint2    ::
            domainConstraintNeg  ::
            //these were for debugging and could be removed probably
            emp1::
            emp2::
            emp3::
            emp4::
            emp5::
            emp6::
            emp7::
            Nil
  
  def main(args:Array[String]):Unit = {
    TestHarness.runSuite(tests)
  }
}
