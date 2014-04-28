import org.scalatest._
import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.parser._
import java.io.File

class ParserParenTests extends FlatSpec with Matchers {
  def makeInput(program : String) : String = {
    "Functions. B a. B b. B c. End." +
    "ProgramVariables. R p. R q. R s. End." +
    "Problem." + program + "\nEnd."
  }

  val parser = new KeYmaeraParser(false) //parser with logger.
  val alpParser = parser.ProofFileParser

  "The Parser" should "place implicit parens correctly" in {
    val equalPairs =
      ("\\forall x . (x > 2) & a", "(\\forall x . (x > 2)) & a") ::
      ("< ?p>q; >(p > 1)", "<?(p > q);>(p>1)") ::
      Nil

    for(pair <- equalPairs) {
      val left : Expr = parser.runParser(makeInput(pair._1))
      val right : Expr = parser.runParser(makeInput(pair._2))
      left should be (right)
    }
  }

  it should "fail to parse bad input" in {
    val badInputs =
      "\\forall x . x > 2 > 3" ::
      Nil

    for(badInput <- badInputs) {
      a [Exception] should be thrownBy {
        parser.runParser(makeInput(badInput))
      }
    }
  }
  
  it should "parse all examples/t/positive files" in {
    val positiveTestsDir = new File("./examples/dev/t/parsing/positive")
    positiveTestsDir.isDirectory() should be (true)
    for(testFile <- positiveTestsDir.listFiles()) {
      val src = io.Source.fromFile(testFile).mkString
      parser.runParser(src) //test fails on exception.
    }
  }
  
  it should "not parse any examples/t/negative files" in {
    val negativeTestsDir = new File("./examples/dev/t/parsing/negative")
    negativeTestsDir.isDirectory() should be (true)
    for(testFile <- negativeTestsDir.listFiles()) {
      val src = io.Source.fromFile(testFile).mkString
      a [Exception] should be thrownBy {
        parser.runParser(src)
      }
    }
  }
  
  //////////////////////////////////////////////////////////////////////////////
  // Begin ALP Parser tests
  //////////////////////////////////////////////////////////////////////////////
  
  "The ALP Parser" should "parse all examples/t/positiveALP files" in {
    val positiveTestsDir = new File("./examples/dev/t/parsing/positiveALP")
    positiveTestsDir.isDirectory() should be (true)
    for(testFile <- positiveTestsDir.listFiles()) {
      val src = io.Source.fromFile(testFile).mkString
      alpParser.runParser(src) //test fails on exception.
    }
  }
  
  it should "not parse any examples/t/negativeALP files" in {
    val negativeTestsDir = new File("./examples/dev/t/parsing/negativeALP")
    negativeTestsDir.isDirectory() should be (true)
    for(testFile <- negativeTestsDir.listFiles()) {
      val src = io.Source.fromFile(testFile).mkString
      a [Exception] should be thrownBy {
        alpParser.runParser(src)
      }
    }
  }
}
