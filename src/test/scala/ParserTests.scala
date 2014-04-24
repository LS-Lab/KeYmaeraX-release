import org.scalatest._
import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.parser._

class ParserParenTests extends FlatSpec with Matchers {
  def makeInput(program : String) : String = {
    "Functions. B a. B b. B c. End." +
    "ProgramVariables. R p. R q. R s. End." +
    "Problem." + program + "\nEnd."
  }

  "The Parser" should "place implicit parens correctly" in {

    val equalPairs = 
      ("\\forall x . (x > 2) & a", "(\\forall x . (x > 2)) & a") ::
      Nil

    val parser = new KeYmaeraParser(false) //parser with logger.

    for(pair <- equalPairs) {
      val left : Expr = parser.runParser(makeInput(pair._1))
      val right : Expr = parser.runParser(makeInput(pair._2))
      left should be (right)
    }
  }
}
