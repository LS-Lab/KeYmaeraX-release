import org.scalatest._
import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.parser._

class ParserParenTests extends FlatSpec with Matchers {
  def makeInput(program : String) : String = {
    "Functions. B a. B b. B c. End." +
    "ProgramVariables. R p. R q. R s. End." +
    "Problem." + program + "\nEnd."
  }

  "left and right" should "match" in {
    val parser = new KeYmaeraParser()

    val pairs = 
      ("\\forall x . (x > 2) & a", "(\\forall x . (x > 2)) & a") ::
      Nil

    for(pair <- pairs) {
      val left : Expr = parser.runParser(makeInput(pair._1))
      val right : Expr = parser.runParser(makeInput(pair._2))
      left should be (right)
    }
  }

  it should "not match" in {
    //counter-examples...
  }

}

