import edu.cmu.cs.ls.keymaera.parser.{KeYmaeraPrettyPrinter, KeYmaeraParser}
import org.scalatest.{Matchers, FlatSpec}

/**
 * Created by smitsch on 1/8/15.
 * @author Stefan Mitsch
 */
class ParsePrintParseTests extends FlatSpec with Matchers {

  // type declaration header for tests
  def makeInput(program : String) : String = {
    "Functions. B a. B b. B c. End." +
    "ProgramVariables. R p. R q. R r. R s. R r_0. End." +
    "Problem." + program + "\nEnd."
  }

  val parser = new KeYmaeraParser(false)
  val printer = new KeYmaeraPrettyPrinter()

  "Parsing of pretty-printed ODEs" should "be the same as the original parse result" in {
    val exprs =
      "[x'=y;]x>0" ::
      "[x'=y & x>0;]x>0" ::
      "[x'=y, y'=z & x>0;]x>0" ::
      "[x'=y & x>2, y'=z, z'=3 & z>1 & z>2;]x>0" :: Nil

    for (e <- exprs) {
      val expected = parser.runParser(makeInput(e))
      parser.runParser(makeInput(printer.stringify(expected))) should be(expected)
    }
  }

  it should "parse, print, and parse ODEs in sequential compositions" in {
    val exprs =
      "[x'=y;x:=2;]x>0" ::
      "[x:=2;x'=y;]x>0" ::
      "[{x'=y;}*;]x>0" ::
      "[{x'=y;x:=2;}*;]x>0" ::
      "[{x:=2;x'=y;}*;]x>0" :: Nil

    for (e <- exprs) {
      val expected = parser.runParser(makeInput(e))
      parser.runParser(makeInput(printer.stringify(expected))) should be(expected)
    }
  }

  it should "print and parse nested choices consistently" in {
    val exprs =
      "[x:=1 ++ x:=2 ++ x:=3;]x>0" ::
      "[x:=10;x:=11 ++ x:=20;x:=21 ++ x:=30;x:=31;]x>0" ::
      "[{x:=10;x:=11 ++ x:=20;x:=21 ++ x:=30;x:=31};x:=40;]x>0" ::
      "[x:=0;{x:=10;x:=11 ++ x:=20;x:=21 ++ x:=30;x:=31};x:=40;]x>0" ::
      "[{x:=1 ++ x:=2}++x:=3;]x>0" :: Nil

    for (e <- exprs) {
      val expected = parser.runParser(makeInput(e))
      parser.runParser(makeInput(printer.stringify(expected))) should be(expected)
    }
  }

  it should "print and parse sequences with superfluous parentheses" in {
    val exprs =
      "[{x:=1;x:=2;};x:=3;]x>0" ::
      "[{{x:=1;x:=2;};x:=3;};{{x:=4;};x:=5;};]x>0" :: Nil

    for (e <- exprs) {
      val expected = parser.runParser(makeInput(e))
      parser.runParser(makeInput(printer.stringify(expected))) should be(expected)
    }
  }
}
