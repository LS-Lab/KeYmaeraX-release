import org.scalatest._
import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.parser._
import java.io.File
import scala.util.Random

class ParserParenTests extends FlatSpec with Matchers {
  // type declaration header for tests
  def makeInput(program : String) : String = {
    "Functions. B a. B b. B c. End." +
    "ProgramVariables. R p. R q. R r. R s. End." +
    "Problem." + program + "\nEnd."
  }

  val parser = new KeYmaeraParser(false) 
  val alpParser = parser.ProofFileParser

  "The Parser" should "place implicit parens correctly (a.k.a. resolve abiguities correctly)" in {
    val equalPairs =
      // unary operator binds stronger than binary operator
      ("! p > 0 & p < 5", "(!(p>0)) & (p<5)") ::
      ("! p = 0 & p = 5", "(!(p=0)) & (p=5)") ::
      ("! p > 0 | p < 5", "(!(p>0)) | (p<5)") ::
      ("! p > 0 -> p > 5", "(!(p>0)) -> (p>5)") ::
      ("! p > 0 <-> p > 5", "(!(p>0)) <-> (p>5)") ::
      // quantifiers do not bind logical connectives but do bind inequalities.
      ("! \\forall x . x > 0 | p < 5", "(!(\\forall x . x>0)) | (p<5)") ::
      ("! \\exists x . x > 0 | p < 5", "(!(\\exists x . x>0)) | (p<5)") ::
      ("! \\forall x . [p:=x;]p >= x | p < 5", "(!(\\forall x . ([p:=x;](p>=x)))) | (p<5)") ::
      // modalities do not bind logical connectives.
      ("[p:=1;] p>0 & p < 1", "([p:=1;](p>0)) & (p<1)") ::
      ("[p:=1;] p>0 | p < 1", "([p:=1;](p>0)) | (p<1)") ::
      ("[p:=1;] p>0 -> p < 1", "([p:=1;](p>0)) -> (p<1)") ::
      ("<p:=1;> p>0 & p < 1", "(<p:=1;>(p>0)) & (p<1)") ::
      ("<p:=1;> p>0 | p < 1", "(<p:=1;>(p>0)) | (p<1)") ::
      ("<p:=1;> p>0 -> p < 1", "(<p:=1;>(p>0)) -> (p<1)") ::
      ("\\forall x . x > 2 & a", "(\\forall x . (x > 2)) & a") ::
      ("\\forall x . x > 2 | a", "(\\forall x . (x > 2)) | a") ::
      ("\\forall x . x > 2 -> a", "(\\forall x . (x > 2)) -> a") ::
      ("\\forall x . x > 2 <-> a", "(\\forall x . (x > 2)) <-> a") ::
      ("\\exists x . x > 2 & a", "(\\exists x . (x > 2)) & a") ::
      ("\\exists x . x > 2 | a", "(\\exists x . (x > 2)) | a") ::
      ("\\exists x . x > 2 -> a", "(\\exists x . (x > 2)) -> a") ::
      ("\\exists x . x > 2 <-> a", "(\\exists x . (x > 2)) <-> a") ::
      //nested modalities
      ("< p:=1; > <p:=2; > p>0", "<p:=1;>(<p:=2;>p>0)") ::
      ("[ p:=1; ] <p:=2; > p>0", "[p:=1;](<p:=2;>p>0)") ::
      ("< p:=1; > [p:=2; ] p>0", "<p:=1;>([p:=2;]p>0)") ::
      //[], <>, \forall, \exists magic.
      ("\\forall x . [x:=1;]<x:=2;>x>0","\\forall x . ([x:=1;]<x:=2;>(x>0))") ::
      ("\\exists x . [x:=1;]<x:=2;>x>0","\\exists x . ([x:=1;]<x:=2;>(x>0))") ::
      ("[p:=0;]\\forall x . [x:=p;] \\exists y . [q := x + y; ] q > 0", "[p:=0;](\\forall  x . [x:=p;] (\\exists y . [q := x + y; ] q > 0))") ::
      // <> vs >.
      ("< ?p>q; > p > 1", "<?(p > q);>(p>1)") ::
      ("[ ?p>q; ] p > 1", "[?(p > q);](p>1)") ::
      ("< ?a; ++ ?a; > a", "< {?a;} ++ {?a;} > a") ::
      //arith.
      ("p + q * r = s", "p + (q * r) = s") ::
      ("p * q + r = s", "(p * q) + r = s") ::
      ("p - q * r = s", "p - (q * r) = s") ::
      ("p * q - r = s", "(p * q) - r = s") ::
      ("-p + q = s", "(-p) + q = s") ::
      ("p - q - s = 0", "(p-q) - s = 0") ::
      ("p^2 >= 0", "(p^2) >= 0") ::
      ("p^2 + q^2 = s^2", "(p^2) + (q^2) = (s^2)") ::
      ("p^5 * p^3 * q^2 >= 0", "(p^5) * (p^3) * (q^2) >= 0") ::
      ("1^2 + 3^2 = s^2", "(1^2) + (3^2) = (s^2)") ::
      ("p^5 * p^3 * q^2 >= 0", "(p^5) * (p^3) * (q^2) >= 0")::
      ("p^2^5 >= 0", "p^(2^5) >= 0")::
      // implicit {} either assumed correctly or rejected
      ("[ p:=1; p:=2; ++ p:=3] p>0", "[ {p:=1; p:=2;} ++ p:=3] p>0") ::
      ("[ p:=1; ++ p:=2; p:=3] p>0", "[ p:=1; ++ {p:=2; p:=3;}] p>0") ::
      ("[ p:=1; p:=2; p:=3*] p>0", "[ p:=1; p:=2; {{p:=3;}*}] p>0") ::
      ("[ p:=1; p:=2; ++ p:=3*] p>0", "[ {p:=1; p:=2;} ++ {{p:=3;}*}] p>0") ::
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

/**
 * Random formula generator
 * @author aplatzer
 */
class RandomFormula(val rand : Random = new Random()) {
  def unfoldRight[A, B](seed: B)(f: B => Option[(A,B)]): List[A] = f(seed) match {
    case Some((a,b)) => a :: unfoldRight(b)(f)
    case None => Nil
  }
  private def nextNames(n : Int) : IndexedSeq[Variable] = unfoldRight(n) { n =>
    if (n==0)
      None
    else
      Some((Variable("z" + n, None, Real), n-1))
      //Some(("x" + (rand.alphanumeric take 5).fold("")((s:String,t:String)=>s+t), n-1))
  }.to[IndexedSeq]
  def nextFormula(size : Int) = {
    val vars = nextNames(size / 3 + 1)
    rand.nextInt(10) match {
      case 0 => False
      case 1 => True
      case it if 2 until 10 contains it => vars(rand.nextInt(vars.length))
      //case it if 11 until 20 contains it => 
    }
  }
}