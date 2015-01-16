import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.parser.KeYmaeraParser
import edu.cmu.cs.ls.keymaera.tests.ProvabilityTestHelper
import org.scalatest.{Matchers, FlatSpec}

/**
 * Created by nfulton on 1/14/15.
 */
class SubstitutionTests extends FlatSpec with Matchers {
  val helper = new ProvabilityTestHelper()

  "Substitution in the DI differential invariant axiom" should "work" in {
    val knowledge = new KeYmaeraParser().ProofFileParser.runParser(
      """
        |Variables.
        | T x.
        | T t.
        | F H.
        | F p.
        |End.
        |
        |Axiom "DI differential invariant".
        |  [x'=t&H;]p <- ([x'=t&H;](H->[x':=t;](p')))
        |End.
      """.stripMargin)

    knowledge.last.name should be("DI differential invariant")
    val axiom:Formula = knowledge.last.formula

    val aX = Variable("x", None, Real)
    val aT = Variable("t", None, Real)
    val aH = PredicateConstant("H", None)
    val aP = Variable("p", None, Bool)

    axiom match {
      case Imply(BoxModality(_, Imply(theH, _)), _) => require(theH == aH)
      case _ => fail("axiom has wrong form.")
    }
    require(Traversals.freeVariables(axiom).contains(aT))


    val substitution = Substitution(List(
      new SubstitutionPair(aT, Number(12345)),
      new SubstitutionPair(aH, And(True, Equals(Real, Number(1), Number(1))))
    ))

    val result = substitution(axiom)
    result match {
      case Imply(BoxModality(_, Imply(theH, _)), _) => require(theH == And(True, Equals(Real,Number(1),Number(1))))
      case _ => fail("axiom has wrong form.")
    }
    require(!Traversals.freeVariables(result).contains(aT))
  }
}
