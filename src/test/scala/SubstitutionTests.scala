import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.parser.KeYmaeraParser
import edu.cmu.cs.ls.keymaera.tests.ProvabilityTestHelper
import org.scalatest.{Matchers, FlatSpec}
import testHelper.StringConverter._

/**
 * Created by nfulton on 1/14/15.
 * @author Nathan Fulton
 * @author Stefan Mitsch
 */
class SubstitutionTests extends FlatSpec with Matchers {
  val helper = new ProvabilityTestHelper()

  "Substitution in the DI differential invariant axiom" should "work" in {
    val knowledge = new KeYmaeraParser().ProofFileParser.runParser(
      """
        |Variables.
        | T x.
        | T t(T).
        | F H(T).
        | F p(T).
        |End.
        |
        |Axiom "DI differential invariant".
        |  [x'=t(x)&H(x);]p(x) <- ([x'=t(x)&H(x);](H(x)->[x':=t(x);](p(x)')))
        |End.
      """.stripMargin)

    knowledge.last.name should be("DI differential invariant")
    val axiom:Formula = knowledge.last.formula

    val x = Variable("x", None, Real)
    val aT = Apply(Function("t", None, Real, Real), CDot)
    val aH = ApplyPredicate(Function("H", None, Real, Bool), CDot)

    axiom match {
      case Imply(BoxModality(_, Imply(theH, _)), _) => theH should be (ApplyPredicate(Function("H", None, Real, Bool), x))
      case _ => fail("axiom has wrong form.")
    }
    Substitution.maybeFreeVariables(axiom) should contain only x

    val substitution = Substitution(List(
      SubstitutionPair(aT, "12345".asTerm),
      SubstitutionPair(aH, "true & 1=1".asFormula)
    ))

    val result = substitution(axiom)
    result match {
      case Imply(BoxModality(_, Imply(theH, _)), _) => theH should be ("true & 1=1".asFormula)
      case _ => fail("axiom has wrong form.")
    }
  }
}
