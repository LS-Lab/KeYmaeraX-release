/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraParser
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tactics.NameCategorizer
import testHelper.ProvabilityTestHelper
import org.scalatest.{Matchers, FlatSpec}

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
    val aT = FuncOf(Function("t", None, Real, Real), DotTerm)
    val aH = PredOf(Function("H", None, Real, Bool), DotTerm)

    axiom match {
      case Imply(Box(_, Imply(theH, _)), _) => theH should be (PredOf(Function("H", None, Real, Bool), x))
      case _ => fail("axiom has wrong form.")
    }
    NameCategorizer.maybeFreeVariables(axiom) should contain only x

    val substitution = USubst(List(
      SubstitutionPair(aT, "12345".asTerm),
      SubstitutionPair(aH, "true & 1=1".asFormula)
    ))

    val result = substitution(axiom)
    result match {
      case Imply(Box(_, Imply(theH, _)), _) => theH should be ("true & 1=1".asFormula)
      case _ => fail("axiom has wrong form.")
    }
  }
}
