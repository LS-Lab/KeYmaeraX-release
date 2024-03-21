/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.core

import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.btactics.macros.DerivationInfoAugmentors._
import edu.cmu.cs.ls.keymaerax.btactics.macros._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tagobjects.NotfixedTest
import edu.cmu.cs.ls.keymaerax.tags.AdvocatusTest

import scala.collection.immutable._

/**
 * Advocatus Test when substituting too many primes into axioms.
 * @author
 *   Yong Kiam Tan
 * @author
 *   Andre Platzer
 */
@AdvocatusTest
class PrimeSubstituterTest extends TacticTestBase {

  private val ode = DifferentialProgramConst("c", AnyArg)
  private val x_ = Variable("x_", None, Real)

  // @author Andre Platzer
  "Substituting primes" should "not put primes into DS&'s evolution domain constraints" in {
    // [{x_'=c()&q(x_)}]p(||) <-> \forall t_ (t_>=0 -> ((\forall s_ ((0<=s_&s_<=t_) -> q(x_+(c()*s_)))) -> [x_:=x_+(c()*t_);]p(||)))
    val pr = ProvableSig.axioms("DS& differential equation solution")

    pr shouldBe Symbol("proved")
    the[CoreException] thrownBy {
      pr(USubst(
        SubstitutionPair(FuncOf(Function("c", None, Unit, Real), Nothing), "2".asTerm) :: SubstitutionPair(
          PredOf(Function("q", None, Real, Bool), DotTerm()),
          GreaterEqual(DifferentialSymbol(x_), Number(5)),
        ) :: SubstitutionPair(UnitPredicational("p", AnyArg), "x<9".asFormula) :: Nil
      ))
    } should have message
      """Substitution clash:
        |USubstOne{(c()~>2), (q(.)~>x_'>=5), (p(||)~>x < 9)}
        |is not ({x_,x_'})-admissible
        |for x_'>=5
        |when substituting in q(x_)
        |""".stripMargin
    // would prove bogus [x'=2&x'>=5]x<9 <-> \forall t>=0 (\forall 0<=s<=t x'>=5 -> [x:=x+2*t;]x<9)
    // which is not valid in a state where x'=0
  }

  // @author Andre Platzer
  it should "not put primes into DS's postcondition" in withTactics {
    // [{x_'=c_()}]p_(x_) <-> \forall t_ (t_>=0 -> [x_:=x_+(c_()*t_);]p_(x_))
    val pr = AxiomInfo("DS differential equation solution").provable

    pr shouldBe Symbol("proved")
    the[CoreException] thrownBy {
      pr(USubst(
        SubstitutionPair(FuncOf(Function("c_", None, Unit, Real), Nothing), "2".asTerm) :: SubstitutionPair(
          PredOf(Function("p_", None, Real, Bool), DotTerm()),
          Equal(DifferentialSymbol(x_), Number(5)),
        ) :: Nil
      ))
    } should have message
      """Substitution clash:
        |USubstOne{(c_()~>2), (p_(.)~>x_'=5)}
        |is not ({x_,x_'})-admissible
        |for x_'=5
        |when substituting in p_(x_)
        |""".stripMargin
    // would prove bogus [x'=2]x'=5 <-> \forall t>=0 [x:=x+2*t;]x'=5
    // which is not valid in a state where x'=5
  }

  // @author Andre Platzer
  it should "not put primes into DS&'s postcondition elder style" in {
    // [{x_'=c()&q(x_)}]p(||) <-> \forall t_ (t_>=0 -> ((\forall s_ ((0<=s_&s_<=t_) -> q(x_+(c()*s_)))) -> [x_:=x_+(c()*t_);]p(||)))
    val pr = ProvableSig.axioms("DS& differential equation solution")

    pr shouldBe Symbol("proved")
    try {
      pr(USubst(
        SubstitutionPair(FuncOf(Function("c", None, Unit, Real), Nothing), "2".asTerm) ::
          SubstitutionPair(PredOf(Function("q", None, Real, Bool), DotTerm()), True) ::
          SubstitutionPair(UnitPredicational("p", AnyArg), Equal(DifferentialSymbol(x_), Number(5))) :: Nil
      ))
      // harmless semi-no-op is an acceptable result
      StaticSemantics.symbols(pr.conclusion) should not contain UnitPredicational("p", AnyArg)
    } catch {
      case _: CoreException =>
      case ex: Throwable => fail("Expected a CoreException, but got " + ex)
    }
    // would prove bogus [x'=2&true]x'=5 <-> \forall t>=0 (\forall 0<=s<=t true -> [x:=x+2*t;]x'=5)
    // which is not valid in a state where x'=5
  }

  // @author Andre Platzer
  it should "not put primes into DS&'s postcondition" in {
    // [{x_'=c()&q(x_)}]p(||) <-> \forall t_ (t_>=0 -> ((\forall s_ ((0<=s_&s_<=t_) -> q(x_+(c()*s_)))) -> [x_:=x_+(c()*t_);]p(||)))
    val pr = ProvableSig.axioms("DS& differential equation solution")

    pr shouldBe Symbol("proved")
    the[CoreException] thrownBy {
      pr(USubst(
        SubstitutionPair(FuncOf(Function("c", None, Unit, Real), Nothing), "2".asTerm) ::
          SubstitutionPair(PredOf(Function("q", None, Real, Bool), DotTerm()), True) :: SubstitutionPair(
            UnitPredicational("p", Except(DifferentialSymbol(x_) :: Nil)),
            Equal(DifferentialSymbol(x_), Number(5)),
          ) :: Nil
      ))
    } should have message "Core requirement failed: Space-compatible substitution expected: (p(|x_'|)~>x_'=5)"
    // would prove bogus [x'=2&true]x'=5 <-> \forall t>=0 (\forall 0<=s<=t true -> [x:=x+2*t;]x'=5)
    // which is not valid in a state where x'=5
  }

  // @author Yong Kiam Tan
  it should "EXPLOIT: not prove x'=1 by putting primes into DX postconditions" taggedAs
    (NotfixedTest, testHelper.KeYmaeraXTestTags.AdvocatusTest) in withMathematica { _ =>
      // @note test is supposed to fail until DX axiom is fixed

      val ante = IndexedSeq()
      val succ = IndexedSeq("x'=1".asFormula)

      val result = proveBy(
        Sequent(ante, succ),
        TactixLibrary.cut("true".asFormula) < (TactixLibrary.implyRi, prop) &
          TactixLibrary.cut("[{x'=1&true}]x'=1".asFormula) <
          (
            TactixLibrary.implyRi & byUS(Ax.DX),
            TactixLibrary.cohide(2) & DE(1) & chase(1, 1 :: Nil) & V(1) & byUS(Ax.equalReflexive),
          ),
      )
      result should not be Symbol("proved")
      result.isProved shouldBe false
    }

  // @author Andre Platzer
  it should "not put primes into DX's evolution domain constraint" taggedAs
    (NotfixedTest, testHelper.KeYmaeraXTestTags.AdvocatusTest) in {
      // [{c&q(||)}]p(||) -> (q(||)->p(||))
      val pr = ProvableSig.axioms("DX differential skip")

      pr shouldBe Symbol("proved")
      // @note currently core datastructure assertion prevents bug until DX axiom is fixed
      the[CoreException] thrownBy {
        pr(USubst(
          SubstitutionPair(ode, "{x'=2}".asDifferentialProgram) ::
            SubstitutionPair(UnitPredicational("q", AnyArg), "x'>=5".asFormula) ::
            SubstitutionPair(UnitPredicational("p", AnyArg), False) :: Nil
        ))
      } should have message "Core requirement failed: No differentials in evolution domain constraints {{x'=2} & x'>=5}"
      // would prove bogus [x'=2&x'>=5]false -> (x'>=5 -> false)
      // which is not valid in a state where x'=5
    }

  // @author Andre Platzer
  it should "EXPLOIT: not put primes into DX's postcondition" taggedAs
    (NotfixedTest, testHelper.KeYmaeraXTestTags.AdvocatusTest) in {
      // @note test is supposed to fail until DX axiom is fixed

      // [{c&q(||)}]p(||) -> (q(||)->p(||))
      val pr = ProvableSig.axioms("DX differential skip")

      pr shouldBe Symbol("proved")
      a[CoreException] shouldBe thrownBy {
        pr(USubst(
          SubstitutionPair(ode, "{x'=2}".asDifferentialProgram) ::
            SubstitutionPair(UnitPredicational("q", AnyArg), True) ::
            SubstitutionPair(UnitPredicational("p", AnyArg), "x'=2".asFormula) :: Nil
        ))
      }
      // would prove bogus [x'=2]x'=2 -> x'=2
      // which is not valid in a state where x'=5
    }
}
