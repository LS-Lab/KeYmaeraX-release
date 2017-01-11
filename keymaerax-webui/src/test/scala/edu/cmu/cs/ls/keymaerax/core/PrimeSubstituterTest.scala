/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/

package edu.cmu.cs.ls.keymaerax.core
import scala.collection.immutable._
import edu.cmu.cs.ls.keymaerax.btactics._
import testHelper.KeYmaeraXTestTags.{CheckinTest, SlowTest, SummaryTest, UsualTest}
import testHelper.CustomAssertions._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tags.AdvocatusTest
import TactixLibrary._

/**
  * Advocatus Test when substituting too many primes into axioms.
  * @author Yong Kiam Tan
  * @author Andre Platzer
  */
@AdvocatusTest
class PrimeSubstituterTest extends TacticTestBase {

  private val ode = DifferentialProgramConst("c", AnyArg)
  val x_ = Variable("x_",None,Real)

  //@author Andre Platzer
  "Substituting primes" should "not put primes into DS&'s evolution domain constraints" in {
    // [{x_'=c()&q(x_)}]p(||) <-> \forall t_ (t_>=0 -> ((\forall s_ ((0<=s_&s_<=t_) -> q(x_+(c()*s_)))) -> [x_:=x_+(c()*t_);]p(||)))
    val pr = ProvableSig.axioms("DS& differential equation solution")

    pr shouldBe 'proved
    a [CoreException] shouldBe thrownBy {pr(USubst(
      SubstitutionPair(FuncOf(Function("c",None,Unit,Real),Nothing), "2".asTerm) ::
        SubstitutionPair(PredOf(Function("q",None,Real,Bool),DotTerm()), GreaterEqual(DifferentialSymbol(x_),Number(5))) ::
        SubstitutionPair(UnitPredicational("p",AnyArg), "x<9".asFormula) ::
        Nil))}
    // would prove bogus [x'=2&x'>=5]x<9 <-> \forall t>=0 (\forall 0<=s<=t x'>=5 -> [x:=x+2*t;]x<9)
    // which is not valid in a state where x'=0
  }

  //@author Andre Platzer
  it should "not put primes into DS's postcondition" in {
    // [{x_'=c_()}]p_(x_) <-> \forall t_ (t_>=0 -> [x_:=x_+(c_()*t_);]p_(x_))
    val pr = AxiomInfo("DS differential equation solution").provable

    pr shouldBe 'proved
    a [CoreException] shouldBe thrownBy {pr(USubst(
      SubstitutionPair(FuncOf(Function("c_",None,Unit,Real),Nothing), "2".asTerm) ::
        SubstitutionPair(PredOf(Function("p_",None,Real,Bool),DotTerm()), Equal(DifferentialSymbol(x_),Number(5))) ::
        Nil))}
    // would prove bogus [x'=2]x'=5 <-> \forall t>=0 [x:=x+2*t;]x'=5
    // which is not valid in a state where x'=5
  }

  //@author Andre Platzer
  it should "not put primes into DS&'s postcondition" in {
    // [{x_'=c()&q(x_)}]p(||) <-> \forall t_ (t_>=0 -> ((\forall s_ ((0<=s_&s_<=t_) -> q(x_+(c()*s_)))) -> [x_:=x_+(c()*t_);]p(||)))
    val pr = ProvableSig.axioms("DS& differential equation solution")

    pr shouldBe 'proved
    a [CoreException] shouldBe thrownBy {pr(USubst(
      SubstitutionPair(FuncOf(Function("c",None,Unit,Real),Nothing), "2".asTerm) ::
        SubstitutionPair(PredOf(Function("q",None,Real,Bool),DotTerm()), True) ::
        SubstitutionPair(UnitPredicational("p",AnyArg), Equal(DifferentialSymbol(x_),Number(5))) ::
        Nil))}
    // would prove bogus [x'=2&true]x'=5 <-> \forall t>=0 (\forall 0<=s<=t true -> [x:=x+2*t;]x'=5)
    // which is not valid in a state where x'=5
  }

  //@author Yong Kiam Tan
  it should "not prove x'=1 by putting primes into DX postconditions" in withMathematica { qeTool =>
    val ante = IndexedSeq()
    val succ = IndexedSeq("x'=1".asFormula)

    val result = proveBy(Sequent(ante, succ),
      TactixLibrary.cut("true".asFormula) < (TactixLibrary.implyRi, prop) &
        TactixLibrary.cut("[{x'=1&true}]x'=1".asFormula) < (
          TactixLibrary.implyRi & byUS("DX differential skip"),
          TactixLibrary.cohide(2) & DE(1) & chase(1, 1 :: Nil) & V(1) & byUS(DerivedAxioms.equalReflex))
    )
    result should not be 'proved
    result.isProved shouldBe false
  }

  //@author Andre Platzer
  it should "not put primes into DX's evolution domain constraint" in {
    // [{c&q(||)}]p(||) -> (q(||)->p(||))
    val pr = ProvableSig.axioms("DX differential skip")

    pr shouldBe 'proved
    a [CoreException] shouldBe thrownBy {pr(USubst(
      SubstitutionPair(ode, "{x'=2}".asDifferentialProgram) ::
        SubstitutionPair(UnitPredicational("q",AnyArg), "x'>=5".asFormula) ::
        SubstitutionPair(UnitPredicational("p",AnyArg), False) ::
        Nil))}
    // would prove bogus [x'=2&x'>=5]false -> (x'>=5 -> false)
    // which is not valid in a state where x'=5
  }

  //@author Andre Platzer
  it should "not put primes into DX's postcondition" in {
    // [{c&q(||)}]p(||) -> (q(||)->p(||))
    val pr = ProvableSig.axioms("DX differential skip")

    pr shouldBe 'proved
    a [CoreException] shouldBe thrownBy {pr(USubst(
      SubstitutionPair(ode, "{x'=2}".asDifferentialProgram) ::
        SubstitutionPair(UnitPredicational("q",AnyArg), True) ::
        SubstitutionPair(UnitPredicational("p",AnyArg), "x'=2".asFormula) ::
        Nil))}
    // would prove bogus [x'=2]x'=2 -> x'=2
    // which is not valid in a state where x'=5
  }
}
