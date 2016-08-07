/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/

package edu.cmu.cs.ls.keymaerax.core
import scala.collection.immutable._
import edu.cmu.cs.ls.keymaerax.btactics.{RandomFormula, TacticTestBase, TactixLibrary}
import testHelper.KeYmaeraXTestTags.{CheckinTest, SlowTest, SummaryTest, UsualTest}
import testHelper.CustomAssertions._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.AdvocatusTest

/**
 * Advocatus Test when substituting systems instead of single differential equations.
 * @author Andre Platzer
 */
@AdvocatusTest
class SystemSubstituterTest extends TacticTestBase {

  private val ode = DifferentialProgramConst("c", AnyArg)
  private val y = Variable("y_",None,Real)


  "Substituting into systems" should "not allow primes in ODEs for DE" in {
    // [{x_'=f(||),c&H(||)}]p(||) <-> [{c,x_'=f(||)&H(||)}][x_':=f(||);]p(||)
    val pr = Provable.axioms("DE differential effect (system)")

    pr shouldBe 'proved
    a [CoreException] shouldBe thrownBy {pr(USubst(
      SubstitutionPair(UnitFunctional("f",AnyArg,Real), "y'+1".asTerm) ::
      SubstitutionPair(UnitPredicational("q",AnyArg), True) ::
      SubstitutionPair(ode, AtomicODE(DifferentialSymbol(Variable("y",None,Real)), Number(2))) ::
      SubstitutionPair(UnitPredicational("p",AnyArg), "x'=3".asFormula) ::
      Nil))}
  }

  "System postconditions" should "not allow ghosts in postconditions of DG differential ghost" in {
    val pr = Provable.axioms("DG differential ghost")
    pr shouldBe 'proved
    a [CoreException] shouldBe thrownBy {pr(USubst(
      SubstitutionPair(UnitFunctional("a",Except(y),Real), Number(0)) ::
      SubstitutionPair(UnitFunctional("a",Except(y),Real), Number(0)) ::
      SubstitutionPair(UnitPredicational("q",Except(y)), True) ::
      SubstitutionPair(DifferentialProgramConst("c",Except(y)), AtomicODE(DifferentialSymbol(Variable("t",None,Real)), Number(1))) ::
      SubstitutionPair(UnitPredicational("p",Except(y)), "y_=0".asFormula) ::
      Nil))}
  }

  it should "not allow ghosts in postconditions of DG differential ghost constant" in {
    val pr = Provable.axioms("DG differential ghost constant")
    pr shouldBe 'proved
    a [CoreException] shouldBe thrownBy {pr(USubst(
      SubstitutionPair(UnitFunctional("g",Except(y),Real), Number(0)) ::
      SubstitutionPair(UnitPredicational("q",Except(y)), True) ::
      SubstitutionPair(DifferentialProgramConst("c",Except(y)), AtomicODE(DifferentialSymbol(Variable("t",None,Real)), Number(1))) ::
      SubstitutionPair(UnitPredicational("p",Except(y)), "y_=0".asFormula) ::
      Nil))}
  }

  it should "not allow ghosts in postconditions of DG inverse differential ghost for y_=9 -> [{y_'=5,x_'=3}]y_=9" in {
    // [{x_'=f(|y_|)&q(|y_|)}]p(|y_|)  ->  \forall y_ [{y_'=g(||),x_'=f(|y_|)&q(|y_|)}]p(|y_|)
    val pr = Provable.axioms("DG inverse differential ghost")
    pr shouldBe 'proved
    a [CoreException] shouldBe thrownBy {pr(USubst(
      SubstitutionPair(UnitFunctional("f",Except(y),Real), Number(3)) ::
        SubstitutionPair(UnitFunctional("g",AnyArg,Real), Number(5)) ::
        SubstitutionPair(UnitPredicational("q",Except(y)), True) ::
        SubstitutionPair(UnitPredicational("p",Except(y)), "y_=9".asFormula) ::
        Nil))}
    //@todo should throw or leave f,p,q untouched since they have different types
    theDeductionOf(pr(USubst(
      SubstitutionPair(FuncOf(Function("f",None,Real,Real),DotTerm), Number(3)) ::
        SubstitutionPair(UnitFunctional("g",AnyArg,Real), Number(5)) ::
        SubstitutionPair(PredOf(Function("q",None,Real,Bool),DotTerm), True) ::
        SubstitutionPair(PredOf(Function("p",None,Real,Bool),DotTerm), "y_=9".asFormula) ::
        Nil))) should throwOrNoop
    //@note this is a mistyped substitution so near no-op would be acceptable
    theDeductionOf {pr(USubst(
      SubstitutionPair(UnitFunctional("f",AnyArg,Real), Number(3)) ::
        SubstitutionPair(UnitFunctional("g",AnyArg,Real), Number(5)) ::
        SubstitutionPair(UnitPredicational("q",AnyArg), True) ::
        SubstitutionPair(UnitPredicational("p",AnyArg), "y_=9".asFormula) ::
        Nil))} should throwOrNoop
  }

  it should "not allow ghosts in postconditions of DG inverse differential ghost system" in {
    // [{x_'=f(|y_|),c{|y_|}&q(|y_|)}]p(|y_|)  ->  \forall y_ [{y_'=g(||),x_'=f(|y_|),c{|y_|}&q(|y_|)}]p(|y_|)
    val pr = Provable.axioms("DG inverse differential ghost system")
    pr shouldBe 'proved
    a [CoreException] shouldBe thrownBy { pr(USubst(
        SubstitutionPair(UnitFunctional("f",Except(y),Real), Number(0)) ::
          SubstitutionPair(UnitFunctional("g",Except(y),Real), Number(0)) ::
          SubstitutionPair(UnitPredicational("q",Except(y)), True) ::
          SubstitutionPair(ode, AtomicODE(DifferentialSymbol(Variable("t",None,Real)), Number(1))) ::
          SubstitutionPair(UnitPredicational("p",Except(y)), "y_=0".asFormula) ::
          Nil))
    }
    //@todo should throw or leave f,g,p,q untouched since they have subtly different spaces
   theDeductionOf(pr(USubst(
      SubstitutionPair(UnitFunctional("f",AnyArg,Real), Number(0)) ::
      SubstitutionPair(UnitFunctional("g",AnyArg,Real), Number(0)) ::
      SubstitutionPair(UnitPredicational("q",AnyArg), True) ::
      SubstitutionPair(ode, AtomicODE(DifferentialSymbol(Variable("t",None,Real)), Number(1))) ::
      SubstitutionPair(UnitPredicational("p",AnyArg), "y_=0".asFormula) ::
      Nil))) should throwOrNoop
  }

  it should "not allow ghosts in postconditions of DG inverse differential ghost system for y_=9 -> [{y_'=5,x_'=3,t'=1}]y_=9" in {
    // [{x_'=f(|y_|),c{|y_|}&q(|y_|)}]p(|y_|)  ->  \forall y_ [{y_'=g(||),x_'=f(|y_|),c{|y_|}&q(|y_|)}]p(|y_|)
    val pr = Provable.axioms("DG inverse differential ghost system")
    pr shouldBe 'proved
    //@todo should throw or leave f,g,p,q untouched since they have subtly different spaces
    theDeductionOf(pr(USubst(
      SubstitutionPair(UnitFunctional("f",AnyArg,Real), Number(3)) ::
      SubstitutionPair(UnitFunctional("g",AnyArg,Real), Number(5)) ::
      SubstitutionPair(UnitPredicational("q",AnyArg), True) ::
      SubstitutionPair(ode, AtomicODE(DifferentialSymbol(Variable("t",None,Real)), Number(1))) ::
      SubstitutionPair(UnitPredicational("p",AnyArg), "y_=9".asFormula) ::
      Nil)))
    //@todo should not prove y_=9 -> [{y_'=5,x_'=3,t'=1}]y_=9 by using such a DG inverse differential ghost system
  }

  it should "not allow ghosts in postconditions of DG inverse differential ghost system System for y_<=m() -> [{y_'=x_,x_'=-b(),t'=1}]y_<=m()" in {
    // [{x_'=f(|y_|),c{|y_|}&q(|y_|)}]p(|y_|)  ->  \forall y_ [{y_'=g(||),x_'=f(|y_|),c{|y_|}&q(|y_|)}]p(|y_|)
    val pr = Provable.axioms("DG inverse differential ghost system")
    pr shouldBe 'proved
    //@todo should throw or leave f,g,p,q untouched since they have subtly different spaces
    theDeductionOf(pr(USubst(
      SubstitutionPair(UnitFunctional("f",AnyArg,Real), "-b()".asTerm) ::
        SubstitutionPair(UnitFunctional("g",AnyArg,Real), Variable("x_",None,Real)) ::
        SubstitutionPair(UnitPredicational("q",AnyArg), True) ::
        SubstitutionPair(ode, AtomicODE(DifferentialSymbol(Variable("t",None,Real)), Number(1))) ::
        SubstitutionPair(UnitPredicational("p",AnyArg), "y_<=m()".asFormula) ::
        Nil)))
    //@todo should not prove this formula by using such a DG inverse differential ghost system
  }


  "System ODEs" should "not allow ghosts in ODEs of DG differential ghost" in {
    // [{c{|y_|}&q(|y_|)}]p(|y_|) <-> \exists y_ [{c{|y_|},y_'=(a(|y_|)*y_)+b(|y_|)&q(|y_|)}]p(|y_|)
    val pr = Provable.axioms("DG differential ghost")
    pr shouldBe 'proved
    a [CoreException] shouldBe thrownBy {pr(USubst(
      SubstitutionPair(UnitFunctional("a",Except(y),Real), Number(0)) ::
        SubstitutionPair(UnitFunctional("b",Except(y),Real), Number(-1)) ::
        SubstitutionPair(UnitPredicational("q",Except(y)), True) ::
        SubstitutionPair(DifferentialProgramConst("c", Except(y)), AtomicODE(DifferentialSymbol(Variable("x",None,Real)), Variable("y_",None,Real))) ::
        SubstitutionPair(UnitPredicational("p",Except(y)), "x<=10".asFormula) ::
        Nil))}
    theDeductionOf(pr(USubst(
      SubstitutionPair(FuncOf(Function("a",None,Unit,Real),Nothing), Number(0)) ::
      SubstitutionPair(FuncOf(Function("b",None,Unit,Real),Nothing), Number(-1)) ::
      SubstitutionPair(UnitPredicational("q",AnyArg), True) ::
      SubstitutionPair(DifferentialProgramConst("c", AnyArg), AtomicODE(DifferentialSymbol(Variable("x",None,Real)), Variable("y_",None,Real))) ::
      SubstitutionPair(UnitPredicational("p",AnyArg), "x<=10".asFormula) ::
      Nil))) shouldBe throwOrNoop
    //@todo should not prove "y_=1&x=0->[x'=y_]x<=10" by DG("y_'=-1")
  }

  it should "not allow ghosts in ODEs of DG differential ghost constant" in {
    // [{c&H(||)}]p(||) <-> \exists y_ [{c,y_'=g()&H(||)}]p(||)
    val pr = Provable.axioms("DG differential ghost constant")
    pr shouldBe 'proved
    a [CoreException] shouldBe thrownBy {pr(USubst(
      SubstitutionPair(FuncOf(Function("g",None,Unit,Real),Nothing), Number(-1)) ::
        SubstitutionPair(UnitPredicational("q",AnyArg), True) ::
        SubstitutionPair(DifferentialProgramConst("c", AnyArg), AtomicODE(DifferentialSymbol(Variable("x",None,Real)), Variable("y_",None,Real))) ::
        SubstitutionPair(UnitPredicational("p",AnyArg), "x<=10".asFormula) ::
        Nil))}
    //@todo should not prove "y_=1&x=0->[x'=y_]x<=10" by DGconstant("y_'=-1")
  }

  it should "not allow ghosts in ODEs of DG inverse differential ghost for y_>=0 -> \\forall y_ [{y_'=5,x_'=y_}]x_>=0" in {
    // ([{x_'=f(x_)&H(x_)}]p(x_))  ->  (\forall y_ [{y_'=g(||),x_'=f(x_)&H(x_)}]p(x_))
    val pr = Provable.axioms("DG inverse differential ghost")
    println(pr)
    pr shouldBe 'proved
    a [CoreException] shouldBe thrownBy {pr(USubst(
      SubstitutionPair(FuncOf(Function("f",None,Real,Real),DotTerm), Variable("y_",None,Real)) ::
        SubstitutionPair(UnitFunctional("g",AnyArg,Real), Number(5)) ::
        SubstitutionPair(PredOf(Function("q",None,Real,Bool),DotTerm), True) ::
        SubstitutionPair(PredOf(Function("p",None,Real,Bool),DotTerm), ".>=0".asFormula) ::
        Nil))}
    //@note this is a mistyped substitution so near no-op would be acceptable
    a [CoreException] shouldBe thrownBy {pr(USubst(
      SubstitutionPair(UnitFunctional("f",AnyArg,Real), Variable("y_",None,Real)) ::
        SubstitutionPair(UnitFunctional("g",AnyArg,Real), Number(5)) ::
        SubstitutionPair(UnitPredicational("q",AnyArg), True) ::
        SubstitutionPair(UnitPredicational("p",AnyArg), "x_>=0".asFormula) ::
        Nil))}
    //@todo should not prove
  }

  it should "not allow ghosts in ODEs of DG inverse differential ghost system for y_>=0 -> \\forall y_ [{y_'=5,x_'=y_,t'=1}]x_>=0" in {
    // ([{x_'=f(||),c&H(||)}]p(||))  ->  (\forall y_ [{y_'=g(||),x_'=f(||),c&H(||)}]p(||))
    val pr = Provable.axioms("DG inverse differential ghost system")
    pr shouldBe 'proved
    a [CoreException] shouldBe thrownBy {pr(USubst(
      SubstitutionPair(UnitFunctional("f",AnyArg,Real), Variable("y_",None,Real)) ::
        SubstitutionPair(UnitFunctional("g",AnyArg,Real), Number(5)) ::
        SubstitutionPair(UnitPredicational("q",AnyArg), True) ::
        SubstitutionPair(ode, AtomicODE(DifferentialSymbol(Variable("x",None,Real)), Variable("y_",None,Real))) ::
        SubstitutionPair(UnitPredicational("p",AnyArg), "x_>=0".asFormula) ::
        Nil))}
    //@todo should not prove
  }
}
