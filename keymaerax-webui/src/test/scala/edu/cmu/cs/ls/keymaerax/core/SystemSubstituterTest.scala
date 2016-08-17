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
      SubstitutionPair(UnitFunctional("b",Except(y),Real), Number(0)) ::
      SubstitutionPair(UnitPredicational("q",Except(y)), True) ::
      SubstitutionPair(DifferentialProgramConst("c",Except(y)), AtomicODE(DifferentialSymbol(Variable("t",None,Real)), Number(1))) ::
      SubstitutionPair(UnitPredicational("p",Except(y)), "y_=0".asFormula) ::
      Nil))}
  }

  private val inverseDGconsideredHarmless: Provable => Boolean = pr =>
    !pr.isProved || (pr.conclusion match {
        //@note this test is conservative. Replacements of p by ppp would also still be possible without endangering soundness.
      case Sequent(IndexedSeq(), IndexedSeq(Imply(
      Box(ODESystem(AtomicODE(DifferentialSymbol(x),UnitFunctional("f",Except(y1),Real)), UnitPredicational("q",Except(y2))), UnitPredicational("p",Except(y3))),
      Forall(Seq(y4), Box(ODESystem(DifferentialProduct(AtomicODE(DifferentialSymbol(y), _),
      AtomicODE(DifferentialSymbol(x2),UnitFunctional("f",Except(y5),Real))
      ), UnitPredicational("q",Except(y6))), UnitPredicational("p",Except(y7))))))) if
      y1==y && y2==y && y3==y && y5==y && y6==y && x2==x => true
      case _ => false
    })

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
      SubstitutionPair(FuncOf(Function("f",None,Real,Real),DotTerm()), Number(3)) ::
        SubstitutionPair(UnitFunctional("g",AnyArg,Real), Number(5)) ::
        SubstitutionPair(PredOf(Function("q",None,Real,Bool),DotTerm()), True) ::
        SubstitutionPair(PredOf(Function("p",None,Real,Bool),DotTerm()), "y_=9".asFormula) ::
        Nil))) should throwOrNoop[CoreException](inverseDGconsideredHarmless)
    //@note this is a mistyped substitution so near no-op would be acceptable
    theDeductionOf {pr(USubst(
      SubstitutionPair(UnitFunctional("f",AnyArg,Real), Number(3)) ::
        SubstitutionPair(UnitFunctional("g",AnyArg,Real), Number(5)) ::
        SubstitutionPair(UnitPredicational("q",AnyArg), True) ::
        SubstitutionPair(UnitPredicational("p",AnyArg), "y_=9".asFormula) ::
        Nil))} should throwOrNoop[CoreException](inverseDGconsideredHarmless)
  }

  val inverseDGSystemconsideredHarmless: Provable => Boolean = pr =>
    !pr.isProved || (pr.conclusion match {
      case Sequent(IndexedSeq(), IndexedSeq(Imply(
      Box(ODESystem(DifferentialProduct(AtomicODE(DifferentialSymbol(x),UnitFunctional("f",Except(y1),Real)),DifferentialProgramConst("c",Except(y2))), UnitPredicational("q",Except(y3))), UnitPredicational("p",Except(y4))),
      Forall(Seq(y5), Box(ODESystem(DifferentialProduct(AtomicODE(DifferentialSymbol(y6), _),
      DifferentialProduct(AtomicODE(DifferentialSymbol(x2),UnitFunctional("f",Except(y7),Real)),DifferentialProgramConst("c",Except(y8))
      )), UnitPredicational("q",Except(y9))), UnitPredicational("p",Except(y10))))))) if
      y1==y && y2==y && y3==y && y5==y && y6==y && y7==y && y8==y && y9==y && y10==y && x2==x => true
      case _ => false
    })

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
      Nil))) should throwOrNoop[CoreException](inverseDGSystemconsideredHarmless)
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


  val DGconsideredHarmless: Provable => Boolean = pr =>
    !pr.isProved || (pr.conclusion match {
      case Sequent(IndexedSeq(), IndexedSeq(Equiv(
      Box(ODESystem(DifferentialProgramConst("c",Except(y1)), UnitPredicational("q",Except(y2))), UnitPredicational("p",Except(y3))),
      Exists(Seq(y4), Box(ODESystem(DifferentialProduct(DifferentialProgramConst("c",Except(y5)),
      AtomicODE(DifferentialSymbol(y6), Plus(Times(UnitFunctional("a",Except(y7),Real), y), UnitFunctional("b",Except(y8),Real)))
      ), UnitPredicational("q",Except(y9))), UnitPredicational("p",Except(y10))))))) if
        y1==y && y2==y && y3==y && y5==y && y6==y && y7==y && y8==y && y9==y && y10==y => true
      case _ => false
    })

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
      Nil))) should throwOrNoop[CoreException](DGconsideredHarmless)
    //@todo should not prove "y_=1&x=0->[x'=y_]x<=10" by DG("y_'=-1")
  }

  val DGconstantconsideredHarmless: Provable => Boolean = pr =>
    !pr.isProved || (pr.conclusion match {
      case Sequent(IndexedSeq(), IndexedSeq(Equiv(
      Box(ODESystem(DifferentialProgramConst("c", Except(y1)), UnitPredicational("q", Except(y2))), UnitPredicational("p", Except(y3))),
      Exists(Seq(y4), Box(ODESystem(DifferentialProduct(DifferentialProgramConst("c", Except(y5)),
      AtomicODE(DifferentialSymbol(y), UnitFunctional("b", Except(y6), Real))
      ), UnitPredicational("q", Except(y7))), UnitPredicational("p", Except(y8))))))) if
      y1 == y && y2 == y && y3 == y && y4==y && y5 == y && y6 == y && y7==y && y8==y => true
      case _ => false
    })

  it should "not allow ghosts in ODEs of DG differential ghost constant" in {
    // [{c{|y_|}&q(|y_|)}]p(|y_|) <-> \exists y_ [{c{|y_|},y_'=g(|y_|)&q(|y_|)}]p(|y_|)
    val pr = Provable.axioms("DG differential ghost constant")
    pr shouldBe 'proved
    a [CoreException] shouldBe thrownBy {pr(USubst(
      SubstitutionPair(UnitFunctional("b",Except(y),Real), Number(-1)) ::
        SubstitutionPair(UnitPredicational("q",Except(y)), True) ::
        SubstitutionPair(DifferentialProgramConst("c", Except(y)), AtomicODE(DifferentialSymbol(Variable("x",None,Real)), Variable("y_",None,Real))) ::
        SubstitutionPair(UnitPredicational("p",Except(y)), "x<=10".asFormula) ::
        Nil))}
    theDeductionOf(pr(USubst(
      SubstitutionPair(FuncOf(Function("b",None,Unit,Real),Nothing), Number(-1)) ::
        SubstitutionPair(UnitPredicational("q",AnyArg), True) ::
        SubstitutionPair(DifferentialProgramConst("c", AnyArg), AtomicODE(DifferentialSymbol(Variable("x",None,Real)), Variable("y_",None,Real))) ::
        SubstitutionPair(UnitPredicational("p",AnyArg), "x<=10".asFormula) ::
        Nil))) should throwOrNoop[CoreException](DGconstantconsideredHarmless)
    //@todo should not prove "y_=1&x=0->[x'=y_]x<=10" by DGconstant("y_'=-1")
  }

  it should "not allow ghosts in ODEs of DG inverse differential ghost for y_>=0 -> \\forall y_ [{y_'=5,x_'=y_}]x_>=0" in {
    // [{x_'=f(|y_|)&q(|y_|)}]p(|y_|)  ->  \forall y_ [{y_'=g(||),x_'=f(|y_|)&q(|y_|)}]p(|y_|)
    val pr = Provable.axioms("DG inverse differential ghost")
    println(pr)
    pr shouldBe 'proved
    a [CoreException] shouldBe thrownBy {pr(USubst(
      SubstitutionPair(UnitFunctional("f",Except(y),Real), Variable("y_",None,Real)) ::
        SubstitutionPair(UnitFunctional("g",Except(y),Real), Number(5)) ::
        SubstitutionPair(UnitPredicational("q",Except(y)), True) ::
        SubstitutionPair(UnitPredicational("p",Except(y)), ".>=0".asFormula) ::
        Nil))}
    theDeductionOf(pr(USubst(
      SubstitutionPair(FuncOf(Function("f",None,Real,Real),DotTerm()), Variable("y_",None,Real)) ::
        SubstitutionPair(UnitFunctional("g",AnyArg,Real), Number(5)) ::
        SubstitutionPair(PredOf(Function("q",None,Real,Bool),DotTerm()), True) ::
        SubstitutionPair(PredOf(Function("p",None,Real,Bool),DotTerm()), ".>=0".asFormula) ::
        Nil))) should throwOrNoop[CoreException](inverseDGconsideredHarmless)
    //@note this is a mistyped substitution so near no-op would be acceptable
    theDeductionOf(pr(USubst(
      SubstitutionPair(UnitFunctional("f",AnyArg,Real), Variable("y_",None,Real)) ::
        SubstitutionPair(UnitFunctional("g",AnyArg,Real), Number(5)) ::
        SubstitutionPair(UnitPredicational("q",AnyArg), True) ::
        SubstitutionPair(UnitPredicational("p",AnyArg), "x_>=0".asFormula) ::
        Nil))) should throwOrNoop[CoreException](inverseDGconsideredHarmless)
    //@todo should not prove
  }

  it should "not allow ghosts in ODEs of DG inverse differential ghost system for y_>=0 -> \\forall y_ [{y_'=5,x_'=y_,t'=1}]x_>=0" in {
    // ([{x_'=f(||),c&H(||)}]p(||))  ->  (\forall y_ [{y_'=g(||),x_'=f(||),c&H(||)}]p(||))
    val pr = Provable.axioms("DG inverse differential ghost system")
    pr shouldBe 'proved
    a [CoreException] shouldBe thrownBy {pr(USubst(
      SubstitutionPair(UnitFunctional("f",Except(y),Real), Variable("y_",None,Real)) ::
        SubstitutionPair(UnitFunctional("g",AnyArg,Real), Number(5)) ::
        SubstitutionPair(UnitPredicational("q",Except(y)), True) ::
        SubstitutionPair(ode, AtomicODE(DifferentialSymbol(Variable("x",None,Real)), Variable("y_",None,Real))) ::
        SubstitutionPair(UnitPredicational("p",Except(y)), "x_>=0".asFormula) ::
        Nil))}
    theDeductionOf(pr(USubst(
      SubstitutionPair(UnitFunctional("f",AnyArg,Real), Variable("y_",None,Real)) ::
        SubstitutionPair(UnitFunctional("g",AnyArg,Real), Number(5)) ::
        SubstitutionPair(UnitPredicational("q",AnyArg), True) ::
        SubstitutionPair(ode, AtomicODE(DifferentialSymbol(Variable("x",None,Real)), Variable("y_",None,Real))) ::
        SubstitutionPair(UnitPredicational("p",AnyArg), "x_>=0".asFormula) ::
        Nil))) should throwOrNoop(inverseDGSystemconsideredHarmless)
    //@todo should not prove
  }
}
