/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/

package edu.cmu.cs.ls.keymaerax.core
import scala.collection.immutable._
import edu.cmu.cs.ls.keymaerax.btactics.{RandomFormula, TacticTestBase, TactixLibrary}
import testHelper.KeYmaeraXTestTags.{CheckinTest, SlowTest, SummaryTest, UsualTest}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.AdvocatusTest

/**
 * Advocatus Test when substituting systems instead of single differential equations.
 * @author Andre Platzer
 */
@AdvocatusTest
class SystemSubstituterTest extends TacticTestBase {
  import TactixLibrary._

  "Substituting into systems" should "not allow primes in ODEs for DE" in {
    // [{x_'=f(??),c&H(??)}]p(??) <-> [{c,x_'=f(??)&H(??)}][x_':=f(??);]p(??)
    val pr = Provable.axioms("DE differential effect (system)")
    pr shouldBe 'proved
    a [CoreException] shouldBe thrownBy {pr(USubst(
      SubstitutionPair(FuncOf(Function("f",None,Real,Real),Anything), "y'+1".asTerm) ::
      SubstitutionPair(PredOf(Function("H",None,Real,Bool),Anything), True) ::
      SubstitutionPair(DifferentialProgramConst("c"), AtomicODE(DifferentialSymbol(Variable("y",None,Real)), Number(2))) ::
      SubstitutionPair(PredOf(Function("p",None,Real,Bool),Anything), "x'=3".asFormula) ::
      Nil))}
  }

  "System postconditions" should "not allow ghosts in postconditions of DG differential ghost" in {
    // [{c&H(??)}]p(??) <-> \exists y_ [{c,y_'=(t()*y_)+s()&H(??)}]p(??)
    val pr = Provable.axioms("DG differential ghost")
    pr shouldBe 'proved
    a [SubstitutionClashException] shouldBe thrownBy {pr(USubst(
      SubstitutionPair(FuncOf(Function("t",None,Unit,Real),Nothing), Number(0)) ::
      SubstitutionPair(FuncOf(Function("s",None,Unit,Real),Nothing), Number(0)) ::
      SubstitutionPair(PredOf(Function("H",None,Real,Bool),Anything), True) ::
      SubstitutionPair(DifferentialProgramConst("c"), AtomicODE(DifferentialSymbol(Variable("t",None,Real)), Number(1))) ::
      SubstitutionPair(PredOf(Function("p",None,Real,Bool),Anything), "y_=0".asFormula) ::
      Nil))}
  }

  it should "not allow ghosts in postconditions of DG differential ghost constant" in {
    // [{c&H(??)}]p(??) <-> \exists y_ [{c,y_'=g()&H(??)}]p(??)
    val pr = Provable.axioms("DG differential ghost constant")
    pr shouldBe 'proved
    a [SubstitutionClashException] shouldBe thrownBy {pr(USubst(
      SubstitutionPair(FuncOf(Function("g",None,Unit,Real),Nothing), Number(0)) ::
      SubstitutionPair(PredOf(Function("H",None,Real,Bool),Anything), True) ::
      SubstitutionPair(DifferentialProgramConst("c"), AtomicODE(DifferentialSymbol(Variable("t",None,Real)), Number(1))) ::
      SubstitutionPair(PredOf(Function("p",None,Real,Bool),Anything), "y_=0".asFormula) ::
      Nil))}
  }

  it should "not allow ghosts in postconditions of DG inverse differential ghost for y_=9 -> [{y_'=5,x_'=3}]y_=9" in {
    // ([{x_'=f(??)&H(??)}]p(??))  ->  (\forall y_ [{y_'=g(??),x_'=f(??)&H(??)}]p(??))
    val pr = Provable.axioms("DG inverse differential ghost")
    pr shouldBe 'proved
    a [SubstitutionClashException] shouldBe thrownBy {pr(USubst(
      SubstitutionPair(FuncOf(Function("f",None,Real,Real),Anything), Number(3)) ::
        SubstitutionPair(FuncOf(Function("g",None,Real,Real),Anything), Number(5)) ::
        SubstitutionPair(PredOf(Function("H",None,Real,Bool),Anything), True) ::
        SubstitutionPair(PredOf(Function("p",None,Real,Bool),Anything), "y_=9".asFormula) ::
        Nil))}
    //@todo should not prove
  }

  it should "not allow ghosts in postconditions of DG inverse differential ghost system" in {
    // ([{x_'=f(??),c&H(??)}]p(??))  ->  (\forall y_ [{y_'=g(??),x_'=f(??),c&H(??)}]p(??))
    val pr = Provable.axioms("DG inverse differential ghost system")
    pr shouldBe 'proved
    a [SubstitutionClashException] shouldBe thrownBy {pr(USubst(
      SubstitutionPair(FuncOf(Function("f",None,Real,Real),Anything), Number(0)) ::
      SubstitutionPair(FuncOf(Function("g",None,Real,Real),Anything), Number(0)) ::
      SubstitutionPair(PredOf(Function("H",None,Real,Bool),Anything), True) ::
      SubstitutionPair(DifferentialProgramConst("c"), AtomicODE(DifferentialSymbol(Variable("t",None,Real)), Number(1))) ::
      SubstitutionPair(PredOf(Function("p",None,Real,Bool),Anything), "y_=0".asFormula) ::
      Nil))}
  }

  it should "not allow ghosts in postconditions of DG inverse differential ghost system for y_=9 -> [{y_'=5,x_'=3,t'=1}]y_=9" in {
    // ([{x_'=f(??),c&H(??)}]p(??))  ->  (\forall y_ [{y_'=g(??),x_'=f(??),c&H(??)}]p(??))
    val pr = Provable.axioms("DG inverse differential ghost system")
    pr shouldBe 'proved
    a [SubstitutionClashException] shouldBe thrownBy {pr(USubst(
      SubstitutionPair(FuncOf(Function("f",None,Real,Real),Anything), Number(3)) ::
      SubstitutionPair(FuncOf(Function("g",None,Real,Real),Anything), Number(5)) ::
      SubstitutionPair(PredOf(Function("H",None,Real,Bool),Anything), True) ::
      SubstitutionPair(DifferentialProgramConst("c"), AtomicODE(DifferentialSymbol(Variable("t",None,Real)), Number(1))) ::
      SubstitutionPair(PredOf(Function("p",None,Real,Bool),Anything), "y_=9".asFormula) ::
      Nil))}
    //@todo should not prove y_=9 -> [{y_'=5,x_'=3,t'=1}]y_=9 by using such a DG inverse differential ghost system
  }

  it should "not allow ghosts in postconditions of DG inverse differential ghost system System for y_<=m() -> [{y_'=x_,x_'=-b(),t'=1}]y_<=m()" in {
    // ([{x_'=f(??),c&H(??)}]p(??))  ->  (\forall y_ [{y_'=g(??),x_'=f(??),c&H(??)}]p(??))
    val pr = Provable.axioms("DG inverse differential ghost system")
    pr shouldBe 'proved
    a [SubstitutionClashException] shouldBe thrownBy {pr(USubst(
      SubstitutionPair(FuncOf(Function("f",None,Real,Real),Anything), "-b()".asTerm) ::
        SubstitutionPair(FuncOf(Function("g",None,Real,Real),Anything), Variable("x_",None,Real)) ::
        SubstitutionPair(PredOf(Function("H",None,Real,Bool),Anything), True) ::
        SubstitutionPair(DifferentialProgramConst("c"), AtomicODE(DifferentialSymbol(Variable("t",None,Real)), Number(1))) ::
        SubstitutionPair(PredOf(Function("p",None,Real,Bool),Anything), "y_<=m()".asFormula) ::
        Nil))}
    //@todo should not prove this formula by using such a DG inverse differential ghost system
  }


  "System ODEs" should "not allow ghosts in ODEs of DG differential ghost" in {
    // [{c&H(??)}]p(??) <-> \exists y_ [{c,y_'=(t()*y_)+s()&H(??)}]p(??)
    val pr = Provable.axioms("DG differential ghost")
    pr shouldBe 'proved
    a [SubstitutionClashException] shouldBe thrownBy {pr(USubst(
      SubstitutionPair(FuncOf(Function("t",None,Unit,Real),Nothing), Number(0)) ::
      SubstitutionPair(FuncOf(Function("s",None,Unit,Real),Nothing), Number(-1)) ::
      SubstitutionPair(PredOf(Function("H",None,Real,Bool),Anything), True) ::
      SubstitutionPair(DifferentialProgramConst("c"), AtomicODE(DifferentialSymbol(Variable("x",None,Real)), Variable("y_",None,Real))) ::
      SubstitutionPair(PredOf(Function("p",None,Real,Bool),Anything), "x<=10".asFormula) ::
      Nil))}
    //@todo should not prove "y_=1&x=0->[x'=y_]x<=10" by DG("y_'=-1")
  }

  it should "not allow ghosts in ODEs of DG differential ghost constant" in {
    // [{c&H(??)}]p(??) <-> \exists y_ [{c,y_'=g()&H(??)}]p(??)
    val pr = Provable.axioms("DG differential ghost constant")
    pr shouldBe 'proved
    a [SubstitutionClashException] shouldBe thrownBy {pr(USubst(
      SubstitutionPair(FuncOf(Function("g",None,Unit,Real),Nothing), Number(-1)) ::
        SubstitutionPair(PredOf(Function("H",None,Real,Bool),Anything), True) ::
        SubstitutionPair(DifferentialProgramConst("c"), AtomicODE(DifferentialSymbol(Variable("x",None,Real)), Variable("y_",None,Real))) ::
        SubstitutionPair(PredOf(Function("p",None,Real,Bool),Anything), "x<=10".asFormula) ::
        Nil))}
    //@todo should not prove "y_=1&x=0->[x'=y_]x<=10" by DGconstant("y_'=-1")
  }

  it should "not allow ghosts in ODEs of DG inverse differential ghost for y_>=0 -> \\forall y_ [{y_'=5,x_'=y_}]x_>=0" in {
    // ([{x_'=f(??)&H(??)}]p(??))  ->  (\forall y_ [{y_'=g(??),x_'=f(??)&H(??)}]p(??))
    val pr = Provable.axioms("DG inverse differential ghost")
    pr shouldBe 'proved
    a [SubstitutionClashException] shouldBe thrownBy {pr(USubst(
      SubstitutionPair(FuncOf(Function("f",None,Real,Real),Anything), Variable("y_",None,Real)) ::
        SubstitutionPair(FuncOf(Function("g",None,Real,Real),Anything), Number(5)) ::
        SubstitutionPair(PredOf(Function("H",None,Real,Bool),Anything), True) ::
        SubstitutionPair(PredOf(Function("p",None,Real,Bool),Anything), "x_>=0".asFormula) ::
        Nil))}
    //@todo should not prove
  }

  it should "not allow ghosts in ODEs of DG inverse differential ghost system for y_>=0 -> \\forall y_ [{y_'=5,x_'=y_,t'=1}]x_>=0" in {
    // ([{x_'=f(??),c&H(??)}]p(??))  ->  (\forall y_ [{y_'=g(??),x_'=f(??),c&H(??)}]p(??))
    val pr = Provable.axioms("DG inverse differential ghost system")
    pr shouldBe 'proved
    a [SubstitutionClashException] shouldBe thrownBy {pr(USubst(
      SubstitutionPair(FuncOf(Function("f",None,Real,Real),Anything), Variable("y_",None,Real)) ::
        SubstitutionPair(FuncOf(Function("g",None,Real,Real),Anything), Number(5)) ::
        SubstitutionPair(PredOf(Function("H",None,Real,Bool),Anything), True) ::
        SubstitutionPair(DifferentialProgramConst("c"), AtomicODE(DifferentialSymbol(Variable("x",None,Real)), Variable("y_",None,Real))) ::
        SubstitutionPair(PredOf(Function("p",None,Real,Bool),Anything), "x_>=0".asFormula) ::
        Nil))}
    //@todo should not prove
  }
}
