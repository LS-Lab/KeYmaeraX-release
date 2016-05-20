/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.core

import edu.cmu.cs.ls.keymaerax.btactics.{RandomFormula, StaticSemanticsTools}
import edu.cmu.cs.ls.keymaerax.core.StaticSemantics.VCF
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXParser, KeYmaeraXPrettyPrinter}
import testHelper.KeYmaeraXTestTags.{CheckinTest, SlowTest, SummaryTest, UsualTest}

import scala.collection.immutable
import scala.collection.immutable._
import org.scalatest.{FlatSpec, Matchers}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
/**
 * Tests static semantics.
  *
 * @author Andre Platzer
 */
class StaticSemanticsTests extends FlatSpec with Matchers {
  val randomTrials = 40000
  val randomComplexity = 6
  val rand = new RandomFormula()

  "Static Semantics" should "compute v>=0&v>0 -> [{{a:=-b;++a:=5;} {x'=v,v'=a&v>=0}}*]v>=0 correctly" in {
    val fml = "v>=0&v>0 -> [{{a:=-b;++a:=5;} {x'=v,v'=a&v>=0}}*]v>=0".asFormula
    val vc = StaticSemantics(fml)
    vc.fv shouldBe SetLattice(Set(Variable("v"),Variable("b"),Variable("x")))
    vc.bv shouldBe SetLattice(Set(Variable("a"),Variable("x"),DifferentialSymbol(Variable("x")),Variable("v"),DifferentialSymbol(Variable("v"))))
  }

  it should "compute x:=1;++{x:=0;y:=x+1;} correctly" in {
    val fml = "x:=1;++{x:=0;y:=x+1;}".asProgram
    val vc = StaticSemantics(fml)
    vc.fv shouldBe SetLattice(Set[Variable]())
    vc.fv shouldBe SetLattice.bottom
    vc.bv shouldBe SetLattice(Set(Variable("x"),Variable("y")))
    vc.mbv shouldBe SetLattice(Set(Variable("x")))
  }

  it should "compute [x:=1;++y:=2;]x>=1 correctly" in {
    val fml = "[x:=1;++y:=2;]x>=1".asFormula
    val vc = StaticSemantics(fml)
    vc.fv shouldBe SetLattice(Set(Variable("x")))
    vc.bv shouldBe SetLattice(Set(Variable("x"),Variable("y")))
  }

  it should "compute {x:=1;++x:=2;}z:=x+y; correctly" in {
    val fml = "{x:=1;++x:=2;}z:=x+y;".asProgram
    val vc = StaticSemantics(fml)
    vc.fv shouldBe SetLattice(Set(Variable("y")))
    vc.bv shouldBe SetLattice(Set(Variable("x"),Variable("z")))
    vc.mbv shouldBe SetLattice(Set(Variable("x"),Variable("z")))
  }

  it should "compute (x*y)' correctly" in {
    val fml = "(x*y)'".asTerm
    val vc = StaticSemantics(fml)
    vc shouldBe SetLattice(Set(Variable("x"),Variable("y"),DifferentialSymbol(Variable("x")),DifferentialSymbol(Variable("y"))))
  }

  it should "compute z:=0;{?false;z:=z+x;}* conservatively correctly even if x will never be really read" in {
    val fml = "z:=0;{?false;z:=z+x;}*".asProgram
    val vc = StaticSemantics(fml)
    vc.fv shouldBe SetLattice(Set(Variable("x")))
    vc.bv shouldBe SetLattice(Set(Variable("z")))
    vc.mbv shouldBe SetLattice(Set(Variable("z")))
  }

  ignore should "@todo test symbols, signature" in {}


  "Static Semantics" should "consistently compute (checkin)" taggedAs(CheckinTest) in {test(10)}
  it should "consistently compute (summary)" taggedAs(SummaryTest) in {test(50)}
  it should "consistently compute (usual)" taggedAs(UsualTest) in {test(1000,10)}
  it should "consistently compute (slow)" taggedAs(SlowTest) in {test(randomTrials,20)}

  private def test(randomTrials: Int= randomTrials, randomComplexity: Int = randomComplexity) = {
    for (i <- 1 to randomTrials) {
      val e = rand.nextTerm(randomComplexity)
      val vc = StaticSemantics(e)
      vc shouldBe StaticSemantics.freeVars(e)
      vc shouldBe StaticSemantics.freeVars(e.asInstanceOf[Expression])
      vc shouldBe StaticSemantics.vars(e)
      vc shouldBe StaticSemantics.vars(e.asInstanceOf[Expression])
      StaticSemantics.signature(e) shouldBe StaticSemantics.signature(e.asInstanceOf[Expression])
      StaticSemantics.symbols(e) shouldBe StaticSemantics.symbols(e.asInstanceOf[Expression])
    }
    for (i <- 1 to randomTrials) {
      val e = rand.nextFormula(randomComplexity)
      val vc = StaticSemantics(e)
      vc.fv shouldBe StaticSemantics.freeVars(e)
      vc.bv shouldBe StaticSemantics.boundVars(e)
      vc.fv shouldBe StaticSemantics.freeVars(e.asInstanceOf[Expression])
      (vc.fv++vc.bv) shouldBe StaticSemantics.vars(e)
      StaticSemantics.vars(e) shouldBe StaticSemantics.vars(e.asInstanceOf[Expression])
      StaticSemantics.signature(e) shouldBe StaticSemantics.signature(e.asInstanceOf[Expression])
      StaticSemantics.symbols(e) shouldBe StaticSemantics.symbols(e.asInstanceOf[Expression])
    }
    for (i <- 1 to randomTrials) {
      val e = rand.nextProgram(randomComplexity)
      val vc = StaticSemantics(e)
      vc.fv shouldBe StaticSemantics.freeVars(e)
      vc.bv shouldBe StaticSemantics.boundVars(e)
      vc.mbv shouldBe StaticSemantics(e).mbv
      vc.fv shouldBe StaticSemantics.freeVars(e.asInstanceOf[Expression])
      (vc.fv++vc.bv) shouldBe StaticSemantics.vars(e)
      StaticSemantics.vars(e) shouldBe StaticSemantics.vars(e.asInstanceOf[Expression])
      StaticSemantics.signature(e) shouldBe StaticSemantics.signature(e.asInstanceOf[Expression])
      StaticSemantics.symbols(e) shouldBe StaticSemantics.symbols(e.asInstanceOf[Expression])
    }
    for (i <- 1 to randomTrials) {
      val e = rand.nextSequent(randomComplexity)
      StaticSemantics.freeVars(e) shouldBe e.ante.map(StaticSemantics.freeVars).foldRight(SetLattice.bottom[NamedSymbol])((a,b)=>a++b) ++ e.succ.map(StaticSemantics.freeVars).foldRight(SetLattice.bottom[NamedSymbol])((a,b)=>a++b)
      StaticSemantics.boundVars(e) shouldBe e.ante.map(StaticSemantics.boundVars).foldRight(SetLattice.bottom[NamedSymbol])((a,b)=>a++b) ++ e.succ.map(StaticSemantics.boundVars).foldRight(SetLattice.bottom[NamedSymbol])((a,b)=>a++b)
      StaticSemantics.symbols(e) shouldBe e.ante.map(StaticSemantics.symbols).foldRight(Set[NamedSymbol]())((a,b)=>a++b) ++ e.succ.map(StaticSemantics.symbols).foldRight(Set[NamedSymbol]())((a,b)=>a++b)
      StaticSemantics.signature(e) shouldBe e.ante.map(StaticSemantics.signature).foldRight(Set[NamedSymbol]())((a,b)=>a++b) ++ e.succ.map(StaticSemantics.signature).foldRight(Set[NamedSymbol]())((a,b)=>a++b)
    }
  }
}
