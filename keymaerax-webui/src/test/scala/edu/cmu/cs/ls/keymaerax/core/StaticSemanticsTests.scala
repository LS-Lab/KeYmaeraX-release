/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.core

import edu.cmu.cs.ls.keymaerax.btactics.RandomFormula
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tagobjects.{SummaryTest, UsualTest}
import edu.cmu.cs.ls.keymaerax.tags.CheckinTest
import org.scalatest.{FlatSpec, Matchers}
import testHelper.CustomAssertions.withSafeClue
import testHelper.KeYmaeraXTestTags
import testHelper.KeYmaeraXTestTags._

import scala.collection.immutable._

/**
 * Tests static semantics.
 *
 * @author
 *   Andre Platzer
 */
@CheckinTest
class StaticSemanticsTests extends FlatSpec with Matchers {
  PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter.pp)
  private val randomTrials = 1000
  private val randomComplexity = 12
  private val rand = if (false) new RandomFormula(-6907410306474577855L) else new RandomFormula()

  "Static Semantics" should "compute v>=0&v>0 -> [{{a:=-b;++a:=5;} {x'=v,v'=a&v>=0}}*]v>=0 correctly" in {
    val fml = "v>=0&v>0 -> [{{a:=-b;++a:=5;} {x'=v,v'=a&v>=0}}*]v>=0".asFormula
    val vc = StaticSemantics(fml)
    vc.fv shouldBe SetLattice(Set(Variable("v"), Variable("b"), Variable("x")))
    vc.bv shouldBe SetLattice(Set(
      Variable("a"),
      Variable("x"),
      DifferentialSymbol(Variable("x")),
      Variable("v"),
      DifferentialSymbol(Variable("v")),
    ))
  }

  it should "compute x:=1;++{x:=0;y:=x+1;} correctly" in {
    val fml = "x:=1;++{x:=0;y:=x+1;}".asProgram
    val vc = StaticSemantics(fml)
    vc.fv shouldBe SetLattice(Set[Variable]())
    vc.fv shouldBe SetLattice.bottom
    vc.bv shouldBe SetLattice(Set(Variable("x"), Variable("y")))
    vc.mbv shouldBe SetLattice(Set(Variable("x")))
  }

  it should "compute [x:=1;++y:=2;]x>=1 correctly" in {
    val fml = "[x:=1;++y:=2;]x>=1".asFormula
    val vc = StaticSemantics(fml)
    vc.fv shouldBe SetLattice(Set(Variable("x")))
    vc.bv shouldBe SetLattice(Set(Variable("x"), Variable("y")))
  }

  it should "compute {x:=1;++x:=2;}z:=x+y; correctly" in {
    val fml = "{x:=1;++x:=2;}z:=x+y;".asProgram
    val vc = StaticSemantics(fml)
    vc.fv shouldBe SetLattice(Set(Variable("y")))
    vc.bv shouldBe SetLattice(Set(Variable("x"), Variable("z")))
    vc.mbv shouldBe SetLattice(Set(Variable("x"), Variable("z")))
  }

  it should "compute (x*y)' correctly" in {
    val fml = "(x*y)'".asTerm
    val vc = StaticSemantics(fml)
    vc shouldBe SetLattice(
      Set(Variable("x"), Variable("y"), DifferentialSymbol(Variable("x")), DifferentialSymbol(Variable("y")))
    )
  }

  it should "compute z:=0;{?false;z:=z+x;}* conservatively correctly even if x will never be really read" in {
    val fml = "z:=0;{?false;z:=z+x;}*".asProgram
    val vc = StaticSemantics(fml)
    vc.fv shouldBe SetLattice(Set(Variable("x")))
    vc.bv shouldBe SetLattice(Set(Variable("z")))
    vc.mbv shouldBe SetLattice(Set(Variable("z")))
  }

  it should "@todo test symbols, signature" ignore {}

  "Static Semantics" should "consistently compute randomly (checkin)" taggedAs (CoverageTest) in { test(10) }
  it should "consistently compute randomly (summary)" taggedAs (SummaryTest, CoverageTest) in { test(50) }
  it should "consistently compute randomly (usual)" taggedAs (UsualTest, CoverageTest) in { test(1000, 12) }
  it should "consistently compute randomly (slow)" taggedAs (SlowTest, CoverageTest) in { test(randomTrials, 20) }

  private def test(randomTrials: Int = randomTrials, randomComplexity: Int = randomComplexity): Unit = {
    for (i <- 1 to randomTrials) {
      val e = rand.nextTerm(randomComplexity)
      val randClue = "Term produced in\n\t " + i + "th run of " + randomTrials + " random trials,\n\t generated with " +
        randomComplexity + " random complexity\n\t from seed " + rand.seed

      val outString = withSafeClue("Error printing random term\n\n" + randClue) { KeYmaeraXPrettyPrinter.stringify(e) }

      withSafeClue("Random term " + outString + "\n\n" + randClue) {
        val vc = StaticSemantics(e)
        vc shouldBe StaticSemantics.freeVars(e)
        vc shouldBe StaticSemantics.freeVars(e.asInstanceOf[Expression])
        vc shouldBe StaticSemantics.vars(e)
        vc shouldBe StaticSemantics.vars(e.asInstanceOf[Expression])
        StaticSemantics.signature(e) shouldBe StaticSemantics.signature(e.asInstanceOf[Expression])
        StaticSemantics.symbols(e) shouldBe StaticSemantics.symbols(e.asInstanceOf[Expression])
      }
    }
    for (i <- 1 to randomTrials) {
      val e = rand.nextFormula(randomComplexity)
      val randClue = "Formula produced in\n\t " + i + "th run of " + randomTrials +
        " random trials,\n\t generated with " + randomComplexity + " random complexity\n\t from seed " + rand.seed

      val outString =
        withSafeClue("Error printing random formula\n\n" + randClue) { KeYmaeraXPrettyPrinter.stringify(e) }

      withSafeClue("Random formula " + outString + "\n\n" + randClue) {
        val vc = StaticSemantics(e)
        vc.fv shouldBe StaticSemantics.freeVars(e)
        vc.bv shouldBe StaticSemantics.boundVars(e)
        vc.fv shouldBe StaticSemantics.freeVars(e.asInstanceOf[Expression])
        (vc.fv ++ vc.bv) shouldBe StaticSemantics.vars(e)
        StaticSemantics.vars(e) shouldBe StaticSemantics.vars(e.asInstanceOf[Expression])
        StaticSemantics.signature(e) shouldBe StaticSemantics.signature(e.asInstanceOf[Expression])
        StaticSemantics.symbols(e) shouldBe StaticSemantics.symbols(e.asInstanceOf[Expression])
      }
    }
    for (i <- 1 to randomTrials) {
      val e = rand.nextProgram(randomComplexity)
      val randClue = "Program produced in\n\t " + i + "th run of " + randomTrials +
        " random trials,\n\t generated with " + randomComplexity + " random complexity\n\t from seed " + rand.seed

      val outString =
        withSafeClue("Error printing random program\n\n" + randClue) { KeYmaeraXPrettyPrinter.stringify(e) }

      withSafeClue("Random program " + outString + "\n\n" + randClue) {
        val vc = StaticSemantics(e)
        vc.fv shouldBe StaticSemantics.freeVars(e)
        vc.bv shouldBe StaticSemantics.boundVars(e)
        vc.mbv shouldBe StaticSemantics(e).mbv
        vc.fv shouldBe StaticSemantics.freeVars(e.asInstanceOf[Expression])
        (vc.fv ++ vc.bv) shouldBe StaticSemantics.vars(e)
        StaticSemantics.vars(e) shouldBe StaticSemantics.vars(e.asInstanceOf[Expression])
        StaticSemantics.signature(e) shouldBe StaticSemantics.signature(e.asInstanceOf[Expression])
        StaticSemantics.symbols(e) shouldBe StaticSemantics.symbols(e.asInstanceOf[Expression])
      }
    }
  }

  it should "consistently compute fir sequents" taggedAs KeYmaeraXTestTags.CoverageTest in {
    for (i <- 1 to randomTrials) {
      val e = rand.nextSequent(randomComplexity)
      val randClue = "Sequent produced in\n\t " + i + "th run of " + randomTrials +
        " random trials,\n\t generated with " + randomComplexity + " random complexity\n\t from seed " + rand.seed

      val outString =
        withSafeClue("Error printing random sequent\n\n" + randClue) { KeYmaeraXPrettyPrinter.stringify(e) }

      withSafeClue("Random sequent " + outString + "\n\n" + randClue) {
        StaticSemantics.freeVars(e) shouldBe
          e.ante.map(StaticSemantics.freeVars).foldRight(SetLattice.bottom[Variable])((a, b) => a ++ b) ++
          e.succ.map(StaticSemantics.freeVars).foldRight(SetLattice.bottom[Variable])((a, b) => a ++ b)
        StaticSemantics.boundVars(e) shouldBe
          e.ante.map(StaticSemantics.boundVars).foldRight(SetLattice.bottom[Variable])((a, b) => a ++ b) ++
          e.succ.map(StaticSemantics.boundVars).foldRight(SetLattice.bottom[Variable])((a, b) => a ++ b)
        StaticSemantics.symbols(e) shouldBe
          e.ante.map(StaticSemantics.symbols).foldRight(Set[NamedSymbol]())((a, b) => a ++ b) ++
          e.succ.map(StaticSemantics.symbols).foldRight(Set[NamedSymbol]())((a, b) => a ++ b)
        StaticSemantics.signature(e) shouldBe
          e.ante.map(StaticSemantics.signature).foldRight(Set[NamedSymbol]())((a, b) => a ++ b) ++
          e.succ.map(StaticSemantics.signature).foldRight(Set[NamedSymbol]())((a, b) => a ++ b)
      }
    }
  }

//  it should "work for crazy sequent" in {
//    val e = Sequent(Nil, IndexedSeq("z4'>=(ff(ff((0+(0*0-70))^1)/((0-(z1-(0-0)))/(62-0*0)^5*0)))'".asFormula),
//      IndexedSeq("qq()->\\forall z3 [{?true;++{{?true;}*++{?true;++?true;}{z1'=0&true}}z4:=*;}*]([{z1:=z3;}*]true|<z3:=*;>(z2>0*(0*0)<->0*0+(0-0)<=0))".asFormula,
//        "qq()".asFormula,
//        "(<{z1'=0&<{{?\\exists z3 true;}*++{{?true;?true;}*}*}{z2:=*;++{?true;?true;}*}*>((z1+(0-0))/46<=73-93->[z3:=0/0;++{?true;++?true;}++?true;]\\exists z4 [?true;++?true;](true|true))}>PP{true})'".asFormula,
//        "<z3:=*;>[?true;][?true;]\\exists z3 (<{?true;++?true;}*{?true;?true;}?true;?true;>ff(0^2)!=z2'^2|(\\exists z3 (true&true)|(0)'>=0*0)&z2' < -63^2))".asFormula))
//    println(e)
//    StaticSemantics.freeVars(e) shouldBe e.ante.map(StaticSemantics.freeVars).foldRight(SetLattice.bottom[NamedSymbol])((a,b)=>a++b) ++ e.succ.map(StaticSemantics.freeVars).foldRight(SetLattice.bottom[NamedSymbol])((a,b)=>a++b)
//    StaticSemantics.boundVars(e) shouldBe e.ante.map(StaticSemantics.boundVars).foldRight(SetLattice.bottom[NamedSymbol])((a,b)=>a++b) ++ e.succ.map(StaticSemantics.boundVars).foldRight(SetLattice.bottom[NamedSymbol])((a,b)=>a++b)
//    StaticSemantics.symbols(e) shouldBe e.ante.map(StaticSemantics.symbols).foldRight(Set[NamedSymbol]())((a,b)=>a++b) ++ e.succ.map(StaticSemantics.symbols).foldRight(Set[NamedSymbol]())((a,b)=>a++b)
//    StaticSemantics.signature(e) shouldBe e.ante.map(StaticSemantics.signature).foldRight(Set[NamedSymbol]())((a,b)=>a++b) ++ e.succ.map(StaticSemantics.signature).foldRight(Set[NamedSymbol]())((a,b)=>a++b)
//  }
}
