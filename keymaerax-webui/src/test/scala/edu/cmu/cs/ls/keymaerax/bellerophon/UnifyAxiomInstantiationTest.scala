package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.core.{Formula, Provable}
import edu.cmu.cs.ls.keymaerax.tags.SummaryTest
import edu.cmu.cs.ls.keymaerax.tools.KeYmaera
import org.scalatest.{FlatSpec, Matchers}

import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

/**
  * Test whether unification algorithm can instantiate axioms correctly.
  *
  * @author Andre Platzer
  */
@SummaryTest
class UnifyAxiomInstantiationTest extends FlatSpec with Matchers {
  KeYmaera.init(Map.empty)

  val unify = UnificationMatch

  private def instantiate(axiom: String, instance: Formula): Boolean = {
    val ax: Formula = Provable.axiom(axiom)
    val u = unify(ax, instance)
    u(ax) shouldBe instance
    true
  }


  "Unification instantiation sample" should "instantiate <>" in {
    instantiate("<> diamond", "![x:=x+1;{x'=55}]!x>=99 <-> <x:=x+1;{x'=55}>x>=99".asFormula)
  }
  it should "instantiate [:=] assign 1" in {
    instantiate("[:=] assign", "[x:=z;]x^2>=9 <-> z^2>=9".asFormula)
  }
  it should "instantiate [:=] assign 2" in {
    instantiate("[:=] assign", "[x:=2*x+1;]x^3>=9*x <-> (2*x+1)^3>=9*(2*x+1)".asFormula)
  }
  it should "instantiate [++]" in {
    instantiate("[++] choice", "[x:=x+1;++{x:=0;{y'=-2}}]x>=y <-> [x:=x+1;]x>=y & [x:=0;{y'=-2}]x>=y".asFormula)
  }
  it should "instantiate [;]" in {
    instantiate("[;] compose", "[x:=x+1;{x:=0;{y'=-2}}]x>=y <-> [x:=x+1;][x:=0;{y'=-2}]x>=y".asFormula)
  }
  it should "instantiate [*]" in {
    instantiate("[*] iterate", "[{x:=x+1;{x:=0;{y'=-2}}}*]x>=y <-> x>=y & [x:=x+1;{x:=0;{y'=-2}}][{x:=x+1;{x:=0;{y'=-2}}}*]x>=y".asFormula)
  }

  "Unification" should "instantiate some schematic axioms" in {
  }

  //@todo add random schematic instantiations based on FormulaAugmentor.replaceAll
}
