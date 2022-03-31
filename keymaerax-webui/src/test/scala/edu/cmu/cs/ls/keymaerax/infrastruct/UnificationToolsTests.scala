package edu.cmu.cs.ls.keymaerax.infrastruct

import edu.cmu.cs.ls.keymaerax.{Configuration, FileConfiguration}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter
import edu.cmu.cs.ls.keymaerax.parser.StringConverter.StringToStringConverter
import org.scalatest.{BeforeAndAfterEach, FlatSpec, Matchers}

class UnificationToolsTests extends FlatSpec with Matchers with BeforeAndAfterEach {

  override protected def beforeEach(): Unit = {
    Configuration.setConfiguration(FileConfiguration)
    PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter.pp)
  }

  "Collect substitutions" should "collect upwards" in {
    val defs = "P(x) ~> x>=0 :: nil".asDeclaration
    UnificationTools.collectSubst(
      Provable.startProof("P(x)".asFormula), 0,
      Provable.startProof("x>=0".asFormula), defs.substs).subsDefsInput should contain theSameElementsAs List(
      "P(x) ~> x>=0".asSubstitutionPair
    )
  }

  it should "collect downwards" in {
    val defs = "P(x) ~> x>=0 :: nil".asDeclaration
    UnificationTools.collectSubst(
      Provable.startProof("x>=0".asFormula), 0,
      Provable.startProof("P(x)".asFormula), defs.substs).subsDefsInput should contain theSameElementsAs List(
      "P(x) ~> x>=0".asSubstitutionPair
    )
  }

  it should "collect nested" in {
    val defs = "P(x) ~> x>=0 & Q(x) :: Q(x) ~> x<=0 :: nil".asDeclaration
    UnificationTools.collectSubst(
      Provable.startProof("P(x)".asFormula), 0,
      Provable.startProof("x>=0 & x<=0".asFormula), defs.substs).subsDefsInput should contain theSameElementsAs List(
      "P(x) ~> x>=0 & Q(x)".asSubstitutionPair, "Q(x) ~> x<=0".asSubstitutionPair
    )
  }

  it should "collect minimal nested definitions upwards" in {
    val defs = "prg{|^@|}; ~> ?Q(x); :: Q(x) ~> x>=0 :: nil".asDeclaration
    UnificationTools.collectSubst(
      Provable.startProof("[prg{|^@|};]P(x)".asFormula), 0,
      Provable.startProof("[?Q(x);]P(x)".asFormula), defs.substs).subsDefsInput should contain theSameElementsAs List(
      "prg{|^@|}; ~> ?Q(x);".asSubstitutionPair
    )
  }

  it should "collect minimal nested definitions downwards" in {
    //@note loop tactic creates several subgoals with cuts, often of the shape
    //      J(x) |- [prg;]J(x)     const(P(x)) |- [expanded(prg);]const(P(x))
    //      -----------------------------------------------------------------
    //      P(x) |- [{prg;}*]Q(x)
    // where expanded(prg) has nested definitions (predicates) that are not expanded. The first pass (on the right
    // branch) finds prg expanded and substitutes in the conclusion, the next pass (on the left branch) then has
    // conclusion P(x) |- [{expanded(prg);}*] and so should start by searching downwards from the premise
    val defs = "prg{|^@|}; ~> ?Q(x); :: Q(x) ~> x>=0 :: nil".asDeclaration
    UnificationTools.collectSubst(
      Provable.startProof("[?Q(x);]P(x)".asFormula), 0,
      Provable.startProof("[prg{|^@|};]P(x)".asFormula), defs.substs).subsDefsInput should contain theSameElementsAs List(
      "prg{|^@|}; ~> ?Q(x);".asSubstitutionPair
    )
  }

  it should "collect minimal nested definitions in any direction" in {
    val defs = "prg{|^@|}; ~> left{|^@|}; ++ right{|^@|}; :: left{|^@|}; ~> ?P(x); :: right{|^@|}; ~> ?Q(x); :: P(x) ~> x<=0 :: Q(x) ~> x>=0 :: nil".asDeclaration
    UnificationTools.collectSubst(
      Provable.startProof("[prg{|^@|};]x<=0".asFormula), 0,
      Provable.startProof("[left{|^@|}; ++ ?Q(x);]P(x)".asFormula), defs.substs).subsDefsInput should contain theSameElementsAs List(
      "prg{|^@|}; ~> left{|^@|}; ++ right{|^@|};".asSubstitutionPair,
      "right{|^@|};~>?Q(x);".asSubstitutionPair,
      "P(x) ~> x<=0".asSubstitutionPair
    )
  }

  it should "focus on expansible symbols" in {
    val defs = "prg{|^@|}; ~> a:=0;?Q(x); :: P(x) ~> x<=0 :: Q(x) ~> x>=0 :: nil".asDeclaration
    UnificationTools.collectSubst(
      Provable.startProof("[prg{|^@|};]x<=0".asFormula), 0,
      Provable.startProof("[a:=0;?Q(x);]P(x)".asFormula), defs.substs).subsDefsInput should contain theSameElementsAs List(
      "prg{|^@|}; ~> a:=0;?Q(x);".asSubstitutionPair,
      "P(x) ~> x<=0".asSubstitutionPair
    )
  }

  it should "find constifications" in {
    UnificationTools.collectSubst(
      Provable.startProof("x>=0 -> x>=0".asFormula), 0,
      Provable.startProof("x()>=0 -> x()>=0".asFormula)(ImplyRight(SuccPos(0)), 0)(Close(AntePos(0), SuccPos(0)), 0),
      List.empty).subsDefsInput should contain theSameElementsAs List(
      "x() ~> x".asSubstitutionPair
    )
  }

  it should "find constifications (2)" in {
    UnificationTools.collectSubst(
      Provable.startProof("x_>=0 & x__0<=0 -> x_>=0 & x__0<=0".asFormula), 0,
      Provable.startProof("x_()>=0 & x__0()<=0 -> x_()>=0 & x__0()<=0".asFormula)(ImplyRight(SuccPos(0)), 0)(Close(AntePos(0), SuccPos(0)), 0),
      List.empty).subsDefsInput should contain theSameElementsAs List(
      "x_() ~> x_".asSubstitutionPair,
      "x__0() ~> x__0".asSubstitutionPair
    )
  }

  it should "combine constifications and defs" in {
    val defs = "P(x) ~> x>=0 :: nil".asDeclaration
    UnificationTools.collectSubst(
      Provable.startProof("P(x) -> P(x)".asFormula), 0,
      Provable.startProof("x()>=0 -> x()>=0".asFormula)(ImplyRight(SuccPos(0)), 0)(Close(AntePos(0), SuccPos(0)), 0),
      defs.substs).subsDefsInput should contain theSameElementsAs List(
      "P(x) ~> x>=0".asSubstitutionPair,
      "x() ~> x".asSubstitutionPair
    )
  }

}
