import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics._
import edu.cmu.cs.ls.keymaera.tactics.Tactics.PositionTactic
import testHelper.StringConverter._

/**
 * Created by nfulton on 2/5/15.
 * @author Nathan Fulton
 * @author Stefan Mitsch
 */
class SyntacticDerivationTests extends TacticTestSuite {
  "AndDerivativeT tactics" should "atomize" in {
    val f = "[x:=2;](1=1 & 2=2)'".asFormula

    val tactic = SyntacticDerivationInContext.AndDerivativeT(SuccPosition(0, PosInExpr(1::Nil)))

    val node = helper.runTactic(tactic, helper.formulaToNode(f), mustApply = true)
    node.openGoals().flatMap(_.sequent.ante) shouldBe empty
    node.openGoals().flatMap(_.sequent.succ) should contain only "[x:=2;]((1=1)' & (2=2)')".asFormula
  }

  it should "agree on atomization" in {
    val f = " [x:=2;](1=1 & 2=2)' ".asFormula

    val tactic1 = SyntacticDerivationInContext.AndDerivativeT(SuccPosition(0, PosInExpr(1::Nil)))
    val node1 = helper.runTactic(tactic1, helper.formulaToNode(f), mustApply = true)

    val tactic2 = SyntacticDerivationInContext.AndDerivativeAtomizeT(SuccPosition(0, PosInExpr(1::Nil)))
    val node2 = helper.runTactic(tactic2, helper.formulaToNode(f), mustApply = true)

    node1.openGoals().flatMap(_.sequent.ante) shouldBe empty
    node1.openGoals().flatMap(_.sequent.succ) should contain only "[x:=2;]((1=1)' & (2=2)')".asFormula
    node2.openGoals().flatMap(_.sequent.ante) shouldBe node2.openGoals().flatMap(_.sequent.ante)
    node2.openGoals().flatMap(_.sequent.succ) shouldBe node2.openGoals().flatMap(_.sequent.succ)
  }

  "OrDerivativeT tactics" should "atomize" in {
    val f = helper.parseFormula( "[x:=2;](1=1 | 2=2)' ")
    val tactic = SyntacticDerivationInContext.OrDerivativeT(SuccPosition(0, PosInExpr(1::Nil)))

    val node = helper.runTactic(tactic, helper.formulaToNode(f), mustApply = true)
    node.openGoals().flatMap(_.sequent.ante) shouldBe empty
    node.openGoals().flatMap(_.sequent.succ) should contain only "[x:=2;]((1=1)' & (2=2)')".asFormula
  }

  it should "agree on atomization" in {
    val f = " [x:=2;](1=1 | 2=2)' ".asFormula

    val tactic1 = SyntacticDerivationInContext.OrDerivativeT(SuccPosition(0, PosInExpr(1::Nil)))
    val node1 = helper.runTactic(tactic1, helper.formulaToNode(f), mustApply = true)

    val tactic2 = SyntacticDerivationInContext.OrDerivativeAtomizeT(SuccPosition(0, PosInExpr(1::Nil)))
    val node2 = helper.runTactic(tactic2, helper.formulaToNode(f), mustApply = true)

    node1.openGoals().flatMap(_.sequent.ante) shouldBe empty
    node1.openGoals().flatMap(_.sequent.succ) should contain only "[x:=2;]((1=1)' & (2=2)')".asFormula
    node2.openGoals().flatMap(_.sequent.ante) shouldBe node2.openGoals().flatMap(_.sequent.ante)
    node2.openGoals().flatMap(_.sequent.succ) shouldBe node2.openGoals().flatMap(_.sequent.succ)
  }

  def testTermOperation(sNoParen : String, tNoParen : String, innerOp : String, outerOp: String, axTactic : DerivativeAxiomInContextTactic, atomizePosTactic : PositionTactic, aggregatePosTactic : PositionTactic) = {
    val tactic = axTactic(SuccPosition(0, PosInExpr(1::Nil)))
    val atomizeTactic = atomizePosTactic(SuccPosition(0, PosInExpr(1::Nil)))

    val node = helper.formulaToNode(s"[x:=2;]($sNoParen $innerOp $tNoParen)'".asFormula)
    val node2 = helper.formulaToNode(s"[x:=2;]($sNoParen $innerOp $tNoParen)'".asFormula)

    val result = helper.runTactic(tactic, node, mustApply = true)
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only s"[x:=2;](($sNoParen)' $outerOp ($tNoParen)')".asFormula

    val result2 = helper.runTactic(atomizeTactic, node2, mustApply = true)
    result2.openGoals().flatMap(_.sequent.ante) shouldBe result.openGoals().flatMap(_.sequent.ante)
    result2.openGoals().flatMap(_.sequent.succ) shouldBe result.openGoals().flatMap(_.sequent.succ)
  }

  import SyntacticDerivationInContext._

  "=" should "work on x,y" in {
    testTermOperation("x", "y", "=", "=", EqualsDerivativeT, EqualsDerivativeAtomizeT, EqualsDerivativeAggregateT)
  }
  ">=" should "work on x,y" in {
    testTermOperation("x", "y", ">=",">=", GreaterEqualDerivativeT, GreaterEqualDerivativeAtomizeT, GreaterEqualDerivativeAggregateT)
  }
  "<=" should "work on x,y" in {
    testTermOperation("x", "y", "<=","<=", LessEqualDerivativeT, LessEqualDerivativeAtomizeT, LessEqualDerivativeAggregateT)
  }

  //These axioms don't follow the above pattern, so we need something slightly modified.

  ">" should "work on x,y" in {
    testTermOperation("x", "y", ">",">=", GreaterThanDerivativeT, GreaterThanDerivativeAtomizeT, GreaterThanDerivativeAggregateT)
  }
  "<" should "work on x,y" in {
    testTermOperation("x", "y", "<", "<=", LessThanDerivativeT, LessThanDerivativeAtomizeT, LessThanDerivativeAggregateT)
  }
  "!=" should "work on x,y" in {
    testTermOperation("x", "y", "!=", "=", NotEqualsDerivativeT, NotEqualsDerivativeAtomizeT, NotEqualsDerivativeAggregateT)
  }


  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Syntactic derivation of terms
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  "syntactic derivation of negation" should "work on x,y" in {
    val outerFormula = " (-(x+x))' = 0".asFormula
    val innerFormula = " -((x+x)') = 0".asFormula

    val node = helper.formulaToNode(outerFormula)
    val tactic = NegativeDerivativeT(SuccPosition(0, PosInExpr(0 :: Nil)))
    val result = helper.runTactic(tactic,node, mustApply = true)
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only innerFormula
  }

  it should "work in context" in {
    val outerFormula = "a=b & (-(x+x))' = 0 -> c>d".asFormula
    val innerFormula = "a=b & -((x+x)') = 0 -> c>d".asFormula

    val node = helper.formulaToNode(outerFormula)
    val tactic = NegativeDerivativeT(SuccPosition(0, PosInExpr(0 :: 1 :: 0 :: Nil)))
    val result = helper.runTactic(tactic,node, mustApply = true)
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only innerFormula
  }

  def innerOuterTest(innerFormula:Formula, outerFormula:Formula, axTactic:TermAxiomTactic) = {
    //first one direction.
    val node = helper.formulaToNode(outerFormula)
    val tactic = axTactic(SuccPosition(0, PosInExpr(0 :: Nil)))
    helper.runTactic(tactic,node, true)
    require(containsOpenGoal(node, innerFormula))
  }

  "syntactic derivation of addition" should "work on x,y" in {
    val in = helper.parseFormula(" (x'+y') = 0")
    val out = helper.parseFormula(" (x+y)' = 0")
    innerOuterTest(in,out,AddDerivativeT)
  }

  "syntactic derivation of subtraction" should "work on x,y" in {
    val in = helper.parseFormula(" (x'-y') = 0")
    val out = helper.parseFormula(" (x-y)' = 0")
    innerOuterTest(in,out,SubtractDerivativeT)
  }

  "syntactic derivation of multiplication" should "work on x,y" in {
    val in = helper.parseFormula(" ((x')*y) + (x*(y')) = 0")
    val out = helper.parseFormula(" (x*y)' = 0")
    innerOuterTest(in,out,MultiplyDerivativeT)
  }

  "syntactic derivation of division" should "work on x,y" in {
    val in = helper.parseFormula("(((x')*y) - (x*(y'))) / (y^2) = 0")
    val out = helper.parseFormula("(x / y)' = 0")
    innerOuterTest(in,out,DivideDerivativeT)

  }

  "TermSyntacticDerivationT" should "work for +" in {
    val in = helper.parseFormula("n*m + (a+b)' + 1 + c^n = a^2 + 2") //nonsense idk just want some extra terms.
    val node = helper.formulaToNode(in)
    val pos = SuccPosition(0, PosInExpr(0 :: Nil))
//    val tactic = TermSyntacticDerivationT(pos)
    val tactic = TacticLibrary.ClosureT(TermSyntacticDerivationT)(pos)
    helper.runTactic(tactic,node)
    require(containsOpenGoal(node, helper.parseFormula("n*m + (a'+b') + 1 + c^n = a^2 + 2"))) //again, nonsense...
  }

  it should "work for -y" in {
    val in = "n*m + (-y)' + 1 + c^n = a^2 + 2".asFormula //nonsense idk just want some extra terms.
    val node = helper.formulaToNode(in)
    val tactic = TermSyntacticDerivationT(SuccPosition(0, PosInExpr(0 :: Nil)))
    val result = helper.runTactic(tactic,node)
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "n*m + -(y') + 1 + c^n = a^2 + 2".asFormula
  }

  it should "work for -x" in {
    val in = "n*m + (-x)' + 1 + c^n = a^2 + 2".asFormula //nonsense idk just want some extra terms.
    val node = helper.formulaToNode(in)
    val tactic = TermSyntacticDerivationT(SuccPosition(0, PosInExpr(0 :: Nil)))
    val result = helper.runTactic(tactic,node)
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "n*m + -(x') + 1 + c^n = a^2 + 2".asFormula
  }

  "Power Derivative" should "work" in {
    val in = "1 + (x^2)' = 1 + 2*x*x'".asFormula
    val node = helper.formulaToNode(in)
    val tactic = PowerDerivativeT(SuccPosition(0, PosInExpr(0 :: 1 :: Nil)))
    val result = helper.runTactic(tactic, node)
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "1+2*x^(2-1)*x'=1+2*x*x'".asFormula
  }

  "DeriveConstant" should "work" in {
    val in = "1 + 2' = 1 + 0".asFormula
    val node = helper.formulaToNode(in)
    val tactic = ConstantDerivativeT(SuccPosition(0, PosInExpr(0 :: 1 :: Nil)))
    val result = helper.runTactic(tactic, node)
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "1+0=1+0".asFormula
  }

  "FormulaSyntacticDerivationT" should "work for |" in {
    val f = "[x:=2;](1'=1 | 2=2)'".asFormula
    val node = helper.formulaToNode(f)

    val tactic = FormulaSyntacticDerivationT(SuccPosition(0, PosInExpr(1::Nil)))
    val result = helper.runTactic(tactic, node, mustApply = true)
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "[x:=2;]((1'=1)' & (2=2)')".asFormula
  }

  it should "work for =" in {
    val f = "[x:=2;](1 = 2)'".asFormula
    val node = helper.formulaToNode(f)
    val ptactic = TacticLibrary.ClosureT(FormulaSyntacticDerivationT)

    val tactic = ptactic(SuccPosition(0, PosInExpr(1::Nil)))
    val result = helper.runTactic(tactic, node, mustApply = true)
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "[x:=2;]1' = 2'".asFormula
  }

  "SyntacticDerivationT" should "intermediate step for next test" in {
    val f = "[x:=2;]((1=1)' & true)".asFormula

    val position = SuccPosition(0, PosInExpr(1 :: 0 :: Nil))
    val tactic = EqualsDerivativeT(position)

    val node = helper.runTactic(tactic, helper.formulaToNode(f), mustApply = true)

    node.openGoals().flatMap(_.sequent.ante) shouldBe empty
    node.openGoals().flatMap(_.sequent.succ) should contain only "[x:=2;](1'=1' & true)".asFormula
  }

  it should "work for | with an internal term that needs rewriting" in {
    val f = "[x:=2;](1'=1 | 2=2)'".asFormula

    val position = SuccPosition(0, PosInExpr(1 :: Nil))
    val tactic = SyntacticDerivationT(position)
    val node = helper.runTactic(tactic, helper.formulaToNode(f), mustApply = true)

    node.openGoals().flatMap(_.sequent.ante) shouldBe empty
    node.openGoals().flatMap(_.sequent.succ) should contain only "[x:=2;](0=0 & 0=0)".asFormula
  }

  // TODO not yet supported, fails assertion because of (!true)'
  ignore should "work on imply" in {
    val f = "[x:=2;](true->(x^2+y^2=1))'".asFormula

    val position = SuccPosition(0, PosInExpr(1 :: Nil))
    val tactic = SyntacticDerivationT(position)
    val node = helper.runTactic(tactic, helper.formulaToNode(f), mustApply = true)

    node.openGoals().flatMap(_.sequent.ante) shouldBe empty
    node.openGoals().flatMap(_.sequent.succ) should contain only "[x:=2;]((!true)' & 2*x^1*x' + 2*y^1*y' = 0)".asFormula
  }

  it should "work on *" in {
    val f = "[x:=2;](x*y=1)'".asFormula
    val node = helper.formulaToNode(f)

    val tactic = SyntacticDerivationT(SuccPosition(0, PosInExpr(1::Nil)))
    val result = helper.runTactic(tactic, node, mustApply = true)
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "[x:=2;]x'*y+x*y'=0".asFormula
  }

  it should "work on +" in {
    val f = "[x:=2;](x+y=1)'".asFormula
    val node = helper.formulaToNode(f)

    val tactic = SyntacticDerivationT(SuccPosition(0, PosInExpr(1::Nil)))
    val result = helper.runTactic(tactic, node, mustApply = true)
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "[x:=2;]x'+y'=0".asFormula
  }

  it should "work on boxes" in {
    val f = "[x'=b;](x-x<1)'".asFormula
    val node = helper.formulaToNode(f)

    val tactic = helper.positionTacticToTactic(SyntacticDerivationT)
    val result = helper.runTactic(tactic, node, mustApply = true)
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "[x'=b;]x'-x'<=0".asFormula
  }

  it should "work on a previous counter-example" in {
    val f = helper.parseFormula("x=1&[$$x'=y,y'=x$$ & (x^2+y^2=1);](x=1)'")
    val node = helper.formulaToNode(f)

    val tactic = helper.positionTacticToTactic(SyntacticDerivationT)
    helper.runTactic(tactic, node, true)

//    val expected = helper.parseFormula("[a:=b;]((!true)'&x'-y'=0)")
    helper.report(node)
//    require(containsOpenGoal(node, expected))
  }
}
