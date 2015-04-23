import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.SyntacticDerivationInContext.ApplicableAtFormula
import edu.cmu.cs.ls.keymaera.tactics._
import edu.cmu.cs.ls.keymaera.tactics.Tactics.PositionTactic
import testHelper.StringConverter._
import testHelper.SequentFactory._

/**
 * Created by nfulton on 2/5/15.
 * @author Nathan Fulton
 * @author Stefan Mitsch
 */
class SyntacticDerivationTests extends TacticTestSuite {
  "ForallDerivativeT tactics" should "atomize" in {
    val f = "[x:=2;](\\forall s. s>0)'".asFormula

    val tactic = SyntacticDerivationInContext.ForallDerivativeT(SuccPosition(0, PosInExpr(1::Nil)))

    val node = helper.runTactic(tactic, helper.formulaToNode(f), mustApply = true)
    node.openGoals().flatMap(_.sequent.ante) shouldBe empty
    node.openGoals().flatMap(_.sequent.succ) should contain only "[x:=2;](\\forall s. (s>0)')".asFormula
  }

  "AndDerivativeT tactics" should "atomize" in {
    val f = "[x:=2;](1=1 & 2=2)'".asFormula

    val tactic = SyntacticDerivationInContext.AndDerivativeT(SuccPosition(0, PosInExpr(1::Nil)))

    val node = helper.runTactic(tactic, helper.formulaToNode(f), mustApply = true)
    node.openGoals().flatMap(_.sequent.ante) shouldBe empty
    node.openGoals().flatMap(_.sequent.succ) should contain only "[x:=2;]((1=1)' & (2=2)')".asFormula
  }

  "OrDerivativeT tactics" should "atomize" in {
    val f = helper.parseFormula( "[x:=2;](1=1 | 2=2)' ")
    val tactic = SyntacticDerivationInContext.OrDerivativeT(SuccPosition(0, PosInExpr(1::Nil)))

    val node = helper.runTactic(tactic, helper.formulaToNode(f), mustApply = true)
    node.openGoals().flatMap(_.sequent.ante) shouldBe empty
    node.openGoals().flatMap(_.sequent.succ) should contain only "[x:=2;]((1=1)' & (2=2)')".asFormula
  }

  def testTermOperation(s : Variable, t : Variable, innerOp : (Term, Term) => Formula,
                        outerOp: (Term, Term) => Formula, axTactic : PositionTactic with ApplicableAtFormula) = {
    val tactic = axTactic(SuccPosition(0, PosInExpr(1::Nil)))

    val sequent = sucSequent(Box("x:=2;".asProgram, DifferentialFormula(innerOp(s, t))))
    // TODO should be DifferentialSymbols once done
    val expected = Box("x:=2;".asProgram, outerOp(Differential(s), Differential(t)))

    val result = helper.runTactic(tactic, new RootNode(sequent), mustApply = true)
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only expected //s"[x:=2;](($sNoParen)' $outerOp ($tNoParen)')".asFormula
  }

  import SyntacticDerivationInContext._

  "=" should "work on x,y" in {
    testTermOperation("x".asVariable, "y".asVariable, Equal.apply, Equal.apply, EqualsDerivativeT)
  }
  ">=" should "work on x,y" in {
    testTermOperation("x".asVariable, "y".asVariable, GreaterEqual.apply, GreaterEqual.apply, GreaterEqualDerivativeT)
  }
  "<=" should "work on x,y" in {
    testTermOperation("x".asVariable, "y".asVariable, LessEqual.apply, LessEqual.apply, LessEqualDerivativeT)
  }

  //These axioms don't follow the above pattern, so we need something slightly modified.

  ">" should "work on x,y" in {
    testTermOperation("x".asVariable, "y".asVariable, Greater.apply, GreaterEqual.apply, GreaterThanDerivativeT)
  }
  "<" should "work on x,y" in {
    testTermOperation("x".asVariable, "y".asVariable, Less.apply, LessEqual.apply, LessThanDerivativeT)
  }
  "!=" should "work on x,y" in {
    testTermOperation("x".asVariable, "y".asVariable, NotEqual.apply, Equal.apply, NotEqualsDerivativeT)
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

  def innerOuterTest(innerFormula:Formula, outerFormula:Formula, axTactic:PositionTactic with ApplicableAtTerm) = {
    //first one direction.
    val node = helper.formulaToNode(outerFormula)
    val tactic = axTactic(SuccPosition(0, PosInExpr(0 :: Nil)))
    val result = helper.runTactic(tactic,node, mustApply = true)
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only innerFormula
  }

  "syntactic derivation of addition" should "work on x,y" in {
    // assumes v' parsed as DifferentialSymbol
    "x'".asTerm shouldBe DifferentialSymbol("x".asVariable)
    val in = "(x'+y') = 0".asFormula
    val out = helper.parseFormula(" (x+y)' = 0")
    innerOuterTest(in,out,AddDerivativeT)
  }

  "syntactic derivation of subtraction" should "work on x,y" in {
    // assumes v' parsed as DifferentialSymbol
    "x'".asTerm shouldBe DifferentialSymbol("x".asVariable)
    val in = "(x'-y') = 0".asFormula
    val out = helper.parseFormula(" (x-y)' = 0")
    innerOuterTest(in,out,SubtractDerivativeT)
  }

  "syntactic derivation of multiplication" should "work on x,y" in {
    // assumes v' parsed as DifferentialSymbol
    "x'".asTerm shouldBe DifferentialSymbol("x".asVariable)
    val in = "((x')*y) + (x*(y')) = 0".asFormula
    val out = "(x*y)' = 0".asFormula
    innerOuterTest(in,out,MultiplyDerivativeT)
  }

  "syntactic derivation of division" should "work on x,y" in {
    // assumes v' parsed as DifferentialSymbol
    "x'".asTerm shouldBe DifferentialSymbol("x".asVariable)
    val in = "(((x')*y) - (x*(y'))) / (y^2) = 0".asFormula
    val out = "(x / y)' = 0".asFormula
    innerOuterTest(in,out,DivideDerivativeT)

  }

  "TermSyntacticDerivationT" should "work for +" in {
    // assumes v' parsed as DifferentialSymbol
    "x'".asTerm shouldBe DifferentialSymbol("x".asVariable)
    val in = "n*m + (a+b)' + 1 + c^n = a^2 + 2".asFormula //nonsense idk just want some extra terms.
    val node = helper.formulaToNode(in)
    val pos = SuccPosition(0, PosInExpr(0 :: Nil))
//    val tactic = TermSyntacticDerivationT(pos)
    val tactic = TacticLibrary.ClosureT(TermSyntacticDerivationT)(pos)
    val result = helper.runTactic(tactic,node)
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "n*m + (a'+b') + 1 + c^n = a^2 + 2".asFormula //again, nonsense...
  }

  it should "work for -y" in {
    // assumes v' parsed as DifferentialSymbol
    "x'".asTerm shouldBe DifferentialSymbol("x".asVariable)
    val in = "n*m + (-y)' + 1 + c^n = a^2 + 2".asFormula //nonsense idk just want some extra terms.
    val node = helper.formulaToNode(in)
    val tactic = TermSyntacticDerivationT(SuccPosition(0, PosInExpr(0 :: Nil)))
    val result = helper.runTactic(tactic,node)
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "n*m + -(y') + 1 + c^n = a^2 + 2".asFormula
  }

  it should "work for -x" in {
    // assumes v' parsed as DifferentialSymbol
    "x'".asTerm shouldBe DifferentialSymbol("x".asVariable)
    val in = "n*m + (-x)' + 1 + c^n = a^2 + 2".asFormula //nonsense idk just want some extra terms.
    val node = helper.formulaToNode(in)
    val tactic = TermSyntacticDerivationT(SuccPosition(0, PosInExpr(0 :: Nil)))
    val result = helper.runTactic(tactic,node)
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "n*m + -(x') + 1 + c^n = a^2 + 2".asFormula
  }

  "Power Derivative" should "work" in {
    // assumes v' parsed as DifferentialSymbol
    "x'".asTerm shouldBe DifferentialSymbol("x".asVariable)
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

  it should "work for complicated =" in {
    // assumes v' parsed as DifferentialSymbol
    "x'".asTerm shouldBe DifferentialSymbol("x".asVariable)

    val f = "[x':=2;](x = 2*0 + x)'".asFormula
    val node = helper.formulaToNode(f)
    val ptactic = SyntacticDerivationT

    val tactic = ptactic(SuccPosition(0, PosInExpr(1::Nil)))
    val result = helper.runTactic(tactic, node, mustApply = true)
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "[x':=2;](x' = 0*0+2*0 + x')".asFormula
  }

  // TODO not yet supported, fails assertion because of (!true)'
  ignore should "work on imply" in {
    // assumes v' parsed as DifferentialSymbol
    "x'".asTerm shouldBe DifferentialSymbol("x".asVariable)

    val f = "[x:=2;](true->(x^2+y^2=1))'".asFormula

    val position = SuccPosition(0, PosInExpr(1 :: Nil))
    val tactic = SyntacticDerivationT(position)
    val node = helper.runTactic(tactic, helper.formulaToNode(f), mustApply = true)

    node.openGoals().flatMap(_.sequent.ante) shouldBe empty
    node.openGoals().flatMap(_.sequent.succ) should contain only "[x:=2;]((!true)' & 2*x^1*x' + 2*y^1*y' = 0)".asFormula
  }

  it should "work on *" in {
    // assumes v' parsed as DifferentialSymbol
    "x'".asTerm shouldBe DifferentialSymbol("x".asVariable)

    val f = "[x:=2;](x*y=1)'".asFormula
    val node = helper.formulaToNode(f)

    val tactic = SyntacticDerivationT(SuccPosition(0, PosInExpr(1::Nil)))
    val result = helper.runTactic(tactic, node, mustApply = true)
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "[x:=2;]x'*y+x*y'=0".asFormula
  }

  it should "work on +" in {
    // assumes v' parsed as DifferentialSymbol
    "x'".asTerm shouldBe DifferentialSymbol("x".asVariable)

    val f = "[x:=2;](x+y=1)'".asFormula
    val node = helper.formulaToNode(f)

    val tactic = SyntacticDerivationT(SuccPosition(0, PosInExpr(1::Nil)))
    val result = helper.runTactic(tactic, node, mustApply = true)
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "[x:=2;]x'+y'=0".asFormula
  }

  it should "work on boxes" in {
    // assumes v' parsed as DifferentialSymbol
    "x'".asTerm shouldBe DifferentialSymbol("x".asVariable)

    val f = "[x'=b;](x-x<1)'".asFormula
    val node = helper.formulaToNode(f)

    val tactic = helper.positionTacticToTactic(SyntacticDerivationT)
    val result = helper.runTactic(tactic, node, mustApply = true)
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "[x'=b;]x'-x'<=0".asFormula
  }

  "symbolizeDifferentials" should "work when the Differential() occurs in a formula without []'s" in {
    val z = Variable("z", None, Real)
    val f = Equal(Differential(z), Number(1))
    val node = helper.formulaToNode(f)

    val tactic = symbolizeDifferential(SuccPosition(0, PosInExpr(0 :: Nil)))
    helper.runTactic(tactic, node, mustApply = true)
    val result = node.openGoals().head.sequent.succ.head
    result shouldBe Equal(DifferentialSymbol(z), Number(1))
  }

  it should "work in context" in {
    val z = Variable("z", None, Real)
    val f = Box(Assign(z, Number(1)), Equal(Differential(z), Number(1)))

    val node = helper.formulaToNode(f)
    val tactic = symbolizeDifferential(SuccPosition(0, PosInExpr(1 :: 0 :: Nil))) //not sure about this position?

    helper.runTactic(tactic, node, mustApply = true)
    helper.report(node)
    val result = node.openGoals().head.sequent.succ.head
    result shouldBe Box(Assign(z, Number(1)), Equal(DifferentialSymbol(z), Number(1)))
  }

}
