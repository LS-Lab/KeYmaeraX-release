/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tactics.{AntePosition, PosInExpr, RootNode, SuccPosition, EqualityRewritingImpl,
  Interpreter, Tactics}
import edu.cmu.cs.ls.keymaerax.tactics.EqualityRewritingImpl._
import edu.cmu.cs.ls.keymaerax.tactics.PolynomialForm._
import edu.cmu.cs.ls.keymaerax.tools.{KeYmaera, Mathematica}
import testHelper.ProvabilityTestHelper
import org.scalatest.{BeforeAndAfterEach, Matchers, FlatSpec}
import testHelper.SequentFactory._

import scala.collection.immutable.{TreeSet, Map}

/**
 * Created by smitsch on 3/16/15.
 * @author Stefan Mitsch
 */
class EqualityRewritingTests extends FlatSpec with Matchers with BeforeAndAfterEach {
  // TODO mathematica is only necessary because of ProofFactory -> make ProofFactory configurable

  val helper = new ProvabilityTestHelper((x) => println(x))
  val mathematicaConfig: Map[String, String] = helper.mathematicaConfig

  override def beforeEach() = {
    Tactics.KeYmaeraScheduler = new Interpreter(KeYmaera)
    Tactics.MathematicaScheduler = new Interpreter(new Mathematica)
    Tactics.MathematicaScheduler.init(mathematicaConfig)
    Tactics.KeYmaeraScheduler.init(Map())
  }

  override def afterEach() = {
    Tactics.MathematicaScheduler.shutdown()
    Tactics.KeYmaeraScheduler.shutdown()
    Tactics.MathematicaScheduler = null
    Tactics.KeYmaeraScheduler = null
  }

//  "Equality rewriting" should "not apply <-> unsoundly" in {
//    val s = sequent(Nil, "x'=0".asFormula :: "(x*y())' <= 0 <-> 0 <= 0".asFormula :: Nil,
//      "[x':=1;]0<=0 -> [x':=1;]((x*y()) <= 0)'".asFormula :: Nil)
//    val tactic = EqualityRewritingImpl.equalityRewriting(AntePosition(1), SuccPosition(0, PosInExpr(1::1::Nil)))
//    tactic.applicable(new RootNode(s)) shouldBe false
//
//    an [IllegalArgumentException] should be thrownBy
//      new EqualityRewriting(AntePosition(0), SuccPosition(0, PosInExpr(1::1::Nil))).apply(s)
//  }
//
//  it should "not apply = unsoundly" in {
//    val s = sequent(Nil, "x'=0".asFormula :: "(x*y())' = 0".asFormula :: Nil,
//      "[x':=1;]0<=0 -> [x':=1;](x*y())' <= 0".asFormula :: Nil)
//    val tactic = EqualityRewritingImpl.equalityRewriting(AntePosition(1), SuccPosition(0, PosInExpr(1::1::Nil)))
//    tactic.applicable(new RootNode(s)) shouldBe false
//
//    an [IllegalArgumentException] should be thrownBy
//      new EqualityRewriting(AntePosition(0), SuccPosition(0, PosInExpr(1::1::Nil))).apply(s)
//  }

  "Const formula congruence" should "rewrite x*y=0 to 0*y=0 using x=0" in {
    val s = sequent(Nil, "x=0".asFormula::Nil, "x*y=0".asFormula::Nil)
    val tactic = constFormulaCongruenceT(AntePosition(0), left = true, exhaustive = false)(SuccPosition(0, PosInExpr(0::0::Nil)))
    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only "x=0".asFormula
    result.openGoals().flatMap(_.sequent.succ) should contain only "0*y=0".asFormula
  }

  it should "rewrite complicated" in {
    val s = sequent(Nil, "x=0".asFormula::Nil, "x*y=0 & x+3>2 | \\forall y y+x>=0".asFormula::Nil)
    val tactic =
      constFormulaCongruenceT(AntePosition(0), left = true, exhaustive = false)(SuccPosition(0, PosInExpr(0::0::0::0::Nil))) &
      constFormulaCongruenceT(AntePosition(0), left = true, exhaustive = false)(SuccPosition(0, PosInExpr(0::1::0::0::Nil))) &
      constFormulaCongruenceT(AntePosition(0), left = true, exhaustive = false)(SuccPosition(0, PosInExpr(1::0::0::1::Nil)))
    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only "x=0".asFormula
    result.openGoals().flatMap(_.sequent.succ) should contain only "0*y=0 & 0+3>2 | \\forall y y+0>=0".asFormula
  }

  it should "rewrite complicated exhaustively" in {
    val s = sequent(Nil, "x=0".asFormula::Nil, "x*y=0 & x+3>2 | \\forall y y+x>=0 & \\exists x x>0".asFormula::Nil)
    val tactic =
      constFormulaCongruenceT(AntePosition(0), left = true)(SuccPosition(0))
    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only "x=0".asFormula
    result.openGoals().flatMap(_.sequent.succ) should contain only "0*y=0 & 0+3>2 | \\forall y y+0>=0 & \\exists x x>0".asFormula
  }

  ignore should "throw a substitution clash exception if it tries to rename bound" in {
    val s = sequent(Nil, "x=0".asFormula::Nil, "\\forall x y+x>=0".asFormula::Nil)
    val tactic = constFormulaCongruenceT(AntePosition(0), left = true, exhaustive = false)(SuccPosition(0, PosInExpr(0::0::1::Nil)))
    // somehow, the exception is thrown but swallowed somewhere
    a [SubstitutionClashException] should be thrownBy helper.runTactic(tactic, new RootNode(s))
  }

  it should "rewrite x*y=0 to 0*y=0 using 0=x" in {
    val s = sequent(Nil, "0=x".asFormula::Nil, "x*y=0".asFormula::Nil)
    val tactic = constFormulaCongruenceT(AntePosition(0), left = false, exhaustive = false)(SuccPosition(0, PosInExpr(0::0::Nil)))
    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only "0=x".asFormula
    result.openGoals().flatMap(_.sequent.succ) should contain only "0*y=0".asFormula
  }

  "EqLeft" should "rewrite a single formula exhaustively" in {
    val s = sequent(Nil, "x=0".asFormula::Nil, "x*y=0".asFormula :: "z>2".asFormula :: "z<x+1".asFormula :: Nil)
    val tactic = eqLeft(exhaustive=true)(AntePosition(0))
    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only "x=0".asFormula
    result.openGoals().flatMap(_.sequent.succ) should contain only ("0*y=0".asFormula, "z>2".asFormula, "z<0+1".asFormula)
  }

  it should "rewrite formulas exhaustively" in {
    val s = sequent(Nil, "x=0".asFormula :: "z=x".asFormula :: Nil, "x*y=0".asFormula :: "z>2".asFormula :: "z<x+1".asFormula :: Nil)
    val tactic = eqLeft(exhaustive=true)(AntePosition(0))
    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only ("x=0".asFormula, "z=0".asFormula)
    result.openGoals().flatMap(_.sequent.succ) should contain only ("0*y=0".asFormula, "z>2".asFormula, "z<0+1".asFormula)
  }

  it should "rewrite formulas exhaustively everywhere" in {
    val s = sequent(Nil, "z=x".asFormula :: "x=0".asFormula :: Nil, "x*y=0".asFormula :: "z>2".asFormula :: "z<x+1".asFormula :: Nil)
    val tactic = eqLeft(exhaustive=true)(AntePosition(1))
    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only ("x=0".asFormula, "z=0".asFormula)
    result.openGoals().flatMap(_.sequent.succ) should contain only ("0*y=0".asFormula, "z>2".asFormula, "z<0+1".asFormula)
  }

  it should "work even if there is only one other formula" in {
    val s = sequent(Nil, "x<5".asFormula :: "x=0".asFormula :: Nil, Nil)
    val tactic = eqLeft(exhaustive=true)(AntePosition(1))
    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only ("0<5".asFormula, "x=0".asFormula)
    result.openGoals().flatMap(_.sequent.succ) shouldBe empty
  }

  it should "replace arbitary terms" in {
    val s = sequent(Nil, "a+b<5".asFormula :: "a+b=c".asFormula :: Nil, Nil)
    val tactic = eqLeft(exhaustive=true)(AntePosition(1))
    val result = helper.runTactic(tactic, new RootNode(s))

    result.openGoals() should have size 1
    result.openGoals().head.sequent.ante should contain only ("c<5".asFormula, "a+b=c".asFormula)
    result.openGoals().head.sequent.succ shouldBe empty
  }

  // rewriting numbers is disallowed, because otherwise we run into endless rewriting
  it should "not rewrite numbers" in {
    val s = sequent(Nil, "0<5".asFormula :: "0=0".asFormula :: Nil, Nil)
    val tactic = eqLeft(exhaustive=true)(AntePosition(1))
    tactic.applicable(new RootNode(s)) shouldBe false
  }

  it should "not try to rewrite bound occurrences" in {
    //@note would clash anyway, but tactic shouldn't even try
    val s = sequent(Nil, "a=1".asFormula :: Nil, "[a:=2;]a=1".asFormula :: Nil)
    val tactic = eqLeft(exhaustive=true)(AntePosition(0))
    tactic.applicable(new RootNode(s)) shouldBe false
  }

  "Equivalence rewriting" should "rewrite if lhs occurs in succedent" in {
    val s = sequent(Nil, "x>=0 <-> y>=0".asFormula :: Nil, "x>=0".asFormula :: Nil)
    val tactic = EqualityRewritingImpl.equivRewriting(AntePosition(0), SuccPosition(0))
    val result = helper.runTactic(tactic, new RootNode(s))

    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "y>=0".asFormula
  }

  it should "rewrite if rhs occurs in succedent" in {
    val s = sequent(Nil, "x>=0 <-> y>=0".asFormula :: Nil, "y>=0".asFormula :: Nil)
    val tactic = EqualityRewritingImpl.equivRewriting(AntePosition(0), SuccPosition(0))
    val result = helper.runTactic(tactic, new RootNode(s))

    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "x>=0".asFormula
  }

  it should "rewrite if lhs occurs in antecedent" in {
    val s = sequent(Nil, "x>=0 <-> y>=0".asFormula :: "x>=0".asFormula :: Nil, Nil)
    val tactic = EqualityRewritingImpl.equivRewriting(AntePosition(0), AntePosition(1))
    val result = helper.runTactic(tactic, new RootNode(s))

    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only "y>=0".asFormula
    result.openGoals().flatMap(_.sequent.succ) shouldBe empty
  }

  it should "rewrite if lhs occurs in antecedent before assumption" in {
    val s = sequent(Nil, "x>=0".asFormula :: "x>=0 <-> y>=0".asFormula :: Nil, Nil)
    val tactic = EqualityRewritingImpl.equivRewriting(AntePosition(1), AntePosition(0))
    val result = helper.runTactic(tactic, new RootNode(s))

    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only "y>=0".asFormula
    result.openGoals().flatMap(_.sequent.succ) shouldBe empty
  }

  it should "rewrite if rhs occurs in antecedent" in {
    val s = sequent(Nil, "x>=0 <-> y>=0".asFormula :: "y>=0".asFormula :: Nil, Nil)
    val tactic = EqualityRewritingImpl.equivRewriting(AntePosition(0), AntePosition(1))
    val result = helper.runTactic(tactic, new RootNode(s))

    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only "x>=0".asFormula
    result.openGoals().flatMap(_.sequent.succ) shouldBe empty
  }

  it should "rewrite if rhs occurs in antecedent before assumption" in {
    val s = sequent(Nil, "y>=0".asFormula :: "x>=0 <-> y>=0".asFormula :: Nil, Nil)
    val tactic = EqualityRewritingImpl.equivRewriting(AntePosition(1), AntePosition(0))
    val result = helper.runTactic(tactic, new RootNode(s))

    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only "x>=0".asFormula
    result.openGoals().flatMap(_.sequent.succ) shouldBe empty
  }

  "Abbrv tactic" should "abbreviate a+b to z" in {
    val s = sucSequent("a+b < c".asFormula)
    val tactic = EqualityRewritingImpl.abbrv(Variable("z"))(SuccPosition(0).first)
    val result = helper.runTactic(tactic, new RootNode(s))

    result.openGoals() should have size 1
    result.openGoals().head.sequent.ante should contain only "z = a+b".asFormula
    result.openGoals().head.sequent.succ should contain only "z < c".asFormula
  }

  it should "abbreviate min(a,b) to z" in {
    val s = sucSequent("min(a,b) < c".asFormula)
    val tactic = EqualityRewritingImpl.abbrv(Variable("z"))(SuccPosition(0).first)
    val result = helper.runTactic(tactic, new RootNode(s))

    result.openGoals() should have size 1
    result.openGoals().head.sequent.ante should contain only "z = min(a,b)".asFormula
    result.openGoals().head.sequent.succ should contain only "z < c".asFormula
  }

  it should "not abbreviate in places where at least one of the arguments is bound" in {
    val s = sequent(Nil, "min(a,b) < c".asFormula :: Nil, "[a:=0;]min(a,b) < c".asFormula :: Nil)
    val tactic = EqualityRewritingImpl.abbrv(Variable("z"))(AntePosition(0).first)
    val result = helper.runTactic(tactic, new RootNode(s))

    result.openGoals() should have size 1
    result.openGoals().head.sequent.ante should contain only ("z = min(a,b)".asFormula, "z < c".asFormula)
    result.openGoals().head.sequent.succ should contain only "[a:=0;]min(a,b) < c".asFormula
  }

  it should "abbreviate min(a,b) to z everywhere (except at bound occurrences)" in {
    val s = sequent(Nil, "min(a,b) < c".asFormula :: "x>y".asFormula :: "5 < min(a,b)".asFormula :: Nil,
      "min(a,b) + 2 = 7".asFormula :: "a<b".asFormula :: "[b:=2;]min(a,b) < 9".asFormula :: Nil)
    val tactic = EqualityRewritingImpl.abbrv(Variable("z"))(AntePosition(0).first)
    val result = helper.runTactic(tactic, new RootNode(s))

    result.openGoals() should have size 1
    result.openGoals().head.sequent.ante should contain only ("z = min(a,b)".asFormula, "z<c".asFormula, "x>y".asFormula, "5<z".asFormula)
    result.openGoals().head.sequent.succ should contain only ("z+2=7".asFormula, "a<b".asFormula, "[b:=2;]min(a,b)<9".asFormula)
  }

  it should "abbreviate min(a,b) to z everywhere (except at bound occurrences) and pick a name automatically" in {
    val s = sequent(Nil, "min(a,b) < c".asFormula :: "x>y".asFormula :: "5 < min(a,b)".asFormula :: Nil,
      "min(a,b) + 2 = 7".asFormula :: "a<b".asFormula :: "[b:=2;]min(a,b) < 9".asFormula :: Nil)
    val tactic = EqualityRewritingImpl.abbrv("min(a,b)".asTerm)
    val result = helper.runTactic(tactic, new RootNode(s))

    result.openGoals() should have size 1
    result.openGoals().head.sequent.ante should contain only ("min_0 = min(a,b)".asFormula, "min_0<c".asFormula, "x>y".asFormula, "5<min_0".asFormula)
    result.openGoals().head.sequent.succ should contain only ("min_0+2=7".asFormula, "a<b".asFormula, "[b:=2;]min(a,b)<9".asFormula)
  }

  it should "abbreviate any argument even if not contained in the sequent and pick a name automatically" in {
    val s = sequent(Nil, "x>y".asFormula :: Nil, "a<b".asFormula :: Nil)
    val tactic = EqualityRewritingImpl.abbrv("f()+g()".asTerm)
    val result = helper.runTactic(tactic, new RootNode(s))

    result.openGoals() should have size 1
    result.openGoals().head.sequent.ante should contain only ("Term = f()+g()".asFormula, "x>y".asFormula)
    result.openGoals().head.sequent.succ should contain only "a<b".asFormula
  }

  def v(str:String):Term= Variable(str, None, Real)
  def v1(str:String):(Term,Int) = (v(str),1)
  def d(str:String):Term = DifferentialSymbol(Variable(str,None,Real))
  def d1(str:String):(Term,Int) = (d(str),1)
  def polysWithin(p1:Polynomial,p2:Polynomial,tolerance:Double):Boolean = {
    val sorted1 = p1.asSet.foldLeft(TreeSet()(MonomialGrlex)){case(acc,mon) => acc.+(mon)}.toList
    val sorted2 = p2.asSet.foldLeft(TreeSet()(MonomialGrlex)){case(acc,mon) => acc.+(mon)}.toList
    if (sorted1.length != sorted2.length) {
      false
    } else {
      sorted1.zip(sorted2).forall({case(p1,p2) =>
        p1.coeff.value - p2.coeff.value <= tolerance &&
        p1.coeff.value - p2.coeff.value >= -tolerance &&
        p1.vars == p2.vars})
    }
  }

  def polyClose(p1:Polynomial,p2:Polynomial):Boolean = polysWithin(p1,p2,0.00001)
  def polyEq(p1:Polynomial, p2:Polynomial):Boolean = polysWithin(p1,p2,0)

  "term normalization" should "handle multiplications" in {
    val input = "(x + 1)*(y + 2)".asTerm
    val output =
      Set (Monomial(Number(1), Set(v1("x"), v1("y"))),
        Monomial(Number(2), Set(v1("x"))),
        Monomial(Number(1), Set(v1("y"))),
        Monomial(Number(2), Set()))
    new Polynomial(input).mons should be (output)
  }

  it should "handle constant powers" in {
    val poly = new Polynomial("(x + 1)^3".asTerm)
    val output: Polynomial =
      new Polynomial (Set (Monomial(Number(1), Set((v("x"), 3))),
          Monomial(Number(3), Set((v("x"),2))),
          Monomial(Number(3), Set((v("x"),1))),
          Monomial(Number(1), Set.empty[(Term,Int)])))
    polyEq(poly, output) should be (true)
  }

  it should "handle constant division" in {
    val poly = new Polynomial ("(x + 3)/3".asTerm)
    val output =
      new Polynomial(Set(Monomial(Number(1.0/3.0), Set(v1("x"))),
          Monomial(Number(1), Set.empty[(Term,Int)])))
    polyClose(poly, output) should be (true)
  }

  it should "raise on non-constant exponents" in {
    val input = "3^x".asTerm
    a [BadPower] should be thrownBy {
      new Polynomial(input)
    }
  }

  it should "raise on non-constant division" in {
    val input = "x/(3-3)".asTerm
    a [BadDivision] should be thrownBy {
      new Polynomial(input)
    }
  }

  it should "handle subtraction" in {
    val input = "(x-(x-2))".asTerm
    val output = Polynomial(Set(Monomial(Number(2),Set.empty[(Term,Int)])))
    polyEq(new Polynomial(input),output) should be (true)
  }

  it should "handle negation" in {
    val input = "-(x-(x-2))".asTerm
    var output = Polynomial(Set(Monomial(Number(-2),Set.empty[(Term,Int)])))
    polyEq(new Polynomial(input),output) should be (true)
  }

  it should "handle differentiation" in {
    val input = "(x + y)'".asTerm
    val output = Polynomial(Set(Monomial(Number(1), Set(d1("x"))),
      Monomial(Number(1),Set(d1("y")))))
    polyEq(new Polynomial(input), output) should be (true)
  }

  "term comparison" should "sort variable names lexicographically" in {
    compareTermComplexity("x".asTerm,"y".asTerm) should be (-1)
    compareTermComplexity("xx".asTerm,"xy".asTerm) should be (-1)
    compareTermComplexity("x".asTerm,"x".asTerm) should be (0)
    compareTermComplexity("xx".asTerm,"xx".asTerm) should be (0)
    compareTermComplexity("xy".asTerm,"xx".asTerm) should be (1)
  }

  it should "sort by total degree first" in {
    compareTermComplexity("x * y^3".asTerm, "x^2 * y".asTerm) should be (1)
  }

  it should "find the leading term" in {
    compareTermComplexity("x + y^3 + z".asTerm, "x^2 + y^2 + z^2".asTerm) should be (1)
  }

  it should "break ties with coefficients" in {
     compareTermComplexity("x".asTerm, "2 * x".asTerm) should be (-1)
  }

  it should "break ties with lex order" in {
    compareTermComplexity("x*y".asTerm,"x*z".asTerm) should be (-1)
  }

  it should "consider exponentials to be more complicated than polynomials" in {
    compareTermComplexity("2^x".asTerm, "x^100".asTerm) should be (1)
  }

  it should "consider exponentials to be more complicated than quotients" in {
    compareTermComplexity("2^x".asTerm, "(x + 2)/(x+1)".asTerm) should be (1)
  }

  it should "consider quotients to be more complicated than polynomials" in {
    compareTermComplexity("(x+2)/(x+1)".asTerm, "x^5".asTerm) should be (1)
  }

  "Smart Equality Rewriting" should "rewrite a single formula exhaustively" in {
    val s = sequent(Nil, "x=0".asFormula::Nil, "x*y=0".asFormula :: "z>2".asFormula :: "z<x+1".asFormula :: Nil)
    val tactic = smartEqualityRewritingT
    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only ("0*y=0".asFormula, "z>2".asFormula, "z<0+1".asFormula)
  }

  it should "rewrite formulas exhaustively" in {
    val s = sequent(Nil, "x=0".asFormula :: "z=x".asFormula :: Nil, "x*y=0".asFormula :: "z>2".asFormula :: "z<x+1".asFormula :: Nil)
    val tactic = smartEqualityRewritingT
    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only ("z=0".asFormula)
    result.openGoals().flatMap(_.sequent.succ) should contain only ("0*y=0".asFormula, "z>2".asFormula, "z<0+1".asFormula)
  }

  it should "rewrite formulas exhaustively everywhere" in {
    val s = sequent(Nil, "z=x".asFormula :: "x=0".asFormula :: Nil, "x*y=0".asFormula :: "z>2".asFormula :: "z<x+1".asFormula :: Nil)
    val tactic = smartEqualityRewritingT
    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.succ) should contain only ("x*y=0".asFormula, "x>2".asFormula, "x<x+1".asFormula)
    result.openGoals().flatMap(_.sequent.ante) should contain only ("x=0".asFormula)
  }

  it should "work even if there is only one other formula" in {
    val s = sequent(Nil, "x<5".asFormula :: "x=0".asFormula :: Nil, Nil)
    val tactic = smartEqualityRewritingT
    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only ("0<5".asFormula)
    result.openGoals().flatMap(_.sequent.succ) shouldBe empty
  }

  // @todo The success of this test depends on variable naming. It seems likely that we should enhance the
  // term ordering so the number of monomials in a polynomial matters when the total order is the same (so d+b is more
  // complex than c)
  it should "replace compound terms" in {
    val s = sequent(Nil, "d+b<5".asFormula :: "d+b=c".asFormula :: Nil, Nil)
    val tactic = smartEqualityRewritingT
    val result = helper.runTactic(tactic, new RootNode(s))

    result.openGoals() should have size 1
    result.openGoals().head.sequent.ante should contain only ("c<5".asFormula)
    result.openGoals().head.sequent.succ shouldBe empty
  }

  // rewriting numbers is disallowed, because otherwise we run into endless rewriting
  it should "not rewrite numbers" in {
    val s = sequent(Nil, "0<5".asFormula :: "0=0".asFormula :: Nil, Nil)
    val tactic = smartEqualityRewritingT
    tactic.applicable(new RootNode(s)) shouldBe false
  }

  it should "not try to rewrite bound occurrences" in {
    //@note would clash anyway, but tactic shouldn't even try
    val s = sequent(Nil, "a=1".asFormula :: Nil, "[a:=2;]a=1".asFormula :: Nil)
    val tactic = smartEqualityRewritingT
    tactic.applicable(new RootNode(s)) shouldBe false
  }

  it should "not rewrite contradictions" in {
    val s = sequent(Nil, "x=x+1".asFormula :: Nil, "x+1=0".asFormula :: Nil)
    var tactic = smartEqualityRewritingT
    val result = helper.runTactic(tactic, new RootNode(s))

    result.openGoals() should have size 1
    result.openGoals().head.sequent.ante should contain only ("x=x+1".asFormula)
    result.openGoals().head.sequent.succ should contain only ("x=0".asFormula)
  }
}
