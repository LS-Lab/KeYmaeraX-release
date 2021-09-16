package edu.cmu.cs.ls.keymaerax.infrastruct

/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */

import edu.cmu.cs.ls.keymaerax.{Configuration, FileConfiguration}
import edu.cmu.cs.ls.keymaerax.bellerophon.UnificationException
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.{RenUSubst, UnificationMatch}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.parser.SystemTestBase
import edu.cmu.cs.ls.keymaerax.tags.{SummaryTest, UsualTest}
import edu.cmu.cs.ls.keymaerax.tools.KeYmaeraXTool
import org.scalatest.{FlatSpec, Matchers}
import testHelper.KeYmaeraXTestTags.{IgnoreInBuildTest, OptimisticTest, TodoTest}

import scala.collection.immutable
import scala.collection.immutable._


/**
  * Testing unifier and its limits.
  *
  * @author Andre Platzer
  * @see [[UnificationMatch]]
  */
@SummaryTest
@UsualTest
class UnificationMatchTest extends SystemTestBase {

  val matcher = {
    Configuration.setConfiguration(FileConfiguration)
    if (true) UnificationMatch else new FreshPostUnificationMatch
  }
  private def Subst(subs: immutable.Seq[(Expression,Expression)]): RenUSubst = if (!semanticRenaming) RenUSubst(subs) else
    new FastURenAboveUSubst(subs)
  private def Subst(us: USubst): RenUSubst = Subst(us.subsDefsInput.map(sp=>(sp.what,sp.repl)))

  private def should(e1: Expression, e2: Expression, us: Option[USubst]): Unit = {
    if (us.isDefined) {
      println("Expression: " + e1)
      println("Expression: " + e2)
      val s = matcher(e1, e2)
      println("Unifier:  " + s)
      println("Expected: " + us.get)
      print("Unifies?")
      s(e1) shouldBe e2
      println(" successfully!")
      shouldBeSameUnifier(s, Subst(us.get))
    } else {
      println("Expression: " + e1)
      println("Expression: " + e2)
      println("Expected: " + "<ununifiable>")
      a [UnificationException] should be thrownBy matcher(e1, e2)
    }
  }

  private def shouldUnify(e1: Expression, e2: Expression, us: USubst): Unit = should(e1,e2,Some(us))

  private def shouldBeSameUnifier(u1: RenUSubst, u2: RenUSubst): Unit = {
    if (u1.subsDefsInput.filterNot(sp=>sp._1==sp._2).toSet != u2.subsDefsInput.filterNot(sp=>sp._1==sp._2).toSet)
      u1 shouldBe (u2)
  }

  // new unification matchers from now on

  private def shouldMatch(e1: Expression, e2: Expression, us: Option[RenUSubst]): Unit = {
    if (us.isDefined) {
      println("Expression1: " + e1)
      println("Expression2: " + e2)
      val s = UnificationMatch(e1, e2)
      println("Unifier:     " + s)
      println("Expected:    " + us.get + "\t" + (if (s==us.get) "identical substitution" else "different substitution"))
      print("Unifies?")
      // expect s to unify e1 against e2
      s(e1) shouldBe (e2)
      println(" successfully!")
      // expect s to unify e1 against e2
      us.get(e1) shouldBe (e2)
      println("recorded unifies successfully")
      println("hence1:      " + s(e1))
      println("Expression2: " + e2)
      s(e1) shouldBe (e2)
      println("Success, now let's compare the unifier with the expected unifier")
      shouldBeSameUnifier(s, us.get)
    } else {
      println("Expression: " + e1)
      println("Expression: " + e2)
      println("Expected: " + "<ununifiable>")
      a [UnificationException] should be thrownBy UnificationMatch(e1, e2)
    }
  }

  private def shouldMatch(e1: Expression, e2: Expression, us: RenUSubst): Unit = shouldMatch(e1, e2, Some(us))




  "Unification terms" should "unify f() with x^2+y" in {
    shouldUnify("f()".asTerm, "x^2+y".asTerm, USubst(
      SubstitutionPair("f()".asTerm, "x^2+y".asTerm) :: Nil))
  }

  it should "unify f(x) with x^2+y" in {
    shouldUnify("f(x)".asTerm, "x^2+y".asTerm, USubst(
      SubstitutionPair("f(.)".asTerm, "(.)^2+y".asTerm) :: Nil))
  }

  it should "unify 3+f() with 3+(x^2+y)" in {
    shouldUnify("3+f()".asTerm, "3+(x^2+y)".asTerm, USubst(
      SubstitutionPair("f()".asTerm, "x^2+y".asTerm) :: Nil))
  }

  it should "unify 3+f(x) with 3+(x^2+y)" taggedAs(IgnoreInBuildTest) in {
    shouldUnify("3+f(x)".asTerm, "3+(x^2+y)".asTerm, USubst(
      SubstitutionPair("f(.)".asTerm, "(.)^2+y".asTerm) :: Nil))
  }

  it should "support mixed term left-right matching" in {
    UnificationMatch(
      "==> a=0, f(x)>=0".asSequent,
      "==> a()=0, x^2>=0".asSequent
    ).usubst shouldBe USubst(List("a()~>a".asSubstitutionPair, "f(.)~>.^2".asSubstitutionPair))
    UnificationMatch(
      "==> a()=0, x^2>=0".asSequent,
      "==> a=0, f(x)>=0".asSequent
    ).usubst shouldBe USubst(List("a()~>a".asSubstitutionPair, "f(.)~>.^2".asSubstitutionPair))
    UnificationMatch(
      "==> g(y)=0, x^2>=0".asSequent,
      "==> y+1=0, f(x)>=0".asSequent
    ).usubst shouldBe USubst(List("g(.)~>.+1".asSubstitutionPair, "f(.)~>.^2".asSubstitutionPair))
  }


  "Unification formulas" should "unify p() with x^2+y>=0" in {
    shouldUnify("p()".asFormula, "x^2+y>=0".asFormula, USubst(
      SubstitutionPair("p()".asFormula, "x^2+y>=0".asFormula) :: Nil))
  }

  it should "unify \\forall x p(x) with \\forall x (!q(x))" in {
    shouldUnify("\\forall x p(x)".asFormula, "\\forall x (!q(x))".asFormula, USubst(
      SubstitutionPair("p(.)".asFormula, "!q(.)".asFormula) :: Nil))
  }

  it should "match \\forall x p(x) with \\forall x (!p(x))" in {
    shouldUnify("\\forall x p(x)".asFormula, "\\forall x (!p(x))".asFormula, USubst(
      SubstitutionPair("p(.)".asFormula, "!p(.)".asFormula) :: Nil))
  }
  it should "match" in {
    shouldUnify("[a;]p() -> [a;]p()".asFormula, "[x:=x+1;]y>0 -> [x:=x+1;]y>0".asFormula, USubst(
      SubstitutionPair("a;".asProgram, "x:=x+1;".asProgram) :: SubstitutionPair("p()".asFormula, "y>0".asFormula) :: Nil
    ))
  }

  it should "rename bound variables" in {
    shouldMatch("p_()&\\exists y_ true".asFormula,
      "(\\exists y true)&\\exists y true".asFormula,
      Subst(Seq(("p_()".asFormula, "(\\exists y_ true)".asFormula), ("y_".asVariable, "y".asVariable)))
    )
  }

  it should "rename bound variables? OPTIMISTIC" taggedAs OptimisticTest in {
    shouldMatch("p_()&\\exists y_ true".asFormula,
      "(\\exists y true)&\\exists y true".asFormula,
      Subst(Seq(("p_()".asFormula, "(\\exists y_ true)".asFormula), ("y_".asVariable, "y".asVariable)))
      //@note this is an illegal unifier but UniformMatching finds correct one
      //Subst(Seq(("p_()".asFormula, "(\\exists z_ true)".asFormula), ("y_".asVariable, "y".asVariable), ("z_".asVariable, "y".asVariable)))
    )
  }

  it should "support mixed left-right matching" in {
    //@note needs to match p(x,y) with x=y but inside r needs the opposite direction
    UnificationMatch(
      "==> p(x,y) & r(x,y,0) -> r(x,y,a)".asSequent,
      "==> x=y & (0>=0 & x^2+y^2=0) -> (a>=0 & x^2+y^2=0)".asSequent).usubst shouldBe USubst(
      List(
        "r(._0,._1,._2)~>._2>=0&._0^2+._1^2=0".asSubstitutionPair,
        "p(._0,._1)~>._0=._1".asSubstitutionPair))
  }

  it should "support more mixed left-right matching" in {
    UnificationMatch(
      "==> a=0, p(x)".asSequent,
      "==> q(a), x^2>=0".asSequent
    ).usubst shouldBe USubst(List("q(.)~>.=0".asSubstitutionPair, "p(.)~>.^2>=0".asSubstitutionPair))
    UnificationMatch(
      "==> q(a), x^2>=0".asSequent,
      "==> a=0, p(x)".asSequent
    ).usubst shouldBe USubst(List("q(.)~>.=0".asSubstitutionPair, "p(.)~>.^2>=0".asSubstitutionPair))
  }

  "Unification programs" should "unify [a;]x>=0 with [x:=x+5;]x>=0" in {
    shouldUnify("[a;]x>=0".asFormula, "[x:=x+5;]x>=0".asFormula, USubst(
      SubstitutionPair("a;".asProgram, "x:=x+5;".asProgram) :: Nil))
  }

  it should "unify [a;x:=7;]x>=0 with [x:=x+5;x:=7;]x>=0" in {
    shouldUnify("[a;x:=7;]x>=0".asFormula, "[x:=x+5;x:=7;]x>=0".asFormula, USubst(
      SubstitutionPair("a;".asProgram, "x:=x+5;".asProgram) :: Nil))
  }

  "Old unification match" should "unify (\\forall x p(x)) -> p(t()) with (\\forall y y>0) -> z>0 (fails)" ignore {
    val s1 = Sequent(IndexedSeq(), IndexedSeq("\\forall x p(x) -> p(t())".asFormula))
    val s2 = Sequent(IndexedSeq(), IndexedSeq("\\forall y y>0 -> z>0".asFormula))
    //@todo not sure about the expected result
    UnificationMatch(s1, s2) shouldBe Subst(new USubst(
      SubstitutionPair(PredOf(Function("p", None, Real, Bool), DotTerm()), Greater(DotTerm(), "0".asTerm)) ::
        SubstitutionPair(Variable("x"), Variable("y")) ::
        SubstitutionPair("t()".asTerm, Variable("z")) :: Nil))
  }

  //@todo split this test case

  private val semanticRenaming =
    UnificationMatch("quark(||)".asFormula, "quarks=6".asFormula).isInstanceOf[URenAboveUSubst] ||
    UnificationMatch("quark(||)".asFormula, "quarks=6".asFormula).isInstanceOf[FastURenAboveUSubst]



  "New unification match" should "unify renaming and instance 3*f(x)>2 and 5*x>2" in {
    shouldMatch("3*f(x)>2".asFormula,
      "3*(5*x)>2".asFormula, Subst(
        (FuncOf(Function("f", None, Real, Real), DotTerm()), Times(Number(5), DotTerm())) :: Nil
      ))
  }

  it should "unify renaming and instance p(x) and x>5" in {
    shouldMatch("p(x)".asFormula,
      "x>5".asFormula, Subst(
        (PredOf(Function("p", None, Real, Bool), DotTerm()), Greater(DotTerm(), Number(5))) :: Nil
      ))
  }


  it should "unify (\\forall x p(x)) -> p(t()) with (\\forall y y>0) -> z>0 (failed setup)" in {
    val s1 = Sequent(IndexedSeq(), IndexedSeq("\\forall x p(x) -> p(t())".asFormula))
    val s2 = Sequent(IndexedSeq(), IndexedSeq("\\forall y y>0 -> z>0".asFormula))
    //@todo not sure about the expected exception
    a[ProverException] shouldBe thrownBy(
    UnificationMatch(s1, s2) shouldBe Subst(new USubst(
      SubstitutionPair(PredOf(Function("p", None, Real, Bool), DotTerm()), Greater(DotTerm(), "0".asTerm)) ::
        SubstitutionPair(Variable("x"), Variable("y")) ::
        SubstitutionPair("t()".asTerm, Variable("z")) :: Nil))
    )
  }

  it should "unify (\\forall x p(x)) -> p(t()) with (\\forall y y>0) -> z>0" in {
    val s1 = Sequent(IndexedSeq(), IndexedSeq("\\forall x p(x) -> p(t())".asFormula))
    val s2 = Sequent(IndexedSeq(), IndexedSeq("\\forall y y>0 -> z>0".asFormula))
    println("Unify " + s1 + "\nwith  " + s2 + "\nyields " + UnificationMatch(s1, s2))
    //@todo not sure about the expected result
    UnificationMatch(s1, s2) shouldBe Subst(
      (PredOf(Function("p", None, Real, Bool), DotTerm()), Greater(DotTerm(), "0".asTerm)) ::
        (Variable("x"), Variable("y")) ::
        ("t()".asTerm, Variable("z")) :: Nil)
  }

  it should "unify [x:=f();]p(x) with [x:=7+x;]x^2>=5" in {
    shouldMatch("[x:=f();]p(x)".asFormula, "[x:=7+x;]x^2>=5".asFormula, Subst(
        ("f()".asTerm, "7+x".asTerm) ::
          (PredOf(Function("p", None, Real, Bool), DotTerm()), GreaterEqual(Power(DotTerm(), "2".asTerm), "5".asTerm)) :: Nil))
  }

  it should "unify [x:=f();]p(x) <-> p(f()) with [x:=7+x;]x^2>=5 <-> (7+x)^2>=5" in {
    shouldMatch("[x:=f();]p(x) <-> p(f())".asFormula, "[x:=7+x;]x^2>=5 <-> (7+x)^2>=5".asFormula, Subst(
      ("f()".asTerm, "7+x".asTerm) ::
        (PredOf(Function("p", None, Real, Bool), DotTerm()), GreaterEqual(Power(DotTerm(), "2".asTerm), "5".asTerm)) :: Nil))
  }

  it should "unify [x:=f();]p(x) with [y:=7+z;]y^2>=5" in {
    shouldMatch("[x:=f();]p(x)".asFormula, "[y:=7+z;]y^2>=5".asFormula, Subst(
      (Variable("x"), Variable("y")) ::
      ("f()".asTerm, "7+z".asTerm) ::
        (PredOf(Function("p", None, Real, Bool), DotTerm()), GreaterEqual(Power(DotTerm(), "2".asTerm), "5".asTerm)) :: Nil))
  }

  it should "unify [y:=f();]p(y) <-> p(f()) with [y:=7+z;]y^2>=5 <-> (7+z)^2>=5" in {
    shouldMatch("[y:=f();]p(y) <-> p(f())".asFormula, "[y:=7+z;]y^2>=5 <-> (7+z)^2>=5".asFormula, Subst(
      (("f()".asTerm, "7+z".asTerm) ::
        (PredOf(Function("p", None, Real, Bool), DotTerm()), GreaterEqual(Power(DotTerm(), "2".asTerm), "5".asTerm)) :: Nil)))
  }

  it should "unify [x_:=f();]p(x_) <-> p(f()) with [y:=7+z;]y^2>=5 <-> (7+z)^2>=5" in {
    shouldMatch("[x_:=f();]p(x_) <-> p(f())".asFormula, "[y:=7+z;]y^2>=5 <-> (7+z)^2>=5".asFormula, Subst(
      (Variable("x_"), Variable("y")) ::
        ("f()".asTerm, "7+z".asTerm) ::
        (PredOf(Function("p", None, Real, Bool), DotTerm()), GreaterEqual(Power(DotTerm(), "2".asTerm), "5".asTerm)) :: Nil))
  }

  it should "unify [x:=f();]p(x) <-> p(f()) with [y:=7+z;]y^2>=5 <-> (7+z)^2>=5" in {
    shouldMatch("[x:=f();]p(x) <-> p(f())".asFormula, "[y:=7+z;]y^2>=5 <-> (7+z)^2>=5".asFormula, Subst(
      (Variable("x"), Variable("y")) ::
        ("f()".asTerm, "7+z".asTerm) ::
        (PredOf(Function("p", None, Real, Bool), DotTerm()), GreaterEqual(Power(DotTerm(), "2".asTerm), "5".asTerm)) :: Nil))
  }

  it should "unify [x_:=y;]p(x_) with [y_0:=y;]y_0>2" in {
    shouldMatch("[x_:=y;]p(x_)".asFormula, "[y_0:=y;]y_0>2".asFormula, Subst(
      (Variable("x_"), Variable("y",Some(0))) ::
        (PredOf(Function("p", None, Real, Bool), DotTerm()), Greater(DotTerm(), "2".asTerm)) :: Nil))
  }

  it should "unify [x_:=f();]p(x_) with [y_0:=y;]y_0>2" in {
    shouldMatch("[x_:=f();]p(x_)".asFormula, "[y_0:=y;]y_0>2".asFormula, Subst(
      (Variable("x_"), Variable("y",Some(0))) ::
        ("f()".asTerm, "y".asTerm) ::
        (PredOf(Function("p", None, Real, Bool), DotTerm()), Greater(DotTerm(), "2".asTerm)) :: Nil))
  }

//  it should "unify [x_:=y;]y_0>0<->y_0>0 with [y_0:=y;]y_0>0<->y>0" in {
//    shouldMatch("[x_:=y;]y_0>0<->y_0>0".asFormula, "[y_0:=y;]y_0>0<->y>0".asFormula, Subst(
//      (Variable("x_"), Variable("y",Some(0))) :: Nil))
//  }

  it should "unify [x_:=y;]y_0>0<->y_0>0 with [a:=z;]y_0>0<->y_0>0" in {
    shouldMatch("[x_:=y;]y_0>0<->y_0>0".asFormula, "[a:=z;]y_0>0<->y_0>0".asFormula, Subst(
      (Variable("x_"), Variable("a")) :: (Variable("y"), Variable("z")) :: Nil))
  }

  it should "unify [x_:=y;]x_>0<->y>0 with [a:=z;]a>0<->z>0" in {
    shouldMatch("[x_:=y;]x_>0<->y>0".asFormula, "[a:=z;]a>0<->z>0".asFormula, Subst(
      (Variable("x_"), Variable("a")) :: (Variable("y"), Variable("z")) :: Nil))
  }

  it should "unify [x_:=y;]y>0<->y>0 with [a:=z;]z>0<->z>0" in {
    shouldMatch("[x_:=y;]y>0<->y>0".asFormula, "[a:=z;]z>0<->z>0".asFormula, Subst(
      (Variable("x_"), Variable("a")) :: (Variable("y"), Variable("z")) :: Nil))
  }

  //@todo really? needs cyclic decluttering to say the least
  it should "unify [x_:=y;]y_0>0<->y_0>0 with [y_0:=z;]y_0>0<->z>0" ignore {
    shouldMatch("[x_:=y;]y_0>0<->y_0>0".asFormula, "[y_0:=z;]y_0>0<->z>0".asFormula, Subst(
      (Variable("x_"), Variable("y",Some(0))) :: Nil))
  }

  it should "unify j()=x+y with s()=s()" ignore {
    //@note unifiable but not by mere matching, needs a proper unifier instead of a single sided matcher
    shouldUnify("s()=s()".asFormula, "j()=x+y".asFormula, USubst(
      SubstitutionPair("s()".asTerm, "x+y".asTerm) :: SubstitutionPair("j()".asTerm, "x+y".asTerm) :: Nil))
  }

  it should "unify x+y=j() with s()=s()" ignore {
    //@note unification but not matching
    shouldUnify("s()=s()".asFormula, "x+y=j()".asFormula, USubst(
      SubstitutionPair("s()".asTerm, "x+y".asTerm) :: SubstitutionPair("j()".asTerm, "x+y".asTerm) :: Nil))
  }

  //@todo single pass does not pick up x_ correctly for predicates before x_=f
  it should "unify q_(x_) & x_=f(x_) -> p_(x_) with complicated formula" ignore {
    shouldMatch("q_(x_) & x_=f(x_) -> p_(x_)".asFormula,
      "((v>=0&x+v^2/(2*B)>=S)&v=0*(kyxtime-kyxtime_0)+v_0)&x=v_0*(kyxtime-kyxtime_0)+x_0->v>=0&x+v^2/(2*B)<=S".asFormula,
      Subst(
        ("q_(.)".asFormula, "(v>=0&.+v^2/(2*B)>=S)&v=0*(kyxtime-kyxtime_0)+v_0".asFormula) ::
        ("f(.)".asTerm, "v_0*(kyxtime-kyxtime_0)+x_0".asTerm) ::
        ("p_(.)".asFormula, "v>=0&.+v^2/(2*B)<=S".asFormula) ::
        ("x_".asVariable, "x".asVariable) ::
        Nil)
    )
  }

  it should "unify x_=f(x_) & q_(x_) -> p_(x_) with complicated formula" in {
    shouldMatch("x_=f(x_) & q_(x_) -> p_(x_)".asFormula,
      "x=v_0*(kyxtime-kyxtime_0)+x_0&((v>=0&x+v^2/(2*B)>=S)&v=0*(kyxtime-kyxtime_0)+v_0)->v>=0&x+v^2/(2*B)<=S".asFormula,
      Subst(
        ("f(.)".asTerm, "v_0*(kyxtime-kyxtime_0)+x_0".asTerm) ::
        ("q_(.)".asFormula, "(v>=0&.+v^2/(2*B)>=S)&v=0*(kyxtime-kyxtime_0)+v_0".asFormula) ::
        ("p_(.)".asFormula, "v>=0&.+v^2/(2*B)<=S".asFormula) ::
        ("x_".asVariable, "x".asVariable) ::
        Nil)
    )
  }

  "Dassignb unification" should "unify [u':=f();]p(u') with [u':=b();]u'>=0" in {
    shouldMatch("[u':=f();]p(u')".asFormula, "[u':=b();]u'>=0".asFormula, Subst(
      (FuncOf(Function("f",None,Unit,Real), Nothing), FuncOf(Function("b",None,Unit,Real),Nothing)) ::
        (PredOf(Function("p",None,Real,Bool),DotTerm()), GreaterEqual(DotTerm(),Number(0))) :: Nil))
  }

  it should "unify [x':=f();]p(x') with [u':=b();]u'>=0" in {
    shouldMatch("[x':=f();]p(x')".asFormula, "[u':=b();]u'>=0".asFormula, Subst(
      (Variable("x"), Variable("u")) :: (FuncOf(Function("f",None,Unit,Real), Nothing), FuncOf(Function("b",None,Unit,Real),Nothing)) ::
        (PredOf(Function("p",None,Real,Bool),DotTerm()), GreaterEqual(DotTerm(),Number(0))) :: Nil))
  }


  "More unification" should "unify y>0 -> [x:=2;]y>0 with p() -> [a;]p()" in {
    shouldMatch("p() -> [a;]p()".asFormula, "y>0 -> [x:=2;]y>0".asFormula, Subst(
      (PredOf(Function("p", None, Unit, Bool), Nothing), "y>0".asFormula) ::
        (ProgramConst("a"), Assign(Variable("x"), Number(2))) :: Nil))
  }

  it should "unify [x:=2;]y>0 -> y>0 with [a;]p() -> p()" in {
    // not an axiom, just to test both directions
    shouldMatch("[a;]p() -> p()".asFormula, "[x:=2;]y>0 -> y>0".asFormula, Subst(
      (ProgramConst("a"), Assign(Variable("x"), Number(2))) ::
        (PredOf(Function("p", None, Unit, Bool), Nothing), "y>0".asFormula) :: Nil))
  }

  it should "unify renaming and instance [y:=y;]p(||) and [y_0:=y_0;](y_0>77&true)" in {
    shouldMatch("[y:=y;]p(||)".asFormula,
      "[y_0:=y_0;](y_0>77&true)".asFormula, Subst(
      (Variable("y"), Variable("y",Some(0))) ::
        (UnitPredicational("p", AnyArg), (if (semanticRenaming) "(y_0>77&true)" else "(y>77&true)").asFormula) ::
        Nil
    ))
  }

  it should "unify renaming and instance [y:=y;]p(||)<->p(||) and [y_0:=y_0;](true)<->(true)" in {
    shouldMatch("[y:=y;]p(||)<->p(||)".asFormula,
      "[y_0:=y_0;](true)<->(true)".asFormula, Subst(
      (Variable("y"), Variable("y",Some(0))) ::
        (UnitPredicational("p", AnyArg), "(true)".asFormula) ::
        Nil
    ))
  }

  it should "unify renaming x=0 and y_0=0" in {
    shouldMatch("x=0".asFormula,
      "y_0=0".asFormula, Subst(
      (Variable("x"), Variable("y",Some(0))) :: Nil))
  }

  it should "unify renaming x=0<->x=0 and y_0=0<->y_0=0" in {
    shouldMatch("x=0<->x=0".asFormula,
      "y_0=0<->y_0=0".asFormula, Subst(
      (Variable("x"), Variable("y",Some(0))) :: Nil))
  }

  it should "unify renaming x=0&x=0<->x=0 and y_0=0&y_0=0<->y_0=0" in {
    shouldMatch("x=0&x=0<->x=0".asFormula,
      "y_0=0&y_0=0<->y_0=0".asFormula, Subst(
      (Variable("x"), Variable("y",Some(0))) :: Nil
    ))
  }

  it should "unify renaming x=0<->x=0&x=0 and y_0=0<->y_0=0&y_0=0" in {
    shouldMatch("x=0<->x=0&x=0".asFormula,
      "y_0=0<->y_0=0&y_0=0".asFormula, Subst(
      (Variable("x"), Variable("y",Some(0))) :: Nil
    ))
  }

  it should "unify renaming x>1&x=2<->x<3 and y_0>1&y_0=2<->y_0<3" in {
    shouldMatch("x>1&x=2<->x<3".asFormula,
      "y_0>1&y_0=2<->y_0<3".asFormula, Subst(
      (Variable("x"), Variable("y",Some(0))) :: Nil
    ))
  }

  it should "unify renaming x>1<->x=2&x<3 and y_0>1<->y_0=2&y_0<3" in {
    shouldMatch("x>1<->x=2&x<3".asFormula,
      "y_0>1<->y_0=2&y_0<3".asFormula, Subst(
      (Variable("x"), Variable("y",Some(0))) :: Nil
    ))
  }

  it should "unify renaming and instance [y:=y;]y>5<->y>5 and [y_0:=y_0;]y_0>5<->y_0>5" in {
    shouldMatch("[y:=y;]y>5<->y>5".asFormula,
      "[y_0:=y_0;]y_0>5<->y_0>5".asFormula, Subst(
      (Variable("y"), Variable("y",Some(0))) :: Nil
    ))
  }

  it should "unify renaming and instance p(||)<->[y:=y;]p(||) and (y_0=1)<->[y_0:=y_0;](y_0=1)" ignore {
    shouldMatch("p(||)<->[y:=y;]p(||)".asFormula,
      "(y_0=1)<->[y_0:=y_0;](y_0=1)".asFormula, Subst(
      (Variable("y"), Variable("y",Some(0))) ::
        (UnitPredicational("p", AnyArg), (if (semanticRenaming) "(y_0=1)" else "y=1").asFormula) ::
        Nil
    ))
  }

  it should "unify renaming and instance [y:=y;]p(||)<->p(||) and [y_0:=y_0;](y_0=0)<->(y_0=0)" in {
    shouldMatch("[y:=y;]p(||)<->p(||)".asFormula,
      "[y_0:=y_0;](y_0=0)<->(y_0=0)".asFormula, Subst(
      (Variable("y"), Variable("y",Some(0))) ::
        (UnitPredicational("p", AnyArg), (if (semanticRenaming) "(y_0=0)" else "y=0").asFormula) ::
        Nil
    ))
  }

  it should "unify renaming and instance p(||)<->[y:=y;]p(||) and (true)<->[y_0:=y_0;](true)" in {
    shouldMatch("p(||)<->[y:=y;]p(||)".asFormula,
      "(true)<->[y_0:=y_0;](true)".asFormula, Subst(
      (Variable("y"), Variable("y",Some(0))) ::
        (UnitPredicational("p", AnyArg), "(true)".asFormula) ::
        Nil
    ))
  }

  it should "unify renaming and instance p(||)<->[y:=y;]p(||) and (y_0>77&true)<->[y_0:=y_0;](y_0>77&true)" ignore {
    shouldMatch("p(||)<->[y:=y;]p(||)".asFormula,
      "(y_0>77&true)<->[y_0:=y_0;](y_0>77&true)".asFormula, Subst(
      (Variable("y"), Variable("y",Some(0))) ::
        (UnitPredicational("p", AnyArg), (if (semanticRenaming) "(y_0>77&true)" else "y>77&true").asFormula) ::
        Nil
    ))
  }

  it should "unify renaming and instance [y:=y;]p(||)<->p(||) and [y_0:=y_0;](y_0>77&true)<->(y_0>77&true)" in {
    shouldMatch("[y:=y;]p(||)<->p(||)".asFormula,
      "[y_0:=y_0;](y_0>77&true)<->(y_0>77&true)".asFormula, Subst(
      (Variable("y"), Variable("y",Some(0))) ::
        (UnitPredicational("p", AnyArg), (if (semanticRenaming) "(y_0>77&true)" else "y>77&true").asFormula) ::
        Nil
    ))
  }

  it should "unify renaming and long instance" in {
    shouldMatch("[x_:=x_;]p(||)<->p(||)".asFormula,
      "[x_0:=x_0;](((x_0>0&true)&true)&true->(2>=0|false)|false)<->((x_0>0&true)&true)&true->(2>=0|false)|false".asFormula, Subst(
      (Variable("x_"), Variable("x",Some(0))) ::
        (UnitPredicational("p", AnyArg), (if (semanticRenaming) "(((x_0>0&true)&true)&true->(2>=0|false)|false)" else "(((x_>0&true)&true)&true->(2>=0|false)|false)").asFormula) ::
        Nil
    ))
  }

  it should "match abstract loop against loopy single ODE" in {
    shouldMatch("[{a;}*]p(||)".asFormula,
      "[{{x'=v}}*](v>=0&true)".asFormula, Subst(
        (ProgramConst("a"), "{x'=v}".asProgram) ::
          (UnitPredicational("p", AnyArg), "v>=0&true".asFormula) ::Nil
      ))
  }

  it should "match abstract loop against loopy ODE system " in {
    shouldMatch("[{a;}*]p(||)".asFormula,
      "[{{x'=v,v'=A}}*](v>=0&true)".asFormula, Subst(
      (ProgramConst("a"), "{x'=v,v'=A}".asProgram) ::
        (UnitPredicational("p", AnyArg), "v>=0&true".asFormula) ::Nil
    ))
  }

  it should "match abstract loop against loopy ODE system with domain" in {
    shouldMatch("[{a;}*]p(||)".asFormula,
      "[{{x'=v,v'=A&v<=5}}*](v>=0&true)".asFormula, Subst(
        (ProgramConst("a"), "{x'=v,v'=A&v<=5}".asProgram) ::
          (UnitPredicational("p", AnyArg), "v>=0&true".asFormula) ::Nil
      ))
  }

  it should "match abstract loop against loopy initialized ODE" in {
    shouldMatch("[{a;}*]p(||)".asFormula,
      "[{v:=5;{x'=v,v'=A}}*](v>=0&true)".asFormula, Subst(
        (ProgramConst("a"), "v:=5;{x'=v,v'=A}".asProgram) ::
          (UnitPredicational("p", AnyArg), "v>=0&true".asFormula) ::Nil
      ))
  }

  it should "match derived powers" in {
    shouldMatch("(f(||)^(c()))'".asTerm,
      "(x^2)'".asTerm, Subst(
        (UnitFunctional("f", AnyArg, Real), "x".asTerm) ::
          (FuncOf(Function("c", None, Unit, Real), Nothing), "2".asTerm) :: Nil
      ))
  }

  it should "say something about broken types" ignore {
    //@todo in principle this should throw a CoreException about incompatible types, actually. Not parse print and incompatible substitution sorts. Both are true but not the first issue.
    a[ProverException] shouldBe thrownBy(
    Subst(
          (UnitFunctional("f", AnyArg, Real), "x".asTerm) ::
          (FuncOf(Function("c", None, Unit, Bool), Nothing), "2".asTerm) :: Nil
      )
    )
  }

  it should "unify DC axiom" in {
    shouldMatch(
      "([{c&q(||)}]p(||) <-> [{c&(q(||)&r(||))}]p(||)) <- [{c&q(||)}]r(||)".asFormula,
      "([{x'=v&v>=0&v>0}]x>=0 <-> [{x'=v&(v>=0&v>0)&x>0}]x>=0) <- [{x'=v&v>=0&v>0}]x>0".asFormula,
      Subst(
        (DifferentialProgramConst("c"), "{x'=v}".asDifferentialProgram) ::
        (UnitPredicational("p", AnyArg), "x>=0".asFormula) ::
        (UnitPredicational("q", AnyArg), "v>=0&v>0".asFormula) ::
        (UnitPredicational("r", AnyArg), "x>0".asFormula) :: Nil
      )
    )
  }

  it should "unify DC axiom without evolution domain" in {
    shouldMatch(
      "([{c&q(||)}]p(||) <-> [{c&(q(||)&r(||))}]p(||)) <- [{c&q(||)}]r(||)".asFormula,
      "([{x'=v}]x>=0 <-> [{x'=v&true&x>0}]x>=0) <- [{x'=v}]x>0".asFormula,
      Subst(
        (DifferentialProgramConst("c"), "{x'=v}".asDifferentialProgram) ::
          (UnitPredicational("p", AnyArg), "x>=0".asFormula) ::
          (UnitPredicational("q", AnyArg), "true".asFormula) ::
          (UnitPredicational("r", AnyArg), "x>0".asFormula) :: Nil
      )
    )
  }

  //@todo this test case would need the expensive reunify to be activated in UnificationMatch again
  "Reunifier ideally" should "unify p(f()) <-> [x:=f();]p(x) with (7+x)^2>=5 <-> [x:=7+x;]x^2>=5" taggedAs OptimisticTest ignore {
    shouldMatch("p(f()) <-> [x:=f();]p(x)".asFormula, "(7+x)^2>=5 <-> [x:=7+x;]x^2>=5".asFormula, Subst(
      ("f()".asTerm, "7+x".asTerm) ::
        (PredOf(Function("p", None, Real, Bool), DotTerm()), GreaterEqual(Power(DotTerm(), "2".asTerm), "5".asTerm)) :: Nil))
  }

  "colored dots unification" should "unify 3+f(x,y) with 3+(x^2+y)" in {
    shouldUnify("3+f(x,y)".asTerm,
      "3+(x^2+y)".asTerm, USubst(
        SubstitutionPair(
          "f((•_0,•_1))".asTerm,
          "•_0^2+•_1".asTerm
        ) :: Nil
      ))
  }

  it should "unify 3+f(x,y,z) with 3+(x^y+z)" in {
    shouldUnify("3+f(x,y,z)".asTerm,
      "3+(x^y+z)".asTerm, USubst(
        SubstitutionPair(
          "f((•_0,•_1,•_2))".asTerm,
          "•_0^•_1+•_2".asTerm
        ) :: Nil
      ))
  }


  it should "unify renaming and instance p(x,y) and x*y>5" in {
    shouldMatch("p(x,y)".asFormula,
      "x*y>5".asFormula, Subst(
        ("p((•_0,•_1))".asFormula,
          "•_0*•_1>5".asFormula) :: Nil
      ))
  }

  it should "unify renaming and instance p(x,y,z) and x*y>z" in {
    shouldMatch("p(x,y,z)".asFormula,
      "x*y>z".asFormula, Subst(
        ("p((•_0,•_1,•_2))".asFormula,
          "•_0*•_1>•_2".asFormula) :: Nil
      ))
  }

  it should "unify renaming and instance f(x,y,x*y)" in {
    shouldMatch("f(x,y,x*y) = f(a, b, c)".asFormula,
      "x*y = a*b".asFormula, Subst(
        ("f((•_0,•_1,•_2))".asTerm,
          "•_0*•_1".asTerm) :: Nil
      ))
    shouldMatch("f(x,y,x*y) = f(a, b, c)".asFormula,
      "x*y = c".asFormula, Subst(
        ("f((•_0,•_1,•_2))".asTerm,
          "•_2".asTerm) :: Nil
      ))
  }
}
