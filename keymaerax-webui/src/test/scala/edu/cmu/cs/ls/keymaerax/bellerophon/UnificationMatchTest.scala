/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.infrastruct

import edu.cmu.cs.ls.keymaerax.bellerophon.UnificationException
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.parser.SystemTestBase
import edu.cmu.cs.ls.keymaerax.tagobjects.OptimisticTest
import edu.cmu.cs.ls.keymaerax.tags.{SummaryTest, UsualTest}
import edu.cmu.cs.ls.keymaerax.{Configuration, FileConfiguration}
import testHelper.KeYmaeraXTestTags.{IgnoreInBuildTest, TodoTest}

import scala.collection.immutable
import scala.collection.immutable._

/**
 * Testing unifier and its limits.
 *
 * @author
 *   Andre Platzer
 * @see
 *   [[UnificationMatch]]
 */
@SummaryTest @UsualTest
class UnificationMatchTest extends SystemTestBase {

  val matcher = {
    Configuration.setConfiguration(FileConfiguration)
    if (true) UnificationMatch else new FreshPostUnificationMatch
  }
  private def Subst(subs: immutable.Seq[(Expression, Expression)]): RenUSubst =
    if (!semanticRenaming) RenUSubst(subs) else new FastURenAboveUSubst(subs)
  private def Subst(us: USubst): RenUSubst = Subst(us.subsDefsInput.map(sp => (sp.what, sp.repl)))

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
      a[UnificationException] should be thrownBy matcher(e1, e2)
    }
  }

  private def shouldUnify(e1: Expression, e2: Expression, us: USubst): Unit = should(e1, e2, Some(us))

  private def shouldBeSameUnifier(u1: RenUSubst, u2: RenUSubst): Unit = {
    if (
      u1.subsDefsInput.filterNot(sp => sp._1 == sp._2).toSet != u2.subsDefsInput.filterNot(sp => sp._1 == sp._2).toSet
    ) u1 shouldBe (u2)
  }

  // new unification matchers from now on

  private def shouldMatch(e1: Expression, e2: Expression, us: Option[RenUSubst]): Unit = {
    if (us.isDefined) {
      println("Expression1: " + e1)
      println("Expression2: " + e2)
      val s = UnificationMatch(e1, e2)
      println("Unifier:     " + s)
      println(
        "Expected:    " + us.get + "\t" + (if (s == us.get) "identical substitution" else "different substitution")
      )
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
      a[UnificationException] should be thrownBy UnificationMatch(e1, e2)
    }
  }

  private def shouldMatch(e1: Expression, e2: Expression, us: RenUSubst): Unit = shouldMatch(e1, e2, Some(us))

  "Unification terms" should "unify f() with x^2+y" in {
    shouldUnify(
      "f()".asPlainTerm,
      "x^2+y".asPlainTerm,
      USubst(SubstitutionPair("f()".asPlainTerm, "x^2+y".asPlainTerm) :: Nil),
    )
  }

  it should "unify f(x) with x^2+y" in {
    shouldUnify(
      "f(x)".asPlainTerm,
      "x^2+y".asPlainTerm,
      USubst(SubstitutionPair("f(._0)".asPlainTerm, "(._0)^2+y".asPlainTerm) :: Nil),
    )
  }

  it should "unify 3+f() with 3+(x^2+y)" in {
    shouldUnify(
      "3+f()".asPlainTerm,
      "3+(x^2+y)".asPlainTerm,
      USubst(SubstitutionPair("f()".asPlainTerm, "x^2+y".asPlainTerm) :: Nil),
    )
  }

  it should "unify 3+f(x) with 3+(x^2+y)" taggedAs (IgnoreInBuildTest) in {
    shouldUnify(
      "3+f(x)".asPlainTerm,
      "3+(x^2+y)".asPlainTerm,
      USubst(SubstitutionPair("f(._0)".asPlainTerm, "(._0)^2+y".asPlainTerm) :: Nil),
    )
  }

  "Simple bidirectional unification" should "support mixed term left-right matching" in {
    RestrictedBiDiUnificationMatch("==> a=0, f(x)>=0".asPlainSequent, "==> a()=0, x^2>=0".asPlainSequent)
      .usubst shouldBe USubst(List("a()~>a".asPlainSubstitutionPair, "f(._0)~>._0^2".asPlainSubstitutionPair))
    RestrictedBiDiUnificationMatch("==> a()=0, x^2>=0".asPlainSequent, "==> a=0, f(x)>=0".asPlainSequent)
      .usubst shouldBe USubst(List("a()~>a".asPlainSubstitutionPair, "f(._0)~>._0^2".asPlainSubstitutionPair))
    RestrictedBiDiUnificationMatch("==> g(y)=0, x^2>=0".asPlainSequent, "==> y+1=0, f(x)>=0".asPlainSequent)
      .usubst shouldBe USubst(List("g(._0)~>._0+1".asPlainSubstitutionPair, "f(._0)~>._0^2".asPlainSubstitutionPair))
  }

  it should "support more mixed left-right matching" in {
    RestrictedBiDiUnificationMatch("==> a=0, p(x)".asPlainSequent, "==> q(a), x^2>=0".asPlainSequent).usubst shouldBe
      USubst(List("q(._0)~>._0=0".asPlainSubstitutionPair, "p(._0)~>._0^2>=0".asPlainSubstitutionPair))
    RestrictedBiDiUnificationMatch("==> q(a), x^2>=0".asPlainSequent, "==> a=0, p(x)".asPlainSequent).usubst shouldBe
      USubst(List("q(._0)~>._0=0".asPlainSubstitutionPair, "p(._0)~>._0^2>=0".asPlainSubstitutionPair))
  }

  it should "unify p(x,y) with x<=2" in {
    RestrictedBiDiUnificationMatch("p(x,y)".asPlainFormula, "x<=2".asPlainFormula).usubst shouldBe
      USubst(List(SubstitutionPair("p(._0,._1)".asPlainFormula, "._0<=._1".asPlainFormula)))
  }

  it should "unify p(x,c()) with x<=2" in {
    RestrictedBiDiUnificationMatch("p(x,c())".asPlainFormula, "x<=2".asPlainFormula).usubst shouldBe
      USubst(List(SubstitutionPair("p(._0,._1)".asPlainFormula, "._0<=._1".asPlainFormula)))
  }

  it should "unify p(x,y,z) with x+2<=3" in {
    // @note unable to guess y=2/y=3 vs. z=2,z=3
    RestrictedBiDiUnificationMatch("p(x,y,z)".asPlainFormula, "x+2<=3".asPlainFormula).usubst shouldBe
      USubst(List(SubstitutionPair("p(._0,._1,._2)".asPlainFormula, "._0+2<=3".asPlainFormula)))
  }

  it should "match numbers with arguments when unambiguous" in {
    RestrictedBiDiUnificationMatch(
      "[{prg;}*](x<=2&any()>=2)".asPlainFormula,
      "[{prg;}*](leq(x,two())&any()>=2)".asPlainFormula,
    ).usubst shouldBe USubst(List(SubstitutionPair("leq(._0,._1)".asPlainFormula, "._0<=._1".asPlainFormula)))

    RestrictedBiDiUnificationMatch(
      "any()>=2&x<=2 ==> [{prg;}*](x<=2&any()>=2)->[{prg;}*]x<=any()".asPlainSequent,
      "p(x) ==> [{prg;}*](leq(x,two())&any()>=2)->[{prg;}*]leq(x,any())".asPlainSequent,
    ).usubst shouldBe USubst(List(
      SubstitutionPair("p(._0)".asPlainFormula, "any()>=2 & ._0<=2".asPlainFormula),
      SubstitutionPair("leq(._0, ._1)".asPlainFormula, "._0<=._1".asPlainFormula),
    ))
  }

  it should "join on numbers" in {
    RestrictedBiDiUnificationMatch(
      "==> 1=1, x=1*2, x=y*2".asPlainSequent,
      "==> f()=f(), p(x,f()), p(x,y)".asPlainSequent,
    ).usubst shouldBe USubst(List(
      SubstitutionPair("f()".asPlainTerm, "1".asPlainTerm),
      SubstitutionPair("p(._0, ._1)".asPlainFormula, "._0=._1*2".asPlainFormula),
    ))
    RestrictedBiDiUnificationMatch(
      "==> 1=1, x=y*2, x=1*2".asPlainSequent,
      "==> f()=f(), p(x,y), p(x,f())".asPlainSequent,
    ).usubst shouldBe USubst(List(
      SubstitutionPair("f()".asPlainTerm, "1".asPlainTerm),
      SubstitutionPair("p(._0, ._1)".asPlainFormula, "._0=._1*2".asPlainFormula),
    ))
  }

  it should "FEATURE_REQUEST: join on numbers (2)" taggedAs TodoTest in {
    RestrictedBiDiUnificationMatch("==> x=1*2, x=y*2".asPlainSequent, "==> p(x,f()), p(x,y)".asPlainSequent)
      .usubst shouldBe USubst(List(
      SubstitutionPair("f()".asPlainTerm, "1".asPlainTerm),
      SubstitutionPair("p(._0, ._1)".asPlainFormula, "._0=._1*2".asPlainFormula),
    ))
  }

  "Unification formulas" should "unify p() with x^2+y>=0" in {
    shouldUnify(
      "p()".asPlainFormula,
      "x^2+y>=0".asPlainFormula,
      USubst(SubstitutionPair("p()".asPlainFormula, "x^2+y>=0".asPlainFormula) :: Nil),
    )
  }

  it should "unify \\forall x p(x) with \\forall x (!q(x))" in {
    shouldUnify(
      "\\forall x p(x)".asPlainFormula,
      "\\forall x (!q(x))".asPlainFormula,
      USubst(SubstitutionPair("p(._0)".asPlainFormula, "!q(._0)".asPlainFormula) :: Nil),
    )
  }

  it should "match \\forall x p(x) with \\forall x (!p(x))" in {
    shouldUnify(
      "\\forall x p(x)".asPlainFormula,
      "\\forall x (!p(x))".asPlainFormula,
      USubst(SubstitutionPair("p(._0)".asPlainFormula, "!p(._0)".asPlainFormula) :: Nil),
    )
  }
  it should "match" in {
    shouldUnify(
      "[a;]p() -> [a;]p()".asPlainFormula,
      "[x:=x+1;]y>0 -> [x:=x+1;]y>0".asPlainFormula,
      USubst(
        SubstitutionPair("a;".asPlainProgram, "x:=x+1;".asPlainProgram) ::
          SubstitutionPair("p()".asPlainFormula, "y>0".asPlainFormula) :: Nil
      ),
    )
  }

  it should "rename bound variables" in {
    shouldMatch(
      "p_()&\\exists y_ true".asPlainFormula,
      "(\\exists y true)&\\exists y true".asPlainFormula,
      Subst(Seq(("p_()".asPlainFormula, "(\\exists y_ true)".asPlainFormula), ("y_".asVariable, "y".asVariable))),
    )
  }

  it should "rename bound variables? OPTIMISTIC" taggedAs OptimisticTest in {
    shouldMatch(
      "p_()&\\exists y_ true".asPlainFormula,
      "(\\exists y true)&\\exists y true".asPlainFormula,
      Subst(Seq(("p_()".asPlainFormula, "(\\exists y_ true)".asPlainFormula), ("y_".asVariable, "y".asVariable))),
      // @note this is an illegal unifier but UniformMatching finds correct one
      // Subst(Seq(("p_()".asPlainFormula, "(\\exists z_ true)".asPlainFormula), ("y_".asVariable, "y".asVariable), ("z_".asVariable, "y".asVariable)))
    )
  }

  it should "support mixed left-right matching" in {
    // @note needs to match p(x,y) with x=y but inside r needs the opposite direction
    UnificationMatch(
      "==> p(x,y) & r(x,y,0) -> r(x,y,a)".asPlainSequent,
      "==> x=y & (0>=0 & x^2+y^2=0) -> (a>=0 & x^2+y^2=0)".asPlainSequent,
    ).usubst shouldBe USubst(List(
      "r(._0,._1,._2)~>._2>=0&._0^2+._1^2=0".asPlainSubstitutionPair,
      "p(._0,._1)~>._0=._1".asPlainSubstitutionPair,
    ))
  }

  "Unification programs" should "unify [a;]x>=0 with [x:=x+5;]x>=0" in {
    shouldUnify(
      "[a;]x>=0".asPlainFormula,
      "[x:=x+5;]x>=0".asPlainFormula,
      USubst(SubstitutionPair("a;".asPlainProgram, "x:=x+5;".asPlainProgram) :: Nil),
    )
  }

  it should "unify [a;x:=7;]x>=0 with [x:=x+5;x:=7;]x>=0" in {
    shouldUnify(
      "[a;x:=7;]x>=0".asPlainFormula,
      "[x:=x+5;x:=7;]x>=0".asPlainFormula,
      USubst(SubstitutionPair("a;".asPlainProgram, "x:=x+5;".asPlainProgram) :: Nil),
    )
  }

  "Old unification match" should "unify (\\forall x p(x)) -> p(t()) with (\\forall y y>0) -> z>0 (fails)" ignore {
    val s1 = Sequent(IndexedSeq(), IndexedSeq("\\forall x p(x) -> p(t())".asPlainFormula))
    val s2 = Sequent(IndexedSeq(), IndexedSeq("\\forall y y>0 -> z>0".asPlainFormula))
    // @todo not sure about the expected result
    UnificationMatch(s1, s2) shouldBe Subst(new USubst(
      SubstitutionPair(
        PredOf(Function("p", None, Real, Bool), DotTerm(Real, Some(0))),
        Greater(DotTerm(Real, Some(0)), "0".asPlainTerm),
      ) :: SubstitutionPair(Variable("x"), Variable("y")) :: SubstitutionPair("t()".asPlainTerm, Variable("z")) :: Nil
    ))
  }

  // @todo split this test case

  private val semanticRenaming = UnificationMatch("quark(||)".asPlainFormula, "quarks=6".asPlainFormula)
    .isInstanceOf[URenAboveUSubst] || UnificationMatch("quark(||)".asPlainFormula, "quarks=6".asPlainFormula)
    .isInstanceOf[FastURenAboveUSubst]

  "New unification match" should "unify renaming and instance 3*f(x)>2 and 5*x>2" in {
    shouldMatch(
      "3*f(x)>2".asPlainFormula,
      "3*(5*x)>2".asPlainFormula,
      Subst(
        (FuncOf(Function("f", None, Real, Real), DotTerm(Real, Some(0))), Times(Number(5), DotTerm(Real, Some(0)))) ::
          Nil
      ),
    )
  }

  it should "unify renaming and instance p(x) and x>5" in {
    shouldMatch(
      "p(x)".asPlainFormula,
      "x>5".asPlainFormula,
      Subst(
        (PredOf(Function("p", None, Real, Bool), DotTerm(Real, Some(0))), Greater(DotTerm(Real, Some(0)), Number(5))) ::
          Nil
      ),
    )
  }

  it should "unify (\\forall x p(x)) -> p(t()) with (\\forall y y>0) -> z>0 (failed setup)" in {
    val s1 = Sequent(IndexedSeq(), IndexedSeq("\\forall x p(x) -> p(t())".asPlainFormula))
    val s2 = Sequent(IndexedSeq(), IndexedSeq("\\forall y y>0 -> z>0".asPlainFormula))
    // @todo not sure about the expected exception
    a[ProverException] shouldBe thrownBy(
      UnificationMatch(s1, s2) shouldBe Subst(new USubst(
        SubstitutionPair(
          PredOf(Function("p", None, Real, Bool), DotTerm(Real, Some(0))),
          Greater(DotTerm(Real, Some(0)), "0".asPlainTerm),
        ) :: SubstitutionPair(Variable("x"), Variable("y")) :: SubstitutionPair("t()".asPlainTerm, Variable("z")) :: Nil
      ))
    )
  }

  it should "unify (\\forall x p(x)) -> p(t()) with (\\forall y y>0) -> z>0" in {
    val s1 = Sequent(IndexedSeq(), IndexedSeq("\\forall x p(x) -> p(t())".asPlainFormula))
    val s2 = Sequent(IndexedSeq(), IndexedSeq("\\forall y y>0 -> z>0".asPlainFormula))
    println("Unify " + s1 + "\nwith  " + s2 + "\nyields " + UnificationMatch(s1, s2))
    // @todo not sure about the expected result
    UnificationMatch(s1, s2) shouldBe Subst(
      (
        PredOf(Function("p", None, Real, Bool), DotTerm(Real, Some(0))),
        Greater(DotTerm(Real, Some(0)), "0".asPlainTerm),
      ) :: (Variable("x"), Variable("y")) :: ("t()".asPlainTerm, Variable("z")) :: Nil
    )
  }

  it should "unify [x:=f();]p(x) with [x:=7+x;]x^2>=5" in {
    shouldMatch(
      "[x:=f();]p(x)".asPlainFormula,
      "[x:=7+x;]x^2>=5".asPlainFormula,
      Subst(
        ("f()".asPlainTerm, "7+x".asPlainTerm) ::
          (
            PredOf(Function("p", None, Real, Bool), DotTerm(Real, Some(0))),
            GreaterEqual(Power(DotTerm(Real, Some(0)), "2".asPlainTerm), "5".asPlainTerm),
          ) :: Nil
      ),
    )
  }

  it should "unify [x:=f();]p(x) <-> p(f()) with [x:=7+x;]x^2>=5 <-> (7+x)^2>=5" in {
    shouldMatch(
      "[x:=f();]p(x) <-> p(f())".asPlainFormula,
      "[x:=7+x;]x^2>=5 <-> (7+x)^2>=5".asPlainFormula,
      Subst(
        ("f()".asPlainTerm, "7+x".asPlainTerm) ::
          (
            PredOf(Function("p", None, Real, Bool), DotTerm(Real, Some(0))),
            GreaterEqual(Power(DotTerm(Real, Some(0)), "2".asPlainTerm), "5".asPlainTerm),
          ) :: Nil
      ),
    )
  }

  it should "unify [x:=f();]p(x) with [y:=7+z;]y^2>=5" in {
    shouldMatch(
      "[x:=f();]p(x)".asPlainFormula,
      "[y:=7+z;]y^2>=5".asPlainFormula,
      Subst(
        (Variable("x"), Variable("y")) :: ("f()".asPlainTerm, "7+z".asPlainTerm) ::
          (
            PredOf(Function("p", None, Real, Bool), DotTerm(Real, Some(0))),
            GreaterEqual(Power(DotTerm(Real, Some(0)), "2".asPlainTerm), "5".asPlainTerm),
          ) :: Nil
      ),
    )
  }

  it should "unify [y:=f();]p(y) <-> p(f()) with [y:=7+z;]y^2>=5 <-> (7+z)^2>=5" in {
    shouldMatch(
      "[y:=f();]p(y) <-> p(f())".asPlainFormula,
      "[y:=7+z;]y^2>=5 <-> (7+z)^2>=5".asPlainFormula,
      Subst((("f()".asPlainTerm, "7+z".asPlainTerm) ::
        (
          PredOf(Function("p", None, Real, Bool), DotTerm(Real, Some(0))),
          GreaterEqual(Power(DotTerm(Real, Some(0)), "2".asPlainTerm), "5".asPlainTerm),
        ) :: Nil)),
    )
  }

  it should "unify [x_:=f();]p(x_) <-> p(f()) with [y:=7+z;]y^2>=5 <-> (7+z)^2>=5" in {
    shouldMatch(
      "[x_:=f();]p(x_) <-> p(f())".asPlainFormula,
      "[y:=7+z;]y^2>=5 <-> (7+z)^2>=5".asPlainFormula,
      Subst(
        (Variable("x_"), Variable("y")) :: ("f()".asPlainTerm, "7+z".asPlainTerm) ::
          (
            PredOf(Function("p", None, Real, Bool), DotTerm(Real, Some(0))),
            GreaterEqual(Power(DotTerm(Real, Some(0)), "2".asPlainTerm), "5".asPlainTerm),
          ) :: Nil
      ),
    )
  }

  it should "unify [x:=f();]p(x) <-> p(f()) with [y:=7+z;]y^2>=5 <-> (7+z)^2>=5" in {
    shouldMatch(
      "[x:=f();]p(x) <-> p(f())".asPlainFormula,
      "[y:=7+z;]y^2>=5 <-> (7+z)^2>=5".asPlainFormula,
      Subst(
        (Variable("x"), Variable("y")) :: ("f()".asPlainTerm, "7+z".asPlainTerm) ::
          (
            PredOf(Function("p", None, Real, Bool), DotTerm(Real, Some(0))),
            GreaterEqual(Power(DotTerm(Real, Some(0)), "2".asPlainTerm), "5".asPlainTerm),
          ) :: Nil
      ),
    )
  }

  it should "unify [x_:=y;]p(x_) with [y_0:=y;]y_0>2" in {
    shouldMatch(
      "[x_:=y;]p(x_)".asPlainFormula,
      "[y_0:=y;]y_0>2".asPlainFormula,
      Subst(
        (Variable("x_"), Variable("y", Some(0))) ::
          (
            PredOf(Function("p", None, Real, Bool), DotTerm(Real, Some(0))),
            Greater(DotTerm(Real, Some(0)), "2".asPlainTerm),
          ) :: Nil
      ),
    )
  }

  it should "unify [x_:=f();]p(x_) with [y_0:=y;]y_0>2" in {
    shouldMatch(
      "[x_:=f();]p(x_)".asPlainFormula,
      "[y_0:=y;]y_0>2".asPlainFormula,
      Subst(
        (Variable("x_"), Variable("y", Some(0))) :: ("f()".asPlainTerm, "y".asPlainTerm) ::
          (
            PredOf(Function("p", None, Real, Bool), DotTerm(Real, Some(0))),
            Greater(DotTerm(Real, Some(0)), "2".asPlainTerm),
          ) :: Nil
      ),
    )
  }

  //  it should "unify [x_:=y;]y_0>0<->y_0>0 with [y_0:=y;]y_0>0<->y>0" in {
  //    shouldMatch("[x_:=y;]y_0>0<->y_0>0".asPlainFormula, "[y_0:=y;]y_0>0<->y>0".asPlainFormula, Subst(
  //      (Variable("x_"), Variable("y",Some(0))) :: Nil))
  //  }

  it should "unify [x_:=y;]y_0>0<->y_0>0 with [a:=z;]y_0>0<->y_0>0" in {
    shouldMatch(
      "[x_:=y;]y_0>0<->y_0>0".asPlainFormula,
      "[a:=z;]y_0>0<->y_0>0".asPlainFormula,
      Subst((Variable("x_"), Variable("a")) :: (Variable("y"), Variable("z")) :: Nil),
    )
  }

  it should "unify [x_:=y;]x_>0<->y>0 with [a:=z;]a>0<->z>0" in {
    shouldMatch(
      "[x_:=y;]x_>0<->y>0".asPlainFormula,
      "[a:=z;]a>0<->z>0".asPlainFormula,
      Subst((Variable("x_"), Variable("a")) :: (Variable("y"), Variable("z")) :: Nil),
    )
  }

  it should "unify [x_:=y;]y>0<->y>0 with [a:=z;]z>0<->z>0" in {
    shouldMatch(
      "[x_:=y;]y>0<->y>0".asPlainFormula,
      "[a:=z;]z>0<->z>0".asPlainFormula,
      Subst((Variable("x_"), Variable("a")) :: (Variable("y"), Variable("z")) :: Nil),
    )
  }

  // @todo really? needs cyclic decluttering to say the least
  it should "unify [x_:=y;]y_0>0<->y_0>0 with [y_0:=z;]y_0>0<->z>0" ignore {
    shouldMatch(
      "[x_:=y;]y_0>0<->y_0>0".asPlainFormula,
      "[y_0:=z;]y_0>0<->z>0".asPlainFormula,
      Subst((Variable("x_"), Variable("y", Some(0))) :: Nil),
    )
  }

  it should "unify j()=x+y with s()=s()" ignore {
    // @note unifiable but not by mere matching, needs a proper unifier instead of a single sided matcher
    shouldUnify(
      "s()=s()".asPlainFormula,
      "j()=x+y".asPlainFormula,
      USubst(
        SubstitutionPair("s()".asPlainTerm, "x+y".asPlainTerm) ::
          SubstitutionPair("j()".asPlainTerm, "x+y".asPlainTerm) :: Nil
      ),
    )
  }

  it should "unify x+y=j() with s()=s()" ignore {
    // @note unification but not matching
    shouldUnify(
      "s()=s()".asPlainFormula,
      "x+y=j()".asPlainFormula,
      USubst(
        SubstitutionPair("s()".asPlainTerm, "x+y".asPlainTerm) ::
          SubstitutionPair("j()".asPlainTerm, "x+y".asPlainTerm) :: Nil
      ),
    )
  }

  // @todo single pass does not pick up x_ correctly for predicates before x_=f
  it should "unify q_(x_) & x_=f(x_) -> p_(x_) with complicated formula" ignore {
    shouldMatch(
      "q_(x_) & x_=f(x_) -> p_(x_)".asPlainFormula,
      "((v>=0&x+v^2/(2*B)>=S)&v=0*(kyxtime-kyxtime_0)+v_0)&x=v_0*(kyxtime-kyxtime_0)+x_0->v>=0&x+v^2/(2*B)<=S"
        .asPlainFormula,
      Subst(
        ("q_(.)".asPlainFormula, "(v>=0&.+v^2/(2*B)>=S)&v=0*(kyxtime-kyxtime_0)+v_0".asPlainFormula) ::
          ("f(.)".asPlainTerm, "v_0*(kyxtime-kyxtime_0)+x_0".asPlainTerm) ::
          ("p_(.)".asPlainFormula, "v>=0&.+v^2/(2*B)<=S".asPlainFormula) :: ("x_".asVariable, "x".asVariable) :: Nil
      ),
    )
  }

  it should "unify x_=f(x_) & q_(x_) -> p_(x_) with complicated formula" in {
    shouldMatch(
      "x_=f(x_) & q_(x_) -> p_(x_)".asPlainFormula,
      "x=v_0*(kyxtime-kyxtime_0)+x_0&((v>=0&x+v^2/(2*B)>=S)&v=0*(kyxtime-kyxtime_0)+v_0)->v>=0&x+v^2/(2*B)<=S"
        .asPlainFormula,
      Subst(
        ("f(._0)".asPlainTerm, "v_0*(kyxtime-kyxtime_0)+x_0".asPlainTerm) ::
          ("q_(._0)".asPlainFormula, "(v>=0&._0+v^2/(2*B)>=S)&v=0*(kyxtime-kyxtime_0)+v_0".asPlainFormula) ::
          ("p_(._0)".asPlainFormula, "v>=0&._0+v^2/(2*B)<=S".asPlainFormula) :: ("x_".asVariable, "x".asVariable) :: Nil
      ),
    )
  }

  "Dassignb unification" should "unify [u':=f();]p(u') with [u':=b();]u'>=0" in {
    shouldMatch(
      "[u':=f();]p(u')".asPlainFormula,
      "[u':=b();]u'>=0".asPlainFormula,
      Subst(
        (FuncOf(Function("f", None, Unit, Real), Nothing), FuncOf(Function("b", None, Unit, Real), Nothing)) ::
          (
            PredOf(Function("p", None, Real, Bool), DotTerm(Real, Some(0))),
            GreaterEqual(DotTerm(Real, Some(0)), Number(0)),
          ) :: Nil
      ),
    )
  }

  it should "unify [x':=f();]p(x') with [u':=b();]u'>=0" in {
    shouldMatch(
      "[x':=f();]p(x')".asPlainFormula,
      "[u':=b();]u'>=0".asPlainFormula,
      Subst(
        (Variable("x"), Variable("u")) ::
          (FuncOf(Function("f", None, Unit, Real), Nothing), FuncOf(Function("b", None, Unit, Real), Nothing)) ::
          (
            PredOf(Function("p", None, Real, Bool), DotTerm(Real, Some(0))),
            GreaterEqual(DotTerm(Real, Some(0)), Number(0)),
          ) :: Nil
      ),
    )
  }

  "More unification" should "unify y>0 -> [x:=2;]y>0 with p() -> [a;]p()" in {
    shouldMatch(
      "p() -> [a;]p()".asPlainFormula,
      "y>0 -> [x:=2;]y>0".asPlainFormula,
      Subst(
        (PredOf(Function("p", None, Unit, Bool), Nothing), "y>0".asPlainFormula) ::
          (ProgramConst("a"), Assign(Variable("x"), Number(2))) :: Nil
      ),
    )
  }

  it should "unify [x:=2;]y>0 -> y>0 with [a;]p() -> p()" in {
    // not an axiom, just to test both directions
    shouldMatch(
      "[a;]p() -> p()".asPlainFormula,
      "[x:=2;]y>0 -> y>0".asPlainFormula,
      Subst(
        (ProgramConst("a"), Assign(Variable("x"), Number(2))) ::
          (PredOf(Function("p", None, Unit, Bool), Nothing), "y>0".asPlainFormula) :: Nil
      ),
    )
  }

  it should "unify renaming and instance [y:=y;]p(||) and [y_0:=y_0;](y_0>77&true)" in {
    shouldMatch(
      "[y:=y;]p(||)".asPlainFormula,
      "[y_0:=y_0;](y_0>77&true)".asPlainFormula,
      Subst(
        (Variable("y"), Variable("y", Some(0))) ::
          (UnitPredicational("p", AnyArg), (if (semanticRenaming) "(y_0>77&true)" else "(y>77&true)").asPlainFormula) ::
          Nil
      ),
    )
  }

  it should "unify renaming and instance [y:=y;]p(||)<->p(||) and [y_0:=y_0;](true)<->(true)" in {
    shouldMatch(
      "[y:=y;]p(||)<->p(||)".asPlainFormula,
      "[y_0:=y_0;](true)<->(true)".asPlainFormula,
      Subst((Variable("y"), Variable("y", Some(0))) :: (UnitPredicational("p", AnyArg), "(true)".asPlainFormula) :: Nil),
    )
  }

  it should "unify renaming x=0 and y_0=0" in {
    shouldMatch("x=0".asPlainFormula, "y_0=0".asPlainFormula, Subst((Variable("x"), Variable("y", Some(0))) :: Nil))
  }

  it should "unify renaming x=0<->x=0 and y_0=0<->y_0=0" in {
    shouldMatch(
      "x=0<->x=0".asPlainFormula,
      "y_0=0<->y_0=0".asPlainFormula,
      Subst((Variable("x"), Variable("y", Some(0))) :: Nil),
    )
  }

  it should "unify renaming x=0&x=0<->x=0 and y_0=0&y_0=0<->y_0=0" in {
    shouldMatch(
      "x=0&x=0<->x=0".asPlainFormula,
      "y_0=0&y_0=0<->y_0=0".asPlainFormula,
      Subst((Variable("x"), Variable("y", Some(0))) :: Nil),
    )
  }

  it should "unify renaming x=0<->x=0&x=0 and y_0=0<->y_0=0&y_0=0" in {
    shouldMatch(
      "x=0<->x=0&x=0".asPlainFormula,
      "y_0=0<->y_0=0&y_0=0".asPlainFormula,
      Subst((Variable("x"), Variable("y", Some(0))) :: Nil),
    )
  }

  it should "unify renaming x>1&x=2<->x<3 and y_0>1&y_0=2<->y_0<3" in {
    shouldMatch(
      "x>1&x=2<->x<3".asPlainFormula,
      "y_0>1&y_0=2<->y_0<3".asPlainFormula,
      Subst((Variable("x"), Variable("y", Some(0))) :: Nil),
    )
  }

  it should "unify renaming x>1<->x=2&x<3 and y_0>1<->y_0=2&y_0<3" in {
    shouldMatch(
      "x>1<->x=2&x<3".asPlainFormula,
      "y_0>1<->y_0=2&y_0<3".asPlainFormula,
      Subst((Variable("x"), Variable("y", Some(0))) :: Nil),
    )
  }

  it should "unify renaming and instance [y:=y;]y>5<->y>5 and [y_0:=y_0;]y_0>5<->y_0>5" in {
    shouldMatch(
      "[y:=y;]y>5<->y>5".asPlainFormula,
      "[y_0:=y_0;]y_0>5<->y_0>5".asPlainFormula,
      Subst((Variable("y"), Variable("y", Some(0))) :: Nil),
    )
  }

  it should "unify renaming and instance p(||)<->[y:=y;]p(||) and (y_0=1)<->[y_0:=y_0;](y_0=1)" ignore {
    shouldMatch(
      "p(||)<->[y:=y;]p(||)".asPlainFormula,
      "(y_0=1)<->[y_0:=y_0;](y_0=1)".asPlainFormula,
      Subst(
        (Variable("y"), Variable("y", Some(0))) ::
          (UnitPredicational("p", AnyArg), (if (semanticRenaming) "(y_0=1)" else "y=1").asPlainFormula) :: Nil
      ),
    )
  }

  it should "unify renaming and instance [y:=y;]p(||)<->p(||) and [y_0:=y_0;](y_0=0)<->(y_0=0)" in {
    shouldMatch(
      "[y:=y;]p(||)<->p(||)".asPlainFormula,
      "[y_0:=y_0;](y_0=0)<->(y_0=0)".asPlainFormula,
      Subst(
        (Variable("y"), Variable("y", Some(0))) ::
          (UnitPredicational("p", AnyArg), (if (semanticRenaming) "(y_0=0)" else "y=0").asPlainFormula) :: Nil
      ),
    )
  }

  it should "unify renaming and instance p(||)<->[y:=y;]p(||) and (true)<->[y_0:=y_0;](true)" in {
    shouldMatch(
      "p(||)<->[y:=y;]p(||)".asPlainFormula,
      "(true)<->[y_0:=y_0;](true)".asPlainFormula,
      Subst((Variable("y"), Variable("y", Some(0))) :: (UnitPredicational("p", AnyArg), "(true)".asPlainFormula) :: Nil),
    )
  }

  it should "unify renaming and instance p(||)<->[y:=y;]p(||) and (y_0>77&true)<->[y_0:=y_0;](y_0>77&true)" ignore {
    shouldMatch(
      "p(||)<->[y:=y;]p(||)".asPlainFormula,
      "(y_0>77&true)<->[y_0:=y_0;](y_0>77&true)".asPlainFormula,
      Subst(
        (Variable("y"), Variable("y", Some(0))) ::
          (UnitPredicational("p", AnyArg), (if (semanticRenaming) "(y_0>77&true)" else "y>77&true").asPlainFormula) ::
          Nil
      ),
    )
  }

  it should "unify renaming and instance [y:=y;]p(||)<->p(||) and [y_0:=y_0;](y_0>77&true)<->(y_0>77&true)" in {
    shouldMatch(
      "[y:=y;]p(||)<->p(||)".asPlainFormula,
      "[y_0:=y_0;](y_0>77&true)<->(y_0>77&true)".asPlainFormula,
      Subst(
        (Variable("y"), Variable("y", Some(0))) ::
          (UnitPredicational("p", AnyArg), (if (semanticRenaming) "(y_0>77&true)" else "y>77&true").asPlainFormula) ::
          Nil
      ),
    )
  }

  it should "unify renaming and long instance" in {
    shouldMatch(
      "[x_:=x_;]p(||)<->p(||)".asPlainFormula,
      "[x_0:=x_0;](((x_0>0&true)&true)&true->(2>=0|false)|false)<->((x_0>0&true)&true)&true->(2>=0|false)|false"
        .asPlainFormula,
      Subst(
        (Variable("x_"), Variable("x", Some(0))) ::
          (
            UnitPredicational("p", AnyArg),
            (if (semanticRenaming) "(((x_0>0&true)&true)&true->(2>=0|false)|false)"
             else "(((x_>0&true)&true)&true->(2>=0|false)|false)").asPlainFormula,
          ) :: Nil
      ),
    )
  }

  it should "match abstract loop against loopy single ODE" in {
    shouldMatch(
      "[{a;}*]p(||)".asPlainFormula,
      "[{{x'=v}}*](v>=0&true)".asPlainFormula,
      Subst(
        (ProgramConst("a"), "{x'=v}".asPlainProgram) :: (UnitPredicational("p", AnyArg), "v>=0&true".asPlainFormula) ::
          Nil
      ),
    )
  }

  it should "match abstract loop against loopy ODE system " in {
    shouldMatch(
      "[{a;}*]p(||)".asPlainFormula,
      "[{{x'=v,v'=A}}*](v>=0&true)".asPlainFormula,
      Subst(
        (ProgramConst("a"), "{x'=v,v'=A}".asPlainProgram) ::
          (UnitPredicational("p", AnyArg), "v>=0&true".asPlainFormula) :: Nil
      ),
    )
  }

  it should "match abstract loop against loopy ODE system with domain" in {
    shouldMatch(
      "[{a;}*]p(||)".asPlainFormula,
      "[{{x'=v,v'=A&v<=5}}*](v>=0&true)".asPlainFormula,
      Subst(
        (ProgramConst("a"), "{x'=v,v'=A&v<=5}".asPlainProgram) ::
          (UnitPredicational("p", AnyArg), "v>=0&true".asPlainFormula) :: Nil
      ),
    )
  }

  it should "match abstract loop against loopy initialized ODE" in {
    shouldMatch(
      "[{a;}*]p(||)".asPlainFormula,
      "[{v:=5;{x'=v,v'=A}}*](v>=0&true)".asPlainFormula,
      Subst(
        (ProgramConst("a"), "v:=5;{x'=v,v'=A}".asPlainProgram) ::
          (UnitPredicational("p", AnyArg), "v>=0&true".asPlainFormula) :: Nil
      ),
    )
  }

  it should "match derived powers" in {
    shouldMatch(
      "(f(||)^(c()))'".asPlainTerm,
      "(x^2)'".asPlainTerm,
      Subst(
        (UnitFunctional("f", AnyArg, Real), "x".asPlainTerm) ::
          (FuncOf(Function("c", None, Unit, Real), Nothing), "2".asPlainTerm) :: Nil
      ),
    )
  }

  it should "say something about broken types" ignore {
    // @todo in principle this should throw a CoreException about incompatible types, actually. Not parse print and incompatible substitution sorts. Both are true but not the first issue.
    a[ProverException] shouldBe thrownBy(Subst(
      (UnitFunctional("f", AnyArg, Real), "x".asPlainTerm) ::
        (FuncOf(Function("c", None, Unit, Bool), Nothing), "2".asPlainTerm) :: Nil
    ))
  }

  it should "unify DC axiom" in {
    shouldMatch(
      "([{c&q(||)}]p(||) <-> [{c&(q(||)&r(||))}]p(||)) <- [{c&q(||)}]r(||)".asPlainFormula,
      "([{x'=v&v>=0&v>0}]x>=0 <-> [{x'=v&(v>=0&v>0)&x>0}]x>=0) <- [{x'=v&v>=0&v>0}]x>0".asPlainFormula,
      Subst(
        (DifferentialProgramConst("c"), "{x'=v}".asPlainDifferentialProgram) ::
          (UnitPredicational("p", AnyArg), "x>=0".asPlainFormula) ::
          (UnitPredicational("q", AnyArg), "v>=0&v>0".asPlainFormula) ::
          (UnitPredicational("r", AnyArg), "x>0".asPlainFormula) :: Nil
      ),
    )
  }

  it should "unify DC axiom without evolution domain" in {
    shouldMatch(
      "([{c&q(||)}]p(||) <-> [{c&(q(||)&r(||))}]p(||)) <- [{c&q(||)}]r(||)".asPlainFormula,
      "([{x'=v}]x>=0 <-> [{x'=v&true&x>0}]x>=0) <- [{x'=v}]x>0".asPlainFormula,
      Subst(
        (DifferentialProgramConst("c"), "{x'=v}".asPlainDifferentialProgram) ::
          (UnitPredicational("p", AnyArg), "x>=0".asPlainFormula) ::
          (UnitPredicational("q", AnyArg), "true".asPlainFormula) ::
          (UnitPredicational("r", AnyArg), "x>0".asPlainFormula) :: Nil
      ),
    )
  }

  // @todo this test case would need the expensive reunify to be activated in UnificationMatch again
  "Reunifier ideally" should "unify p(f()) <-> [x:=f();]p(x) with (7+x)^2>=5 <-> [x:=7+x;]x^2>=5" taggedAs
    OptimisticTest ignore {
      shouldMatch(
        "p(f()) <-> [x:=f();]p(x)".asPlainFormula,
        "(7+x)^2>=5 <-> [x:=7+x;]x^2>=5".asPlainFormula,
        Subst(
          ("f()".asPlainTerm, "7+x".asPlainTerm) ::
            (
              PredOf(Function("p", None, Real, Bool), DotTerm(Real, Some(0))),
              GreaterEqual(Power(DotTerm(Real, Some(0)), "2".asPlainTerm), "5".asPlainTerm),
            ) :: Nil
        ),
      )
    }

  "colored dots unification" should "unify 3+f(x,y) with 3+(x^2+y)" in {
    shouldUnify(
      "3+f(x,y)".asPlainTerm,
      "3+(x^2+y)".asPlainTerm,
      USubst(SubstitutionPair("f((•_0,•_1))".asPlainTerm, "•_0^2+•_1".asPlainTerm) :: Nil),
    )
  }

  it should "unify 3+f(x,y,z) with 3+(x^y+z)" in {
    shouldUnify(
      "3+f(x,y,z)".asPlainTerm,
      "3+(x^y+z)".asPlainTerm,
      USubst(SubstitutionPair("f((•_0,•_1,•_2))".asPlainTerm, "•_0^•_1+•_2".asPlainTerm) :: Nil),
    )
  }

  it should "unify renaming and instance p(x,y) and x*y>5" in {
    shouldMatch(
      "p(x,y)".asPlainFormula,
      "x*y>5".asPlainFormula,
      Subst(("p((•_0,•_1))".asPlainFormula, "•_0*•_1>5".asPlainFormula) :: Nil),
    )
  }

  it should "unify renaming and instance p(x,y,z) and x*y>z" in {
    shouldMatch(
      "p(x,y,z)".asPlainFormula,
      "x*y>z".asPlainFormula,
      Subst(("p((•_0,•_1,•_2))".asPlainFormula, "•_0*•_1>•_2".asPlainFormula) :: Nil),
    )
  }

  it should "unify renaming and instance f(x,y,x*y)" in {
    shouldMatch(
      "f(x,y,x*y) = f(a, b, c)".asPlainFormula,
      "x*y = a*b".asPlainFormula,
      Subst(("f((•_0,•_1,•_2))".asPlainTerm, "•_0*•_1".asPlainTerm) :: Nil),
    )
    shouldMatch(
      "f(x,y,x*y) = f(a, b, c)".asPlainFormula,
      "x*y = c".asPlainFormula,
      Subst(("f((•_0,•_1,•_2))".asPlainTerm, "•_2".asPlainTerm) :: Nil),
    )
  }
}
