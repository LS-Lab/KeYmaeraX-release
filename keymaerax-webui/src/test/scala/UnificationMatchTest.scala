/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.tags.{UsualTest, SummaryTest}
import edu.cmu.cs.ls.keymaerax.tools.KeYmaera
import testHelper.KeYmaeraXTestTags.OptimisticTest
import scala.collection.immutable._
import org.scalatest.{Matchers, FlatSpec}


/**
 * Created by aplatzer on 7/28/15.
  *
  * @author Andre Platzer
 */
@SummaryTest
@UsualTest
class UnificationMatchTest extends FlatSpec with Matchers {
  KeYmaera.init(Map.empty)

  private def should(e1: Expression, e2: Expression, us: Option[USubst]): Unit = {
    if (us.isDefined) {
      println("Expression: " + e1)
      println("Expression: " + e2)
      val s = UnificationMatch(e1, e2)
      println("Unified:  " + s)
      println("Expected: " + us.get)
      s shouldBe (/*us.get,*/ RenUSubst(us.get))
    } else {
      println("Expression: " + e1)
      println("Expression: " + e2)
      println("Expected: " + "<ununifiable>")
      a [UnificationException] should be thrownBy UnificationMatch(e1, e2)
    }
  }

  private def shouldUnify(e1: Expression, e2: Expression, us: USubst): Unit = should(e1,e2,Some(us))

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

  it should "unify 3+f(x) with 3+(x^2+y)" in {
    shouldUnify("3+f(x)".asTerm, "3+(x^2+y)".asTerm, USubst(
      SubstitutionPair("f(.)".asTerm, "(.)^2+y".asTerm) :: Nil))
  }

  it should "unify 3+f(x,y) with 3+(x^2+y)" in {
    //val dot = DotTerm(Tuple(Real, Real))
    shouldUnify("3+f(x,y)".asTerm,
      "3+(x^2+y)".asTerm, USubst(
        SubstitutionPair(
          //FuncOf(Function("f", None, Tuple(Real, Real), Real), dot),
          "f(.(.,.))".asTerm,
          //Plus(Power(Projection(dot, 0::Nil), Number(2)), Projection(dot, 1::Nil))
          "π(.(.,.),1,0)^2+π(.(.,.),1,1)".asTerm) :: Nil
      ))
  }

  it should "unify 3+f(x,y,z) with 3+(x^2+y)" in {
    shouldUnify("3+f(x,y,z)".asTerm,
      "3+(x^y+z)".asTerm, USubst(
        SubstitutionPair(
          "f(.(.,.,.))".asTerm,
          "π(.(.,.,.),1,0)^π(.(.,.,.),2,2)+π(.(.,.,.),2,3)".asTerm
        ) :: Nil
      ))
  }

  "Unification formulas" should "unify p() with x^2+y>=0" in {
    shouldUnify("p()".asFormula, "x^2+y>=0".asFormula, USubst(
      SubstitutionPair("p()".asFormula, "x^2+y>=0".asFormula) :: Nil))
  }

  it should "unify \\forall x p(x) with \\forall x (!q(x)) " in {
    shouldUnify("\\forall x p(x)".asFormula, "\\forall x (!q(x))".asFormula, USubst(
      SubstitutionPair("p(.)".asFormula, "!q(.)".asFormula) :: Nil))
  }

  it should "match \\forall x p(x) with \\forall x (!p(x)) " in {
    shouldUnify("\\forall x p(x)".asFormula, "\\forall x (!p(x))".asFormula, USubst(
      SubstitutionPair("p(.)".asFormula, "!p(.)".asFormula) :: Nil))
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
    UnificationMatch(s1, s2) shouldBe RenUSubst(new USubst(
      SubstitutionPair(PredOf(Function("p", None, Real, Bool), DotTerm), Greater(DotTerm, "0".asTerm)) ::
        SubstitutionPair(Variable("x"), Variable("y")) ::
        SubstitutionPair("t()".asTerm, Variable("z")) :: Nil))
  }

  //@todo split this test case

  // new unification matchers from now on
  import edu.cmu.cs.ls.keymaerax.bellerophon.{RenUSubst, UnificationMatch}

  private def shouldMatch(e1: Expression, e2: Expression, us: Option[RenUSubst]): Unit = {
    if (us.isDefined) {
      println("Expression1: " + e1)
      println("Expression2: " + e2)
      val s = UnificationMatch(e1, e2)
      println("Unified:     " + s)
      println("Expected:    " + us.get + "\t" + (if (s==us.get) "identical" else "different"))
      print("Expectation unifies?")
      // check expectation whether it even unifies
      us.get(e1) shouldBe (e2)
      println("!")
      println("hence1:      " + s(e1))
      println("Expression2: " + e2)
      s(e1) shouldBe (e2)
      s shouldBe (us.get)
    } else {
      println("Expression: " + e1)
      println("Expression: " + e2)
      println("Expected: " + "<ununifiable>")
      a [UnificationException] should be thrownBy UnificationMatch(e1, e2)
    }
  }

  private def shouldMatch(e1: Expression, e2: Expression, us: RenUSubst): Unit = shouldMatch(e1, e2, Some(us))

  private val semanticRenaming = UnificationMatch("quark(||)".asFormula, "quarks=6".asFormula).isInstanceOf[URenAboveUSubst]


  "New unification match" should "unify renaming and instance 3*f(x)>2 and 5*x>2" in {
    shouldMatch("3*f(x)>2".asFormula,
      "3*(5*x)>2".asFormula, RenUSubst(
        (FuncOf(Function("f", None, Real, Real), DotTerm), Times(Number(5), DotTerm)) :: Nil
      ))
  }

  it should "unify renaming and instance p(x) and x>5" in {
    shouldMatch("p(x)".asFormula,
      "x>5".asFormula, RenUSubst(
        (PredOf(Function("p", None, Real, Bool), DotTerm), Greater(DotTerm, Number(5))) :: Nil
      ))
  }

  it should "unify renaming and instance p(x,y) and x*y>5" in {
    shouldMatch("p(x,y)".asFormula,
      "x*y>5".asFormula, RenUSubst(
        ("p(.(.,.))".asFormula,
         "π(.(.,.),1,0)*π(.(.,.),1,1)>5".asFormula) :: Nil
      ))
  }

  it should "unify renaming and instance p(x,y,z) and x*y>z" in {
    shouldMatch("p(x,y,z)".asFormula,
      "x*y>z".asFormula, RenUSubst(
        ("p(.(.,.,.))".asFormula,
         "π(.(.,.,.),1,0)*π(.(.,.,.),2,2)>π(.(.,.,.),2,3)".asFormula) :: Nil
      ))
  }


  it should "unify (\\forall x p(x)) -> p(t()) with (\\forall y y>0) -> z>0 (failed setup)" in {
    val s1 = Sequent(IndexedSeq(), IndexedSeq("\\forall x p(x) -> p(t())".asFormula))
    val s2 = Sequent(IndexedSeq(), IndexedSeq("\\forall y y>0 -> z>0".asFormula))
    import edu.cmu.cs.ls.keymaerax.btactics._
    //@todo not sure about the expected exception
    a[ProverException] shouldBe thrownBy(
    UnificationMatch(s1, s2) shouldBe RenUSubst(new USubst(
      SubstitutionPair(PredOf(Function("p", None, Real, Bool), DotTerm), Greater(DotTerm, "0".asTerm)) ::
        SubstitutionPair(Variable("x"), Variable("y")) ::
        SubstitutionPair("t()".asTerm, Variable("z")) :: Nil))
    )
  }

  it should "unify (\\forall x p(x)) -> p(t()) with (\\forall y y>0) -> z>0" in {
    val s1 = Sequent(IndexedSeq(), IndexedSeq("\\forall x p(x) -> p(t())".asFormula))
    val s2 = Sequent(IndexedSeq(), IndexedSeq("\\forall y y>0 -> z>0".asFormula))
    println("Unify " + s1 + "\nwith  " + s2 + "\nyields " + UnificationMatch(s1, s2))
    //@todo not sure about the expected result
    UnificationMatch(s1, s2) shouldBe RenUSubst(
      (PredOf(Function("p", None, Real, Bool), DotTerm), Greater(DotTerm, "0".asTerm)) ::
        (Variable("x"), Variable("y")) ::
        ("t()".asTerm, Variable("z")) :: Nil)
  }

  it should "unify [x:=f();]p(x) with [x:=7+x;]x^2>=5" in {
    shouldMatch("[x:=f();]p(x)".asFormula, "[x:=7+x;]x^2>=5".asFormula, RenUSubst(
        ("f()".asTerm, "7+x".asTerm) ::
          (PredOf(Function("p", None, Real, Bool), DotTerm), GreaterEqual(Power(DotTerm, "2".asTerm), "5".asTerm)) :: Nil))
  }

  it should "unify [x:=f();]p(x) <-> p(f()) with [x:=7+x;]x^2>=5 <-> (7+x)^2>=5" in {
    shouldMatch("[x:=f();]p(x) <-> p(f())".asFormula, "[x:=7+x;]x^2>=5 <-> (7+x)^2>=5".asFormula, RenUSubst(
      ("f()".asTerm, "7+x".asTerm) ::
        (PredOf(Function("p", None, Real, Bool), DotTerm), GreaterEqual(Power(DotTerm, "2".asTerm), "5".asTerm)) :: Nil))
  }

  it should "unify [x:=f();]p(x) with [y:=7+z;]y^2>=5" in {
    shouldMatch("[x:=f();]p(x)".asFormula, "[y:=7+z;]y^2>=5".asFormula, RenUSubst(
      (Variable("x"), Variable("y")) ::
      ("f()".asTerm, "7+z".asTerm) ::
        (PredOf(Function("p", None, Real, Bool), DotTerm), GreaterEqual(Power(DotTerm, "2".asTerm), "5".asTerm)) :: Nil))
  }

  it should "unify [y:=f();]p(y) <-> p(f()) with [y:=7+z;]y^2>=5 <-> (7+z)^2>=5" in {
    shouldMatch("[y:=f();]p(y) <-> p(f())".asFormula, "[y:=7+z;]y^2>=5 <-> (7+z)^2>=5".asFormula, RenUSubst(
      (("f()".asTerm, "7+z".asTerm) ::
        (PredOf(Function("p", None, Real, Bool), DotTerm), GreaterEqual(Power(DotTerm, "2".asTerm), "5".asTerm)) :: Nil)))
  }

  it should "unify [x_:=f();]p(x_) <-> p(f()) with [y:=7+z;]y^2>=5 <-> (7+z)^2>=5" in {
    shouldMatch("[x_:=f();]p(x_) <-> p(f())".asFormula, "[y:=7+z;]y^2>=5 <-> (7+z)^2>=5".asFormula, RenUSubst(
      (Variable("x_"), Variable("y")) ::
        ("f()".asTerm, "7+z".asTerm) ::
        (PredOf(Function("p", None, Real, Bool), DotTerm), GreaterEqual(Power(DotTerm, "2".asTerm), "5".asTerm)) :: Nil))
  }

  it should "unify [x:=f();]p(x) <-> p(f()) with [y:=7+z;]y^2>=5 <-> (7+z)^2>=5" in {
    shouldMatch("[x:=f();]p(x) <-> p(f())".asFormula, "[y:=7+z;]y^2>=5 <-> (7+z)^2>=5".asFormula, RenUSubst(
      (Variable("x"), Variable("y")) ::
        ("f()".asTerm, "7+z".asTerm) ::
        (PredOf(Function("p", None, Real, Bool), DotTerm), GreaterEqual(Power(DotTerm, "2".asTerm), "5".asTerm)) :: Nil))
  }

  it should "unify [x_:=y;]p(x_) with [y_0:=y;]y_0>2" in {
    shouldMatch("[x_:=y;]p(x_)".asFormula, "[y_0:=y;]y_0>2".asFormula, RenUSubst(
      (Variable("x_"), Variable("y",Some(0))) ::
        (PredOf(Function("p", None, Real, Bool), DotTerm), Greater(DotTerm, "2".asTerm)) :: Nil))
  }

  it should "unify [x_:=f();]p(x_) with [y_0:=y;]y_0>2" in {
    shouldMatch("[x_:=f();]p(x_)".asFormula, "[y_0:=y;]y_0>2".asFormula, RenUSubst(
      (Variable("x_"), Variable("y",Some(0))) ::
        ("f()".asTerm, "y".asTerm) ::
        (PredOf(Function("p", None, Real, Bool), DotTerm), Greater(DotTerm, "2".asTerm)) :: Nil))
  }

//  it should "unify [x_:=y;]y_0>0<->y_0>0 with [y_0:=y;]y_0>0<->y>0" in {
//    shouldMatch("[x_:=y;]y_0>0<->y_0>0".asFormula, "[y_0:=y;]y_0>0<->y>0".asFormula, RenUSubst(
//      (Variable("x_"), Variable("y",Some(0))) :: Nil))
//  }

  it should "unify [x_:=y;]y_0>0<->y_0>0 with [a:=z;]y_0>0<->y_0>0" in {
    shouldMatch("[x_:=y;]y_0>0<->y_0>0".asFormula, "[a:=z;]y_0>0<->y_0>0".asFormula, RenUSubst(
      (Variable("x_"), Variable("a")) :: (Variable("y"), Variable("z")) :: Nil))
  }

  it should "unify [x_:=y;]x_>0<->y>0 with [a:=z;]a>0<->z>0" in {
    shouldMatch("[x_:=y;]x_>0<->y>0".asFormula, "[a:=z;]a>0<->z>0".asFormula, RenUSubst(
      (Variable("x_"), Variable("a")) :: (Variable("y"), Variable("z")) :: Nil))
  }

  it should "unify [x_:=y;]y>0<->y>0 with [a:=z;]z>0<->z>0" in {
    shouldMatch("[x_:=y;]y>0<->y>0".asFormula, "[a:=z;]z>0<->z>0".asFormula, RenUSubst(
      (Variable("x_"), Variable("a")) :: (Variable("y"), Variable("z")) :: Nil))
  }

  //@todo really? needs cyclic decluttering to say the least
  it should "unify [x_:=y;]y_0>0<->y_0>0 with [y_0:=z;]y_0>0<->z>0" ignore {
    shouldMatch("[x_:=y;]y_0>0<->y_0>0".asFormula, "[y_0:=z;]y_0>0<->z>0".asFormula, RenUSubst(
      (Variable("x_"), Variable("y",Some(0))) :: Nil))
  }

  "Dassignb unification" should "unify [u':=f();]p(u') with [u':=b();]u'>=0" in {
    shouldMatch("[u':=f();]p(u')".asFormula, "[u':=b();]u'>=0".asFormula, RenUSubst(
      (FuncOf(Function("f",None,Unit,Real), Nothing), FuncOf(Function("b",None,Unit,Real),Nothing)) ::
        (PredOf(Function("p",None,Real,Bool),DotTerm), GreaterEqual(DotTerm,Number(0))) :: Nil))
  }

  it should "unify [x':=f();]p(x') with [u':=b();]u'>=0" in {
    shouldMatch("[x':=f();]p(x')".asFormula, "[u':=b();]u'>=0".asFormula, RenUSubst(
      (Variable("x"), Variable("u")) :: (FuncOf(Function("f",None,Unit,Real), Nothing), FuncOf(Function("b",None,Unit,Real),Nothing)) ::
        (PredOf(Function("p",None,Real,Bool),DotTerm), GreaterEqual(DotTerm,Number(0))) :: Nil))
  }


  "More unification" should "unify y>0 -> [x:=2;]y>0 with p() -> [a;]p()" in {
    shouldMatch("p() -> [a;]p()".asFormula, "y>0 -> [x:=2;]y>0".asFormula, RenUSubst(
      (PredOf(Function("p", None, Unit, Bool), Nothing), "y>0".asFormula) ::
        (ProgramConst("a"), Assign(Variable("x"), Number(2))) :: Nil))
  }

  it should "unify [x:=2;]y>0 -> y>0 with [a;]p() -> p()" in {
    // not an axiom, just to test both directions
    shouldMatch("[a;]p() -> p()".asFormula, "[x:=2;]y>0 -> y>0".asFormula, RenUSubst(
      (ProgramConst("a"), Assign(Variable("x"), Number(2))) ::
        (PredOf(Function("p", None, Unit, Bool), Nothing), "y>0".asFormula) :: Nil))
  }

  it should "unify renaming and instance [y:=y;]p(||) and [y_0:=y_0;](y_0>77&true)" in {
    shouldMatch("[y:=y;]p(||)".asFormula,
      "[y_0:=y_0;](y_0>77&true)".asFormula, RenUSubst(
      (Variable("y"), Variable("y",Some(0))) ::
        (UnitPredicational("p", AnyArg), (if (semanticRenaming) "(y_0>77&true)" else "(y>77&true)").asFormula) ::
        Nil
    ))
  }

  it should "unify renaming and instance [y:=y;]p(||)<->p(||) and [y_0:=y_0;](true)<->(true)" in {
    shouldMatch("[y:=y;]p(||)<->p(||)".asFormula,
      "[y_0:=y_0;](true)<->(true)".asFormula, RenUSubst(
      (Variable("y"), Variable("y",Some(0))) ::
        (UnitPredicational("p", AnyArg), "(true)".asFormula) ::
        Nil
    ))
  }

  it should "unify renaming x=0 and y_0=0" in {
    shouldMatch("x=0".asFormula,
      "y_0=0".asFormula, RenUSubst(
      (Variable("x"), Variable("y",Some(0))) :: Nil))
  }

  it should "unify renaming x=0<->x=0 and y_0=0<->y_0=0" in {
    shouldMatch("x=0<->x=0".asFormula,
      "y_0=0<->y_0=0".asFormula, RenUSubst(
      (Variable("x"), Variable("y",Some(0))) :: Nil))
  }

  it should "unify renaming x=0&x=0<->x=0 and y_0=0&y_0=0<->y_0=0" in {
    shouldMatch("x=0&x=0<->x=0".asFormula,
      "y_0=0&y_0=0<->y_0=0".asFormula, RenUSubst(
      (Variable("x"), Variable("y",Some(0))) :: Nil
    ))
  }

  it should "unify renaming x=0<->x=0&x=0 and y_0=0<->y_0=0&y_0=0" in {
    shouldMatch("x=0<->x=0&x=0".asFormula,
      "y_0=0<->y_0=0&y_0=0".asFormula, RenUSubst(
      (Variable("x"), Variable("y",Some(0))) :: Nil
    ))
  }

  it should "unify renaming x>1&x=2<->x<3 and y_0>1&y_0=2<->y_0<3" in {
    shouldMatch("x>1&x=2<->x<3".asFormula,
      "y_0>1&y_0=2<->y_0<3".asFormula, RenUSubst(
      (Variable("x"), Variable("y",Some(0))) :: Nil
    ))
  }

  it should "unify renaming x>1<->x=2&x<3 and y_0>1<->y_0=2&y_0<3" in {
    shouldMatch("x>1<->x=2&x<3".asFormula,
      "y_0>1<->y_0=2&y_0<3".asFormula, RenUSubst(
      (Variable("x"), Variable("y",Some(0))) :: Nil
    ))
  }

  it should "unify renaming and instance [y:=y;]y>5<->y>5 and [y_0:=y_0;]y_0>5<->y_0>5" in {
    shouldMatch("[y:=y;]y>5<->y>5".asFormula,
      "[y_0:=y_0;]y_0>5<->y_0>5".asFormula, RenUSubst(
      (Variable("y"), Variable("y",Some(0))) :: Nil
    ))
  }

  it should "unify renaming and instance p(||)<->[y:=y;]p(||) and (y_0=1)<->[y_0:=y_0;](y_0=1)" ignore {
    shouldMatch("p(||)<->[y:=y;]p(||)".asFormula,
      "(y_0=1)<->[y_0:=y_0;](y_0=1)".asFormula, RenUSubst(
      (Variable("y"), Variable("y",Some(0))) ::
        (UnitPredicational("p", AnyArg), (if (semanticRenaming) "(y_0=1)" else "y=1").asFormula) ::
        Nil
    ))
  }

  it should "unify renaming and instance [y:=y;]p(||)<->p(||) and [y_0:=y_0;](y_0=0)<->(y_0=0)" in {
    shouldMatch("[y:=y;]p(||)<->p(||)".asFormula,
      "[y_0:=y_0;](y_0=0)<->(y_0=0)".asFormula, RenUSubst(
      (Variable("y"), Variable("y",Some(0))) ::
        (UnitPredicational("p", AnyArg), (if (semanticRenaming) "(y_0=0)" else "y=0").asFormula) ::
        Nil
    ))
  }

  it should "unify renaming and instance p(||)<->[y:=y;]p(||) and (true)<->[y_0:=y_0;](true)" in {
    shouldMatch("p(||)<->[y:=y;]p(||)".asFormula,
      "(true)<->[y_0:=y_0;](true)".asFormula, RenUSubst(
      (Variable("y"), Variable("y",Some(0))) ::
        (UnitPredicational("p", AnyArg), "(true)".asFormula) ::
        Nil
    ))
  }

  it should "unify renaming and instance p(||)<->[y:=y;]p(||) and (y_0>77&true)<->[y_0:=y_0;](y_0>77&true)" ignore {
    shouldMatch("p(||)<->[y:=y;]p(||)".asFormula,
      "(y_0>77&true)<->[y_0:=y_0;](y_0>77&true)".asFormula, RenUSubst(
      (Variable("y"), Variable("y",Some(0))) ::
        (UnitPredicational("p", AnyArg), (if (semanticRenaming) "(y_0>77&true)" else "y>77&true").asFormula) ::
        Nil
    ))
  }

  it should "unify renaming and instance [y:=y;]p(||)<->p(||) and [y_0:=y_0;](y_0>77&true)<->(y_0>77&true)" in {
    shouldMatch("[y:=y;]p(||)<->p(||)".asFormula,
      "[y_0:=y_0;](y_0>77&true)<->(y_0>77&true)".asFormula, RenUSubst(
      (Variable("y"), Variable("y",Some(0))) ::
        (UnitPredicational("p", AnyArg), (if (semanticRenaming) "(y_0>77&true)" else "y>77&true").asFormula) ::
        Nil
    ))
  }

  it should "unify renaming and long instance" in {
    shouldMatch("[x_:=x_;]p(||)<->p(||)".asFormula,
      "[x_0:=x_0;](((x_0>0&true)&true)&true->(2>=0|false)|false)<->((x_0>0&true)&true)&true->(2>=0|false)|false".asFormula, RenUSubst(
      (Variable("x_"), Variable("x",Some(0))) ::
        (UnitPredicational("p", AnyArg), (if (semanticRenaming) "(((x_0>0&true)&true)&true->(2>=0|false)|false)" else "(((x_>0&true)&true)&true->(2>=0|false)|false)").asFormula) ::
        Nil
    ))
  }

  it should "match abstract loop against loopy single ODE" in {
    shouldMatch("[{a;}*]p(||)".asFormula,
      "[{{x'=v}}*](v>=0&true)".asFormula, RenUSubst(
        (ProgramConst("a"), "{x'=v}".asProgram) ::
          (UnitPredicational("p", AnyArg), "v>=0&true".asFormula) ::Nil
      ))
  }

  it should "match abstract loop against loopy ODE system " in {
    shouldMatch("[{a;}*]p(||)".asFormula,
      "[{{x'=v,v'=A}}*](v>=0&true)".asFormula, RenUSubst(
      (ProgramConst("a"), "{x'=v,v'=A}".asProgram) ::
        (UnitPredicational("p", AnyArg), "v>=0&true".asFormula) ::Nil
    ))
  }

  it should "match abstract loop against loopy ODE system with domain" in {
    shouldMatch("[{a;}*]p(||)".asFormula,
      "[{{x'=v,v'=A&v<=5}}*](v>=0&true)".asFormula, RenUSubst(
        (ProgramConst("a"), "{x'=v,v'=A&v<=5}".asProgram) ::
          (UnitPredicational("p", AnyArg), "v>=0&true".asFormula) ::Nil
      ))
  }

  it should "match abstract loop against loopy initialized ODE" in {
    shouldMatch("[{a;}*]p(||)".asFormula,
      "[{v:=5;{x'=v,v'=A}}*](v>=0&true)".asFormula, RenUSubst(
        (ProgramConst("a"), "v:=5;{x'=v,v'=A}".asProgram) ::
          (UnitPredicational("p", AnyArg), "v>=0&true".asFormula) ::Nil
      ))
  }

  it should "match derived powers" in {
    shouldMatch("(f(||)^(c()))'".asTerm,
      "(x^2)'".asTerm, RenUSubst(
        (UnitFunctional("f", AnyArg, Real), "x".asTerm) ::
          (FuncOf(Function("c", None, Unit, Real), Nothing), "2".asTerm) :: Nil
      ))
  }

  it should "say something about broken types" ignore {
    //@todo in principle this should throw a CoreException about incompatible types, actually. Not parse print and incompatible substitution sorts. Both are true but not the first issue.
    a[ProverException] shouldBe thrownBy(
    RenUSubst(
          (UnitFunctional("f", AnyArg, Real), "x".asTerm) ::
          (FuncOf(Function("c", None, Unit, Bool), Nothing), "2".asTerm) :: Nil
      )
    )
  }

  //@todo this test case would need the expensive reunify to be activated in UnificationMatch again
  "Reunifier ideally" should "unify p(f()) <-> [x:=f();]p(x) with (7+x)^2>=5 <-> [x:=7+x;]x^2>=5" taggedAs OptimisticTest ignore {
    shouldMatch("p(f()) <-> [x:=f();]p(x)".asFormula, "(7+x)^2>=5 <-> [x:=7+x;]x^2>=5".asFormula, RenUSubst(
      ("f()".asTerm, "7+x".asTerm) ::
        (PredOf(Function("p", None, Real, Bool), DotTerm), GreaterEqual(Power(DotTerm, "2".asTerm), "5".asTerm)) :: Nil))
  }
}
