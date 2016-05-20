/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.core

import scala.collection.immutable
import edu.cmu.cs.ls.keymaerax.btactics.{DerivedRuleInfo, RandomFormula}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.{SummaryTest, USubstTest, UsualTest}
import edu.cmu.cs.ls.keymaerax.tools.KeYmaera
import org.scalatest._
import testHelper.KeYmaeraXTestTags

import scala.collection.immutable.List
import scala.collection.immutable.Seq
import scala.collection.immutable.IndexedSeq

/**
 * @author Andre Platzer
 * @author smitsch
  * @todo adapt tests to new uniform substitution framework
 */
@SummaryTest
@UsualTest
@USubstTest
class USubstTests extends FlatSpec with Matchers {
  KeYmaera.init(Map.empty)

  val randomTrials = 50
  val randomComplexity = 20
  val rand = new RandomFormula()

  //@note former core.UniformSubstitutionRule used here merely for the tests to continue to work even if they are less helpful
  private def UniformSubstitutionRule(subst: USubst, origin: Sequent) : Sequent => immutable.List[Sequent] = conclusion =>
      try {
        //log("---- " + subst + "\n    " + origin + "\n--> " + subst(origin) + (if (subst(origin) == conclusion) "\n==  " else "\n!=  ") + conclusion)
        if (subst(origin) == conclusion) immutable.List(origin)
        else throw new InapplicableRuleException(this + "\non premise   " + origin + "\nresulted in  " + subst(origin) + "\nbut expected " + conclusion, null, conclusion)
        /*("From\n  " + origin + "\nuniform substitution\n  " + subst +
          "\ndid not conclude the intended\n  " + conclusion + "\nbut instead\n  " + subst(origin))*/
      } catch { case exc: SubstitutionClashException => throw exc.inContext(this + "\non premise   " + origin + "\nresulted in  " + "clash " + exc.clashes + "\nbut expected " + conclusion) }


  val x = Variable("x", None, Real)
  val z = Variable("z", None, Real)
  val p0 = PredOf(Function("p", None, Unit, Bool), Nothing)
  val p1 = Function("p", None, Real, Bool)
  val p1_ = Function("p_", None, Real, Bool)
  val pn = Function("p", None, Real, Bool)
  val pn_ = Function("p_", None, Real, Bool)
  val qn = Function("q", None, Real, Bool)
  val qn_ = Function("q_", None, Real, Bool)
  val ap = ProgramConst("a")
  val ap_ = ProgramConst("a_")
  //val f1 = Function("f", None, Real, Real)
  val f1_ = Function("f_", None, Real, Real)
  //val g1 = Function("g", None, Real, Real)
  val g1_ = Function("g_", None, Real, Real)

  val ctx  = Function("ctx_", None, Bool, Bool)
  val ctxt = Function("ctx_", None, Real, Real)
  val ctxf = Function("ctx_", None, Real, Bool)

  "Uniform substitution" should "substitute simple formula p(x) <-> ! ! p(- - x)" in {
    val p = Function("p", None, Real, Bool)
    val x = Variable("x", None, Real)
    // p(x) <-> ! ! p(- - x)
    val prem = Equiv(PredOf(p, x), Not(Not(PredOf(p, Neg(Neg(x))))))
    val s = USubst(Seq(SubstitutionPair(PredOf(p, DotTerm), GreaterEqual(Power(DotTerm, Number(5)), Number(0)))))
    s(prem) should be ("x^5>=0 <-> !(!((-(-x))^5>=0))".asFormula)
  }

  it should "substitute simple sequent p(x) <-> ! ! p(- - x)" in {
    val p = Function("p", None, Real, Bool)
    val x = Variable("x", None, Real)
    // p(x) <-> ! ! p(- - x)
    val prem = Equiv(PredOf(p, x), Not(Not(PredOf(p, Neg(Neg(x))))))
    val s = USubst(Seq(SubstitutionPair(PredOf(p, DotTerm), GreaterEqual(Power(DotTerm, Number(5)), Number(0)))))
    val conc = "x^5>=0 <-> !(!((-(-x))^5>=0))".asFormula
    UniformSubstitutionRule(s,
      Sequent(Seq(), IndexedSeq(), IndexedSeq(prem)))(
        Sequent(Seq(), IndexedSeq(), IndexedSeq(conc))) shouldBe List(Sequent(Seq(), IndexedSeq(), IndexedSeq(prem)))
  }

  it should "substitute simple formula [a]p(x) <-> [a](p(x)&true)" in {
    val p = Function("p", None, Real, Bool)
    val x = Variable("x", None, Real)
    val a = ProgramConst("a")
    // [a]p(x) <-> [a](p(x)&true)
    val prem = Equiv(Box(a, PredOf(p, x)), Box(a, And(PredOf(p, x), True)))
    val s = USubst(Seq(SubstitutionPair(PredOf(p, DotTerm), GreaterEqual(DotTerm, Number(2))),
      SubstitutionPair(a, ODESystem(AtomicODE(DifferentialSymbol(x), Number(5)), True))))
    s(prem) should be ("[{x'=5}]x>=2 <-> [{x'=5}](x>=2&true)".asFormula)
  }

  it should "substitute simple sequent [a]p(x) <-> [a](p(x)&true)" in {
    val p = Function("p", None, Real, Bool)
    val x = Variable("x", None, Real)
    val a = ProgramConst("a")
    // [a]p(x) <-> [a](p(x)&true)
    val prem = Equiv(Box(a, PredOf(p, x)), Box(a, And(PredOf(p, x), True)))
    val s = USubst(Seq(SubstitutionPair(PredOf(p, DotTerm), GreaterEqual(DotTerm, Number(2))),
      SubstitutionPair(a, ODESystem(AtomicODE(DifferentialSymbol(x), Number(5)), True))))
    val conc = "[{x'=5}]x>=2 <-> [{x'=5}](x>=2&true)".asFormula
    UniformSubstitutionRule(s,
      Sequent(Seq(), IndexedSeq(), IndexedSeq(prem)))(
        Sequent(Seq(), IndexedSeq(), IndexedSeq(conc))) shouldBe List(Sequent(Seq(), IndexedSeq(), IndexedSeq(prem)))
  }


  it should "clash when using [:=] for a substitution with a free occurrence of a bound variable" taggedAs(KeYmaeraXTestTags.USubstTest,KeYmaeraXTestTags.CheckinTest) in {
    val fn = FuncOf(Function("f", None, Unit, Real), Nothing)
    val prem = Equiv(
      Box("x:=f();".asProgram, PredOf(p1, "x".asTerm)),
      PredOf(p1, fn)) // axioms.axiom("[:=])
    val conc = "[x:=x+1;]x!=x <-> x+1!=x".asFormula
    val s = USubst(Seq(SubstitutionPair(PredOf(p1, DotTerm), NotEqual(DotTerm, "x".asTerm)),
      SubstitutionPair(fn, "x+1".asTerm)))
    a [SubstitutionClashException] should be thrownBy UniformSubstitutionRule(s,
      Sequent(Seq(), IndexedSeq(), IndexedSeq(prem)))(
      Sequent(Seq(), IndexedSeq(), IndexedSeq(conc)))
  }
  
  it should "clash when using [:=] for a substitution with a free occurrence of a bound variable for constants" taggedAs(KeYmaeraXTestTags.USubstTest,KeYmaeraXTestTags.CheckinTest) in {
    val fn = FuncOf(Function("f", None, Unit, Real), Nothing)
    val prem = Equiv(
      Box("x:=f();".asProgram, PredOf(p1, "x".asTerm)),
      PredOf(p1, fn)) // axioms.axiom("[:=])
    val conc = "[x:=0;]x=x <-> 0=x".asFormula
    val s = USubst(Seq(SubstitutionPair(PredOf(p1, DotTerm), Equal(DotTerm, "x".asTerm)),
      SubstitutionPair(fn, "0".asTerm)))
    a [SubstitutionClashException] should be thrownBy UniformSubstitutionRule(s,
      Sequent(Seq(), IndexedSeq(), IndexedSeq(prem)))(
      Sequent(Seq(), IndexedSeq(), IndexedSeq(conc)))
  }

  it should "handle nontrivial binding structures" taggedAs KeYmaeraXTestTags.USubstTest in {
    val fn = FuncOf(Function("f", None, Unit, Real), Nothing)
    val prem = Equiv(
      Box("x:=f();".asProgram, PredOf(p1, "x".asTerm)),
      PredOf(p1, fn)) // axioms.axiom("[:=])
    val conc = "[x:=x^2;][{y:=y+1;++{z:=x+z;}*}; z:=x+y*z;]y>x <-> [{y:=y+1;++{z:=x^2+z;}*}; z:=x^2+y*z;]y>x^2".asFormula

    val y = Variable("y", None, Real)
    val z = Variable("z", None, Real)
    val s = USubst(Seq(
      // [{y:=y+1++{z:=.+z}*}; z:=.+y*z]y>.
      SubstitutionPair(PredOf(p1, DotTerm), Box(
        Compose(
          Choice(
            Assign(y, Plus(y, Number(1))),
            Loop(Assign(z, Plus(DotTerm, z)))
          ),
          Assign(z, Plus(DotTerm, Times(y, z)))),
        Greater(y, DotTerm))),
      SubstitutionPair(fn, "x^2".asTerm)))
    UniformSubstitutionRule(s, Sequent(Seq(), IndexedSeq(), IndexedSeq(prem)))(Sequent(Seq(), IndexedSeq(), IndexedSeq(conc))) should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(prem))))
  }

  it should "clash when using vacuous all quantifier forall x for a postcondition x>=0 with a free occurrence of the bound variable" taggedAs(KeYmaeraXTestTags.USubstTest,KeYmaeraXTestTags.SummaryTest) in {
    val fml = GreaterEqual(x, Number(0))
    val prem = Provable.axiom("vacuous all quantifier")
    val conc = Forall(Seq(x), fml)
    val s = USubst(Seq(SubstitutionPair(p0, fml)))
    //a [SubstitutionClashException] should be thrownBy
    val e = intercept[ProverException] {
      UniformSubstitutionRule(s,
        Sequent(Seq(), IndexedSeq(), IndexedSeq(prem)))(
        Sequent(Seq(), IndexedSeq(), IndexedSeq(conc)))
    }
    e.isInstanceOf[SubstitutionClashException] || e.isInstanceOf[InapplicableRuleException] shouldBe true
  }
  
  it should "clash when using V on x:=x-1 for a postcondition x>=0 with a free occurrence of a bound variable" taggedAs(KeYmaeraXTestTags.USubstTest,KeYmaeraXTestTags.SummaryTest) in {
    val fml = GreaterEqual(x, Number(0))
    val prem = Provable.axiom("V vacuous")
    val prog = Assign(x, Minus(x, Number(1)))
    val conc = Box(prog, fml)
    val s = USubst(Seq(SubstitutionPair(p0, fml),
      SubstitutionPair(ap, prog)))
    a [SubstitutionClashException] should be thrownBy UniformSubstitutionRule(s,
      Sequent(Seq(), IndexedSeq(), IndexedSeq(prem)))(
      Sequent(Seq(), IndexedSeq(), IndexedSeq(conc)))
  }
  
  it should "clash when using \"c()' derive constant fn\" for a substitution with free occurrences" taggedAs KeYmaeraXTestTags.USubstTest in {
    val aC = FuncOf(Function("c", None, Unit, Real), Nothing)
    val prem = "(c())'=0".asFormula // axioms.axiom("c()' derive constant fn")
    val conc = "(x)'=0".asFormula
    val s = USubst(Seq(SubstitutionPair(aC, "x".asTerm)))
    a [SubstitutionClashException] should be thrownBy UniformSubstitutionRule(s,
      Sequent(Seq(), IndexedSeq(), IndexedSeq(prem)))(
      Sequent(Seq(), IndexedSeq(), IndexedSeq(conc)))
  }
  
  it should "clash when using \"c()' derive constant fn\" for a substitution with free differential occurrences" taggedAs KeYmaeraXTestTags.USubstTest in {
    val aC = FuncOf(Function("c", None, Unit, Real), Nothing)
    val prem = "(c())'=0".asFormula // axioms.axiom("c()' derive constant fn")
    val conc = "(x')'=0".asFormula
    val s = USubst(Seq(SubstitutionPair(aC, "x'".asTerm)))
    a [SubstitutionClashException] should be thrownBy UniformSubstitutionRule(s,
      Sequent(Seq(), IndexedSeq(), IndexedSeq(prem)))(
      Sequent(Seq(), IndexedSeq(), IndexedSeq(conc)))
  }

  it should "refuse to accept ill-kinded substitutions outright" in {
    a[CoreException] should be thrownBy SubstitutionPair(FuncOf(Function("a", None, Unit, Real), Nothing), Greater(Variable("x"), Number(5)))
    a[CoreException] should be thrownBy SubstitutionPair(FuncOf(Function("a", None, Real, Real), DotTerm), Greater(Variable("x"), Number(5)))
    a[CoreException] should be thrownBy SubstitutionPair(FuncOf(Function("a", None, Unit, Real), Nothing), ProgramConst("c"))
    a[CoreException] should be thrownBy SubstitutionPair(FuncOf(Function("a", None, Real, Real), DotTerm), ProgramConst("c"))
    a[CoreException] should be thrownBy SubstitutionPair(PredOf(Function("p", None, Unit, Bool), Nothing), Number(5))
    a[CoreException] should be thrownBy SubstitutionPair(PredOf(Function("p", None, Real, Bool), DotTerm), Number(5))
    a[CoreException] should be thrownBy SubstitutionPair(PredOf(Function("p", None, Unit, Bool), Nothing), ProgramConst("c"))
    a[CoreException] should be thrownBy SubstitutionPair(PredOf(Function("p", None, Real, Bool), DotTerm), ProgramConst("c"))
    a[CoreException] should be thrownBy SubstitutionPair(ProgramConst("c"), FuncOf(Function("a", None, Unit, Real), Nothing))
    a[CoreException] should be thrownBy SubstitutionPair(ProgramConst("c"), Greater(Variable("x"), Number(5)))
  }

  it should "refuse to accept ill-shaped substitutions outright" in {
    a [CoreException] should be thrownBy SubstitutionPair(Number(7), Number(9))
    a [CoreException] should be thrownBy SubstitutionPair(Variable("x"), Number(9))
    a [CoreException] should be thrownBy SubstitutionPair(Plus(Variable("x"),Number(7)), Number(9))
    a [CoreException] should be thrownBy SubstitutionPair(Plus(Number(2),Number(7)), Number(9))
    a [CoreException] should be thrownBy SubstitutionPair(Plus(FuncOf(Function("a", None, Unit, Real), Nothing),FuncOf(Function("b", None, Unit, Real), Nothing)), Number(9))
    a [CoreException] should be thrownBy SubstitutionPair(And(Greater(Number(7),Number(2)), Less(Number(2),Number(1))), False)
    a [CoreException] should be thrownBy SubstitutionPair(AssignAny(Variable("x")), ProgramConst("c"))
    a [CoreException] should be thrownBy SubstitutionPair(AssignAny(Variable("x")), AssignAny(Variable("y")))
    a [CoreException] should be thrownBy SubstitutionPair(Assign(Variable("x"), Number(7)), Assign(Variable("y"), Number(7)))
    a [CoreException] should be thrownBy SubstitutionPair(Assign(Variable("x"), Number(7)), AssignAny(Variable("y")))
    a [CoreException] should be thrownBy SubstitutionPair(AtomicODE(DifferentialSymbol(Variable("x")), Number(7)), AssignAny(Variable("x")))
    a [CoreException] should be thrownBy SubstitutionPair(ODESystem(AtomicODE(DifferentialSymbol(Variable("x")), Number(7)), True), AssignAny(Variable("x")))
  }

  it should "refuse duplicate substitutions outright" in {
    val list1 = SubstitutionPair(FuncOf(Function("a", None, Real, Real), DotTerm), Number(5)) ::
      SubstitutionPair(FuncOf(Function("a", None, Real, Real), DotTerm), Number(22)) :: Nil
    a[CoreException] should be thrownBy USubst(list1)
    val list2 = SubstitutionPair(PredOf(Function("p", None, Unit, Bool), Nothing), Greater(Variable("x"), Number(5))) ::
      SubstitutionPair(PredOf(Function("p", None, Unit, Bool), Nothing), Less(Variable("z"), Number(99))) :: Nil
    a[CoreException] should be thrownBy USubst(list2)
    val list3 = SubstitutionPair(ProgramConst("c"), Assign(Variable("y"), Number(7))) ::
      SubstitutionPair(ProgramConst("c"), AssignAny(Variable("y"))) :: Nil
    a[CoreException] should be thrownBy USubst(list3)
  }

  // uniform substitution of rules

  "Uniform substitution of rules" should "instantiate Goedel from (-x)^2>=0 (I)" taggedAs(KeYmaeraXTestTags.USubstTest,KeYmaeraXTestTags.SummaryTest) in {
    val fml = GreaterEqual(Power(Neg(x), Number(2)), Number(0))
    val prog = Assign(x, Minus(x, Number(1)))
    val conc = Box(prog, fml)
    val s = USubst(Seq(SubstitutionPair(PredOf(p1_, Anything), fml),
      SubstitutionPair(ap_, prog)))
    val pr = Provable.rules("Goedel")(s)
    pr.conclusion shouldBe Sequent(Seq(), IndexedSeq(), IndexedSeq(conc))
    pr.subgoals should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
  }

  it should "instantiate Goedel from (-x)^2>=0 (II)" taggedAs KeYmaeraXTestTags.USubstTest in {
    val fml = "(-x)^2>=0".asFormula
    val prog = "x:=x-1;".asProgram
    val s = USubst(
      SubstitutionPair(PredOf(p1_, Anything), fml) ::
      SubstitutionPair(ap_, prog) :: Nil)
    val pr = Provable.rules("Goedel")(s)
    pr.conclusion shouldBe Sequent(Seq(), IndexedSeq(), IndexedSeq(Box(prog, fml)))
    pr.subgoals should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
  }
  
  it should "instantiate nontrivial binding structures in [] congruence" taggedAs(KeYmaeraXTestTags.USubstTest,KeYmaeraXTestTags.CheckinTest) in {
    val prem = "(-x)^2>=y <-> x^2>=y".asFormula
    val conc = "[{y:=y+1;++{z:=x+z;}*}; z:=x+y*z;](-x)^2>=y <-> [{y:=y+1;++{z:=x+z;}*}; z:=x+y*z;]x^2>=y".asFormula

    val prog = "{y:=y+1;++{z:=x+z;}*}; z:=x+y*z;".asProgram
    val q_ = Function("q_", None, Real, Bool)
    val ctx_ = Function("ctx_", None, Bool, Bool)
    val s = USubst(
      SubstitutionPair(ap_, prog) ::
      SubstitutionPair(PredOf(pn_, Anything), "(-x)^2>=y".asFormula) ::
      SubstitutionPair(PredOf(q_, Anything), "x^2>=y".asFormula) ::
      SubstitutionPair(PredicationalOf(ctx_, DotFormula), Box("{y:=y+1;++{z:=x+z;}*}; z:=x+y*z;".asProgram, DotFormula)) :: Nil)
    val pr = Provable.rules("CE congruence")(s)
    pr.conclusion shouldBe Sequent(Seq(), IndexedSeq(), IndexedSeq(conc))
    pr.subgoals should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(prem))))
  }

  it should "instantiate random programs in [] monotone" taggedAs KeYmaeraXTestTags.USubstTest in {
    for (i <- 1 to randomTrials) {
      val prem1 = "(-z1)^2>=z4".asFormula
      val prem2 = "z4<=z1^2".asFormula
      val prog = rand.nextProgram(randomComplexity)
      val concLhs = Box(prog, prem1)
      val concRhs = Box(prog, prem2)
      println("Random precontext " + prog.prettyString)

      val q_ = Function("q_", None, Real, Bool)
      val s = USubst(Seq(
        SubstitutionPair(ap_, prog),
        SubstitutionPair(PredOf(pn_, Anything), prem1),
        SubstitutionPair(PredOf(q_, Anything), prem2)
         ))
      val pr = DerivedRuleInfo("[] monotone").provable(s)
      pr.conclusion shouldBe Sequent(Seq(), IndexedSeq(concLhs), IndexedSeq(concRhs))
      pr.subgoals should contain only Sequent(Seq(), IndexedSeq(prem1), IndexedSeq(prem2))
    }
  }

  it should "instantiate random programs in [] congruence" taggedAs KeYmaeraXTestTags.USubstTest in {
    for (i <- 1 to randomTrials) {
      val prem1 = "(-z1)^2>=z4".asFormula
      val prem2 = "z4<=z1^2".asFormula
      val prem = Equiv(prem1, prem2)
      val prog = rand.nextProgram(randomComplexity)
      val conc = Equiv(Box(prog, prem1), Box(prog, prem2))
      println("Random precontext " + prog.prettyString)

      val q_ = Function("q_", None, Real, Bool)
      val ctx_ = Function("ctx_", None, Bool, Bool)

      val s = USubst(SubstitutionPair(ap_, prog) ::
        SubstitutionPair(PredOf(pn_, Anything), prem1) ::
        SubstitutionPair(PredOf(q_, Anything), prem2) ::
        SubstitutionPair(PredicationalOf(ctx_, DotFormula), Box(prog, DotFormula)) :: Nil)
      val pr = Provable.rules("CE congruence")(s)
      pr.conclusion shouldBe Sequent(Seq(), IndexedSeq(), IndexedSeq(conc))
      pr.subgoals should contain only Sequent(Seq(), IndexedSeq(), IndexedSeq(prem))
    }
  }

  ignore should "instantiate {?[{?true;}*]PP{⎵};}* in <> congruence" taggedAs KeYmaeraXTestTags.USubstTest in {
    val prem1 = "(-z1)^2>=z4".asFormula
    val prem2 = "z4<=z1^2".asFormula
    val prem = Equiv(prem1, prem2)
    //@todo DotFormula is not replaced in substitution so this case will fail
    val prog = "{?[{?true;}*]PP{⎵};}*".asProgram
    val conc = Equiv(Diamond(prog, prem1), Diamond(prog, prem2))
    println("Precontext " + prog.prettyString)

    val q_ = Function("q_", None, Real, Bool)
    val ctx_ = Function("ctx_", None, Bool, Bool)

    val s = USubst(SubstitutionPair(ap_, prog) ::
      SubstitutionPair(PredOf(pn_, Anything), prem1) ::
      SubstitutionPair(PredOf(q_, Anything), prem2) ::
      SubstitutionPair(PredicationalOf(ctx_, DotFormula), Diamond(prog, DotFormula)) :: Nil)
    val pr = Provable.rules("CE congruence")(s)
    pr.conclusion shouldBe Sequent(Seq(), IndexedSeq(), IndexedSeq(conc))
    pr.subgoals should contain only Sequent(Seq(), IndexedSeq(), IndexedSeq(prem))
  }

  it should "instantiate random programs in <> congruence" taggedAs KeYmaeraXTestTags.USubstTest in {
    for (i <- 1 to randomTrials) {
      val prem1 = "(-z1)^2>=z4".asFormula
      val prem2 = "z4<=z1^2".asFormula
      val prem = Equiv(prem1, prem2)
      val prog = rand.nextProgram(randomComplexity)
      val conc = Equiv(Diamond(prog, prem1), Diamond(prog, prem2))
      println("Random precontext " + prog.prettyString)

      val q_ = Function("q_", None, Real, Bool)
      val ctx_ = Function("ctx_", None, Bool, Bool)

      val s = USubst(SubstitutionPair(ap_, prog) ::
        SubstitutionPair(PredOf(pn_, Anything), prem1) ::
        SubstitutionPair(PredOf(q_, Anything), prem2) ::
        SubstitutionPair(PredicationalOf(ctx_, DotFormula), Diamond(prog, DotFormula)) :: Nil)
      val pr = Provable.rules("CE congruence")(s)
      pr.conclusion shouldBe Sequent(Seq(), IndexedSeq(), IndexedSeq(conc))
      pr.subgoals should contain only Sequent(Seq(), IndexedSeq(), IndexedSeq(prem))
    }
  }

  it should "instantiate random programs in <> monotone" taggedAs KeYmaeraXTestTags.USubstTest in {
    for (i <- 1 to randomTrials) {
      val prem1 = "(-z1)^2>=z4".asFormula
      val prem2 = "z4<=z1^2".asFormula
      val prog = rand.nextProgram(randomComplexity)
      val concLhs = Diamond(prog, prem1)
      val concRhs = Diamond(prog, prem2)
      println("Random precontext " + prog.prettyString)

      val q_ = Function("q_", None, Real, Bool)
      val s = USubst(Seq(
        SubstitutionPair(ap_, prog),
        SubstitutionPair(PredOf(pn_, Anything), prem1),
        SubstitutionPair(PredOf(q_, Anything), prem2)
         ))
      val pr = Provable.rules("<> monotone")(s)
      pr.conclusion shouldBe Sequent(Seq(), IndexedSeq(concLhs), IndexedSeq(concRhs))
      pr.subgoals should contain only Sequent(Seq(), IndexedSeq(prem1), IndexedSeq(prem2))
    }
  }

  it should "instantiate random programs in Goedel" taggedAs KeYmaeraXTestTags.USubstTest in {
    for (i <- 1 to randomTrials) {
      val prem = "(-z1)^2>=0".asFormula
      val prog = rand.nextProgram(randomComplexity)
      val conc = Box(prog, prem)
      println("Random precontext " + prog.prettyString)

      val s = USubst(Seq(
        SubstitutionPair(ap_, prog),
        SubstitutionPair(PredOf(pn_, Anything), prem)
         ))
      val pr = Provable.rules("Goedel")(s)
      pr.conclusion shouldBe Sequent(Seq(), IndexedSeq(), IndexedSeq(conc))
      pr.subgoals should contain only Sequent(Seq(), IndexedSeq(), IndexedSeq(prem))
    }
  }

  "Congruence rules" should "instantiate CT from y+z=z+y" taggedAs KeYmaeraXTestTags.USubstTest in {
      val term1 = "y+z".asTerm
      val term2 = "z+y".asTerm
      val fml = Equal(term1, term2)
      val s = USubst(
        SubstitutionPair(FuncOf(f1_, Anything), term1) ::
        SubstitutionPair(FuncOf(g1_, Anything), term2) ::
        SubstitutionPair(FuncOf(ctxt, DotTerm), Minus(DotTerm, Number(5))) :: Nil)
      val pr = DerivedRuleInfo("CT term congruence").provable(s)
      pr.conclusion shouldBe Sequent(Seq(), IndexedSeq(), IndexedSeq(Equal(Minus(term1, Number(5)),
        Minus(term2, Number(5)))))
      pr.subgoals should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
    }
    
  ignore should "instantiate CT from y+z=z+y in more context" taggedAs KeYmaeraXTestTags.USubstTest in {
    val term1 = "y+z".asTerm
    val term2 = "z+y".asTerm
    val fml = Equal(term1, term2)
    val s = USubst(
      SubstitutionPair(FuncOf(f1_, Anything), term1) ::
      SubstitutionPair(FuncOf(g1_, Anything), term2) ::
      SubstitutionPair(FuncOf(ctxt, DotTerm), Times(Power(x, Number(3)), DotTerm)) :: Nil)
    val pr = Provable.rules("CT term congruence")(s)
    pr.conclusion shouldBe Sequent(Seq(), IndexedSeq(), IndexedSeq(Equal(Times(Power(x, Number(3)), term1),
        Times(Power(x, Number(3)), term2))
        ))
    pr.subgoals should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
  }
    
  ignore should "instantiate CT from y+z=z+y in random context" taggedAs KeYmaeraXTestTags.USubstTest in {
    for (i <- 1 to randomTrials) {
      val term1 = "y+z".asTerm
      val term2 = "z+y".asTerm
      val fml = Equal(term1, term2)
      val context = rand.nextDotTerm(randomComplexity)
      println("Random context " + context.prettyString)
      val s = USubst(
        SubstitutionPair(FuncOf(f1_, Anything), term1) ::
        SubstitutionPair(FuncOf(g1_, Anything), term2) ::
        SubstitutionPair(FuncOf(ctxt, DotTerm), context) :: Nil)
      val pr = Provable.rules("CT term congruence")(s)
      pr.conclusion shouldBe
        Sequent(Seq(), IndexedSeq(), IndexedSeq(Equal(contextapp(context, term1), contextapp(context, term2))))
      pr.subgoals should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
    }
  }

  ignore should "instantiate CT from z1+z3*z2=z2*z3+z1 in random context" taggedAs KeYmaeraXTestTags.USubstTest in {
    for (i <- 1 to randomTrials) {
      val term1 = "z1+z3*z2".asTerm
      val term2 = "z2*z3+z1".asTerm
      val fml = Equal(term1, term2)
      val context = rand.nextDotTerm(randomComplexity)
      println("Random context " + context.prettyString)
      val s = USubst(
        SubstitutionPair(FuncOf(f1_, Anything), term1) ::
        SubstitutionPair(FuncOf(g1_, Anything), term2) ::
        SubstitutionPair(FuncOf(ctxt, DotTerm), context) :: Nil)
      val pr = Provable.rules("CT term congruence")(s)
      pr.conclusion shouldBe
        Sequent(Seq(), IndexedSeq(), IndexedSeq(Equal(contextapp(context, term1), contextapp(context, term2))))
      pr.subgoals should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
    }
  }

  ignore should "instantiate CT from z1*z3-z2=z2-z4/z1 in random context" taggedAs KeYmaeraXTestTags.USubstTest in {
    for (i <- 1 to randomTrials) {
      val term1 = "z1*z3-z2".asTerm
      val term2 = "z2-z4/z1".asTerm
      val fml = Equal(term1, term2)
      val context = rand.nextDotTerm(randomComplexity)
      println("Random context " + context.prettyString)
      val s = USubst(
        SubstitutionPair(FuncOf(f1_, Anything), term1) ::
        SubstitutionPair(FuncOf(g1_, Anything), term2) ::
        SubstitutionPair(FuncOf(ctxt, DotTerm), context) :: Nil)
      val pr = Provable.rules("CT term congruence")(s)
      pr.conclusion shouldBe
        Sequent(Seq(), IndexedSeq(), IndexedSeq(Equal(contextapp(context, term1), contextapp(context, term2))))
      pr.subgoals should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
    }
  }

  it should "instantiate CQ from y+z=z+y in context y>1&.<=5" taggedAs KeYmaeraXTestTags.USubstTest in {
    val term1 = "y+z".asTerm
    val term2 = "z+y".asTerm
    val fml = Equal(term1, term2)
    val y = Variable("y", None, Real)
    val s = USubst(
      SubstitutionPair(FuncOf(f1_, Anything), term1) ::
      SubstitutionPair(FuncOf(g1_, Anything), term2) ::
      SubstitutionPair(PredOf(ctxf, DotTerm), And(Greater(y, Number(1)), LessEqual(DotTerm, Number(5)))) :: Nil)
    val pr = Provable.rules("CQ equation congruence")(s)
    pr.conclusion shouldBe
          Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv( And(Greater(y, Number(1)), LessEqual(term1, Number(5))),
          And(Greater(y, Number(1)), LessEqual(term2, Number(5)))
          )))
    pr.subgoals should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
  }
        
  it should "instantiate CQ from y+z=z+y in context \\forall x .<=5" taggedAs KeYmaeraXTestTags.USubstTest in {
    val term1 = "y+z".asTerm
    val term2 = "z+y".asTerm
    val fml = Equal(term1, term2)
    val y = Variable("x", None, Real)
    val s = USubst(
      SubstitutionPair(FuncOf(f1_, Anything), term1) ::
      SubstitutionPair(FuncOf(g1_, Anything), term2) ::
      SubstitutionPair(PredOf(ctxf, DotTerm), Forall(Seq(y),  LessEqual(DotTerm, Number(5)))) :: Nil)
    val pr = Provable.rules("CQ equation congruence")(s)
    pr.conclusion shouldBe
          Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv( Forall(Seq(y),  LessEqual(term1, Number(5))),
          Forall(Seq(y),  LessEqual(term2, Number(5)))
          )))
    pr.subgoals should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
  }

  ignore should "?instantiate CQ from y+z=z+y in context \\forall y .<=5" taggedAs KeYmaeraXTestTags.OptimisticTest in {
    val term1 = "y+z".asTerm
    val term2 = "z+y".asTerm
    val fml = Equal(term1, term2)
    val y = Variable("y", None, Real)
    val s = USubst(
      SubstitutionPair(FuncOf(f1_, Anything), term1) ::
      SubstitutionPair(FuncOf(g1_, Anything), term2) ::
      SubstitutionPair(PredOf(ctxf, DotTerm), Forall(Seq(y),  LessEqual(DotTerm, Number(5)))) :: Nil)
    val pr = Provable.rules("CQ equation congruence")(s)
    pr.conclusion shouldBe
          Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv( Forall(Seq(y),  LessEqual(term1, Number(5))),
          Forall(Seq(y),  LessEqual(term2, Number(5)))
          )))
    pr.subgoals should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
  }

  it should "instantiate CQ from y+z=z+y in context [x:=x-1]" taggedAs KeYmaeraXTestTags.USubstTest in {
    val term1 = "y+z".asTerm
    val term2 = "z+y".asTerm
    val fml = Equal(term1, term2)
    val prog = "x:=x-1;".asProgram
    val s = USubst(
      SubstitutionPair(FuncOf(f1_, Anything), term1) ::
      SubstitutionPair(FuncOf(g1_, Anything), term2) ::
      SubstitutionPair(PredOf(ctxf, DotTerm), Box(prog, GreaterEqual(DotTerm, Number(0)))) :: Nil)
    val pr = Provable.rules("CQ equation congruence")(s)
    pr.conclusion shouldBe
        Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv( Box(prog, GreaterEqual(term1, Number(0))),
        Box(prog, GreaterEqual(term2, Number(0)))
        )))
    pr.subgoals should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
  }

  ignore should "?instantiate CQ from y+z=z+y in context [y:=y-1]" taggedAs KeYmaeraXTestTags.OptimisticTest in {
    val term1 = "y+z".asTerm
    val term2 = "z+y".asTerm
    val fml = Equal(term1, term2)
    val prog = "y:=y-1;".asProgram
    val s = USubst(
      SubstitutionPair(FuncOf(f1_, Anything), term1) ::
      SubstitutionPair(FuncOf(g1_, Anything), term2) ::
      SubstitutionPair(PredOf(ctxf, DotTerm), Box(prog, GreaterEqual(DotTerm, Number(0)))) :: Nil)
    val pr = Provable.rules("CQ equation congruence")(s)
    pr.conclusion shouldBe
        Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(Box(prog, GreaterEqual(term1, Number(0))),
        Box(prog, GreaterEqual(term2, Number(0)))
        )))
    pr.subgoals should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
  }

  ignore should "instantiate CT from z^2*y=-(-z)^2*-y+0" taggedAs KeYmaeraXTestTags.USubstTest in {
    val term1 = "z^2*y".asTerm
    val term2 = "-(-z)^2*-y+0".asTerm
    val fml = Equal(term1, term2)
    val s = USubst(
      SubstitutionPair(FuncOf(f1_, Anything), term1) ::
      SubstitutionPair(FuncOf(g1_, Anything), term2) ::
      SubstitutionPair(FuncOf(ctxt, DotTerm), Times(Power(x, Number(3)), DotTerm)) :: Nil)
    val pr = Provable.rules("CT term congruence")(s)
    pr.conclusion shouldBe
          Sequent(Seq(), IndexedSeq(), IndexedSeq(Equal(Times(Power(x, Number(3)), term1),
          Times(Power(x, Number(3)), term2))
          ))
    pr.subgoals should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
  }
    
  ignore should "?instantiate CQ from z^2*y=-(-z)^2*-y+0 in context \\forall y" taggedAs KeYmaeraXTestTags.OptimisticTest in {
    val term1 = "z^2*y".asTerm
    val term2 = "-(-z)^2*-y+0".asTerm
    val fml = Equal(term1, term2)
    val y = Variable("y", None, Real)
    val s = USubst(
      SubstitutionPair(FuncOf(f1_, Anything), term1) ::
      SubstitutionPair(FuncOf(g1_, Anything), term2) ::
      SubstitutionPair(PredOf(ctxf, DotTerm), Forall(Seq(y), GreaterEqual(DotTerm, Number(0)))) :: Nil)
    val pr = Provable.rules("CQ equation congruence")(s)
    pr.conclusion shouldBe
        Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv( Forall(Seq(y), GreaterEqual(term1, Number(0))),
        Forall(Seq(y), GreaterEqual(term2, Number(0)))
        )))
    pr.subgoals should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
  }
  
  ignore should "?instantiate CQ from z^2*y=-(-z)^2*-y+0 in context [y:=y-1]" taggedAs KeYmaeraXTestTags.OptimisticTest in {
    val term1 = "z^2*y".asTerm
    val term2 = "-(-z)^2*-y+0".asTerm
    val fml = Equal(term1, term2)
    val prog = "y:=y-1;".asProgram
    val s = USubst(
      SubstitutionPair(FuncOf(f1_, Anything), term1) ::
      SubstitutionPair(FuncOf(g1_, Anything), term2) ::
      SubstitutionPair(PredOf(ctxf, DotTerm), Box(prog, GreaterEqual(DotTerm, Number(0)))) :: Nil)
    val pr = Provable.rules("CQ equation congruence")(s)
    pr.conclusion shouldBe
        Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(Box(prog, GreaterEqual(term1, Number(0))),
        Box(prog, GreaterEqual(term2, Number(0)))
        )))
    pr.subgoals should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
  }
  
  it should "instantiate CE from x=0 <-> x^2=0 into \\forall x context (manual test)" taggedAs KeYmaeraXTestTags.USubstTest in {
    val fml1 = "x=0".asFormula
    val fml2 = "x^2=0".asFormula
    val fml = Equiv(fml1, fml2)
    val context = Forall(Seq(x), DotFormula)
    val s = USubst(
      SubstitutionPair(PredOf(pn_, Anything), fml1) ::
      SubstitutionPair(PredOf(qn_, Anything), fml2) ::
      SubstitutionPair(PredicationalOf(ctx, DotFormula), context) :: Nil)
    val pr = Provable.rules("CE congruence")(s)
    pr.conclusion shouldBe
      Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(contextapp(context, fml1), contextapp(context, fml2))))
    pr.subgoals should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
  }

  it should "instantiate CE from x=0 <-> x^2=0 into \\forall x context (schematic test)" taggedAs KeYmaeraXTestTags.USubstTest in {
    val fml1 = "x=0".asFormula
    val fml2 = "x^2=0".asFormula
    val fml = Equiv(fml1, fml2)
    val context = Forall(Seq(x), DotFormula)
    val s = USubst(
      SubstitutionPair(PredOf(pn_, Anything), fml1) ::
      SubstitutionPair(PredOf(qn_, Anything), fml2) ::
      SubstitutionPair(PredicationalOf(ctx, DotFormula), context) :: Nil)
    val pr = Provable.rules("CE congruence")(s)
    pr.conclusion shouldBe
      Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(Forall(Seq(x), fml1), Forall(Seq(x), fml2))))
    pr.subgoals should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
  }
  
  it should "instantiate CE from x=0 <-> x^2=0 into [x:=5] context (schematic test)" taggedAs KeYmaeraXTestTags.USubstTest in {
    val fml1 = "x=0".asFormula
    val fml2 = "x^2=0".asFormula
    val fml = Equiv(fml1, fml2)
    val prog = "x:=5;".asProgram
    val context = Box(prog, DotFormula)
    val s = USubst(
      SubstitutionPair(PredOf(pn_, Anything), fml1) ::
      SubstitutionPair(PredOf(qn_, Anything), fml2) ::
      SubstitutionPair(PredicationalOf(ctx, DotFormula), context) :: Nil)
    val pr = Provable.rules("CE congruence")(s)
    pr.conclusion shouldBe
      Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(Box(prog, fml1), Box(prog, fml2))))
    pr.subgoals should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
  }

  it should "instantiate CE from x=0 <-> x^2=0 into [x'=5] context (schematic test)" taggedAs KeYmaeraXTestTags.USubstTest in {
    val fml1 = "x=0".asFormula
    val fml2 = "x^2=0".asFormula
    val fml = Equiv(fml1, fml2)
    val prog = "{x'=5}".asProgram  //ODESystem(Seq(), AtomicODE(Derivative(Real, x), Number(5)), True)
    val context = Box(prog, DotFormula)
    val s = USubst(
      SubstitutionPair(PredOf(pn_, Anything), fml1) ::
      SubstitutionPair(PredOf(qn_, Anything), fml2) ::
      SubstitutionPair(PredicationalOf(ctx, DotFormula), context) :: Nil)
    val pr = Provable.rules("CE congruence")(s)
    pr.conclusion shouldBe
      Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(Box(prog, fml1), Box(prog, fml2))))
    pr.subgoals should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
  }

  
  ignore should "?instantiate CQ from z^2*y=-(-z)^2*-y+0 in complex contexts" taggedAs KeYmaeraXTestTags.OptimisticTest in {
    val term1 = "z^2*y".asTerm
    val term2 = "-(-z)^2*-y+0".asTerm
    val fml = Equal(term1, term2)
    val prog = "y:=y-1;{z:=-z+2++z:=0}".asProgram
    val u = Variable("u", None, Real)
    val s = USubst(
      SubstitutionPair(FuncOf(f1_, Anything), term1) ::
      SubstitutionPair(FuncOf(g1_, Anything), term2) ::
      SubstitutionPair(PredOf(ctxf, DotTerm), Forall(Seq(u), Box(prog, GreaterEqual(DotTerm, u)))) :: Nil)
    val pr = Provable.rules("CQ equation congruence")(s)
    pr.conclusion shouldBe
      Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(Forall(Seq(u), Box(prog, GreaterEqual(term1, u))),
      Forall(Seq(u), Box(prog, GreaterEqual(term2, u)))
      )))
    pr.subgoals should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
  }
  
  it should "instantiate CQ from z^2*y=-(-z)^2*-y+0 in random contexts" taggedAs KeYmaeraXTestTags.USubstTest in {
    val term1 = "z^2*y".asTerm
    val term2 = "-(-z)^2*-y+0".asTerm
    val fml = Equal(term1, term2)
    for (i <- 1 to randomTrials) {
      val context = rand.nextDotFormula(randomComplexity)
      println("Random context " + context.prettyString)
      val s = USubst(
        SubstitutionPair(FuncOf(f1_, Anything), term1) ::
          SubstitutionPair(FuncOf(g1_, Anything), term2) ::
          SubstitutionPair(PredOf(ctxf, DotTerm), context) :: Nil)
      val pr = Provable.rules("CQ equation congruence")(s)
      pr.conclusion shouldBe
        Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(contextapp(context, term1), contextapp(context, term2))))
      pr.subgoals should be(List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
    }
  }
  
  it should "instantiate CE from z^2*y>=5 <-> (-z)^2*-y+0<=-5 in random contexts" taggedAs KeYmaeraXTestTags.USubstTest in {
    val fml1 = "z^2*y>=5".asFormula
    val fml2 = "(-z)^2*-y+0<=-5".asFormula
    val fml = Equiv(fml1, fml2)
    for (i <- 1 to randomTrials) {
      val context = rand.nextDotFormula(randomComplexity)
      println("Random context " + context.prettyString)
      val s = USubst(
        SubstitutionPair(PredOf(pn_, Anything), fml1) ::
          SubstitutionPair(PredOf(qn_, Anything), fml2) ::
          SubstitutionPair(PredicationalOf(ctx, DotFormula), context) :: Nil)
      val pr = Provable.rules("CE congruence")(s)
      pr.conclusion shouldBe
        Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(contextapp(context, fml1), contextapp(context, fml2))))
      pr.subgoals should be(List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
    }
  }

  "Random uniform substitutions" should "have no effect on random formulas without dots" taggedAs KeYmaeraXTestTags.USubstTest in {
    val trm1 = "x^2*y^3".asTerm
    val fml1 = "z1^2*z2>=x".asFormula
    for (i <- 1 to randomTrials) {
      val fml = rand.nextFormula(randomComplexity)
      println("Random dot-free formula " + fml.prettyString)
      val s = USubst(
        SubstitutionPair(DotTerm, trm1) ::
          SubstitutionPair(DotFormula, fml1) :: Nil)
      s(fml) shouldBe fml
      val dotfml = rand.nextDotFormula(randomComplexity)
      s(dotfml) shouldBe s(dotfml.asInstanceOf[Expression])
      val dottrm = rand.nextDotTerm(randomComplexity)
      s(dottrm) shouldBe s(dottrm.asInstanceOf[Expression])
      val dotprg = rand.nextDotProgram(randomComplexity)
      s(dotprg) shouldBe s(dotprg.asInstanceOf[Expression])
    }
  }

  it should "have no effect on random formulas without that predicate" taggedAs KeYmaeraXTestTags.USubstTest in {
    val trm1 = "x^2*y^3".asTerm
    val fml1 = "z1^2*z2>=x".asFormula
    for (i <- 1 to randomTrials) {
      val fml = rand.nextFormula(randomComplexity)
      println("Random context-free formula " + fml.prettyString)
      val s = USubst(
        SubstitutionPair(DotTerm, trm1) ::
        SubstitutionPair(PredOf(ctxf, DotTerm), fml1) :: Nil)
      s(fml) shouldBe fml
      val dotfml = rand.nextDotFormula(randomComplexity)
      s(dotfml) shouldBe s(dotfml.asInstanceOf[Expression])
      val dottrm = rand.nextDotTerm(randomComplexity)
      s(dottrm) shouldBe s(dottrm.asInstanceOf[Expression])
      val dotprg = rand.nextDotProgram(randomComplexity)
      s(dotprg) shouldBe s(dotprg.asInstanceOf[Expression])
    }
  }

  it should "have no effect on random formulas without that predicational" taggedAs KeYmaeraXTestTags.USubstTest in {
    val trm1 = "x^2*y^3".asTerm
    val fml1 = "z1^2*z2>=x".asFormula
    for (i <- 1 to randomTrials) {
      val fml = rand.nextFormula(randomComplexity)
      println("Random context-free formula " + fml.prettyString)
      val s = USubst(
        SubstitutionPair(DotTerm, trm1) ::
        SubstitutionPair(PredicationalOf(ctx, DotFormula), fml1) :: Nil)
      s(fml) shouldBe fml
      val dotfml = rand.nextDotFormula(randomComplexity)
      s(dotfml) shouldBe s(dotfml.asInstanceOf[Expression])
      val dottrm = rand.nextDotTerm(randomComplexity)
      s(dottrm) shouldBe s(dottrm.asInstanceOf[Expression])
      val dotprg = rand.nextDotProgram(randomComplexity)
      s(dotprg) shouldBe s(dotprg.asInstanceOf[Expression])
    }
  }

  // apply given context to the given argument
  def contextapp(context: Term, arg: Term) : Term =
   USubst(SubstitutionPair(DotTerm, arg) :: Nil)(context)

  def contextapp(context: Formula, arg: Term) : Formula =
    USubst(SubstitutionPair(DotTerm, arg) :: Nil)(context)
  
  def contextapp(context: Formula, arg: Formula) : Formula = {
    val mycontext = Function("dottingC_", None, Bool, Bool)//@TODO eisegesis  should be Function("dottingC_", None, Real->Bool, Bool) //@TODO introduce function types or the Predicational datatype

    USubst(SubstitutionPair(PredicationalOf(mycontext, DotFormula), context) :: Nil)(PredicationalOf(mycontext, arg))
  }
}