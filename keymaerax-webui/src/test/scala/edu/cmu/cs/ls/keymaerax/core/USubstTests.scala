/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.core

import scala.collection.immutable
import edu.cmu.cs.ls.keymaerax.btactics.{DerivedRuleInfo, RandomFormula}
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.{SummaryTest, USubstTest, UsualTest}
import edu.cmu.cs.ls.keymaerax.tools.KeYmaera
import org.scalatest._
import testHelper.KeYmaeraXTestTags
import testHelper.CustomAssertions.withSafeClue
import testHelper.KeYmaeraXTestTags.AdvocatusTest
import testHelper.CustomAssertions._

import scala.collection.immutable.List
import scala.collection.immutable.Seq
import scala.collection.immutable.IndexedSeq
import scala.language.postfixOps

/**
  * Uniform substitution clash test dummies.
  *
  * @author Andre Platzer
 * @author smitsch
 */
@SummaryTest
@UsualTest
@USubstTest
class USubstTests extends FlatSpec with Matchers {
  KeYmaera.init(Map.empty)

  val randomTrials = 50
  val randomComplexity = 20
  val rand = new RandomFormula()

  /** Test whether `operation(data)` is either a no-op returning `data` or throws an exception of type `E`. */
  def throwOrNoOp[In,Out,E:Manifest](operation: In => Out, data: In) = {
    var done = false
    try {
      // noop
      done = (operation(data) == data)
    }
    catch {
      case ignore : Throwable => done = false
    }
    if (!done) a [E] should be thrownBy {
      operation(data)
    }
  }


  //@note former core.UniformSubstitutionRule used here merely for the tests to continue to work even if they are less helpful
  @deprecated("Use Provable(USubst) rule instead")
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

  ignore should "substitute with dot projection" in {
    val p = Function("p", None, Tuple(Real, Real), Bool)
    val x = Variable("x", None, Real)
    val y = Variable("y", None, Real)
    val dot = DotTerm(Tuple(Real, Real))
    // p(x,y) <-> ! ! p(- - x, - -y)
    val prem = Equiv(PredOf(p, Pair(x, y)), Not(Not(PredOf(p, Pair(Neg(Neg(x)), Neg(Neg(y)))))))
    //@todo fst/snd not yet available
    val s = USubst(Seq(SubstitutionPair(PredOf(p, dot), GreaterEqual(Power("fst(.(.,.))".asTerm, "snd(.(.,.))".asTerm), Number(0)))))
    s(prem) should be ("x^y>=0 <-> !(!((-(-x))^(-(-(y)))>=0))".asFormula)
  }

  ignore should "substitute with more complicated dot projection" in {
    val p = Function("p", None, Tuple(Real, Tuple(Real, Real)), Bool)
    val x = Variable("x", None, Real)
    val y = Variable("y", None, Real)
    val z = Variable("z", None, Real)
    val f = Function("f", None, Tuple(Real, Real), Real)
    val dot = DotTerm(Tuple(Real, Tuple(Real, Real)))
    // p(x,y,z) <-> ! ! p(- - x, - -y,z)
    val prem = Equiv(PredOf(p, Pair(x, Pair(y, z))), Not(Not(PredOf(p, Pair(Neg(Neg(x)), Pair(Neg(Neg(y)), z))))))
    //@todo fst/snd not yet available
    val s = USubst(Seq(SubstitutionPair(PredOf(p, dot),
      GreaterEqual(Power("fst(.(.,.))".asTerm, FuncOf(f, Pair("fst(snd(.(.,(.,.))))".asTerm, "snd(snd(.(.,(.,.))))".asTerm))), Number(0)))))
    s(prem) should be ("x^f(y,z)>=0 <-> !(!((-(-x))^f(-(-(y)),z)>=0))".asFormula)
  }

  it should "substitute simple sequent p(x) <-> ! ! p(- - x)" in {
    val p = Function("p", None, Real, Bool)
    val x = Variable("x", None, Real)
    // p(x) <-> ! ! p(- - x)
    val prem = Equiv(PredOf(p, x), Not(Not(PredOf(p, Neg(Neg(x))))))
    val s = USubst(Seq(SubstitutionPair(PredOf(p, DotTerm), GreaterEqual(Power(DotTerm, Number(5)), Number(0)))))
    val conc = "x^5>=0 <-> !(!((-(-x))^5>=0))".asFormula
    Provable.startProof(prem)(s).conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq(conc))
  }

  it should "old substitute simple sequent p(x) <-> ! ! p(- - x)" in {
    val p = Function("p", None, Real, Bool)
    val x = Variable("x", None, Real)
    // p(x) <-> ! ! p(- - x)
    val prem = Equiv(PredOf(p, x), Not(Not(PredOf(p, Neg(Neg(x))))))
    val s = USubst(Seq(SubstitutionPair(PredOf(p, DotTerm), GreaterEqual(Power(DotTerm, Number(5)), Number(0)))))
    val conc = "x^5>=0 <-> !(!((-(-x))^5>=0))".asFormula
    UniformSubstitutionRule(s,
      Sequent(IndexedSeq(), IndexedSeq(prem)))(
        Sequent(IndexedSeq(), IndexedSeq(conc))) shouldBe List(Sequent(IndexedSeq(), IndexedSeq(prem)))
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
    Provable.startProof(prem)(s).conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq(conc))
  }
  it should "old substitute simple sequent [a]p(x) <-> [a](p(x)&true)" in {
    val p = Function("p", None, Real, Bool)
    val x = Variable("x", None, Real)
    val a = ProgramConst("a")
    // [a]p(x) <-> [a](p(x)&true)
    val prem = Equiv(Box(a, PredOf(p, x)), Box(a, And(PredOf(p, x), True)))
    val s = USubst(Seq(SubstitutionPair(PredOf(p, DotTerm), GreaterEqual(DotTerm, Number(2))),
      SubstitutionPair(a, ODESystem(AtomicODE(DifferentialSymbol(x), Number(5)), True))))
    val conc = "[{x'=5}]x>=2 <-> [{x'=5}](x>=2&true)".asFormula
    UniformSubstitutionRule(s,
      Sequent(IndexedSeq(), IndexedSeq(prem)))(
      Sequent(IndexedSeq(), IndexedSeq(conc))) shouldBe List(Sequent(IndexedSeq(), IndexedSeq(prem)))
  }


  it should "clash when using [:=] for a substitution with a free occurrence of a bound variable" taggedAs(KeYmaeraXTestTags.USubstTest,KeYmaeraXTestTags.CheckinTest) in {
    val fn = FuncOf(Function("f", None, Unit, Real), Nothing)
    val prem = Provable.axioms("[:=] assign")/*Equiv(
      Box("x:=f();".asProgram, PredOf(p1, "x".asTerm)),
      PredOf(p1, fn)) // axioms.axiom("[:=])
      */
    val conc = "[x_:=x_+1;]x_!=x_ <-> x_+1!=x_".asFormula
    val s = USubst(Seq(SubstitutionPair(PredOf(p1, DotTerm), NotEqual(DotTerm, "x_".asTerm)),
      SubstitutionPair(fn, "x_+1".asTerm)))
    a [SubstitutionClashException] should be thrownBy (prem(s))

  }
  it should "old clash when using [:=] for a substitution with a free occurrence of a bound variable" taggedAs(KeYmaeraXTestTags.USubstTest,KeYmaeraXTestTags.CheckinTest) in {
    val fn = FuncOf(Function("f", None, Unit, Real), Nothing)
    val prem = Equiv(
      Box("x:=f();".asProgram, PredOf(p1, "x".asTerm)),
      PredOf(p1, fn)) // axioms.axiom("[:=])
    val conc = "[x:=x+1;]x!=x <-> x+1!=x".asFormula
    val s = USubst(Seq(SubstitutionPair(PredOf(p1, DotTerm), NotEqual(DotTerm, "x".asTerm)),
      SubstitutionPair(fn, "x+1".asTerm)))
    a [SubstitutionClashException] should be thrownBy UniformSubstitutionRule(s,
      Sequent(IndexedSeq(), IndexedSeq(prem)))(
      Sequent(IndexedSeq(), IndexedSeq(conc)))
  }

  it should "clash when using [:=] for a substitution with a free occurrence of a bound variable for constants" taggedAs(KeYmaeraXTestTags.USubstTest,KeYmaeraXTestTags.CheckinTest) in {
    val fn = FuncOf(Function("f", None, Unit, Real), Nothing)
    val prem = Provable.axioms("[:=] assign")/*Equiv(
      Box("x:=f();".asProgram, PredOf(p1, "x".asTerm)),
      PredOf(p1, fn)) // axioms.axiom("[:=])
      */
    val conc = "[x_:=0;]x_=x_ <-> 0=x_".asFormula
    val s = USubst(Seq(SubstitutionPair(PredOf(p1, DotTerm), Equal(DotTerm, "x_".asTerm)),
      SubstitutionPair(fn, "0".asTerm)))
    a [SubstitutionClashException] should be thrownBy prem(s)
  }
  it should "old clash when using [:=] for a substitution with a free occurrence of a bound variable for constants" taggedAs(KeYmaeraXTestTags.USubstTest,KeYmaeraXTestTags.CheckinTest) in {
    val fn = FuncOf(Function("f", None, Unit, Real), Nothing)
    val prem = Equiv(
      Box("x:=f();".asProgram, PredOf(p1, "x".asTerm)),
      PredOf(p1, fn)) // axioms.axiom("[:=])
    val conc = "[x:=0;]x=x <-> 0=x".asFormula
    val s = USubst(Seq(SubstitutionPair(PredOf(p1, DotTerm), Equal(DotTerm, "x".asTerm)),
      SubstitutionPair(fn, "0".asTerm)))
    a [SubstitutionClashException] should be thrownBy UniformSubstitutionRule(s,
      Sequent(IndexedSeq(), IndexedSeq(prem)))(
      Sequent(IndexedSeq(), IndexedSeq(conc)))
  }

  it should "handle nontrivial binding structures" taggedAs KeYmaeraXTestTags.USubstTest in {
    val fn = FuncOf(Function("f", None, Unit, Real), Nothing)
    val prem = Provable.axioms("[:=] assign")/*Equiv(
      Box("x:=f();".asProgram, PredOf(p1, "x".asTerm)),
      PredOf(p1, fn)) // axioms.axiom("[:=])
      */
    val conc = "[x_:=x_^2;][{y:=y+1;++{z:=x_+z;}*}; z:=x_+y*z;]y>x_ <-> [{y:=y+1;++{z:=x_^2+z;}*}; z:=x_^2+y*z;]y>x_^2".asFormula

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
      SubstitutionPair(fn, "x_^2".asTerm)))
    prem(s).conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq(conc))
  }
  it should "old handle nontrivial binding structures" taggedAs KeYmaeraXTestTags.USubstTest in {
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
    UniformSubstitutionRule(s, Sequent(IndexedSeq(), IndexedSeq(prem)))(Sequent(IndexedSeq(), IndexedSeq(conc))) should be (List(Sequent(IndexedSeq(), IndexedSeq(prem))))
  }

  it should "clash when using vacuous all quantifier forall x for a postcondition x>=0 with a free occurrence of the bound variable" taggedAs(KeYmaeraXTestTags.USubstTest,KeYmaeraXTestTags.SummaryTest) in {
    val x = Variable("x_",None,Real)
    val fml = GreaterEqual(x, Number(0))
    val prem = Provable.axioms("vacuous all quantifier")
    val conc = Forall(Seq(x), fml)
    val s = USubst(Seq(SubstitutionPair(p0, fml)))
    //a [SubstitutionClashException] should be thrownBy
    val e = intercept[ProverException] {
      prem(s)
    }
    (e.isInstanceOf[SubstitutionClashException] || e.isInstanceOf[InapplicableRuleException]) shouldBe true
  }
  it should "old clash when using vacuous all quantifier forall x for a postcondition x>=0 with a free occurrence of the bound variable" taggedAs(KeYmaeraXTestTags.USubstTest,KeYmaeraXTestTags.SummaryTest) in {
    val fml = GreaterEqual(x, Number(0))
    val prem = Provable.axiom("vacuous all quantifier")
    val conc = Forall(Seq(x), fml)
    val s = USubst(Seq(SubstitutionPair(p0, fml)))
    //a [SubstitutionClashException] should be thrownBy
    val e = intercept[ProverException] {
      UniformSubstitutionRule(s,
        Sequent(IndexedSeq(), IndexedSeq(prem)))(
        Sequent(IndexedSeq(), IndexedSeq(conc)))
    }
    (e.isInstanceOf[SubstitutionClashException] || e.isInstanceOf[InapplicableRuleException]) shouldBe true
  }

  it should "clash when using V on x:=x-1 for a postcondition x>=0 with a free occurrence of a bound variable" taggedAs(KeYmaeraXTestTags.USubstTest,KeYmaeraXTestTags.SummaryTest) in {
    val x = Variable("x_",None,Real)
    val fml = GreaterEqual(x, Number(0))
    val prem = Provable.axioms("V vacuous")
    val prog = Assign(x, Minus(x, Number(1)))
    val conc = Box(prog, fml)
    val s = USubst(Seq(SubstitutionPair(p0, fml),
      SubstitutionPair(ap, prog)))
    a [SubstitutionClashException] should be thrownBy prem(s)
  }
  it should "old clash when using V on x:=x-1 for a postcondition x>=0 with a free occurrence of a bound variable" taggedAs(KeYmaeraXTestTags.USubstTest,KeYmaeraXTestTags.SummaryTest) in {
    val fml = GreaterEqual(x, Number(0))
    val prem = Provable.axiom("V vacuous")
    val prog = Assign(x, Minus(x, Number(1)))
    val conc = Box(prog, fml)
    val s = USubst(Seq(SubstitutionPair(p0, fml),
      SubstitutionPair(ap, prog)))
    a [SubstitutionClashException] should be thrownBy UniformSubstitutionRule(s,
      Sequent(IndexedSeq(), IndexedSeq(prem)))(
      Sequent(IndexedSeq(), IndexedSeq(conc)))
  }
  
  it should "clash when using \"c()' derive constant fn\" for a substitution with free occurrences" taggedAs KeYmaeraXTestTags.USubstTest in {
    val aC = FuncOf(Function("c", None, Unit, Real), Nothing)
    val prem = Provable.axioms("c()' derive constant fn") //(c())'=0".asFormula // axioms.axiom("c()' derive constant fn")
    val conc = "(x)'=0".asFormula
    val s = USubst(Seq(SubstitutionPair(aC, "x".asTerm)))
    a [SubstitutionClashException] should be thrownBy prem(s)
  }
  it should "old clash when using \"c()' derive constant fn\" for a substitution with free occurrences" taggedAs KeYmaeraXTestTags.USubstTest in {
    val aC = FuncOf(Function("c", None, Unit, Real), Nothing)
    val prem = "(c())'=0".asFormula // axioms.axiom("c()' derive constant fn")
    val conc = "(x)'=0".asFormula
    val s = USubst(Seq(SubstitutionPair(aC, "x".asTerm)))
    a [SubstitutionClashException] should be thrownBy UniformSubstitutionRule(s,
      Sequent(IndexedSeq(), IndexedSeq(prem)))(
      Sequent(IndexedSeq(), IndexedSeq(conc)))
  }

  it should "clash when using \"c()' derive constant fn\" for a substitution with free differential occurrences" taggedAs KeYmaeraXTestTags.USubstTest in {
    val aC = FuncOf(Function("c", None, Unit, Real), Nothing)
    val prem = Provable.axioms("c()' derive constant fn") //"(c())'=0".asFormula // axioms.axiom("c()' derive constant fn")
    val conc = "(x')'=0".asFormula
    val s = USubst(Seq(SubstitutionPair(aC, "x'".asTerm)))
    a [SubstitutionClashException] should be thrownBy prem(s)
  }
  it should "old clash when using \"c()' derive constant fn\" for a substitution with free differential occurrences" taggedAs KeYmaeraXTestTags.USubstTest in {
    val aC = FuncOf(Function("c", None, Unit, Real), Nothing)
    val prem = "(c())'=0".asFormula // axioms.axiom("c()' derive constant fn")
    val conc = "(x')'=0".asFormula
    val s = USubst(Seq(SubstitutionPair(aC, "x'".asTerm)))
    a [SubstitutionClashException] should be thrownBy UniformSubstitutionRule(s,
      Sequent(IndexedSeq(), IndexedSeq(prem)))(
      Sequent(IndexedSeq(), IndexedSeq(conc)))
  }

  it should "not allow bound variables to occur free in V with assignment" taggedAs(AdvocatusTest) in {
    a[SubstitutionClashException] shouldBe thrownBy {
      Provable.axioms("V vacuous")(USubst(
        SubstitutionPair(PredOf(Function("p", None, Unit, Bool), Nothing), "x=2".asFormula) ::
          SubstitutionPair(ProgramConst("a"), "x:=5;".asProgram) :: Nil))
    }
  }

  it should "not allow bound variables to occur free in V with ODE" taggedAs(AdvocatusTest) in {
    a[SubstitutionClashException] shouldBe thrownBy {
      Provable.axioms("V vacuous")(USubst(
        SubstitutionPair(PredOf(Function("p", None, Unit, Bool), Nothing), "x=2".asFormula) ::
          SubstitutionPair(ProgramConst("a"), "{x'=2}".asProgram) :: Nil))
    }
  }

  it should "not allow Anything-escalated substitutions on predicates of something" taggedAs(AdvocatusTest) in {
    val pr = Provable.axioms("V vacuous")(USubst(
      SubstitutionPair(PredOf(Function("p",None,Unit,Bool), Nothing), "q(y)".asFormula) ::
        SubstitutionPair(ProgramConst("a"), "x:=5;".asProgram) :: Nil))
    pr shouldBe 'proved
    pr.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("q(y) -> [x:=5;]q(y)".asFormula))
    // this should not prove x=0->[x:=5;]x=0
//    a [SubstitutionClashException] should be thrownBy {
//      pr(USubst(SubstitutionPair(UnitPredicational("q", AnyArg), "x=0".asFormula) :: Nil))
//    }
//    throwOrNoOp[Provable,Provable,SubstitutionClashException] (
//      pr => pr(USubst(SubstitutionPair(UnitPredicational("q", AnyArg), "x=0".asFormula) :: Nil)),
//      pr
//    )
    theDeductionOf {
      pr(USubst(SubstitutionPair(UnitPredicational("q", AnyArg), "x=0".asFormula) :: Nil))
    } should throwOrNoop[SubstitutionClashException](p =>
        p.conclusion.ante.isEmpty &&
        p.conclusion.succ.size == 1 &&
        (p.conclusion.succ.head match { case Imply(_, Box(prg, q)) => StaticSemantics.boundVars(prg).intersect(StaticSemantics.freeVars(q)).isEmpty }))
    // more specific phrasing (current behavior)
    // should throwOrNoop(_.conclusion == Sequent(IndexedSeq(), IndexedSeq("q(x) -> [x:=5;]q(x)".asFormula)))
  }

  it should "not allow Anything-escalated substitutions on functions of something" taggedAs(AdvocatusTest) in {
    val pr = Provable.axioms("V vacuous")(USubst(
      SubstitutionPair(PredOf(Function("p",None,Unit,Bool), Nothing), "f(y)=0".asFormula) ::
        SubstitutionPair(ProgramConst("a"), "x:=5;".asProgram) :: Nil))
    pr shouldBe 'proved
    pr.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("f(y)=0 -> [x:=5;]f(y)=0".asFormula))
    // this should not prove x=0->[x:=5;]x=0
    theDeductionOf {
      pr(USubst(SubstitutionPair(UnitFunctional("f",AnyArg,Real), "x".asTerm) :: Nil))
    } should throwOrNoop[SubstitutionClashException](p =>
        p.conclusion.ante.isEmpty &&
        p.conclusion.succ.size == 1 &&
        (p.conclusion.succ.head match { case Imply(_, Box(prg, q)) => StaticSemantics.boundVars(prg).intersect(StaticSemantics.freeVars(q)).isEmpty }))
    // more specific phrasing (current behavior)
    // should throwOrNoop(_.conclusion == Sequent(IndexedSeq(), IndexedSeq("f(x)=0 -> [x:=5;]f(x)=0".asFormula)))
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

  it should "refuse ++ union that lead to duplicate substitutions" in {
    val list1 = (USubst(SubstitutionPair(FuncOf(Function("a", None, Real, Real), DotTerm), Number(5))::Nil),
      USubst(SubstitutionPair(FuncOf(Function("a", None, Real, Real), DotTerm), Number(22)) :: Nil))
    a[CoreException] should be thrownBy (list1._1 ++ list1._2)
    (list1._1 ++ list1._1) shouldBe list1._1
    (list1._2 ++ list1._2) shouldBe list1._2
    val list2 = (USubst(SubstitutionPair(PredOf(Function("p", None, Unit, Bool), Nothing), Greater(Variable("x"), Number(5))) :: Nil),
      USubst(SubstitutionPair(PredOf(Function("p", None, Unit, Bool), Nothing), Less(Variable("z"), Number(99))) :: Nil))
    a[CoreException] should be thrownBy (list2._1 ++ list2._2)
    (list2._1 ++ list2._1) shouldBe list2._1
    (list2._2 ++ list2._2) shouldBe list2._2
    val list3 = (USubst(SubstitutionPair(ProgramConst("c"), Assign(Variable("y"), Number(7))) :: Nil),
      USubst(SubstitutionPair(ProgramConst("c"), AssignAny(Variable("y"))) :: Nil))
    a[CoreException] should be thrownBy (list3._1 ++ list3._2)
    (list3._1 ++ list3._1) shouldBe list3._1
    (list3._2 ++ list3._2) shouldBe list3._2
  }

  // uniform substitution of rules

  "Uniform substitution of rules" should "instantiate Goedel from (-x)^2>=0 (I)" taggedAs(KeYmaeraXTestTags.USubstTest,KeYmaeraXTestTags.SummaryTest) in {
    val fml = GreaterEqual(Power(Neg(x), Number(2)), Number(0))
    val prog = Assign(x, Minus(x, Number(1)))
    val conc = Box(prog, fml)
    val s = USubst(Seq(SubstitutionPair(UnitPredicational("p_", AnyArg), fml),
      SubstitutionPair(ap_, prog)))
    val pr = Provable.rules("Goedel")(s)
    pr.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq(conc))
    pr.subgoals should be (List(Sequent(IndexedSeq(), IndexedSeq(fml))))
  }

  it should "instantiate Goedel from (-x)^2>=0 (II)" taggedAs KeYmaeraXTestTags.USubstTest in {
    val fml = "(-x)^2>=0".asFormula
    val prog = "x:=x-1;".asProgram
    val s = USubst(
      SubstitutionPair(UnitPredicational("p_", AnyArg), fml) ::
      SubstitutionPair(ap_, prog) :: Nil)
    val pr = Provable.rules("Goedel")(s)
    pr.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq(Box(prog, fml)))
    pr.subgoals should be (List(Sequent(IndexedSeq(), IndexedSeq(fml))))
  }
  
  it should "instantiate nontrivial binding structures in [] congruence" taggedAs(KeYmaeraXTestTags.USubstTest,KeYmaeraXTestTags.CheckinTest) in {
    val prem = "(-x)^2>=y <-> x^2>=y".asFormula
    val conc = "[{y:=y+1;++{z:=x+z;}*}; z:=x+y*z;](-x)^2>=y <-> [{y:=y+1;++{z:=x+z;}*}; z:=x+y*z;]x^2>=y".asFormula

    val prog = "{y:=y+1;++{z:=x+z;}*}; z:=x+y*z;".asProgram
    val q_ = Function("q_", None, Real, Bool)
    val ctx_ = Function("ctx_", None, Bool, Bool)
    val s = USubst(
      SubstitutionPair(ap_, prog) ::
      SubstitutionPair(UnitPredicational("p_", AnyArg), "(-x)^2>=y".asFormula) ::
      SubstitutionPair(UnitPredicational("q_", AnyArg), "x^2>=y".asFormula) ::
      SubstitutionPair(PredicationalOf(ctx_, DotFormula), Box("{y:=y+1;++{z:=x+z;}*}; z:=x+y*z;".asProgram, DotFormula)) :: Nil)
    val pr = Provable.rules("CE congruence")(s)
    pr.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq(conc))
    pr.subgoals should be (List(Sequent(IndexedSeq(), IndexedSeq(prem))))
  }


  it should "instantiate random programs in [] monotone" taggedAs KeYmaeraXTestTags.USubstTest in {
    for (i <- 1 to randomTrials) {
      val prem1 = "(-z1)^2>=z4".asFormula
      val prem2 = "z4<=z1^2".asFormula
      val prog = rand.nextProgram(randomComplexity)
      val concLhs = Box(prog, prem1)
      val concRhs = Box(prog, prem2)
      val randClue = "Program produced in\n\t " + i + "th run of " + randomTrials +
        " random trials,\n\t generated with " + randomComplexity + " random complexity\n\t from seed " + rand.seed

      val prgString = withSafeClue("Error printing random program\n\n" + randClue) {
        KeYmaeraXPrettyPrinter.stringify(prog)
      }

      withSafeClue("Random precontext " + prgString + "\n\n" + randClue) {
        println("Random precontext " + prog.prettyString)

        val q_ = Function("q_", None, Real, Bool)
        val s = USubst(Seq(
          SubstitutionPair(ap_, prog),
          SubstitutionPair(UnitPredicational("p_", AnyArg), prem1),
          SubstitutionPair(UnitPredicational("q_", AnyArg), prem2)
        ))
        val pr = DerivedRuleInfo("[] monotone").provable(s)
        pr.conclusion shouldBe Sequent(IndexedSeq(concLhs), IndexedSeq(concRhs))
        pr.subgoals should contain only Sequent(IndexedSeq(prem1), IndexedSeq(prem2))
      }
    }
  }

  /** Program produced in
    * 12th run of 50 random trials,
    * generated with 20 random complexity
    * from seed -3583806640264782477L
    */
  ignore should "instantiate crazy program in [] monotone" taggedAs KeYmaeraXTestTags.USubstTest in {
      val prem1 = "(-z1)^2>=z4".asFormula
      val prem2 = "z4<=z1^2".asFormula
      val prog = "{{z6'=0^2,z3'=0+(0+-50)&<?\\forall z6 [{{z4:=*;{{z7'=0,z6'=0&[{z2:=z2;{z2:=*;++?true;}}{{?true;z6:=*;++?true;}++{?true;?true;++{?true;}*}++{?true;}*++{?true;}*}]\\forall z3 (\\forall z4 true)'}z2:=z5';}*}{z5:=0;{{{z1:=z1;++?true;++{?true;?true;}*}{{z7'=0,z2'=0&\\forall z5 true}}*?true;++{{{?true;++?true;}*{{?true;}*++?true;}}{{?true;++z5:=0;}++{{?true;}*}*}}*}++?true;}?true;}*++{z6:=-30+0;++{{z5:=(0+z3)'-0;++z5:=(0+0-0/0)^0+z2+((gg()^4)'+ff(0));}++{{{{?true;?true;}*{z2'=28&true&true}++?true;}++z3:=z2;}++?true;}*}?\\forall z6 \\forall z4 true;}{{{{?true;}*}*++{z7'=0&z2*-97*(0)'>=(z4/(0-(0+0)))'}}*}*{?false;++{{{?true;}*++z7:=z7;}++z6:=*;}{?[{z1'=0&\\exists z1 <?true;>true}]\\exists z2 -97 < 0*0&<{{?true;}*}*++?true;++?true;++?true;>[{?true;++?true;}*]\\forall z2 <?true;>true;}*}}?<{{{{{{z3'=-12&\\exists z2 true}{?true;++?true;}*}*}*++z1:=-35;}?true;}*++?true;}++z6:=*;++?false;{{z2:=z2;++{{?true;?true;++{?true;}*}++?true;?true;++z3:=0;}*}{{{z5:=z5;}*++{?true;++?true;}{?true;}*}{{?true;}*{?true;++?true;}++?true;}}{z3:=*;++{z4:=0;}*{?true;?true;}{?true;++?true;}}++{{{{?true;}*}*++{?true;?true;++?true;}*}++{{?true;?true;}{?true;}*}*{{{?true;}*++{z6'=0&true}}++{?true;}*}}*}>\\forall z1 <{{{{{?true;}*++?true;++?true;}*}*{{?true;++?true;}*}*{{?true;}*}*z1:=*;}*++{{{{?true;?true;}*}*++z4:=*;}++{z6'=39&\\forall z3 <?true;>true|\\forall z4 [?true;]true}}?[{{?true;?true;}*}*][{?true;++?true;}*]\\exists z2 0>=0;}?(false&ff(z4) < (39-0*0)/-54)';>true;]0<=ff(z6);{{{{?[{?true;}*]\\exists z6 0=(55-z5)';++{z5:=z1';++{?true;}*?true;++?true;}{{{{{{?true;++?true;}++?true;}*++{z7'=0&[{?true;}*]\\forall z7 true}}++{?true;?true<->true;}*}{{{?true;?true;++{?true;}*}++{z7'=0,z5'=0,z2'=0&0=0}}?true;{z7'=0,z3'=0&true}{?true;++?true;}}*}*{z6:=z6;++{{z5:=*;++?[?true;]true;}{{?true;?true;}z1:=z1;}{?true;++?true;?true;}}?true;++{z2'=ff((0-0)^1)+25&z6'>z5'}}}z3:=z5';}++{{{{{{z4:=(93)';{?true;++?\\exists z6 true;}*}{{?true;++?true;?true;}++?true;}*{{{z3'=0&true}{z2'=0&true}}*}*}?true;}{{?true;++{?true;++z4:=*;{?true;++?true;?true;}}++z4:=z1/0;}++{{{?true;?true;}*z1:=*;{z7'=0&true}++z6:=0/0+0/0;}?true;}{{z4:=*;++z7:=*;}{z4:=z4;{?true;}*++{?true;?true;}*}}*}}{z7'=0&10-87<=0-z4-z1'}{?true;}*}{z3:=*;++{{{{?true;}*}*}*{{{?true;}*++{?true;}*}{?true;++{?true;}*}++{z2:=0;{?true;}*}*}}{{{{?true;++?true;}++z5:=0;}++?true;?true;++?true;}*++{{{?true;}*?true;?true;}{?true;++?true;}}z4:=0+0-0;}++{z3'=24&true}}{{z6'=0&(78^0)'>z7'}++{{{{?true;++?true;}{?true;}*++?true;}*}*{z6:=ff((0)')*(0*0)^0;++?true;++{?true;++?true;}*{?true;}*?true;?true;}}{{?true;}*++{{{z5:=0;}*{z4:=0;}*}?true;?0!=0;}{{{?true;?true;}?true;++{?true;++?true;}++{?true;}*}++{z3'=0,z1'=0&<?true;++?true;>(true|true)}}}}}*}{z1:=*;++?(gg()*(z4*(z3+z4)))^1/((ff(0-0+(0)'+(0+0)*(0*0))+0)/-17)^4!=(90)'-0;++{{z6'=0,z3'=0&[?true;++{{?true;?true;++?true;?true;}*}*++{?true;++{?true;++?true;}*}{{z2'=0-0&<?true;>true}}*][?true;]<{{?true;?true;}{?true;++?true;}}*++?[{?true;}*]qq();>(0/-13)^3 < z7}}*{{{{z7:=z7;}*++{{{?false;{?true;}*}z5:=0+0;}z1:=z2';}{?true;++{?true;++?true;}*++{?true;?true;}{?true;++?true;}}}{{{{z6'=0,z3'=8&true&true->true->true}}*}*++{{{{?true;}*}*{?true;?true;++{?true;}*}}?true;}*}}*++{{z5'=0,z3'=78&z2'>=0}}*{z7'=0&<?true;{z7'=0&[{?true;}*++{z4'=0,z3'=0&true}]true}>(((0*0=0-0<-><{?true;}*>\\forall z3 true)<->(gg()>=-86)')&(true|!<z4:=0;>0<=0))}}}++z4:=z2;}++z4:=*;++{?true;}*}*>(<{{{?true;?true;{{{{?true;}*}*{?true;}*}*{z4:=0*(0*0)'*(24^1)'+(0-(gg())'-z3');}*++?true;z4:=(93)';++z1:=z1';++{{z6'=0,z4'=0&[{?true;}*]true}{?true;?true;}*{{?true;}*}*}*{z5:=z5;++{?true;?true;++?true;}*++{{?true;}*}*{?true;?true;++{?true;}*}}}}{?true;++{{{{z6'=0-z5&ff(0)*(-10-z6)>=z5-35*z3}}*++?true;}++{{?[?true;]true|0>0;?true;z4:=z4;++{{z7:=z7;{?true;}*}*}*}{?true;{z1'=0&<?true;?true;>0!=0}}{?(true)';++?[?true;]true;}*}{{?true;?<?true;>true|0>0;++{z6:=*;{z4:=0;}*}?<?true;++?true;>0 < 0;}++z4:=0/(0+0)*-56^3;++{{?true;}*}*}}{z7:=ff((42)'+(0+0-0*0)');}*{?true;++z5:=z5;}++{z6:=ff((-74-0-(0*0+0))');{{{z4:=0;?true;}{{?true;}*}*}*++z6:=z6;}z2:=*;++{{{z2:=(z1)';}*}*}*}*}}*{z1:=z7;++{{?true;}*++{{{z7'=0,z1'=0&0-z5'-z2'>(z7)'}++?true;}++z4:=z4;{z7'=0,z2'=0&\\exists z5 z6'--11!=(0^2+(0-0))'/z1}}*}*}}*><{?true;{z3'=0,z2'=0&([{z6'=0,z2'=0&<{z2:=z2;++?true;++{?true;}*}*++{?true;?true;++?true;?true;}*{{?true;++?true;++?true;}++?true;}>(54-(z5+z5))^2=0}]\\exists z7 [?true;][{z1:=z1;}*++{?true;?true;}*++?true;?true;?true;]0+(z7-0*0)>z3*0*(0+0+gg()))'}{z5'=0&<{?ff((0-0)/(0+0))*((95)'+z1*0) < z6';++{{z6'=0,z1'=0&0^1+0>z7'}++z7:=z7;}?true;}*><?true;>(25/ff(0^3))'/((0-0)^4*(0*0+z3')*(9/(0*0)*73))+gg()>ff(0/z7)*(z6/(((0)'+(0+0))/z7+(0-0-0*0)'))}++{z1:=*;++?true;}{z4'=0&pp(((z3-50^1)^3)')}}*>0=z5-((58-50)'+z6)+0<-><{{?true;{{?true;}*++{{{{{{{?true;?true;++?true;?true;}++{?true;++?true;}++?true;++?true;}++{z4:=0;++?true;}{?true;?true;++?true;}}++?true;++{?true;++?true;++?true;}++{?true;}*++{?true;}*}*++?true;{{{?true;++?true;}*}*++z7:=*;}?true;}++?[{?true;{{?true;++?true;}++?true;?true;}}{?true;?true;}*?true;]<{z6:=0;++?true;?true;}{?true;}*{?true;++?true;}>0<=0;{{{{{?true;}*}*}*++{{?true;++?true;}++{?true;}*}*}*++z7:=z4*z5';++{?true;++?true;}*?<?true;>true;{?true;?true;++{?true;}*}}}++z3:=*;}++{z2:=z2';{{z7'=0&<{?true;?true;++z5:=z5;}++{?true;++?true;}++?true;++?true;>\\exists z3 <?true;?true;>0>0}}*++{{{{{?true;++?true;}{?true;++?true;}}*}*{?<{?true;}*>\\exists z5 true;++{z2'=87&true|true}++?true;}}*}*}++{z2'=0&<?true;>(93)'>-51}{{{z1'=0&<?true;>true}}*{{z1'=0&<z7:=0*0;>(\\forall z7 true&!true)}}*}{z4:=*;{{?true;++?true;}?true;?true;}z3:=*;++?true;}?true;z6:=z3*(0-0);{{{z5'=0&true}}*}*}}{{{z7'=0&true}}*++{z5:=z5;++{{z7'=0&ff(0*0)-(-15-z4)+gg()>0-58}++?true;}++z4:=z4;}{{{{{?true;}*{?true;?true;}?true;?true;}*++{?true;}*}z5:=2;{z6:=0;++z3:=9;}++z3:=*;}{{{z4'=(0+0)^0,z2'=0&true}z5:=*;}*++?true;{z1:=z1;++{z7:=0;++z1:=z1;}*{?true;++{?true;++?true;}++?true;?true;}}}}{{{z5:=*;++?true;++{?true;?true;++?true;?true;}++{?true;++?true;}?true;?true;}*}*++{{?true;++{{z5'=0/0&[?true;]true}?0=0;}?true;}{z6:=*;++{{?true;++?true;}z5:=0;++{?true;}*++?true;?true;}{?false;}*}}*}}*}*?true;>\\forall z6 (gg())'!=z4')}}*".asProgram
      val concLhs = Box(prog, prem1)
      val concRhs = Box(prog, prem2)
      val prgString = withSafeClue("Error printing crazy program") {
        KeYmaeraXPrettyPrinter.stringify(prog)
      }

      withSafeClue("Random precontext " + prgString + "\n\n") {
        println("Random precontext " + prog.prettyString)

        val q_ = Function("q_", None, Real, Bool)
        val s = USubst(Seq(
          SubstitutionPair(ap_, prog),
          SubstitutionPair(UnitPredicational("p_", AnyArg), prem1),
          SubstitutionPair(UnitPredicational("q_", AnyArg), prem2)
        ))
        val pr = DerivedRuleInfo("[] monotone").provable(s)
        pr.conclusion shouldBe Sequent(IndexedSeq(concLhs), IndexedSeq(concRhs))
        pr.subgoals should contain only Sequent(IndexedSeq(prem1), IndexedSeq(prem2))
      }
  }

  it should "instantiate random programs in [] congruence" taggedAs KeYmaeraXTestTags.USubstTest in {
    for (i <- 1 to randomTrials) {
      val prem1 = "(-z1)^2>=z4".asFormula
      val prem2 = "z4<=z1^2".asFormula
      val prem = Equiv(prem1, prem2)
      val prog = rand.nextProgram(randomComplexity)
      val conc = Equiv(Box(prog, prem1), Box(prog, prem2))
      val randClue = "Program produced in\n\t " + i + "th run of " + randomTrials +
        " random trials,\n\t generated with " + randomComplexity + " random complexity\n\t from seed " + rand.seed

      val prgString = withSafeClue("Error printing random program\n\n" + randClue) {
        KeYmaeraXPrettyPrinter.stringify(prog)
      }

      withSafeClue("Random precontext " + prgString + "\n\n" + randClue) {
        println("Random precontext " + prog.prettyString)

        val q_ = Function("q_", None, Real, Bool)
        val ctx_ = Function("ctx_", None, Bool, Bool)

        val s = USubst(SubstitutionPair(ap_, prog) ::
          SubstitutionPair(UnitPredicational("p_", AnyArg), prem1) ::
          SubstitutionPair(UnitPredicational("q_", AnyArg), prem2) ::
          SubstitutionPair(PredicationalOf(ctx_, DotFormula), Box(prog, DotFormula)) :: Nil)
        val pr = Provable.rules("CE congruence")(s)
        pr.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq(conc))
        pr.subgoals should contain only Sequent(IndexedSeq(), IndexedSeq(prem))
      }
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
      SubstitutionPair(UnitPredicational("p_", AnyArg), prem1) ::
      SubstitutionPair(UnitPredicational("q_", AnyArg), prem2) ::
      SubstitutionPair(PredicationalOf(ctx_, DotFormula), Diamond(prog, DotFormula)) :: Nil)
    val pr = Provable.rules("CE congruence")(s)
    pr.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq(conc))
    pr.subgoals should contain only Sequent(IndexedSeq(), IndexedSeq(prem))
  }

  it should "instantiate random programs in <> congruence" taggedAs KeYmaeraXTestTags.USubstTest in {
    for (i <- 1 to randomTrials) {
      val prem1 = "(-z1)^2>=z4".asFormula
      val prem2 = "z4<=z1^2".asFormula
      val prem = Equiv(prem1, prem2)
      val prog = rand.nextProgram(randomComplexity)
      val conc = Equiv(Diamond(prog, prem1), Diamond(prog, prem2))
      val randClue = "Program produced in\n\t " + i + "th run of " + randomTrials +
        " random trials,\n\t generated with " + randomComplexity + " random complexity\n\t from seed " + rand.seed

      val prgString = withSafeClue("Error printing random program\n\n" + randClue) {
        KeYmaeraXPrettyPrinter.stringify(prog)
      }

      withSafeClue("Random precontext " + prgString + "\n\n" + randClue) {
        println("Random precontext " + prog.prettyString)

        val q_ = Function("q_", None, Real, Bool)
        val ctx_ = Function("ctx_", None, Bool, Bool)

        val s = USubst(SubstitutionPair(ap_, prog) ::
          SubstitutionPair(UnitPredicational("p_", AnyArg), prem1) ::
          SubstitutionPair(UnitPredicational("q_", AnyArg), prem2) ::
          SubstitutionPair(PredicationalOf(ctx_, DotFormula), Diamond(prog, DotFormula)) :: Nil)
        val pr = Provable.rules("CE congruence")(s)
        pr.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq(conc))
        pr.subgoals should contain only Sequent(IndexedSeq(), IndexedSeq(prem))
        val pr2 = s(Provable.rules("CE congruence"))
        pr2.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq(conc))
        pr2.subgoals should contain only Sequent(IndexedSeq(), IndexedSeq(prem))
      }
    }
  }

  /**
    * Program produced in
	 38th run of 50 random trials,
	 generated with 20 random complexity
	 from seed -3583806640264782477L
    */
  ignore should "instantiate crazy program in <> congruence" taggedAs KeYmaeraXTestTags.USubstTest in {
      val prem1 = "(-z1)^2>=z4".asFormula
      val prem2 = "z4<=z1^2".asFormula
      val prem = Equiv(prem1, prem2)
      val prog = "{{{{?true;++{?\\forall z6 ([{z5'=21&[{?true;{?true;++?true;{?true;}*}}*]-40 < 0}]<{{{{z7'=0&true}{?true;++{z5'=0,z3'=0&\\forall z5 true}{?true;?true;}?true;?true;}}{{{z3'=0*0&true}++{?false;}*}++z1:=*;}{{{?true;++?true;}*}*++z1:=*;}}?true;?true;}*{{{z5:=z5;++?true;}++z7:=*;z6:=z6;}{{z6'=6&z5 < 0}}*++?true;}*>PP{qq()})';}*}z3:=z3;}{{?true;z3:=ff((gg()-ff(((0/(z2*z4)-(1-48))/(-28-66))')+(z5+z2')/(0*(gg()+(z4'-gg())-z7)/z1*z2'))/((z5'-z4)*gg())^5);++z2:=z2;?true;}z4:=*;++{{?true;}*++?true;}z5:=*;}}{{?true;{{{{z7'=0&true}}*++{{z1:=z3';++{{{z3:=z6;z2:=z2;}*?qq();}{z6:=*;}*}*}++{?true;z1:=*;}*++z4:=z4;?<{?<?true;>[?true;]true;{z4:=0;{?true;}*}{?true;?true;}{?true;}*}{{z1:=0;}*}*?true;++{{?true;++{{?true;}*}*}++?<z5:=0;><?true;>true;}{{{?true;++?true;}{z5'=0&true}}?true;}*>[{{z3'=0+0+(0+0)&[?true;?true;]\\forall z2 true}++?true;++?true;?true;?true;}{{?true;}*{?true;?true;}?true;}z2:=*;]<?true;><z7:=*;++z5:=z5;++?true;++?true;>z4'+gg()!=z1+(0-0);}{z4:=-50/z1^1;}*?true;}*}*}*++?true;}}z2:=(ff(-13-z5))';".asProgram
      val conc = Equiv(Diamond(prog, prem1), Diamond(prog, prem2))

      val prgString = withSafeClue("Error printing crazy program\n\n") {
        KeYmaeraXPrettyPrinter.stringify(prog)
      }

      withSafeClue("Random precontext " + prgString + "\n\n") {
        println("Random precontext " + prog.prettyString)

        val q_ = Function("q_", None, Real, Bool)
        val ctx_ = Function("ctx_", None, Bool, Bool)

        val s = USubst(SubstitutionPair(ap_, prog) ::
          SubstitutionPair(UnitPredicational("p_", AnyArg), prem1) ::
          SubstitutionPair(UnitPredicational("q_", AnyArg), prem2) ::
          SubstitutionPair(PredicationalOf(ctx_, DotFormula), Diamond(prog, DotFormula)) :: Nil)
        val pr = Provable.rules("CE congruence")(s)
        pr.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq(conc))
        pr.subgoals should contain only Sequent(IndexedSeq(), IndexedSeq(prem))
      }
  }

  it should "instantiate random programs in <> monotone" taggedAs KeYmaeraXTestTags.USubstTest in {
    for (i <- 1 to randomTrials) {
      val prem1 = "(-z1)^2>=z4".asFormula
      val prem2 = "z4<=z1^2".asFormula
      val prog = rand.nextProgram(randomComplexity)
      val concLhs = Diamond(prog, prem1)
      val concRhs = Diamond(prog, prem2)
      val randClue = "Program produced in\n\t " + i + "th run of " + randomTrials +
        " random trials,\n\t generated with " + randomComplexity + " random complexity\n\t from seed " + rand.seed

      val prgString = withSafeClue("Error printing random program\n\n" + randClue) {
        KeYmaeraXPrettyPrinter.stringify(prog)
      }

      withSafeClue("Random precontext " + prgString + "\n\n" + randClue) {
        println("Random precontext " + prog.prettyString)

        val q_ = Function("q_", None, Real, Bool)
        val s = USubst(Seq(
          SubstitutionPair(ap_, prog),
          SubstitutionPair(UnitPredicational("p_", AnyArg), prem1),
          SubstitutionPair(UnitPredicational("q_", AnyArg), prem2)
        ))
        val pr = Provable.rules("<> monotone")(s)
        pr.conclusion shouldBe Sequent(IndexedSeq(concLhs), IndexedSeq(concRhs))
        pr.subgoals should contain only Sequent(IndexedSeq(prem1), IndexedSeq(prem2))
      }
    }
  }

  it should "instantiate random programs in Goedel" taggedAs KeYmaeraXTestTags.USubstTest in {
    for (i <- 1 to randomTrials) {
      val prem = "(-z1)^2>=0".asFormula
      val prog = rand.nextProgram(randomComplexity)
      val conc = Box(prog, prem)

      val randClue = "Program produced in\n\t " + i + "th run of " + randomTrials +
        " random trials,\n\t generated with " + randomComplexity + " random complexity\n\t from seed " + rand.seed

      val prgString = withSafeClue("Error printing random program\n\n" + randClue) {
        KeYmaeraXPrettyPrinter.stringify(prog)
      }

      withSafeClue("Random precontext " + prgString + "\n\n" + randClue) {
        val s = USubst(Seq(
          SubstitutionPair(ap_, prog),
          SubstitutionPair(UnitPredicational("p_", AnyArg), prem)
        ))
        val pr = Provable.rules("Goedel")(s)
        pr.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq(conc))
        pr.subgoals should contain only Sequent(IndexedSeq(), IndexedSeq(prem))
      }
    }
  }

  "Congruence rules" should "instantiate CT from y+z=z+y" taggedAs KeYmaeraXTestTags.USubstTest in {
      val term1 = "y+z".asTerm
      val term2 = "z+y".asTerm
      val fml = Equal(term1, term2)
      val s = USubst(
        SubstitutionPair(UnitFunctional("f_", AnyArg, Real), term1) ::
        SubstitutionPair(UnitFunctional("g_", AnyArg, Real), term2) ::
        SubstitutionPair(FuncOf(ctxt, DotTerm), Minus(DotTerm, Number(5))) :: Nil)
      val pr = DerivedRuleInfo("CT term congruence").provable(s)
      pr.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq(Equal(Minus(term1, Number(5)),
              Minus(term2, Number(5)))))
      pr.subgoals should be (List(Sequent(IndexedSeq(), IndexedSeq(fml))))
    }
    
  ignore should "instantiate CT from y+z=z+y in more context" taggedAs KeYmaeraXTestTags.USubstTest in {
    val term1 = "y+z".asTerm
    val term2 = "z+y".asTerm
    val fml = Equal(term1, term2)
    val s = USubst(
      SubstitutionPair(UnitFunctional("f_", AnyArg, Real), term1) ::
      SubstitutionPair(UnitFunctional("g_", AnyArg, Real), term2) ::
      SubstitutionPair(FuncOf(ctxt, DotTerm), Times(Power(x, Number(3)), DotTerm)) :: Nil)
    val pr = Provable.rules("CT term congruence")(s)
    pr.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq(Equal(Times(Power(x, Number(3)), term1),
            Times(Power(x, Number(3)), term2))
            ))
    pr.subgoals should be (List(Sequent(IndexedSeq(), IndexedSeq(fml))))
  }
    
  ignore should "instantiate CT from y+z=z+y in random context" taggedAs KeYmaeraXTestTags.USubstTest in {
    for (i <- 1 to randomTrials) {
      val term1 = "y+z".asTerm
      val term2 = "z+y".asTerm
      val fml = Equal(term1, term2)
      val context = rand.nextDotTerm(randomComplexity)
      val randClue = "Program produced in\n\t " + i + "th run of " + randomTrials +
        " random trials,\n\t generated with " + randomComplexity + " random complexity\n\t from seed " + rand.seed

      val prgString = withSafeClue("Error printing random program\n\n" + randClue) {
        KeYmaeraXPrettyPrinter.stringify(context)
      }

      withSafeClue("Random context " + prgString + "\n\n" + randClue) {
        println("Random context " + context.prettyString)
        val s = USubst(
          SubstitutionPair(UnitFunctional("f_", AnyArg, Real), term1) ::
            SubstitutionPair(UnitFunctional("g_", AnyArg, Real), term2) ::
            SubstitutionPair(FuncOf(ctxt, DotTerm), context) :: Nil)
        val pr = Provable.rules("CT term congruence")(s)
        pr.conclusion shouldBe
          Sequent(IndexedSeq(), IndexedSeq(Equal(contextapp(context, term1), contextapp(context, term2))))
        pr.subgoals should be(List(Sequent(IndexedSeq(), IndexedSeq(fml))))
      }
    }
  }

  ignore should "instantiate CT from z1+z3*z2=z2*z3+z1 in random context" taggedAs KeYmaeraXTestTags.USubstTest in {
    for (i <- 1 to randomTrials) {
      val term1 = "z1+z3*z2".asTerm
      val term2 = "z2*z3+z1".asTerm
      val fml = Equal(term1, term2)
      val context = rand.nextDotTerm(randomComplexity)
      val randClue = "Program produced in\n\t " + i + "th run of " + randomTrials +
        " random trials,\n\t generated with " + randomComplexity + " random complexity\n\t from seed " + rand.seed

      val prgString = withSafeClue("Error printing random program\n\n" + randClue) {
        KeYmaeraXPrettyPrinter.stringify(context)
      }

      withSafeClue("Random precontext " + prgString + "\n\n" + randClue) {
        println("Random context " + context.prettyString)
        val s = USubst(
          SubstitutionPair(UnitFunctional("f_", AnyArg, Real), term1) ::
            SubstitutionPair(UnitFunctional("g_", AnyArg, Real), term2) ::
            SubstitutionPair(FuncOf(ctxt, DotTerm), context) :: Nil)
        val pr = Provable.rules("CT term congruence")(s)
        pr.conclusion shouldBe
          Sequent(IndexedSeq(), IndexedSeq(Equal(contextapp(context, term1), contextapp(context, term2))))
        pr.subgoals should be(List(Sequent(IndexedSeq(), IndexedSeq(fml))))
      }
    }
  }

  ignore should "instantiate CT from z1*z3-z2=z2-z4/z1 in random context" taggedAs KeYmaeraXTestTags.USubstTest in {
    for (i <- 1 to randomTrials) {
      val term1 = "z1*z3-z2".asTerm
      val term2 = "z2-z4/z1".asTerm
      val fml = Equal(term1, term2)
      val context = rand.nextDotTerm(randomComplexity)
      val randClue = "Program produced in\n\t " + i + "th run of " + randomTrials +
        " random trials,\n\t generated with " + randomComplexity + " random complexity\n\t from seed " + rand.seed

      val prgString = withSafeClue("Error printing random program\n\n" + randClue) {
        KeYmaeraXPrettyPrinter.stringify(context)
      }

      withSafeClue("Random precontext " + prgString + "\n\n" + randClue) {
        println("Random context " + context.prettyString)
        val s = USubst(
          SubstitutionPair(UnitFunctional("f_", AnyArg, Real), term1) ::
            SubstitutionPair(UnitFunctional("g_", AnyArg, Real), term2) ::
            SubstitutionPair(FuncOf(ctxt, DotTerm), context) :: Nil)
        val pr = Provable.rules("CT term congruence")(s)
        pr.conclusion shouldBe
          Sequent(IndexedSeq(), IndexedSeq(Equal(contextapp(context, term1), contextapp(context, term2))))
        pr.subgoals should be(List(Sequent(IndexedSeq(), IndexedSeq(fml))))
      }
    }
  }

  it should "instantiate CQ from y+z=z+y in context y>1&.<=5" taggedAs KeYmaeraXTestTags.USubstTest in {
    val term1 = "y+z".asTerm
    val term2 = "z+y".asTerm
    val fml = Equal(term1, term2)
    val y = Variable("y", None, Real)
    val s = USubst(
      SubstitutionPair(UnitFunctional("f_", AnyArg, Real), term1) ::
      SubstitutionPair(UnitFunctional("g_", AnyArg, Real), term2) ::
      SubstitutionPair(PredOf(ctxf, DotTerm), And(Greater(y, Number(1)), LessEqual(DotTerm, Number(5)))) :: Nil)
    val pr = Provable.rules("CQ equation congruence")(s)
    pr.conclusion shouldBe
          Sequent(IndexedSeq(), IndexedSeq(Equiv( And(Greater(y, Number(1)), LessEqual(term1, Number(5))),
                    And(Greater(y, Number(1)), LessEqual(term2, Number(5)))
                    )))
    pr.subgoals should be (List(Sequent(IndexedSeq(), IndexedSeq(fml))))
  }
        
  it should "instantiate CQ from y+z=z+y in context \\forall x .<=5" taggedAs KeYmaeraXTestTags.USubstTest in {
    val term1 = "y+z".asTerm
    val term2 = "z+y".asTerm
    val fml = Equal(term1, term2)
    val y = Variable("x", None, Real)
    val s = USubst(
      SubstitutionPair(UnitFunctional("f_", AnyArg, Real), term1) ::
      SubstitutionPair(UnitFunctional("g_", AnyArg, Real), term2) ::
      SubstitutionPair(PredOf(ctxf, DotTerm), Forall(Seq(y),  LessEqual(DotTerm, Number(5)))) :: Nil)
    val pr = Provable.rules("CQ equation congruence")(s)
    pr.conclusion shouldBe
          Sequent(IndexedSeq(), IndexedSeq(Equiv( Forall(Seq(y),  LessEqual(term1, Number(5))),
                    Forall(Seq(y),  LessEqual(term2, Number(5)))
                    )))
    pr.subgoals should be (List(Sequent(IndexedSeq(), IndexedSeq(fml))))
  }

  ignore should "?instantiate CQ from y+z=z+y in context \\forall y .<=5" taggedAs KeYmaeraXTestTags.OptimisticTest in {
    val term1 = "y+z".asTerm
    val term2 = "z+y".asTerm
    val fml = Equal(term1, term2)
    val y = Variable("y", None, Real)
    val s = USubst(
      SubstitutionPair(UnitFunctional("f_", AnyArg, Real), term1) ::
      SubstitutionPair(UnitFunctional("g_", AnyArg, Real), term2) ::
      SubstitutionPair(PredOf(ctxf, DotTerm), Forall(Seq(y),  LessEqual(DotTerm, Number(5)))) :: Nil)
    val pr = Provable.rules("CQ equation congruence")(s)
    pr.conclusion shouldBe
          Sequent(IndexedSeq(), IndexedSeq(Equiv( Forall(Seq(y),  LessEqual(term1, Number(5))),
                    Forall(Seq(y),  LessEqual(term2, Number(5)))
                    )))
    pr.subgoals should be (List(Sequent(IndexedSeq(), IndexedSeq(fml))))
  }

  it should "instantiate CQ from y+z=z+y in context [x:=x-1]" taggedAs KeYmaeraXTestTags.USubstTest in {
    val term1 = "y+z".asTerm
    val term2 = "z+y".asTerm
    val fml = Equal(term1, term2)
    val prog = "x:=x-1;".asProgram
    val s = USubst(
      SubstitutionPair(UnitFunctional("f_", AnyArg, Real), term1) ::
      SubstitutionPair(UnitFunctional("g_", AnyArg, Real), term2) ::
      SubstitutionPair(PredOf(ctxf, DotTerm), Box(prog, GreaterEqual(DotTerm, Number(0)))) :: Nil)
    val pr = Provable.rules("CQ equation congruence")(s)
    pr.conclusion shouldBe
        Sequent(IndexedSeq(), IndexedSeq(Equiv( Box(prog, GreaterEqual(term1, Number(0))),
                Box(prog, GreaterEqual(term2, Number(0)))
                )))
    pr.subgoals should be (List(Sequent(IndexedSeq(), IndexedSeq(fml))))
  }

  ignore should "?instantiate CQ from y+z=z+y in context [y:=y-1]" taggedAs KeYmaeraXTestTags.OptimisticTest in {
    val term1 = "y+z".asTerm
    val term2 = "z+y".asTerm
    val fml = Equal(term1, term2)
    val prog = "y:=y-1;".asProgram
    val s = USubst(
      SubstitutionPair(UnitFunctional("f_", AnyArg, Real), term1) ::
      SubstitutionPair(UnitFunctional("g_", AnyArg, Real), term2) ::
      SubstitutionPair(PredOf(ctxf, DotTerm), Box(prog, GreaterEqual(DotTerm, Number(0)))) :: Nil)
    val pr = Provable.rules("CQ equation congruence")(s)
    pr.conclusion shouldBe
        Sequent(IndexedSeq(), IndexedSeq(Equiv(Box(prog, GreaterEqual(term1, Number(0))),
                Box(prog, GreaterEqual(term2, Number(0)))
                )))
    pr.subgoals should be (List(Sequent(IndexedSeq(), IndexedSeq(fml))))
  }

  ignore should "instantiate CT from z^2*y=-(-z)^2*-y+0" taggedAs KeYmaeraXTestTags.USubstTest in {
    val term1 = "z^2*y".asTerm
    val term2 = "-(-z)^2*-y+0".asTerm
    val fml = Equal(term1, term2)
    val s = USubst(
      SubstitutionPair(UnitFunctional("f_", AnyArg, Real), term1) ::
      SubstitutionPair(UnitFunctional("g_", AnyArg, Real), term2) ::
      SubstitutionPair(FuncOf(ctxt, DotTerm), Times(Power(x, Number(3)), DotTerm)) :: Nil)
    val pr = Provable.rules("CT term congruence")(s)
    pr.conclusion shouldBe
          Sequent(IndexedSeq(), IndexedSeq(Equal(Times(Power(x, Number(3)), term1),
                    Times(Power(x, Number(3)), term2))
                    ))
    pr.subgoals should be (List(Sequent(IndexedSeq(), IndexedSeq(fml))))
  }
    
  ignore should "?instantiate CQ from z^2*y=-(-z)^2*-y+0 in context \\forall y" taggedAs KeYmaeraXTestTags.OptimisticTest in {
    val term1 = "z^2*y".asTerm
    val term2 = "-(-z)^2*-y+0".asTerm
    val fml = Equal(term1, term2)
    val y = Variable("y", None, Real)
    val s = USubst(
      SubstitutionPair(UnitFunctional("f_", AnyArg, Real), term1) ::
      SubstitutionPair(UnitFunctional("g_", AnyArg, Real), term2) ::
      SubstitutionPair(PredOf(ctxf, DotTerm), Forall(Seq(y), GreaterEqual(DotTerm, Number(0)))) :: Nil)
    val pr = Provable.rules("CQ equation congruence")(s)
    pr.conclusion shouldBe
        Sequent(IndexedSeq(), IndexedSeq(Equiv( Forall(Seq(y), GreaterEqual(term1, Number(0))),
                Forall(Seq(y), GreaterEqual(term2, Number(0)))
                )))
    pr.subgoals should be (List(Sequent(IndexedSeq(), IndexedSeq(fml))))
  }
  
  ignore should "?instantiate CQ from z^2*y=-(-z)^2*-y+0 in context [y:=y-1]" taggedAs KeYmaeraXTestTags.OptimisticTest in {
    val term1 = "z^2*y".asTerm
    val term2 = "-(-z)^2*-y+0".asTerm
    val fml = Equal(term1, term2)
    val prog = "y:=y-1;".asProgram
    val s = USubst(
      SubstitutionPair(UnitFunctional("f_", AnyArg, Real), term1) ::
      SubstitutionPair(UnitFunctional("g_", AnyArg, Real), term2) ::
      SubstitutionPair(PredOf(ctxf, DotTerm), Box(prog, GreaterEqual(DotTerm, Number(0)))) :: Nil)
    val pr = Provable.rules("CQ equation congruence")(s)
    pr.conclusion shouldBe
        Sequent(IndexedSeq(), IndexedSeq(Equiv(Box(prog, GreaterEqual(term1, Number(0))),
                Box(prog, GreaterEqual(term2, Number(0)))
                )))
    pr.subgoals should be (List(Sequent(IndexedSeq(), IndexedSeq(fml))))
  }
  
  it should "instantiate CE from x=0 <-> x^2=0 into \\forall x context (manual test)" taggedAs KeYmaeraXTestTags.USubstTest in {
    val fml1 = "x=0".asFormula
    val fml2 = "x^2=0".asFormula
    val fml = Equiv(fml1, fml2)
    val context = Forall(Seq(x), DotFormula)
    val s = USubst(
      SubstitutionPair(UnitPredicational("p_", AnyArg), fml1) ::
      SubstitutionPair(UnitPredicational("q_", AnyArg), fml2) ::
      SubstitutionPair(PredicationalOf(ctx, DotFormula), context) :: Nil)
    val pr = Provable.rules("CE congruence")(s)
    pr.conclusion shouldBe
      Sequent(IndexedSeq(), IndexedSeq(Equiv(contextapp(context, fml1), contextapp(context, fml2))))
    pr.subgoals should be (List(Sequent(IndexedSeq(), IndexedSeq(fml))))
  }

  it should "instantiate CE from x=0 <-> x^2=0 into \\forall x context (schematic test)" taggedAs KeYmaeraXTestTags.USubstTest in {
    val fml1 = "x=0".asFormula
    val fml2 = "x^2=0".asFormula
    val fml = Equiv(fml1, fml2)
    val context = Forall(Seq(x), DotFormula)
    val s = USubst(
      SubstitutionPair(UnitPredicational("p_", AnyArg), fml1) ::
      SubstitutionPair(UnitPredicational("q_", AnyArg), fml2) ::
      SubstitutionPair(PredicationalOf(ctx, DotFormula), context) :: Nil)
    val pr = Provable.rules("CE congruence")(s)
    pr.conclusion shouldBe
      Sequent(IndexedSeq(), IndexedSeq(Equiv(Forall(Seq(x), fml1), Forall(Seq(x), fml2))))
    pr.subgoals should be (List(Sequent(IndexedSeq(), IndexedSeq(fml))))
  }
  
  it should "instantiate CE from x=0 <-> x^2=0 into [x:=5] context (schematic test)" taggedAs KeYmaeraXTestTags.USubstTest in {
    val fml1 = "x=0".asFormula
    val fml2 = "x^2=0".asFormula
    val fml = Equiv(fml1, fml2)
    val prog = "x:=5;".asProgram
    val context = Box(prog, DotFormula)
    val s = USubst(
      SubstitutionPair(UnitPredicational("p_", AnyArg), fml1) ::
      SubstitutionPair(UnitPredicational("q_", AnyArg), fml2) ::
      SubstitutionPair(PredicationalOf(ctx, DotFormula), context) :: Nil)
    val pr = Provable.rules("CE congruence")(s)
    pr.conclusion shouldBe
      Sequent(IndexedSeq(), IndexedSeq(Equiv(Box(prog, fml1), Box(prog, fml2))))
    pr.subgoals should be (List(Sequent(IndexedSeq(), IndexedSeq(fml))))
  }

  it should "instantiate CE from x=0 <-> x^2=0 into [x'=5] context (schematic test)" taggedAs KeYmaeraXTestTags.USubstTest in {
    val fml1 = "x=0".asFormula
    val fml2 = "x^2=0".asFormula
    val fml = Equiv(fml1, fml2)
    val prog = "{x'=5}".asProgram  //ODESystem(Seq(), AtomicODE(Derivative(Real, x), Number(5)), True)
    val context = Box(prog, DotFormula)
    val s = USubst(
      SubstitutionPair(UnitPredicational("p_", AnyArg), fml1) ::
      SubstitutionPair(UnitPredicational("q_", AnyArg), fml2) ::
      SubstitutionPair(PredicationalOf(ctx, DotFormula), context) :: Nil)
    val pr = Provable.rules("CE congruence")(s)
    pr.conclusion shouldBe
      Sequent(IndexedSeq(), IndexedSeq(Equiv(Box(prog, fml1), Box(prog, fml2))))
    pr.subgoals should be (List(Sequent(IndexedSeq(), IndexedSeq(fml))))
  }

  
  ignore should "?instantiate CQ from z^2*y=-(-z)^2*-y+0 in complex contexts" taggedAs KeYmaeraXTestTags.OptimisticTest in {
    val term1 = "z^2*y".asTerm
    val term2 = "-(-z)^2*-y+0".asTerm
    val fml = Equal(term1, term2)
    val prog = "y:=y-1;{z:=-z+2++z:=0}".asProgram
    val u = Variable("u", None, Real)
    val s = USubst(
      SubstitutionPair(UnitFunctional("f_", AnyArg, Real), term1) ::
      SubstitutionPair(UnitFunctional("g_", AnyArg, Real), term2) ::
      SubstitutionPair(PredOf(ctxf, DotTerm), Forall(Seq(u), Box(prog, GreaterEqual(DotTerm, u)))) :: Nil)
    val pr = Provable.rules("CQ equation congruence")(s)
    pr.conclusion shouldBe
      Sequent(IndexedSeq(), IndexedSeq(Equiv(Forall(Seq(u), Box(prog, GreaterEqual(term1, u))),
            Forall(Seq(u), Box(prog, GreaterEqual(term2, u)))
            )))
    pr.subgoals should be (List(Sequent(IndexedSeq(), IndexedSeq(fml))))
  }
  
  it should "instantiate CQ from z^2*y=-(-z)^2*-y+0 in random contexts" taggedAs KeYmaeraXTestTags.USubstTest in {
    val term1 = "z^2*y".asTerm
    val term2 = "-(-z)^2*-y+0".asTerm
    val fml = Equal(term1, term2)
    for (i <- 1 to randomTrials) {
      val context = rand.nextDotFormula(randomComplexity)
      val randClue = "Program produced in\n\t " + i + "th run of " + randomTrials +
        " random trials,\n\t generated with " + randomComplexity + " random complexity\n\t from seed " + rand.seed

      val prgString = withSafeClue("Error printing random context\n\n" + randClue) {
        KeYmaeraXPrettyPrinter.stringify(context)
      }

      withSafeClue("Random precontext " + prgString + "\n\n" + randClue) {
        println("Random context " + context.prettyString)
        val s = USubst(
          SubstitutionPair(UnitFunctional("f_", AnyArg, Real), term1) ::
            SubstitutionPair(UnitFunctional("g_", AnyArg, Real), term2) ::
            SubstitutionPair(PredOf(ctxf, DotTerm), context) :: Nil)
        val pr = Provable.rules("CQ equation congruence")(s)
        pr.conclusion shouldBe
          Sequent(IndexedSeq(), IndexedSeq(Equiv(contextapp(context, term1), contextapp(context, term2))))
        pr.subgoals should be(List(Sequent(IndexedSeq(), IndexedSeq(fml))))
      }
    }
  }
  
  it should "instantiate CE from z^2*y>=5 <-> (-z)^2*-y+0<=-5 in random contexts" taggedAs KeYmaeraXTestTags.USubstTest in {
    val fml1 = "z^2*y>=5".asFormula
    val fml2 = "(-z)^2*-y+0<=-5".asFormula
    val fml = Equiv(fml1, fml2)
    for (i <- 1 to randomTrials) {
      val context = rand.nextDotFormula(randomComplexity)
      val randClue = "Program produced in\n\t " + i + "th run of " + randomTrials +
        " random trials,\n\t generated with " + randomComplexity + " random complexity\n\t from seed " + rand.seed

      val prgString = withSafeClue("Error printing random context\n\n" + randClue) {
        KeYmaeraXPrettyPrinter.stringify(context)
      }

      withSafeClue("Random precontext " + prgString + "\n\n" + randClue) {
        println("Random context " + context.prettyString)
        val s = USubst(
          SubstitutionPair(UnitPredicational("p_", AnyArg), fml1) ::
            SubstitutionPair(UnitPredicational("q_", AnyArg), fml2) ::
            SubstitutionPair(PredicationalOf(ctx, DotFormula), context) :: Nil)
        val pr = Provable.rules("CE congruence")(s)
        pr.conclusion shouldBe
          Sequent(IndexedSeq(), IndexedSeq(Equiv(contextapp(context, fml1), contextapp(context, fml2))))
        pr.subgoals should be(List(Sequent(IndexedSeq(), IndexedSeq(fml))))
      }
    }
  }

  "Random uniform substitutions" should "have no effect on random expressions without dots" taggedAs KeYmaeraXTestTags.USubstTest in {
    val trm1 = "x^2*y^3".asTerm
    val fml1 = "z1^2*z2>=x".asFormula
    for (i <- 1 to randomTrials) {
      val expr = rand.nextExpression(randomComplexity)
      val randClue = "Expression produced in\n\t " + i + "th run of " + randomTrials +
        " random trials,\n\t generated with " + randomComplexity + " random complexity\n\t from seed " + rand.seed

      val exprString = withSafeClue("Error printing random expression\n\n" + randClue) {
        KeYmaeraXPrettyPrinter.stringify(expr)
      }

      withSafeClue("Random expression " + exprString + "\n\n" + randClue) {
        println("Random dot-free " + expr.prettyString)
        val s = USubst(
          SubstitutionPair(DotTerm, trm1) ::
            SubstitutionPair(DotFormula, fml1) :: Nil)
        s(expr) shouldBe expr
        expr match {
          case e: Term => s(e) shouldBe expr
          case e: Formula => s(e) shouldBe expr
          case e: DifferentialProgram => s(e) shouldBe expr
          case e: Program => s(e) shouldBe expr
        }
        val dotfml = rand.nextDotFormula(randomComplexity)
        s(dotfml) shouldBe s(dotfml.asInstanceOf[Expression])
        val dottrm = rand.nextDotTerm(randomComplexity)
        s(dottrm) shouldBe s(dottrm.asInstanceOf[Expression])
        val dotprg = rand.nextDotProgram(randomComplexity)
        s(dotprg) shouldBe s(dotprg.asInstanceOf[Expression])
      }
    }
  }

  it should "have no effect on random formulas without that predicate" taggedAs KeYmaeraXTestTags.USubstTest in {
    val trm1 = "x^2*y^3".asTerm
    val fml1 = "z1^2*z2>=x".asFormula
    for (i <- 1 to randomTrials) {
      val fml = rand.nextFormula(randomComplexity)
      val randClue = "Formula produced in\n\t " + i + "th run of " + randomTrials +
        " random trials,\n\t generated with " + randomComplexity + " random complexity\n\t from seed " + rand.seed

      val prgString = withSafeClue("Error printing random formula\n\n" + randClue) {
        KeYmaeraXPrettyPrinter.stringify(fml)
      }

      withSafeClue("Random formula " + prgString + "\n\n" + randClue) {
        println("Random context-free formula " + fml.prettyString)
        val s = USubst(
          SubstitutionPair(DotTerm, trm1) ::
            SubstitutionPair(PredOf(ctxf, DotTerm), fml1) :: Nil)
        s(fml) shouldBe fml
        val dotfml = rand.nextDotFormula(randomComplexity)
        println("test on: " + dotfml)
        s(dotfml) shouldBe s(dotfml.asInstanceOf[Expression])
        val dottrm = rand.nextDotTerm(randomComplexity)
        println("test on: " + dottrm)
        s(dottrm) shouldBe s(dottrm.asInstanceOf[Expression])
        val dotprg = rand.nextDotProgram(randomComplexity)
        println("test on: " + dotprg)
        s(dotprg) shouldBe s(dotprg.asInstanceOf[Expression])
      }
    }
  }

  it should "have no effect on random formulas without that predicational" taggedAs KeYmaeraXTestTags.USubstTest in {
    val trm1 = "x^2*y^3".asTerm
    val fml1 = "z1^2*z2>=x".asFormula
    for (i <- 1 to randomTrials) {
      val fml = rand.nextFormula(randomComplexity)
      val randClue = "Formula produced in\n\t " + i + "th run of " + randomTrials +
        " random trials,\n\t generated with " + randomComplexity + " random complexity\n\t from seed " + rand.seed

      val prgString = withSafeClue("Error printing random formula\n\n" + randClue) {
        KeYmaeraXPrettyPrinter.stringify(fml)
      }

      withSafeClue("Random formula " + prgString + "\n\n" + randClue) {
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