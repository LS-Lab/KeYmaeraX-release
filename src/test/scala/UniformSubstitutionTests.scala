import edu.cmu.cs.ls.keymaera.core._
import org.scalatest.{PrivateMethodTester, BeforeAndAfterEach, Matchers, FlatSpec}
import testHelper.StringConverter
import scala.collection.immutable.{List, Set, Seq}
import StringConverter._

import scala.util.Random

/**
 * Created by rjcn on 01/09/15.
 * @author Ran Ji
 */

class UniformSubstitutionTests extends FlatSpec with Matchers with BeforeAndAfterEach with PrivateMethodTester {

  private def V(s: String) = Variable(s, None, Real)

  private def applySubstitutionT(s: Substitution, o: Set[NamedSymbol], u: Set[NamedSymbol], t: Term) : Term = {
    val applySubstitution = PrivateMethod[Term]('usubst)
    try {
      s invokePrivate applySubstitution(SetLattice(o), SetLattice(u), t)
    } catch {
      // distinguish between IllegalArgumentExceptions thrown by the test framework and those thrown by usubst itself
      case ex: IllegalArgumentException if ex.getMessage != "Can't find a private method named: usubst" =>
        throw new SubstitutionClashException(ex.getMessage, t, t).initCause(ex)
    }
  }

  private def applySubstitutionF(s: Substitution, o: Set[NamedSymbol], u: Set[NamedSymbol], f: Formula) : Formula = {
    val applySubstitution = PrivateMethod[Formula]('usubst)
    try {
      s invokePrivate applySubstitution(SetLattice(o), SetLattice(u), f)
    } catch {
      // distinguish between IllegalArgumentExceptions thrown by the test framework and those thrown by usubst itself
      case ex: IllegalArgumentException if ex.getMessage != "Can't find a private method named: usubst" =>
        throw new SubstitutionClashException(ex.getMessage, f, f).initCause(ex)
    }
  }

  private def applySubstitution(s: Substitution, o: Set[NamedSymbol], u: Set[NamedSymbol], p: Program) : Any = {
    val applySubstitution = PrivateMethod[Any]('usubstComps)
    try {
      s invokePrivate applySubstitution(o, u, p)
    } catch {
      // distinguish between IllegalArgumentExceptions thrown by the test framework and those thrown by usubst itself
      case ex: IllegalArgumentException if ex.getMessage != "Can't find a private method named: usubstComps" =>
        throw new SubstitutionClashException(ex.getMessage, p, p).initCause(ex)
    }
  }

  object SubstitutionTester {
    def create(subs: SubstitutionPair*) = new SubstitutionTester(scala.collection.immutable.Seq(subs: _*))
  }
  class SubstitutionTester(val subsDefs: scala.collection.immutable.Seq[SubstitutionPair]) {
    private val ls = Substitution(subsDefs)
    private val gs = GlobalSubstitution(subsDefs)

    private def tryBoth[T <: Expr](t: T, global: T => T, local: T => T): T = {
      val globalResult = try {
        global(t)
      } catch {
        case ex: SubstitutionClashException =>
          withClue("Global and local substitution disagree")(a [SubstitutionClashException] should be thrownBy local(t))
          throw ex
      }
      withClue("Global and local substitution disagree")(local(t) should be (globalResult))
      globalResult
    }

    def apply(t: Term): Term = tryBoth[Term](t, gs.apply, ls.apply)
    def apply(f: Formula): Formula = tryBoth[Formula](f, gs.apply, ls.apply)
    def apply(p: Program): Program = tryBoth[Program](p, gs.apply, ls.apply)
  }

  /**
   * ==================================================
   * tests for base cases
   */

  import SubstitutionTester.create

  // \theta +/- \eta

  "Uniform substitution of (x,y) |-> x+y" should "be y+y" in {
    val s = create(SubstitutionPair("x()".asTerm, "y".asTerm))
    s("x()+y".asTerm) should be ("y+y".asTerm)
  }

  "Uniform substitution of (x,y)(y,x) |-> x-y" should "be y-x" in {
    val s = create(SubstitutionPair("x()".asTerm, "y".asTerm), SubstitutionPair("y()".asTerm, "x".asTerm))
    s("x()-y()".asTerm) should be ("y-x".asTerm)
  }

  "Uniform substitution of (x,y)(y,t) |-> x*y where {y} is bound" should "throw a SubstitutionClashException" in {
    val s = Substitution(List(SubstitutionPair("x()".asTerm, "y".asTerm), SubstitutionPair("y()".asTerm, "t".asTerm)))
    a [SubstitutionClashException] should be thrownBy applySubstitutionT(s, Set.empty, Set(V("y")),"x()*y".asTerm)
  }

  "Uniform substitution of (x,y)(y,x) |-> x/y where {y} is bound" should "not be permitted" in {
    val s = Substitution(List(SubstitutionPair("x()".asTerm, "y".asTerm), SubstitutionPair("y()".asTerm, "x".asTerm)))
    a [SubstitutionClashException] should be thrownBy applySubstitutionT(s, Set.empty, Set(V("y")),"x()/y".asTerm)
  }

  // f(\theta) apply on f

  "Uniform substitution of (x,y)(f(.),.+1) |-> f(x)" should "be y+1" in {
    val f = Function("f", None, Real, Real)
    val s = create(SubstitutionPair("x()".asTerm, "y".asTerm), SubstitutionPair(Apply(f, CDot), Add(Real, CDot, Number(1))))
    s(Apply(f, "x()".asTerm)) should be ("y+1".asTerm)
  }

  ignore /*"Uniform substitution f(x)"*/ should "be y+1 with (x,y)(f(x),x+1)" in {
    val f = Function("f", None, Real, Real)
    val s = create(SubstitutionPair("x".asTerm, "y".asTerm), SubstitutionPair(Apply(f, "x".asTerm), "x+1".asTerm))
    s(Apply(f, "x".asTerm)) should be ("y+1".asTerm)
  }

  ignore /*"Uniform substitution of f(x)"*/ should "be y+z+1 with (x,y+z)(f(x),x+1)" in {
    val f = Function("f", None, Real, Real)
    val s = create(SubstitutionPair("x".asTerm, "y+z".asTerm), SubstitutionPair(Apply(f, "x".asTerm), "x+1".asTerm))
    s(Apply(f, "x".asTerm)) should be ("y+z+1".asTerm)
  }
  "Uniform substitution of f(x)" should "be y+z+1 with (x,y+z)(f(.),.+1)" in {
    val f = Function("f", None, Real, Real)
    val s = create(SubstitutionPair("x()".asTerm, "y+z".asTerm), SubstitutionPair(Apply(f, CDot), Add(Real, CDot, "1".asTerm)))
    s(Apply(f, "x()".asTerm)) should be ("y+z+1".asTerm)
  }

  "Uniform substitution of (x,y)(f(.),.+x+1) |-> f(x)" should "be y+x+1" in {
    val f = Function("f", None, Real, Real)
    val s = create(SubstitutionPair("x()".asTerm, "y".asTerm),
      SubstitutionPair(Apply(f, CDot), Add(Real, Add(Real, CDot, "x".asTerm), Number(1))))
    s(Apply(f, "x()".asTerm)) should be ("y+x+1".asTerm)
  }

  ignore /*"Uniform substitution of f(x)"*/ should "be y+y+1 with (x,y)(f(x),x+x+1)" in {
    val f = Function("f", None, Real, Real)
    val s = create(SubstitutionPair("x()".asTerm, "y".asTerm),
      SubstitutionPair(Apply(f, "x()".asTerm), Add(Real, Add(Real, "x".asTerm, "x".asTerm), Number(1))))
    s(Apply(f, "x()".asTerm)) should be ("y+y+1".asTerm)
  }
  "Uniform substitution of f(x)" should "be y+y+1 with (x,y)(f(.),.+.+1)" in {
    val f = Function("f", None, Real, Real)
    val s = create(SubstitutionPair("x()".asTerm, "y".asTerm),
      SubstitutionPair(Apply(f, CDot), Add(Real, Add(Real, CDot, CDot), Number(1))))
    s(Apply(f, "x()".asTerm)) should be ("y+y+1".asTerm)
  }

  "Uniform substitution of  p(x)" should "be [x:=y+1;]x>0 with (x,y)(p(.),[x:=.+1;]x>0)" in {
    val p = Function("p", None, Real, Bool)
    val s = create(SubstitutionPair("x()".asTerm, "y".asTerm),
      SubstitutionPair(ApplyPredicate(p, CDot), BoxModality(Assign("x".asTerm,
        Add(Real, CDot, Number(1))), GreaterThan(Real, "x".asTerm, Number(0)))))
    s(ApplyPredicate(p, "x()".asTerm)) should be ("[x:=y+1;]x>0".asFormula)
  }

  ignore should "be [x:=y+1;]x>0 with (x,y)(p(x),[x:=x+1;]x>0)" in {
    val p = Function("p", None, Real, Bool)
    val s = create(SubstitutionPair("x".asTerm, "y".asTerm),
      SubstitutionPair(ApplyPredicate(p, "x".asTerm), BoxModality(Assign("x".asTerm,
        Add(Real, "x".asTerm, Number(1))), GreaterThan(Real, "x".asTerm, Number(0)))))
    s(ApplyPredicate(p, "x".asTerm)) should be ("[x:=y+1;]x>0".asFormula)
  }

  // g(\theta) apply on \theta

  "Uniform substitution of (x,1)(y,x) |-> g(x)" should "be g(1)" in {
    val g = Function("g", None, Real, Real)
    val s = create(SubstitutionPair("x()".asTerm, Number(1)), SubstitutionPair("y()".asTerm, "x".asTerm))
    s(Apply(g, "x()".asTerm)) should be (Apply(g, Number(1)))
  }

  "Uniform substitution of (x,1)(y,x) |-> g(x) where {x} is bound" should "not be permitted" in {
    val g = Function("g", None, Real, Bool)
    val s = Substitution(List(SubstitutionPair("y()".asTerm, "x".asTerm)))
    a [SubstitutionClashException] should be thrownBy applySubstitutionT(s, Set.empty, Set(V("x")), Apply(g, "y()".asTerm))
  }

  "Uniform substitution of (x,y)(y,x) |-> g(x)" should "be g(y)" in {
    val g = Function("g", None, Real, Bool)
    val s = create(SubstitutionPair("x()".asTerm, "y".asTerm), SubstitutionPair("y()".asTerm, "x".asTerm))
    s(Apply(g, "x()".asTerm)) should be (Apply(g, "y".asTerm))
  }

  "Uniform substitution of (x,y)(y,x) |-> f(x)=g(y)" should "be f(y)=g(x)" in {
    val f = Function("f", None, Real, Bool)
    val g = Function("g", None, Real, Bool)
    val s = create(SubstitutionPair("x()".asTerm, "y".asTerm), SubstitutionPair("y()".asTerm, "x".asTerm))
    s(Equals(Bool, Apply(f, "x()".asTerm), Apply(g, "y()".asTerm))) should be (
      Equals(Bool, Apply(f, "y".asTerm), Apply(g, "x".asTerm)))
  }

  // x substituable

  "Uniform substitution of (x,y) |-> x" should "be y" in {
    val s = create(SubstitutionPair("x()".asTerm, "y".asTerm))
    s("x()".asTerm) should be ("y".asTerm)
  }

  "Uniform substitution of (x,y) |-> x where {y} is bound" should "not be permitted" in {
    val s = Substitution(Seq(new SubstitutionPair("x()".asTerm, "y".asTerm)))
    a [SubstitutionClashException] should be thrownBy applySubstitutionT(s, Set.empty, Set(V("y")),"x()".asTerm)
  }

  "Uniform substitution of (x,y) |-> y" should "be y" in {
    val s = create(SubstitutionPair("x()".asTerm, "y".asTerm))
    s("y".asTerm) should be ("y".asTerm)
  }

  /**
   * ==================================================
   * tests for programs
   */

  // \alpha U \beta

  "Uniform substitution of (x,1) |-> x:=1 ++ x:=x+1 ++ z:=x;" should "be x:=1 ++ x:=1+1 ++ z:=1;" in {
    val s = Substitution(List(SubstitutionPair("x()".asTerm, "1".asTerm)))
    // TODO not yet supported, hence exception
    a [SubstitutionClashException] should be thrownBy s.apply("x:=1 ++ x:=x()+1 ++ z:=x()".asProgram) //should be ("x:=1 ++ x:=1+1 ++ z:=1;".asProgram)
//    applySubstitution(Set.empty, Set.empty,"x:=1 ++ x:=x+1 ++ z:=x".asProgram) should be (
//      Set.empty, Set(V("x"),V("z")), "x:=1 ++ x:=1+1 ++ z:=1;".asProgram)
  }

  // TODO not yet supported
  "Uniform substitution of (x,t) |-> x:=1 ++ x:=x+1 ++ z:=x;" should "be x:=1 ++ x:=t+1 ++ z:=t;" in {
    val s = Substitution(List(SubstitutionPair("x()".asTerm, "t".asTerm)))
    // TODO not yet supported, hence exception
    a [SubstitutionClashException] should be thrownBy s.apply("x:=1 ++ x:=x()+1 ++ z:=x()".asProgram) //should be ("x:=1 ++ x:=t+1 ++ z:=t;".asProgram)
//    applySubstitution(Set.empty, Set.empty, "x:=1 ++ x:=x+1 ++ z:=x".asProgram) should be (
//      Set.empty, Set(V("x"),V("z")),"x:=1 ++ x:=t+1 ++ z:=t;".asProgram)
  }

  "Uniform substitution of [a ++ b]p" should "throw a clash exception when a, b, and p are substituted simultaneously" in {
    val s = Substitution(List(SubstitutionPair(ProgramConstant("a"), "x:=2;".asProgram),
      SubstitutionPair(ProgramConstant("b"), "y:=3;".asProgram),
      SubstitutionPair(PredicateConstant("p"), "x*y>5".asFormula)))
    a [SubstitutionClashException] should be thrownBy
      s(BoxModality(Choice(ProgramConstant("a"), ProgramConstant("b")), PredicateConstant("p")))
  }

  it should "work when cascaded" in {
    val s = create(SubstitutionPair(ProgramConstant("a"), "x:=2;".asProgram),
      SubstitutionPair(ProgramConstant("b"), "y:=3;".asProgram))
    val t = create(SubstitutionPair(ApplyPredicate(Function("p", None, Real, Bool), Anything), "x*y>5".asFormula))

    s(t(BoxModality(Choice(ProgramConstant("a"), ProgramConstant("b")),
        ApplyPredicate(Function("p", None, Real, Bool), Anything)))) should be (
      "[x:=2 ++ y:=3]x*y>5".asFormula
    )
  }

  // \alpha ; \beta

  "Uniform substitution of (y,x+y) |-> x:=y;z:=x+y;" should "not be permitted" in {
    val s = create(SubstitutionPair("y()".asTerm, "x+y".asTerm))
    a [SubstitutionClashException] should be thrownBy s("x:=y(); z:=x+y();".asProgram)
  }

  "Uniform substitution of (x,1) |-> x:=x+1;z:=x;" should "be x:=1+1;z:=x;" in {
    val s = create(SubstitutionPair("x()".asTerm, "1".asTerm))
    s("x:=x()+1;z:=x;".asProgram) should be ("x:=1+1; z:=x;".asProgram)
  }

  "Uniform substitution of (x,1) |-> {x:=1 ++ x:=x+1 ++ z:=x};{x:=1 ++ x:=x+1 ++ z:=x};" should "be {x:=1 ++ x:=1+1 ++ z:=1};{x:=1 ++ x:=x+1 ++ z:=x};" in {
    val s = Substitution(Seq(new SubstitutionPair("x()".asTerm, "1".asTerm)))
    // TODO not yet supported, hence exception
    a [SubstitutionClashException] should be thrownBy s("{x:=1 ++ x:=x()+1 ++ z:=x()};{x:=1 ++ x:=x+1 ++ z:=x};".asProgram)// should be ("{x:=1 ++ x:=1+1 ++ z:=1};{x:=1 ++ x:=x+1 ++ z:=x};".asProgram)
    // TODO when supported, also add a case to O and U set of local substitution tests
  }

  // (\alpha)*

  "Uniform substitution of (x(),1)(y(),t) |-> {x:=x+y}*;" should "be {x:=x+y;}*" in {
    val s = create(SubstitutionPair("x()".asTerm, "1".asTerm), SubstitutionPair("y()".asTerm, "t".asTerm))
    s("{x:=x+y;}*".asProgram) should be ("{x:=x+y;}*".asProgram)
    s("{x:=x()+y();}*".asProgram) should be ("{x:=1+t;}*".asProgram)
  }

  // TODO test case for variable substitution
  ignore should "not be permitted" in {
    val s = create(SubstitutionPair("x".asTerm, "1".asTerm), SubstitutionPair("y".asTerm, "t".asTerm))
    a [SubstitutionClashException] should be thrownBy s("{x:=x+y;}*".asProgram)
  }

  "Uniform substitution of {x:=x+y}*;" should "not be permitted with (x(),1)(y(),x)" in {
    val s = create(SubstitutionPair("x()".asTerm, "1".asTerm), SubstitutionPair("y()".asTerm, "x".asTerm))
    a [SubstitutionClashException] should be thrownBy s("{x:=x()+y();}*".asProgram)
  }

  ignore should "not be permitted" in {
    val s = create(SubstitutionPair("x".asTerm, "1".asTerm), SubstitutionPair("y".asTerm, "x".asTerm))
    a [SubstitutionClashException] should be thrownBy s("{x:=x+y;}*".asProgram)
  }

  "Uniform substitution of (x,1) |-> {x:=1 ++ x:=x+1 ++ z:=x}*;" should "be {x:=1 ++ x:=x+1 ++ z:=x}*" in {
    val s = create(SubstitutionPair("x()".asTerm, "1".asTerm))
    // TODO not yet supported
    a [SubstitutionClashException] should be thrownBy s("{x:=1 ++ x:=x()+1 ++ z:=x()}*".asProgram) //should be ("{x:=1 ++ x:=x+1 ++ z:=x}*".asProgram)
  }

  // ?\psi

  "Uniform substitution of (x,1)(y,x) |-> ?x+y>0;" should "be ?1+x>0;" in {
    val s = create(SubstitutionPair("x()".asTerm, "1".asTerm), SubstitutionPair("y()".asTerm, "x".asTerm))
    s("?x()+y()>0;".asProgram) should be ("?1+x>0;".asProgram)
  }

  "Uniform substitution of (x,1)(y,x) |-> ?[x:=*;]x>0 -> y>0;" should "be ?[x:=*;]x>0 -> x>0;" in {
    val s = create(SubstitutionPair("x()".asTerm, "1".asTerm), SubstitutionPair("y()".asTerm, "x".asTerm))
    s("?[x:=*;]x>0 -> y()>0;".asProgram) should be ("?[x:=*;]x>0 -> x>0;".asProgram)
  }

  // x := \theta

  "Uniform substitution of (x,y) |-> t:=0;" should "be t:=0;" in {
    val s = create(SubstitutionPair("x()".asTerm, "y".asTerm))
    s("t:=0;".asProgram) should be ("t:=0;".asProgram)
  }

  "Uniform substitution of (x,1) |-> x:=x+y" should "be x:=1+y;" in {
    val s = create(SubstitutionPair("x()".asTerm, "1".asTerm))
    s("x:=x()+y;".asProgram) should be ("x:=1+y;".asProgram)
  }

  "Uniform substitution of (y,x+y) |-> x:=y" should "be x:=x+y;" in {
    val s = create(SubstitutionPair("y()".asTerm, "x+y".asTerm))
    s("x:=y();".asProgram) should be ("x:=x+y;".asProgram)
  }

  "Uniform substitution of (y,x+y) |-> z:=x+y;" should "be z:=x+x+y;" in {
    val s = Substitution(Seq(SubstitutionPair("y()".asTerm, "x+y".asTerm)))
    s("z:=x+y();".asProgram) should be ("z:=x+(x+y);".asProgram)
  }

  "Uniform substitution of (x,y)(y,x+y) |-> x:=y" should "be x:=x+y" in {
    val s = create(SubstitutionPair("x()".asTerm, "y".asTerm), SubstitutionPair("y()".asTerm, "x+y".asTerm))
    s("x:=y();".asProgram) should be ("x:=x+y;".asProgram)
  }

  // x' = \theta & \psi

  "Uniform substitution of (x,y) |-> t'=x; where {t} is bound" should "be t'=y;" in {
    val s = create(SubstitutionPair("x()".asTerm, "y".asTerm))
    s("t'=x();".asProgram) should be ("t'=y;".asProgram)
  }

  // TODO substitution of variables not yet supported
  ignore /*"Uniform substitution of (t,1)(x,y) |-> t'=x; where {t} is bound"*/ should "not be permitted" in {
    val s = Substitution(Seq(SubstitutionPair("t".asTerm, "1".asTerm), SubstitutionPair("x".asTerm, "y".asTerm)))
    a [SubstitutionClashException] should be thrownBy applySubstitution(s, Set.empty, Set(V("t")), "t'=x;".asProgram)
  }

  // TODO substitution of variables not yet supported
  ignore /*"Uniform substitution of t'=x;"*/ should "not be permitted with (t,1)(x,y)" in {
    val s = Substitution(Seq(SubstitutionPair("t".asTerm, "1".asTerm), SubstitutionPair("x".asTerm, "y".asTerm)))
    a [SubstitutionClashException] should be thrownBy applySubstitution(s, Set.empty, Set.empty, "t'=x;".asProgram)
  }

  "Uniform substitution of (x,y) |-> t'=x;" should "be t'=y;" in {
    val s = create(SubstitutionPair("x()".asTerm, "y".asTerm))
    s("t'=x();".asProgram) should be  ("t'=y;".asProgram)
  }

  "Uniform substitution of (x,t) |-> t'=x;" should "not be permitted" in {
    val s = create(SubstitutionPair("x()".asTerm, "t".asTerm))
    a [SubstitutionClashException] should be thrownBy s("t'=x();".asProgram)
  }

  "Uniform substitution of (x,y) |-> t'=x & x*y+t+1>0; where {t} is bound" should "be t'=y & y*y+t+1>0;" in {
    val s = create(SubstitutionPair("x()".asTerm, "y".asTerm))
    s("t'=x() & x()*y+t+1>0;".asProgram) should be ("t'=y & y*y+t+1>0;".asProgram)
  }

  // TODO substitution of variables not yet supported
  ignore /*"Uniform substitution of (t,1)(x,y) |-> t'=x & x*y+t+1>0; where {t} is bound"*/ should "not be permitted" in {
    val s = Substitution(Seq(SubstitutionPair("t".asTerm, "1".asTerm), SubstitutionPair("x()".asTerm, "y".asTerm)))
    a [SubstitutionClashException] should be thrownBy applySubstitution(s, Set.empty, Set(V("t")), "t'=x() & x()*y+t+1>0;".asProgram)
  }

  ignore /*"Uniform substitution of (t,1)(x,y) |-> t'=x & x*y+t+1>0;"*/ should "be t'=y & y*y+t+1>0 when {t} is must-bound" in {
    val s = Substitution(Seq(SubstitutionPair("t".asTerm, "1".asTerm), SubstitutionPair("x()".asTerm, "y".asTerm)))
    applySubstitution(s, Set(V("t")), Set(V("t")), "t'=x() & x()*y+t+1>0;".asProgram) should be (Set(V("t")), Set(V("t")),"t'=y & y*y+t+1>0;".asProgram)
  }

  // TODO substitution of variables not yet supported
  ignore /*"Uniform substitution of (t,1)(x,y) |-> t'=x & x*y+t+1>0;"*/ should "not be permitted 2" in {
    val s = Substitution(Seq(SubstitutionPair("t".asTerm, "1".asTerm), SubstitutionPair("x()".asTerm, "y".asTerm)))
    a [SubstitutionClashException] should be thrownBy applySubstitution(s, Set.empty, Set.empty, "t'=x() & x()*y+t+1>0;".asProgram)
  }

  "Uniform substitution of (x,y) |-> t'=x & x*y+t+1>0;" should "be t'=y & y*y+t+1>0;" in {
    val s = create(SubstitutionPair("x()".asTerm, "y".asTerm))
    s("t'=x() & x()*y+t+1>0;".asProgram) should be ("t'=y & y*y+t+1>0;".asProgram)
  }

  "Uniform substitution of (x,t) |-> t'=x & x*y+t+1>0;" should "not be permitted" in {
    val s = create(SubstitutionPair("x()".asTerm, "t".asTerm))
    a [SubstitutionClashException] should be thrownBy s("t'=x() & x()*y+t+1>0;".asProgram)
  }

  "Uniform substitution of (x,t) |-> [x:=5;x'=y,y'=x & x*y>0;]1>0" should "be [x:=5;x'=y,y'=x & x*y>0;]1>0" in {
    val s = create(SubstitutionPair("x()".asTerm, "t".asTerm))
    s("[x:=5;x'=y,y'=x & x*y>0;]1>0".asFormula) should be ("[x:=5;x'=y,y'=x & x*y>0;]1>0".asFormula)
  }

  // TODO substitution of variables not yet supported
  ignore should "be [x:=5;x'=y,y'=x & x*y>0;]1>0 (the same)" in {
    val s = create(SubstitutionPair("x".asTerm, "t".asTerm))
    s("[x:=5;x'=y,y'=x & x*y>0;]1>0".asFormula) should be ("[x:=5;x'=y,y'=x & x*y>0;]1>0".asFormula)
  }

  ignore /*"Uniform substitution of (x,t) |-> [x'=y,y'=x & x*y>0;]1>0"*/ should "not be permitted" in {
    val s = create(SubstitutionPair("x".asTerm, "t".asTerm))
    // x not must-bound when substituting
    a [SubstitutionClashException] should be thrownBy s("[x'=y,y'=x & x*y>0;]1>0".asFormula)
    a [SubstitutionClashException] should be thrownBy s("[{x:=1 ++ y:=2};x'=y,y'=x & x*y>0;]1>0".asFormula)
  }

  /**
   * ==================================================
   * tests for formulas
   */

  // \phi and/or \psi

  "Uniform substitution of (x,y)(y,x+y) |-> x>y & x<=y+1 " should "be y>x+y & y<=x+y+1" in {
    val s = create(SubstitutionPair("x()".asTerm, "y".asTerm), SubstitutionPair("y()".asTerm, "x+y".asTerm))
    s("x()>y() & x()<=y()+1".asFormula) should be ("y>x+y & y<=x+y+1".asFormula)
  }

  // \forall x. \phi

  "Uniform substitution of (x,y)(y,y+1) |-> \\forall x. x>y" should "be forall x. x>y+1" in {
    val s = create(SubstitutionPair("x()".asTerm, "y".asTerm), SubstitutionPair("y()".asTerm, "y+1".asTerm))
    s("\\forall x. x>y()".asFormula) should be ("\\forall x. x>y+1".asFormula)
  }

  // TODO variable substitution not yet supported
  ignore should "be forall x. x>y+1 (the same)" in {
    val s = create(SubstitutionPair("x".asTerm, "y".asTerm), SubstitutionPair("y".asTerm, "y+1".asTerm))
    s("\\forall x. x>y".asFormula) should be ("\\forall x. x>y+1".asFormula)
  }

  "Uniform substitution of (x(),y)(y(),y+1) |-> \\forall x. x()>y() | x()<=y()+1" should "be forall x. y>y+1 | y<=y+1+1" in {
    val s = create(SubstitutionPair("x()".asTerm, "y".asTerm), SubstitutionPair("y()".asTerm, "y+1".asTerm))
    s("\\forall x. x()>y() | x()<=y()+1".asFormula) should be ("\\forall x. y>y+1 | y<=y+1+1".asFormula)
  }

  // TODO variable substitution not yet supported
  ignore should "be forall x. x>y+1 | y<=y+1+1" in {
    val s = create(SubstitutionPair("x".asTerm, "y".asTerm), SubstitutionPair("y".asTerm, "y+1".asTerm))
    s("\\forall x. x>y | x<=y+1".asFormula) should be ("\\forall x. y>y+1 | y<=y+1+1".asFormula)
  }

  "Uniform substitution of (x,y)(y,x+y) |-> \\forall x. x>y | x<=y+1" should "not be permitted" in {
    val s = create(SubstitutionPair("y()".asTerm, "x+y".asTerm))
    a [SubstitutionClashException] should be thrownBy s("\\forall x. x>y() | x<=y()+1".asFormula)
  }

  // \exists x. \phi

  "Uniform substitution of (x,y)(y,y+1) |-> \\exists x. x>y" should "be exists x. y>y+1" in {
    val s = create(SubstitutionPair("x()".asTerm, "y".asTerm), SubstitutionPair("y()".asTerm, "y+1".asTerm))
    s("\\exists x. x()>y()".asFormula) should be ("\\exists x. y>y+1".asFormula)
    s("\\exists x. x>y()".asFormula) should be ("\\exists x. x>y+1".asFormula)
  }

  ignore /*"Uniform substitution of (x,y)(y,y+1) |-> \\exists x. x>y"*/ should "be exists x. x>y+1" in {
    val s = create(SubstitutionPair("x".asTerm, "y".asTerm), SubstitutionPair("y".asTerm, "y+1".asTerm))
    s("\\exists x. x>y".asFormula) should be ("\\exists x. x>y+1".asFormula)
  }

  "Uniform substitution of (x,y)(y,y+1) |-> \\exists x. x>y -> x<=y+1" should "be exists x. y>y+1 -> y<=y+1+1" in {
    val s = create(SubstitutionPair("x()".asTerm, "y".asTerm), SubstitutionPair("y()".asTerm, "y+1".asTerm))
    s("\\exists x. x()>y() -> x()<=y()+1".asFormula) should be ("\\exists x. y>y+1 -> y<=y+1+1".asFormula)
    s("\\exists x. x>y() -> x()<=y()+1".asFormula) should be ("\\exists x. x>y+1 -> y<=y+1+1".asFormula)
    s("\\exists x. x>y() -> x<=y()+1".asFormula) should be ("\\exists x. x>y+1 -> x<=y+1+1".asFormula)
  }

  ignore /*"Uniform substitution of (x,y)(y,y+1) |-> \\exists x. x>y -> x<=y+1"*/ should "be exists x. x>y+1 -> y<=y+1+1" in {
    val s = create(SubstitutionPair("x".asTerm, "y".asTerm), SubstitutionPair("y".asTerm, "y+1".asTerm))
    s("\\exists x. x>y -> x<=y+1".asFormula) should be ("\\exists x. x>y+1 -> y<=y+1+1".asFormula)
  }

  "Uniform substitution of (y,x+y) |-> \\exists x. x>y -> x<=y+1" should "not be permitted" in {
    val s = create(SubstitutionPair("y()".asTerm, "x+y".asTerm))
    a [SubstitutionClashException] should be thrownBy s("\\exists x. x>y() -> x<=y()+1".asFormula)
  }

  // p(\theta) apply on p

  "Uniform substitution of (x,y)(p(t),t<1) |-> p(x)" should "be y<1" in {
    val p = Function("p", None, Real, Bool)
    val s = create(SubstitutionPair("x()".asTerm, "y".asTerm), SubstitutionPair(ApplyPredicate(p, CDot), LessThan(Real, CDot, Number(1))))
    s(ApplyPredicate(p, "x()".asTerm)) should be ("y<1".asFormula)
  }

  "Uniform substitution of (x,y)(p(t),t>x) |-> p(x)" should "be y>x" in {
    val p = Function("p", None, Real, Bool)
    val s = create(SubstitutionPair("x()".asTerm, "y".asTerm), SubstitutionPair(ApplyPredicate(p, CDot), GreaterThan(Real, CDot, "x".asTerm)))
    s(ApplyPredicate(p, "x()".asTerm)) should be ("y>x".asFormula)
  }

  // q(\theta) apply on \theta

  "Uniform substitution of (x,1)(y,x) |-> q(x)" should "be q(1)" in {
    val q = Function("q", None, Real, Bool)
    val s = create(SubstitutionPair("x()".asTerm, Number(1)), SubstitutionPair("y()".asTerm, "x".asTerm))
    s(ApplyPredicate(q, "x()".asTerm)) should be (ApplyPredicate(q, Number(1)))
  }

  "Uniform substitution of (x,y)(y,x) |-> q(x)" should "be q(y)" in {
    val q = Function("q", None, Real, Bool)
    val s = create(SubstitutionPair("x()".asTerm, "y".asTerm), SubstitutionPair("y()".asTerm, "x".asTerm))
    s(ApplyPredicate(q, "x()".asTerm)) should be (ApplyPredicate(q, "y".asTerm))
  }

  "Uniform substitution of (x,y)(y,x) |-> p(x)=q(y)" should "be p(y)=q(x)" in {
    val p = Function("p", None, Real, Bool)
    val q = Function("q", None, Real, Bool)
    val s = create(SubstitutionPair("x()".asTerm, "y".asTerm), SubstitutionPair("y()".asTerm, "x".asTerm))
    s(Equals(Bool,Apply(p, "x()".asTerm), Apply(q, "y()".asTerm))) should be (Equals(Bool,Apply(p,"y".asTerm), Apply(q,"x".asTerm)))
  }

  // \theta =/>/< \eta

  "Uniform substitution of (x,1) |-> x=y" should "be 1=y" in {
    val s = create(SubstitutionPair("x()".asTerm, "1".asTerm))
    s("x()=y".asFormula) should be ("1=y".asFormula)
  }

  "Uniform substitution of (x,y) |-> x=y" should "be y=y" in {
    val s = create(SubstitutionPair("x()".asTerm, "y".asTerm))
    s("x()=y".asFormula) should be ("y=y".asFormula)
  }

  "Uniform substitution of (y,x+y) |-> z=x+y" should "be z=x+x+y" in {
    val s = create(SubstitutionPair("y()".asTerm, "x+y".asTerm))
    s("z=x+y()".asFormula) should be ("z=x+(x+y)".asFormula)
  }

  "Uniform substitution of (x,y)(y,x+y) |-> x=y" should "be y=x+y" in {
    val s = create(SubstitutionPair("x()".asTerm, "y".asTerm), SubstitutionPair("y()".asTerm, "x+y".asTerm))
    s("x()=y()".asFormula) should be ("y=x+y".asFormula)
  }

  // [\alpha]\phi

  "Uniform substitution of (x,1) |-> [y:=x;]x>0" should "be [y:=1;]1>0" in {
    val s = create(SubstitutionPair("x()".asTerm, "1".asTerm))
    s("[y:=x();]x()>0".asFormula) should be ("[y:=1;]1>0".asFormula)
    s("[y:=x();]x>0".asFormula) should be ("[y:=1;]x>0".asFormula)
  }

  "Uniform substitution of (x,1) |-> [x:=y;]x>0" should "be [x:=y;]x>0" in {
    val s = create(SubstitutionPair("x()".asTerm, "1".asTerm))
    s("[x:=y;]x()>0".asFormula) should be ("[x:=y;]1>0".asFormula)
    s("[x:=y;]x>0".asFormula) should be ("[x:=y;]x>0".asFormula)
  }

  // TODO variable substitution not yet supported
  ignore /*"Uniform substitution of (x,t) |-> [{x:=x+y;}*]x>0"*/ should "not be permitted" in {
    val s = create(SubstitutionPair("x".asTerm, "t".asTerm))
    a [SubstitutionClashException] should be thrownBy s("[{x:=x+y;}*]x>0".asFormula)
  }

  // TODO variable substitution not yet supported
  ignore /*"Uniform substitution of (x,t) |-> [{x'=x+y;}*]x>0"*/ should "not be permitted either" in {
    val s = create(new SubstitutionPair("x".asTerm, "t".asTerm))
    a [SubstitutionClashException] should be thrownBy s("[{x'=x+y;}*]x>0".asFormula)
  }

  // TODO variable substitution not yet supported
  ignore /*"Uniform substitution of (x,1) |-> [x'=y;]x>0"*/ should "not be permitted 3" in {
    val s = create(SubstitutionPair("x".asTerm, "1".asTerm))
    a [SubstitutionClashException] should be thrownBy s("[x'=y;]x>0".asFormula)
  }

  "Uniform substitution of (x,t) |-> [x:=1 ++ x:=x+1 ++ z:=x;]x>0" should "be [x:=1 ++ x:=t+1 ++ z:=t;]x>0" in {
    val s = create(SubstitutionPair("x()".asTerm, "t".asTerm))
    // TODO not yet supported, hence exception
    a [SubstitutionClashException] should be thrownBy s("[x:=1 ++ x:=x()+1 ++ z:=x()]x()>0".asFormula)// should be ("[x:=1 ++ x:=t+1 ++ z:=t;]x>0".asFormula)
  }

  // <\alpha>\phi

  "Uniform substitution of (x,1) |-> <y:=x;>x>0" should "be <y:=1;>1>0" in {
    val s = create(SubstitutionPair("x()".asTerm, "1".asTerm))
    s("<y:=x();>x()>0".asFormula) should be ("<y:=1;>1>0".asFormula)
  }

  "Uniform substitution of (x,1) |-> <x:=y;>x>0" should "be <x:=y;>x>0" in {
    val s = create(SubstitutionPair("x()".asTerm, "1".asTerm))
    s("<x:=y;>x>0".asFormula) should be ("<x:=y;>x>0".asFormula)
    s("<x:=y;>x()>0".asFormula) should be ("<x:=y;>1>0".asFormula)
  }

  // TODO variable substitution not yet supported
  ignore /*"Uniform substitution of (x,1) |-> <x'=y;>x>0"*/ should "not be permitted" in {
    val s = create(SubstitutionPair("x".asTerm, "1".asTerm))
    a [SubstitutionClashException] should be thrownBy s("<x'=y;>x>0".asFormula)
  }

  /**
   * ==================================================
   * tests for complicated cases
   */

  "Uniform substitution of (x,y) |-> t:=0;t'=x;" should "be t:=0;t'=y;" in {
    val s = create(SubstitutionPair("x()".asTerm, "y".asTerm))
    s("[t:=0;t'=x();]true".asFormula) should be ("[t:=0;t'=y;]true".asFormula)
    s("[t:=0;][t'=x();]true".asFormula) should be ("[t:=0;][t'=y;]true".asFormula)
  }

  // TODO variable substitution not yet supported
  ignore /*"Uniform substitution of (t,y) |-> t:=0;t'=x;"*/ should "be t:=0;t'=x;" in {
    val s = create(SubstitutionPair("t".asTerm, "y".asTerm))
    s("[t:=0;t'=x;]true".asFormula) should be ("[t:=0;t'=x;]true".asFormula)
    s("[t:=0;][t'=x;]true".asFormula) should be ("[t:=0;][t'=x;]true".asFormula)
  }

  "Uniform substitution of (x,y) |-> (y,x+y) |-> x=y" should "be y=y+y" in {
    val s = create(SubstitutionPair("x()".asTerm, "y".asTerm))
    val s1 = create(SubstitutionPair("y()".asTerm, "x()+y".asTerm))
    s(s1("x()=y()".asFormula)) should be ("y=y+y".asFormula)
  }

  "Uniform substitution of (x,y) |-> (y,x+y) |-> x:=y" should "be x:=y+y" in {
    val s = create(SubstitutionPair("x()".asTerm, "y".asTerm))
    val s1 = create(SubstitutionPair("y()".asTerm, "x()+y".asTerm))
    s(s1("x:=y();".asProgram)) should be ("x:=y+y;".asProgram)
  }

  /**
   * ==================================================
   * tests for the cases that are forbidden
   */

  // TODO variable substitution not yet supported
  ignore /*"Uniform substitution of [y:=1][y:=2+y;]true"*/ should "not perform \\alpha renaming" in {
    val s = create(SubstitutionPair("y".asTerm, "y0".asTerm))
    s("\\forall y. (y=1 -> [y:=2+y;]true)".asFormula) should not be "\\forall y0. (y0=1 -> [y0:=2+y0;]true)".asFormula
    s("\\forall y. (y=1 -> [y:=2+y;]true)".asFormula) should be ("\\forall y. (y=1 -> [y:=2+y;]true)".asFormula)
  }

  // TODO variable substitution not yet supported
  ignore /*"Uniform substitution of [{x:=x+1;}*;]true"*/ should "not be permitted" in {
    val s = create(SubstitutionPair("x".asTerm, "y".asTerm))
    a [SubstitutionClashException] should be thrownBy s("[{x:=x+1;}*;]true".asFormula)
  }

  "Uniform substitution of [y:=t;]p(y) <-> p(t)" should "[y:=t;]y>0 <-> z>0" in {
    def p(x: Term) = ApplyPredicate(Function("p", None, Real, Bool), x)
    val s = create(SubstitutionPair("t()".asTerm, "z".asTerm),
      SubstitutionPair(p(CDot), GreaterThan(Real, CDot, Number(0))))

    // [x:=t;]p(x) <-> p(t)
    val o = Equiv(BoxModality("y:=t();".asProgram, p("y".asTerm)), p("t()".asTerm))
    s(o) should be ("[y:=z;]y>0 <-> z>0".asFormula)
  }

  "Uniform substitution (p(.) |-> .>0),z |-> 2) of [x:=2y+1;]p(3x+z)" should "[x:=2y+1;]3x+2>0" in {
    def p(x: Term) = ApplyPredicate(Function("p", None, Real, Bool), x)
    val s = create(SubstitutionPair("z()".asTerm, "2".asTerm),
      SubstitutionPair(p(CDot), GreaterThan(Real, CDot, Number(0))))

    // [x:=2y+1;]p(3x+z)
    val o = BoxModality("x:=2*y+1;".asProgram, p("3*x+z()".asTerm))
    s(o) should be ("[x:=2*y+1;]3*x+2>0".asFormula)
  }

  "Uniform substitution (p(.) |-> .>0),z |-> x+2) of [x:=2y+1;]p(3x+z)" should "throw a clash exception" in {
    def p(x: Term) = ApplyPredicate(Function("p", None, Real, Bool), x)
    val s = create(SubstitutionPair("z()".asTerm, "2+x".asTerm),
      SubstitutionPair(p(CDot), GreaterThan(Real, CDot, Number(0))))

    // [x:=2y+1;]p(3x+z)
    val o = BoxModality("x:=2*y+1;".asProgram, p("3*x+z()".asTerm))
    a [SubstitutionClashException] should be thrownBy  s(o)
  }

  // TODO variable substitution not yet supported
  ignore /*"Uniform substitution (x |-> 9) of x=9 -> [x'=x;]x>=0"*/ should "throw a clash exception too" in {
    val s = create(SubstitutionPair("x".asTerm, "9".asTerm))
    val o = "x=9 -> [x'=x;]x>=0".asFormula
    a [SubstitutionClashException] should be thrownBy s(o)
  }

//  "Uniform substitution of p(x)"
  ignore should "alpha rename x to any other variable in modalities" in {
    val s = create(SubstitutionPair(ApplyPredicate(Function("p", None, Real, Bool), "x".asTerm),
      "[x:=2;]x>5".asFormula))
    s(ApplyPredicate(Function("p", None, Real, Bool), "y".asTerm)) should be ("[y:=2;]y>5".asFormula)
    val t = create(SubstitutionPair(ApplyPredicate(Function("p", None, Real, Bool), "x".asTerm),
      "[x:=y;][x:=z;]x>5".asFormula))
    t(ApplyPredicate(Function("p", None, Real, Bool), "y".asTerm)) should be ("[y:=z;]y>5".asFormula)
    val u = create(SubstitutionPair(ApplyPredicate(Function("p", None, Real, Bool), "x".asTerm),
      "[x:=y;][x:=z;][{x:=x+1;}*;]x>5".asFormula))
    u(ApplyPredicate(Function("p", None, Real, Bool), "y".asTerm)) should be ("[y:=z;][{y:=y+1;}*;]y>5".asFormula)

    val v = create(SubstitutionPair(ApplyPredicate(Function("p", None, Real, Bool), "x".asTerm),
      "<x:=2;>x>5".asFormula))
    v(ApplyPredicate(Function("p", None, Real, Bool), "y".asTerm)) should be ("<y:=2;>y>5".asFormula)
  }

  ignore should "not alpha rename to arbitrary terms in modalities" in {
    val s = create(SubstitutionPair(ApplyPredicate(Function("p", None, Real, Bool), "x".asTerm),
      "[x:=2;]true".asFormula))

    val o = ApplyPredicate(Function("p", None, Real, Bool), "a+1".asTerm)
    s(o) should be ("[x:=2;]true".asFormula)
    s(o) should not be "[(a+1):=2;]true".asFormula
  }

  ignore should "substitute to arbitrary terms in simple formulas" in {
    val s = create(SubstitutionPair(ApplyPredicate(Function("p", None, Real, Bool), "x".asTerm), "x>5".asFormula))
    s(ApplyPredicate(Function("p", None, Real, Bool), "a+1".asTerm)) should be ("a+1>5".asFormula)
  }

  ignore should "not rename bound variables before substitution except in modalities" in {
    val s = create(SubstitutionPair(ApplyPredicate(Function("p", None, Real, Bool), "x".asTerm),
      "\\forall x. (x = 1 -> [x:=x+2;]x>0)".asFormula))
    s(ApplyPredicate(Function("p", None, Real, Bool), "y".asTerm)) should be ("\\forall x. (x = 1 -> [x:=x+2;]x>0)".asFormula)

    val t = create(SubstitutionPair(ApplyPredicate(Function("p", None, Real, Bool), "x".asTerm),
      "\\exists x. (x = 1 -> [x:=x+2;]x>0)".asFormula))
    t(ApplyPredicate(Function("p", None, Real, Bool), "y".asTerm)) should be ("\\exists x. (x = 1 -> [x:=x+2;]x>0)".asFormula)
  }

  "Uniform substitution of (p,x>5) on p & y!=1" should "substitute predicate constants" in {
    val s = create(SubstitutionPair(PredicateConstant("p"), "x>5".asFormula))
    s(And(PredicateConstant("p"), "y!=1".asFormula)) should be ("x>5 & y!=1".asFormula)
  }

  it should "not be permitted to substitute predicate constants with bound names" in {
    val s = create(SubstitutionPair(PredicateConstant("p"), "x>5".asFormula))
    a [SubstitutionClashException] should be thrownBy s(Forall("x".asNamedSymbol::Nil, PredicateConstant("p")))
    a [SubstitutionClashException] should be thrownBy s(BoxModality("x:=1 ++ y:=3".asProgram, PredicateConstant("p")))
  }

  "Uniform substitution of predicates in \\forall x. (p(x) | q) <-> (\\forall x. p(x)) | q" should "be allowed" in {
    val s = create(
      SubstitutionPair(ApplyPredicate(Function("p", None, Real, Bool), CDot), GreaterThan(Real, CDot, Number(0))),
      SubstitutionPair(PredicateConstant("q"), "y>5".asFormula))
    // \forall x. (p(x) | q) <-> (\forall x. p(x)) | q
    val f = Equiv(
      Forall("x".asNamedSymbol::Nil, Or(ApplyPredicate(Function("p", None, Real, Bool), "x".asTerm), PredicateConstant("q"))),
      Or(Forall("x".asNamedSymbol::Nil, ApplyPredicate(Function("p", None, Real, Bool), "x".asTerm)), PredicateConstant("q")))
    s(f) should be ("\\forall x. (x>0 | y>5) <-> (\\forall x. x>0) | y>5".asFormula)

    val t = create(
      SubstitutionPair(ApplyPredicate(Function("p", None, Real, Bool), CDot), "z>0".asFormula),
      SubstitutionPair(PredicateConstant("q"), "y>5".asFormula))
    t(f) should be ("\\forall x. (z>0 | y>5) <-> (\\forall x. z>0) | y>5".asFormula)
  }

  it should "not be permitted" in {
    val s = create(
      SubstitutionPair(ApplyPredicate(Function("p", None, Real, Bool), CDot), GreaterThan(Real, CDot, Number(0))),
      SubstitutionPair(PredicateConstant("q"), "x>5".asFormula))
    // \forall x. (p(x) | q)
    val f = Forall("x".asNamedSymbol::Nil, Or(ApplyPredicate(Function("p", None, Real, Bool), "x".asTerm), PredicateConstant("q")))
    a [SubstitutionClashException] should be thrownBy s(f)
    // \forall x. (p(x) | q) <-> (\forall x. p(x)) | q
    val h = Equiv(
      Forall("x".asNamedSymbol::Nil, Or(ApplyPredicate(Function("p", None, Real, Bool), "x".asTerm), PredicateConstant("q"))),
      Or(Forall("x".asNamedSymbol::Nil, ApplyPredicate(Function("p", None, Real, Bool), "x".asTerm)), PredicateConstant("q")))
    a [SubstitutionClashException] should be thrownBy s(h)

    val t = create(
      SubstitutionPair(ApplyPredicate(Function("p", None, Real, Bool), CDot), "z>0".asFormula),
      SubstitutionPair(PredicateConstant("q"), "x>5".asFormula))
    a [SubstitutionClashException] should be thrownBy t(f)
    a [SubstitutionClashException] should be thrownBy t(h)
  }

  "Uniform substitution in converse-Barcan " should "be allowed" in {
    val s = create(
      SubstitutionPair(ApplyPredicate(Function("p", None, Real, Bool), CDot), GreaterThan(Real, CDot, Number(0))),
      SubstitutionPair(ProgramConstant("a"), "y:=5;".asProgram))

    //([a;] \forall x. p(x)) -> \forall x. [a;] p(x)
    val f = Imply(
      BoxModality(ProgramConstant("a"), Forall("x".asNamedSymbol::Nil, ApplyPredicate(Function("p", None, Real, Bool), "x".asTerm))),
      Forall("x".asNamedSymbol::Nil, BoxModality(ProgramConstant("a"), ApplyPredicate(Function("p", None, Real, Bool), "x".asTerm)))
    )
    s(f) should be ("[y:=5;]\\forall x. x>0 -> \\forall x. [y:=5;]x>0".asFormula)
  }

  // TODO not yet implemented correctly -> substitution will succeed
  ignore should "not be permitted" in {
    //([a;] \forall x. p(x)) -> \forall x. [a;] p(x)
    val f = Imply(
      BoxModality(ProgramConstant("a"), Forall("x".asNamedSymbol::Nil, ApplyPredicate(Function("p", None, Real, Bool), "x".asTerm))),
      Forall("x".asNamedSymbol::Nil, BoxModality(ProgramConstant("a"), ApplyPredicate(Function("p", None, Real, Bool), "x".asTerm)))
    )

    val s = create(
      SubstitutionPair(ApplyPredicate(Function("p", None, Real, Bool), CDot), GreaterThan(Real, CDot, Number(0))),
      SubstitutionPair(ProgramConstant("a"), "x:=5;".asProgram))

    a [SubstitutionClashException] should be thrownBy s(f)
  }

  it should "not be permitted to replace [a;] with a program that contains free x" in {
    //([a;] \forall x. p(x)) -> \forall x. [a;] p(x)
    val h = Imply(
      BoxModality(ProgramConstant("a"), Forall("x".asNamedSymbol::Nil, ApplyPredicate(Function("p", None, Real, Bool), "x".asTerm))),
      Forall("x".asNamedSymbol::Nil, BoxModality(ProgramConstant("a"), ApplyPredicate(Function("p", None, Real, Bool), "x".asTerm)))
    )

    val s = create(
      SubstitutionPair(ApplyPredicate(Function("p", None, Real, Bool), CDot), GreaterThan(Real, CDot, Number(0))),
      SubstitutionPair(ProgramConstant("a"), "y:=x;".asProgram))
    a [SubstitutionClashException] should be thrownBy s(h)
  }

  "Uniform substitution in vacuous quantification" should "work when FV(p) is disjoint from newly quantified variable x" in {
    val f = Equiv(PredicateConstant("p"), Forall("x".asNamedSymbol::Nil, PredicateConstant("p")))

    val s = create(SubstitutionPair(PredicateConstant("p"), "y>0".asFormula))
    s(f) should be ("y>0 <-> \\forall x. y>0".asFormula)

    val h = Equiv(PredicateConstant("p"), Exists("x".asNamedSymbol::Nil, PredicateConstant("p")))
    s(h) should be ("y>0 <-> \\exists x. y>0".asFormula)

    val t = create(SubstitutionPair(PredicateConstant("p"), "[x:=5;]x>0".asFormula))
    t(f) should be ("[x:=5;]x>0 <-> \\forall x. [x:=5;]x>0".asFormula)
    t(h) should be ("[x:=5;]x>0 <-> \\exists x. [x:=5;]x>0".asFormula)
  }

  it should "not be permitted on p->[a]p with FV(p) not being disjoint from newly quantified variable x" in {
    val f = Equiv(PredicateConstant("p"), Forall("x".asNamedSymbol::Nil, PredicateConstant("p")))

    val s = create(SubstitutionPair(PredicateConstant("p"), "[y:=x;]y>0".asFormula))
    a [SubstitutionClashException] should be thrownBy s(f)

    val h = Equiv(PredicateConstant("p"), Exists("x".asNamedSymbol::Nil, PredicateConstant("p")))
    a [SubstitutionClashException] should be thrownBy s(h)

    val t = create(SubstitutionPair(PredicateConstant("p"), "x>0".asFormula))
    a [SubstitutionClashException] should be thrownBy t(f)
    a [SubstitutionClashException] should be thrownBy t(h)
  }

  "Uniform substitution in vacuous assignment [v:=t]p <-> p" should "work with FV(p) being disjoint from newly assigned variable v" in {
    val f = Equiv(BoxModality(Assign("v".asTerm, "t".asTerm), PredicateConstant("p")), PredicateConstant("p"))

    val s = create(SubstitutionPair(PredicateConstant("p"), "y>0".asFormula))
    s(f) should be ("[v:=t;]y>0 <-> y>0".asFormula)

    val t = create(SubstitutionPair(PredicateConstant("p"), "[x:=y;]x>0".asFormula))
    t(f) should be ("[v:=t;][x:=y;]x>0 <-> [x:=y;]x>0".asFormula)

    val h = Equiv(DiamondModality(Assign("v".asTerm, "t".asTerm), PredicateConstant("p")), PredicateConstant("p"))
    s(h) should be ("<v:=t;>y>0 <-> y>0".asFormula)
    t(h) should be ("<v:=t;>[x:=y;]x>0 <-> [x:=y;]x>0".asFormula)
  }

  it should "not be permitted with FV(p) not being disjoint from newly assigned variable v" in {
    val f = Equiv(BoxModality(Assign("v".asTerm, "t".asTerm), PredicateConstant("p")), PredicateConstant("p"))

    val s = create(SubstitutionPair(PredicateConstant("p"), "v>0".asFormula))
    a [SubstitutionClashException] should be thrownBy s(f)

    val h = Equiv(DiamondModality(Assign("v".asTerm, "t".asTerm), PredicateConstant("p")), PredicateConstant("p"))
    a [SubstitutionClashException] should be thrownBy s(h)
  }

  /*
   * Andre's tests
   */
  def sToT(s: String, t: String) = create(SubstitutionPair(s.asTerm, t.asTerm))

  "Substitution clash" should "be reported on substitution of (maybe) bound variables" in {
    def rndSubstDefs(max: Int) = {
      val rnd = new Random()
      val numSubsts = rnd.nextInt(max)
      val names = new RandomFormula(rnd).nextNames("lhs", numSubsts).map(v => Apply(Function(v.name, v.index, Unit, Real), Nothing))
      names.map(SubstitutionPair(_, rndTerm(rnd.nextInt(10), rnd)))
    }
    def rndTerm(size: Int, rnd: Random = new Random()) = {
      val rndF = new RandomFormula(rnd)
      rndF.nextT(rndF.nextNames("rhs", size/3+1), size)
    }

    def rndExtensionOf(s: SubstitutionTester) = create(new Random().shuffle(s.subsDefs ++ rndSubstDefs(5)): _*)

    // TODO variable substitution not yet supported (commented cases), all current cases should work for variables too
    val cases =
//      (sToT("x", "5"), "[{x:=0 ++ z:=z}; a:=x;]1>0".asFormula) ::         // subst(a:=x): x (maybe) bound by {x:=0 ++ ...}
      (sToT("b()", "z+1"), "[{x:=0 ++ z:=z}; a:=b();]1>0".asFormula) ::       // subst(a:=b): z free in z+1 but (maybe) bound by {... ++ z:=z}
//      (sToT("x", "5"), "[x:=0 ++ z:=z]x>0".asFormula) ::                  // subst(x>0): x (maybe) bound by {x:=0 ++ ...}
//      (sToT("z", "1"), "[x:=x+1 ++ x:=x+z;z:=z-1]x>z".asFormula) ::       // subst(x>z): z (maybe) bound by {... ++ z:=z+1}
      (sToT("z()", "2*x"), "[x:=x+1 ++ x:=x+z;z:=z()-1]x>0".asFormula) ::     // subst(z:=z-1): x free in 2*x but bound by x:=x+z
      (sToT("z()", "2*x"), "[x:=x+1 ++ x:=x+z()]x>z()".asFormula) ::            // subst(x>z): x free in 2*x but mustbe (and thus maybe) bound by {x:=x+1 ++ x:=x+z;...}
      (sToT("a()", "2*x"), "[{x:=x+1 ++ y:=5}; z:=x-a()]x>0".asFormula) ::    // subst(z:=x-a): x free in 2*x but (maybe) bound by {x:=x+1 ++ ...}
      (sToT("a()", "2*x"), "[{x:=x+1 ++ ?1>0}; z:=x-a()]x>0".asFormula) ::    // subst(z:=x-a): x free in 2*x but (maybe) bound by {x:=x+1 ++ ...}
//      (sToT("x", "2"), "[{x:=x+1;}*; z:=x+z]1>0".asFormula) ::            // subst(z:=x+z): x (maybe) bound by {x:=x+1}*
      (sToT("a()", "x"), "[{x:=x+1;}*; z:=a()]1>0".asFormula) ::              // subst(z:=a): x free in x but maybe bound by {x:=x+1}*
      (sToT("a()", "x"), "[x:=x+1; z:=a()]1>0".asFormula) ::                  // subst(z:=a): x free in x but mustbe (and thus maybe) bound by x:=x+1
//      (sToT("x", "a"), "[{x:=x+1;}*; x:=x+1]1>0".asFormula) ::            // subst(x:=x+1): x (maybe) bound by {x:=x+1}*
        Nil

    cases.foreach(c => withClue(c._1 + " on " + c._2) { a [SubstitutionClashException] should be thrownBy c._1(c._2) })

    cases.map(c => (rndExtensionOf(c._1), c._2)).
      foreach(c => withClue(c._1 + " on " + c._2) { a [SubstitutionClashException] should be thrownBy c._1(c._2) })
  }

  "Uniform substitution of mustbe bound" should "be same as input" in {
    // TODO variable substitution not yet supported
    val cases =
      (sToT("x()", "5"), "[{x:=0 ++ z:=z}]1>0".asFormula) ::                // x no free occurrence
//      (sToT("x", "5"), "[x:=0 ++ x:=1]x>0".asFormula) ::                  // x mustbe bound
//      (sToT("z", "2"), "[{x:=x+1 ++ y:=5}; z:=x-1]x>0".asFormula) ::      // z mustbe bound
//      (sToT("z", "2"), "[{x:=x+1 ++ y:=5}; z:=x-1]x>z".asFormula) ::      // z mustbe bound
        Nil

    cases.foreach(c => c._1(c._2) should be (c._2))
  }

  "Uniform substitution of free" should "be as expected" in {
    // TODO cases for variable substitution
//    val cases =
//      (sToT("z", "1"), "[x:=x+1 ++ x:=x+z;z:=z-1]x>0".asFormula, "[x:=x+1 ++ x:=x+1;z:=1-1]x>0".asFormula) ::
//      (sToT("x", "2"), "[x:=x+1 ++ x:=x+z;z:=z-1]x>0".asFormula, "[x:=2+1 ++ x:=2+z;z:=z-1]x>0".asFormula) ::
//      (sToT("x", "2"), "[x:=x+1 ++ x:=x+z;z:=z-1]x>z".asFormula, "[x:=2+1 ++ x:=2+z;z:=z-1]x>z".asFormula) ::
//      (sToT("z", "2"), "[{x:=x+1;}*; z:=x+z]x>z".asFormula, "[{x:=x+1;}*; z:=x+2]x>z".asFormula) ::
//      (sToT("x", "a"), "[x:=x+1; z:=a]1>0".asFormula, "[x:=a+1; z:=a]1>0".asFormula) ::
//      (sToT("x", "a"), "[x:=x+1; {x:=x+1;}*]1>0".asFormula, "[x:=a+1; {x:=x+1;}*]1>0".asFormula) ::
//      (sToT("z", "-z"), "[{x:=x+1 ++ x:=x+z}; z:=x-1]x>z".asFormula, "[{x:=x+1 ++ x:=x+-z}; z:=x-1]x>z".asFormula) ::
//        Nil
    val cases =
      (sToT("z()", "1"), "[x:=x+1 ++ x:=x+z();z:=z()-1]x>0".asFormula, "[x:=x+1 ++ x:=x+1;z:=1-1]x>0".asFormula) ::
      (sToT("x()", "2"), "[x:=x()+1 ++ x:=x()+z;z:=z-1]x>0".asFormula, "[x:=2+1 ++ x:=2+z;z:=z-1]x>0".asFormula) ::
      (sToT("x()", "2"), "[x:=x()+1 ++ x:=x()+z;z:=z-1]x>z".asFormula, "[x:=2+1 ++ x:=2+z;z:=z-1]x>z".asFormula) ::
      (sToT("z()", "2"), "[{x:=x+1;}*; z:=x+z()]x>z".asFormula, "[{x:=x+1;}*; z:=x+2]x>z".asFormula) ::
      (sToT("x()", "a"), "[x:=x()+1; z:=a]1>0".asFormula, "[x:=a+1; z:=a]1>0".asFormula) ::
      (sToT("x()", "a"), "[x:=x()+1; {x:=x+1;}*]1>0".asFormula, "[x:=a+1; {x:=x+1;}*]1>0".asFormula) ::
      (sToT("z()", "-z"), "[{x:=x+1 ++ x:=x+z()}; z:=x-1]x>z".asFormula, "[{x:=x+1 ++ x:=x+-z}; z:=x-1]x>z".asFormula) ::
        Nil

    cases.foreach(c => c._1(c._2) should be (c._3))
  }

  "O and U sets after local uniform substitution" should "be {x,z} and {x,z} on x:=1+1;z:=x" in {
    val s = Substitution(List(SubstitutionPair("x()".asTerm, "1".asTerm)))
    applySubstitution(s, Set.empty, Set.empty, "x:=x()+1;z:=x;".asProgram) should be (
      Set(V("x"), V("z")), Set(V("x"), V("z")), "x:=1+1; z:=x;".asProgram)
  }

  it should "be {} and {} on ?[x:=*;]x>0 -> x>0;" in {
    val s = Substitution(List(SubstitutionPair("x()".asTerm, "1".asTerm), SubstitutionPair("y()".asTerm, "x".asTerm)))
    applySubstitution(s, Set.empty, Set.empty, "?[x:=*;]x>0 -> y()>0;".asProgram) should be (
      Set.empty, Set.empty,"?[x:=*;]x>0 -> x>0;".asProgram)
  }

  it should "be {t} and {t} on t:=0" in {
    val s = Substitution(Seq(SubstitutionPair("x()".asTerm, "y".asTerm)))
    applySubstitution(s, Set.empty, Set.empty, "t:=0;".asProgram) should be (Set(V("t")), Set(V("t")), "t:=0;".asProgram)
  }

  it should "be {x} and {x} on x:=x()+y;" in {
    val s = Substitution(List(SubstitutionPair("x()".asTerm, "1".asTerm)))
    applySubstitution(s, Set.empty, Set.empty, "x:=x()+y;".asProgram) should be (Set(V("x")), Set(V("x")),"x:=1+y;".asProgram)
  }

  it should "be {x}, and {x} on x:=y();" in {
    val s = Substitution(Seq(SubstitutionPair("y()".asTerm, "x+y".asTerm)))
    applySubstitution(s, Set.empty, Set.empty, "x:=y();".asProgram) should be (Set(V("x")), Set(V("x")),"x:=x+y;".asProgram)
  }

  it should "be {t} and {t} on t'=y;" in {
    val s = Substitution(Seq(SubstitutionPair("x()".asTerm, "y".asTerm)))
    applySubstitution(s, Set.empty, Set(V("t")), "t'=x();".asProgram) should be (Set(V("t")), Set(V("t")),"t'=y;".asProgram)
  }

  it should "be {t} and {t} on t:=0;t'=y;" in {
    val s = Substitution(Seq(SubstitutionPair("x()".asTerm, "y".asTerm)))
    applySubstitution(s, Set.empty, Set.empty, "t:=0;t'=x();".asProgram) should be (Set(V("t")), Set(V("t")), "t:=0;t'=y;".asProgram)
  }

  "Forced clash in local uniform substitution" should "occur on x:=x()+y when BV={x}" in {
    val s = Substitution(Seq(SubstitutionPair("x()".asTerm, "x".asTerm)))
    a [SubstitutionClashException] should be thrownBy applySubstitution(s, Set.empty, Set(V("x")),"x:=x()+y;".asProgram)
  }

  it should "occur on x:=y() when BV={x}" in {
    val s = Substitution(Seq(SubstitutionPair("y()".asTerm, "x+y".asTerm)))
    a [SubstitutionClashException] should be thrownBy applySubstitution(s, Set.empty, Set(V("x")), "x:=y();".asProgram)
  }

  it should "occur on t'=x() when BV={t}" in {
    val s = Substitution(Seq(SubstitutionPair("t()".asTerm, "1".asTerm), SubstitutionPair("x()".asTerm, "t".asTerm)))
    a [SubstitutionClashException] should be thrownBy applySubstitution(s, Set.empty, Set(V("t")), "t'=x();".asProgram)
  }

  it should "occur on t'=x() & x()*y+t+1>0 when BV={t}" in {
    val s = Substitution(Seq(SubstitutionPair("x()".asTerm, "t".asTerm)))
    a [SubstitutionClashException] should be thrownBy applySubstitution(s, Set.empty, Set(V("t")), "t'=x() & x()*y+t+1>0;".asProgram)
  }

  it should "occur on y() when BV={x}" in {
    val q = Function("q", None, Real, Bool)
    val s = Substitution(Seq(SubstitutionPair("x()".asTerm, Number(1)), SubstitutionPair("y()".asTerm, "x".asTerm)))
    a [SubstitutionClashException] should be thrownBy applySubstitutionF(s, Set.empty, Set(V("x")), ApplyPredicate(q, "y()".asTerm))
  }

  it should "occur on x()=y when BV={y}" in {
    val s = Substitution(Seq(SubstitutionPair("x()".asTerm, "y".asTerm)))
    a [SubstitutionClashException] should be thrownBy applySubstitutionF(s, Set.empty, Set(V("y")), "x()=y".asFormula)
  }
}
