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
  private var s: Substitution = null

  override def beforeEach() = {
    s = new Substitution(List())
  }

  private def V(s: String) = Variable(s, None, Real)

  private def applySubstitutionT(o: Set[NamedSymbol], u: Set[NamedSymbol], t: Term) : Term = {
    val applySubstitution = PrivateMethod[Term]('usubst)
    s invokePrivate applySubstitution(o, u, t)
  }

  private def applySubstitutionF(o: Set[NamedSymbol], u: Set[NamedSymbol], f: Formula) : Formula = {
    val applySubstitution = PrivateMethod[Formula]('usubst)
    s invokePrivate applySubstitution(o, u, f)
  }

  private def applySubstitution(o: Set[NamedSymbol], u: Set[NamedSymbol], p: Program) : Any = {
    val applySubstitution = PrivateMethod[Any]('usubstComps)
    s invokePrivate applySubstitution(o, u, p)
  }

  /**
   * ==================================================
   * tests for base cases
   */

  // \theta +/- \eta

  "Uniform substitution of (x,y) |-> x+y" should "be y+y" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "y".asTerm)))
    s.apply("x+y".asTerm) should be ("y+y".asTerm)
  }

  "Uniform substitution of (x,y)(y,x) |-> x-y" should "be y-x" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "y".asTerm),new SubstitutionPair("y".asTerm, "x".asTerm)))
    s.apply("x-y".asTerm) should be ("y-x".asTerm)
  }

  "Uniform substitution of (x,y)(y,t) |-> x*y where {x} is bound" should "throw an IllegalArgumentException" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "y".asTerm),new SubstitutionPair("y".asTerm, "t".asTerm)))
    an [IllegalArgumentException] should be thrownBy applySubstitutionT(Set.empty, Set(V("x")),"x*y".asTerm)
  }

  "Uniform substitution of (x,y)(y,x) |-> x/y where {x} is bound" should "not be permitted" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "y".asTerm),new SubstitutionPair("y".asTerm, "x".asTerm)))
    an [IllegalArgumentException] should be thrownBy applySubstitutionT(Set.empty, Set(V("x")),"x/y".asTerm)
  }

  // f(\theta) apply on f

  "Uniform substitution of (x,y)(f(.),.+1) |-> f(x)" should "be y+1" in {
    val x = Variable("x", None, Real)
    val y = Variable("y", None, Real)
    val f = Function("f", None, Real, Real)
    s = Substitution(Seq(new SubstitutionPair(x, y),new SubstitutionPair(Apply(f,CDot), Add(Real, CDot, Number(1)))))
    s.apply(Apply(f,x)) should be ("y+1".asTerm)
  }

  "Uniform substitution of (x,y)(f(x),x+1) |-> f(x)" should "be y+1" in {
    val x = Variable("x", None, Real)
    val y = Variable("y", None, Real)
    val f = Function("f", None, Real, Real)
    s = Substitution(Seq(new SubstitutionPair(x, y),new SubstitutionPair(Apply(f, x), Add(Real, x, Number(1)))))
    s.apply(Apply(f,x)) should be ("y+1".asTerm)
  }

  "Uniform substitution of (x,y+z)(f(x),x+1) |-> f(x)" should "be y+z+1" in {
    val x = Variable("x", None, Real)
    val y = Variable("y", None, Real)
    val f = Function("f", None, Real, Real)
    s = Substitution(Seq(new SubstitutionPair(x, "y+z".asTerm),new SubstitutionPair(Apply(f, x), "x+1".asTerm)))
    s.apply(Apply(f,x)) should be ("y+z+1".asTerm)
  }

  "Uniform substitution of (x,y)(f(.),.+x+1) |-> f(x)" should "be y+x+1" in {
    val x = Variable("x", None, Real)
    val y = Variable("y", None, Real)
    val f = Function("f", None, Real, Real)
    s = Substitution(Seq(new SubstitutionPair(x, y),
      new SubstitutionPair(Apply(f, CDot), Add(Real, Add(Real, CDot, x), Number(1)))))
    s.apply(Apply(f,x)) should be ("y+x+1".asTerm)
  }

  "Uniform substitution of (x,y)(f(x),x+x+1) |-> f(x)" should "be y+y+1" in {
    val x = Variable("x", None, Real)
    val y = Variable("y", None, Real)
    val f = Function("f", None, Real, Real)
    s = Substitution(Seq(new SubstitutionPair(x, y),
      new SubstitutionPair(Apply(f, x), Add(Real, Add(Real, x, x), Number(1)))))
    s.apply(Apply(f,x)) should be ("y+y+1".asTerm)
  }

  "Uniform substitution of (x,y)(p(•),[x:=•+1;]x>0) |-> p(x)" should "be [x:=y+1;]x>0" in {
    val x = Variable("x", None, Real)
    val y = Variable("y", None, Real)
    val p = Function("p", None, Real, Bool)
    s = Substitution(Seq(new SubstitutionPair(x, y),
      new SubstitutionPair(ApplyPredicate(p, CDot), BoxModality(Assign(x,
        Add(Real, CDot, Number(1))), GreaterThan(Real, x, Number(0))))))
    s.apply(ApplyPredicate(p,x)) should be ("[x:=y+1;]x>0".asFormula)
  }

  "Uniform substitution of (x,y)(p(x),[x:=x+1;]x>0) |-> p(x)" should "be [x:=y+1;]x>0" in {
    val x = Variable("x", None, Real)
    val y = Variable("y", None, Real)
    val p = Function("p", None, Real, Bool)
    s = Substitution(Seq(new SubstitutionPair(x, y),
      new SubstitutionPair(ApplyPredicate(p, x), BoxModality(Assign(x,
        Add(Real, x, Number(1))), GreaterThan(Real, x, Number(0))))))
    s.apply(ApplyPredicate(p,x)) should be ("[x:=y+1;]x>0".asFormula)
  }

  "Uniform substitution of (x,y)(p(•),[•:=•+1;]•>0) |-> p(x)" should "be [•:=y+1;]•>0" in {
    val x = Variable("x", None, Real)
    val y = Variable("y", None, Real)
    val p = Function("p", None, Real, Bool)
    s = Substitution(Seq(new SubstitutionPair(x, y),
      new SubstitutionPair(ApplyPredicate(p, CDot), BoxModality(Assign(CDot,
        Add(Real, CDot, Number(1))), GreaterThan(Real, CDot, Number(0))))))
    s.apply(ApplyPredicate(p,x)) should be (
      BoxModality(Assign(CDot, Add(Real, y, Number(1))), GreaterThan(Real, CDot, Number(0))))
  }

  // g(\theta) apply on \theta

  "Uniform substitution of (x,1)(y,x) |-> g(x)" should "be g(1)" in {
    val x = Variable("x", None, Real)
    val y = Variable("y", None, Real)
    val g = Function("g", None, Real, Real)
    s = Substitution(Seq(new SubstitutionPair(x, Number(1)),new SubstitutionPair(y, x)))
    s.apply(Apply(g,x)) should be (Apply(g,Number(1)))
  }

  "Uniform substitution of (x,1)(y,x) |-> g(x) where {x} is bound" should "not be permitted" in {
    val x = Variable("x", None, Real)
    val y = Variable("y", None, Real)
    val g = Function("g", None, Real, Bool)
    s = Substitution(Seq(new SubstitutionPair(x, Number(1)),new SubstitutionPair(y, x)))
    an [IllegalArgumentException] should be thrownBy applySubstitutionT(Set.empty, Set(x), Apply(g,x))
  }

  "Uniform substitution of (x,y)(y,x) |-> g(x)" should "be g(y)" in {
    val x = Variable("x", None, Real)
    val y = Variable("y", None, Real)
    val g = Function("g", None, Real, Bool)
    s = Substitution(Seq(new SubstitutionPair(x, y),new SubstitutionPair(y, x)))
    s.apply(Apply(g,x)) should be (Apply(g,y))
  }

  "Uniform substitution of (x,y)(y,x) |-> f(x)=g(y)" should "be f(y)=g(x)" in {
    val x = Variable("x", None, Real)
    val y = Variable("y", None, Real)
    val f = Function("f", None, Real, Bool)
    val g = Function("g", None, Real, Bool)
    s = Substitution(Seq(new SubstitutionPair(x, y),new SubstitutionPair(y, x)))
    s.apply(Equals(Bool,Apply(f,x),Apply(g,y))) should be (Equals(Bool,Apply(f,y),Apply(g,x)))
  }

  // x substituable

  "Uniform substitution of (x,y) |-> x" should "be y" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "y".asTerm)))
    s.apply("x".asTerm) should be ("y".asTerm)
  }

  "Uniform substitution of (x,y) |-> x where {y} is bound" should "not be permitted" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "y".asTerm)))
    an [IllegalArgumentException] should be thrownBy applySubstitutionT(Set.empty, Set(V("y")),"x".asTerm)
  }

  // x nonsubstituable

  "Uniform substitution of (x,y) |-> x where {x} is bound" should "not be permitted" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "y".asTerm)))
    an [IllegalArgumentException] should be thrownBy applySubstitutionT(Set.empty, Set(V("x")),"x".asTerm)
  }

  "Uniform substitution of (x,y) |-> y" should "be y" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "y".asTerm)))
    s.apply("y".asTerm) should be ("y".asTerm)
  }

  /**
   * ==================================================
   * tests for programs
   */

  // \alpha U \beta

  "Uniform substitution of (x,1) |-> x:=1 ++ x:=x+1 ++ z:=x;" should "be x:=1 ++ x:=1+1 ++ z:=1;" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "1".asTerm)))
    // TODO not yet supported, hence exception
    an [IllegalArgumentException] should be thrownBy s.apply("x:=1 ++ x:=x+1 ++ z:=x".asProgram) //should be ("x:=1 ++ x:=1+1 ++ z:=1;".asProgram)
//    applySubstitution(Set.empty, Set.empty,"x:=1 ++ x:=x+1 ++ z:=x".asProgram) should be (
//      Set.empty, Set(V("x"),V("z")), "x:=1 ++ x:=1+1 ++ z:=1;".asProgram)
  }

  // TODO not yet supported
  "Uniform substitution of (x,t) |-> x:=1 ++ x:=x+1 ++ z:=x;" should "be x:=1 ++ x:=t+1 ++ z:=t;" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "t".asTerm)))
    // TODO not yet supported, hence exception
    an [IllegalArgumentException] should be thrownBy s.apply("x:=1 ++ x:=x+1 ++ z:=x".asProgram) //should be ("x:=1 ++ x:=t+1 ++ z:=t;".asProgram)
//    applySubstitution(Set.empty, Set.empty, "x:=1 ++ x:=x+1 ++ z:=x".asProgram) should be (
//      Set.empty, Set(V("x"),V("z")),"x:=1 ++ x:=t+1 ++ z:=t;".asProgram)
  }

  // \alpha ; \beta

  "Uniform substitution of (y,x+y) |-> x:=y;z:=x+y;" should "not be permitted" in {
    s = Substitution(Seq(new SubstitutionPair("y".asTerm, "x+y".asTerm)))
    an [IllegalArgumentException] should be thrownBy s.apply("x:=y;z:=x+y;".asProgram)
  }

  "Uniform substitution of (x,1) |-> x:=x+1;z:=x;" should "be x:=1+1;z:=x;" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "1".asTerm)))
    s.apply("x:=x+1;z:=x;".asProgram) should be ("x:=1+1; z:=x;".asProgram)
    applySubstitution(Set.empty, Set.empty, "x:=x+1;z:=x;".asProgram) should be (
      Set(V("x"), V("z")), Set(V("x"), V("z")), "x:=1+1; z:=x;".asProgram)
  }

  "Uniform substitution of (x,1) |-> {x:=1 ++ x:=x+1 ++ z:=x};{x:=1 ++ x:=x+1 ++ z:=x};" should "be {x:=1 ++ x:=1+1 ++ z:=1};{x:=1 ++ x:=x+1 ++ z:=x};" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "1".asTerm)))
    // TODO not yet supported, hence exception
    an [IllegalArgumentException] should be thrownBy s.apply("{x:=1 ++ x:=x+1 ++ z:=x};{x:=1 ++ x:=x+1 ++ z:=x};".asProgram)// should be ("{x:=1 ++ x:=1+1 ++ z:=1};{x:=1 ++ x:=x+1 ++ z:=x};".asProgram)
//    applySubstitution(Set.empty, Set.empty, "{x:=1 ++ x:=x+1 ++ z:=x};{x:=1 ++ x:=x+1 ++ z:=x};".asProgram) should be (
//      Set.empty, Set(V("x"),V("z")),"{x:=1 ++ x:=1+1 ++ z:=1};{x:=1 ++ x:=x+1 ++ z:=x};".asProgram)
  }

  // (\alpha)*

  "Uniform substitution of (x,1)(y,t) |-> {x:=x+y}*;" should "not be permitted" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "1".asTerm),new SubstitutionPair("y".asTerm, "t".asTerm)))
    an [IllegalArgumentException] should be thrownBy s.apply("{x:=x+y;}*".asProgram)
  }

  "Uniform substitution of (x,1)(y,x) |-> {x:=x+y}*;" should "be {x:=x+y}*" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "1".asTerm),new SubstitutionPair("y".asTerm, "x".asTerm)))
    an [IllegalArgumentException] should be thrownBy s.apply("{x:=x+y;}*".asProgram)
  }

  "Uniform substitution of (x,1) |-> {x:=1 ++ x:=x+1 ++ z:=x}*;" should "be {x:=1 ++ x:=x+1 ++ z:=x}*" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "1".asTerm)))
    // TODO not yet supported. also: check if it should clash anyway
    an [IllegalArgumentException] should be thrownBy s.apply("{x:=1 ++ x:=x+1 ++ z:=x}*".asProgram) //should be ("{x:=1 ++ x:=x+1 ++ z:=x}*".asProgram)
  }

  // ?\psi

  "Uniform substitution of (x,1)(y,x) |-> ?x+y>0;" should "be ?1+x>0;" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "1".asTerm),new SubstitutionPair("y".asTerm, "x".asTerm)))
    s.apply("?x+y>0;".asProgram) should be ("?1+x>0;".asProgram)
  }

  "Uniform substitution of (x,1)(y,x) |-> ?[x:=*;]x>0 -> y>0;" should "be ?[x:=*;]x>0 -> x>0;" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "1".asTerm),new SubstitutionPair("y".asTerm, "x".asTerm)))
    s.apply("?[x:=*;]x>0 -> y>0;".asProgram) should be ("?[x:=*;]x>0 -> x>0;".asProgram)
    applySubstitution(Set.empty, Set.empty, "?[x:=*;]x>0 -> y>0;".asProgram) should be (
      Set.empty, Set.empty,"?[x:=*;]x>0 -> x>0;".asProgram)
  }

  // x := \theta

  "Uniform substitution of (x,y) |-> t:=0;" should "be t:=0;" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "y".asTerm)))
    applySubstitution(Set.empty, Set.empty, "t:=0;".asProgram) should be (Set(V("t")), Set(V("t")), "t:=0;".asProgram)
  }

  "Uniform substitution of (x,1) |-> x:=x+y" should "be x:=1+y;" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "1".asTerm)))
    s.apply("x:=x+y;".asProgram) should be ("x:=1+y;".asProgram)
    applySubstitution(Set.empty, Set.empty, "x:=x+y;".asProgram) should be (Set(V("x")), Set(V("x")),"x:=1+y;".asProgram)
  }

  "Uniform substitution of (x,1) |-> x:=x+y where x is bound" should "not be permitted" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "1".asTerm)))
    an [IllegalArgumentException] should be thrownBy applySubstitution(Set.empty, Set(V("x")),"x:=x+y;".asProgram)
  }

  "Uniform substitution of (y,x+y) |-> x:=y" should "be x:=x+y;" in {
    s = Substitution(Seq(new SubstitutionPair("y".asTerm, "x+y".asTerm)))
    s.apply("x:=y;".asProgram) should be ("x:=x+y;".asProgram)
    applySubstitution(Set.empty, Set.empty, "x:=y;".asProgram) should be (Set(V("x")), Set(V("x")),"x:=x+y;".asProgram)
  }

  "Uniform substitution of (y,x+y) |-> x:=y where {x} is bound" should "be not be permitted" in {
    s = Substitution(Seq(new SubstitutionPair("y".asTerm, "x+y".asTerm)))
    an [IllegalArgumentException] should be thrownBy applySubstitution(Set.empty, Set(V("x")), "x:=y;".asProgram)
  }

  "Uniform substitution of (y,x+y) |-> z:=x+y;" should "be z:=x+x+y;" in {
    s = Substitution(Seq(new SubstitutionPair("y".asTerm, "x+y".asTerm)))
    s.apply("z:=x+y;".asProgram) should be ("z:=x+(x+y);".asProgram)
  }

  "Uniform substitution of (x,y)(y,x+y) |-> x:=y" should "be x:=x+y" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "y".asTerm),new SubstitutionPair("y".asTerm, "x+y".asTerm)))
    s.apply("x:=y;".asProgram) should be ("x:=x+y;".asProgram)
  }

  // x' = \theta & \psi

  "Uniform substitution of (x,y) |-> t'=x; where {t} is bound" should "be t'=y;" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "y".asTerm)))
    applySubstitution(Set.empty, Set(V("t")), "t'=x;".asProgram) should be (Set(V("t")), Set(V("t")),"t'=y;".asProgram)
  }

  "Uniform substitution of (t,1)(x,y) |-> t'=x; where {t} is bound" should "not be permitted" in {
    s = Substitution(Seq(new SubstitutionPair("t".asTerm, "1".asTerm),new SubstitutionPair("x".asTerm, "y".asTerm)))
    an [IllegalArgumentException] should be thrownBy applySubstitution(Set.empty, Set(V("t")), "t'=x;".asProgram)
  }

  "Uniform substitution of (t,1)(x,t) |-> t'=x; where {t} is bound" should "not be permitted" in {
    s = Substitution(Seq(new SubstitutionPair("t".asTerm, "1".asTerm),new SubstitutionPair("x".asTerm, "t".asTerm)))
    an [IllegalArgumentException] should be thrownBy applySubstitution(Set.empty, Set(V("t")), "t'=x;".asProgram)
  }

  "Uniform substitution of (t,1)(x,y) |-> t'=x;" should "not be permitted" in {
    s = Substitution(Seq(new SubstitutionPair("t".asTerm, "1".asTerm),new SubstitutionPair("x".asTerm, "y".asTerm)))
    an [IllegalArgumentException] should be thrownBy applySubstitution(Set.empty, Set.empty, "t'=x;".asProgram)
  }

  "Uniform substitution of (x,y) |-> t'=x;" should "be t'=y;" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "y".asTerm)))
    applySubstitution(Set.empty, Set.empty, "t'=x;".asProgram) should be  (Set(V("t")), Set(V("t")), "t'=y;".asProgram)
  }

  "Uniform substitution of (x,t) |-> t'=x;" should "not be permitted" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "t".asTerm)))
    an [IllegalArgumentException] should be thrownBy applySubstitution(Set.empty, Set.empty, "t'=x;".asProgram)
  }

  "Uniform substitution of (x,y) |-> t'=x & x*y+t+1>0; where {t} is bound" should "be t'=y & y*y+t+1>0;" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "y".asTerm)))
    applySubstitution(Set.empty, Set(V("t")), "t'=x & x*y+t+1>0;".asProgram) should be (
      Set(V("t")), Set(V("t")),"t'=y & y*y+t+1>0;".asProgram)
  }

  "Uniform substitution of (t,1)(x,y) |-> t'=x & x*y+t+1>0; where {t} is bound" should "not be permitted" in {
    s = Substitution(Seq(new SubstitutionPair("t".asTerm, "1".asTerm),new SubstitutionPair("x".asTerm, "y".asTerm)))
    an [IllegalArgumentException] should be thrownBy applySubstitution(Set.empty, Set(V("t")), "t'=x & x*y+t+1>0;".asProgram)
  }

  "Uniform substitution of (t,1)(x,y) |-> t'=x & x*y+t+1>0; where {t} is must-bound" should "be t'=y & y*y+t+1>0" in {
    s = Substitution(Seq(new SubstitutionPair("t".asTerm, "1".asTerm),new SubstitutionPair("x".asTerm, "y".asTerm)))
    applySubstitution(Set(V("t")), Set(V("t")), "t'=x & x*y+t+1>0;".asProgram) should be (Set(V("t")), Set(V("t")),"t'=y & y*y+t+1>0;".asProgram)
  }

  "Uniform substitution of (t,1)(x,t) |-> t'=x & x*y+t+1>0; where {t} is bound" should "not be permitted" in {
    s = Substitution(Seq(new SubstitutionPair("t".asTerm, "1".asTerm),new SubstitutionPair("x".asTerm, "t".asTerm)))
    an [IllegalArgumentException] should be thrownBy applySubstitution(Set.empty, Set(V("t")), "t'=x & x*y+t+1>0;".asProgram)
  }

  "Uniform substitution of (t,1)(x,y) |-> t'=x & x*y+t+1>0;" should "not be permitted" in {
    s = Substitution(Seq(new SubstitutionPair("t".asTerm, "1".asTerm),new SubstitutionPair("x".asTerm, "y".asTerm)))
    an [IllegalArgumentException] should be thrownBy applySubstitution(Set.empty, Set.empty, "t'=x & x*y+t+1>0;".asProgram)
  }

  "Uniform substitution of (x,y) |-> t'=x & x*y+t+1>0;" should "be t'=y & y*y+t+1>0;" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "y".asTerm)))
    applySubstitution(Set.empty, Set.empty, "t'=x & x*y+t+1>0;".asProgram) should be (Set(V("t")), Set(V("t")), "t'=y & y*y+t+1>0;".asProgram)
  }

  "Uniform substitution of (x,t) |-> t'=x & x*y+t+1>0;" should "not be permitted" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "t".asTerm)))
    an [IllegalArgumentException] should be thrownBy applySubstitution(Set.empty, Set.empty, "t'=x & x*y+t+1>0;".asProgram)
  }

  "Uniform substitution of (x,t) |-> [x:=5;x'=y,y'=x & x*y>0;]1>0" should "be [x:=5;x'=y,y'=x & x*y>0;]1>0" in {
    s = Substitution(List(SubstitutionPair("x".asTerm, "t".asTerm)))
    s("[x:=5;x'=y,y'=x & x*y>0;]1>0".asFormula) should be ("[x:=5;x'=y,y'=x & x*y>0;]1>0".asFormula)
  }

  "Uniform substitution of (x,t) |-> [x'=y,y'=x & x*y>0;]1>0" should "not be permitted" in {
    s = Substitution(List(SubstitutionPair("x".asTerm, "t".asTerm)))
    // x not must-bound when substituting
    an [IllegalArgumentException] should be thrownBy s("[x'=y,y'=x & x*y>0;]1>0".asFormula)
    an [IllegalArgumentException] should be thrownBy s("[{x:=1 ++ y:=2};x'=y,y'=x & x*y>0;]1>0".asFormula)
  }

  /**
   * ==================================================
   * tests for formulas
   */

  // \phi and/or \psi

  "Uniform substitution of (x,y)(y,x+y) |-> x>y & x<=y+1 " should "be y>x+y & y<=x+y+1" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "y".asTerm),new SubstitutionPair("y".asTerm, "x+y".asTerm)))
    s.apply("x>y & x<=y+1".asFormula) should be ("y>x+y & y<=x+y+1".asFormula)
  }

  // \forall x. \phi

  "Uniform substitution of (x,y)(y,y+1) |-> \\forall x. x>y" should "be forall x. x>y+1" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "y".asTerm),new SubstitutionPair("y".asTerm, "y+1".asTerm)))
    s.apply("\\forall x. x>y".asFormula) should be ("\\forall x. x>y+1".asFormula)
  }

  "Uniform substitution of (x,y)(y,y+1) |-> \\forall x. x>y | x<=y+1 " should "be forall x. x>y+1 | y<=y+1+1" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "y".asTerm),new SubstitutionPair("y".asTerm, "y+1".asTerm)))
    s.apply("\\forall x. x>y | x<=y+1".asFormula) should be ("\\forall x. x>y+1 | y<=y+1+1".asFormula)
  }

  "Uniform substitution of (x,y)(y,x+y) |-> \\forall x. x>y | x<=y+1 " should "not be permitted" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "y".asTerm),new SubstitutionPair("y".asTerm, "x+y".asTerm)))
    an [IllegalArgumentException] should be thrownBy s.apply("\\forall x. x>y | x<=y+1".asFormula)
  }

  // \exists x. \phi

  "Uniform substitution of (x,y)(y,y+1) |-> \\exists x. x>y" should "be exists x. x>y+1" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "y".asTerm),new SubstitutionPair("y".asTerm, "y+1".asTerm)))
    s.apply("\\exists x. x>y".asFormula) should be ("\\exists x. x>y+1".asFormula)
  }

  "Uniform substitution of (x,y)(y,y+1) |-> \\exists x. x>y -> x<=y+1 " should "be exists x. x>y+1 -> y<=y+1+1" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "y".asTerm),new SubstitutionPair("y".asTerm, "y+1".asTerm)))
    s.apply("\\exists x. x>y -> x<=y+1".asFormula) should be ("\\exists x. x>y+1 -> y<=y+1+1".asFormula)
  }

  "Uniform substitution of (x,y)(y,x+y) |-> \\exists x. x>y -> x<=y+1 " should "not be permitted" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "y".asTerm),new SubstitutionPair("y".asTerm, "x+y".asTerm)))
    an [IllegalArgumentException] should be thrownBy s.apply("\\exists x. x>y -> x<=y+1".asFormula)
  }

  // p(\theta) apply on p

  "Uniform substitution of (x,y)(p(t),t<1) |-> p(x)" should "be y<1" in {
    val x = Variable("x", None, Real)
    val y = Variable("y", None, Real)
    val p = Function("p", None, Real, Bool)
    s = Substitution(Seq(new SubstitutionPair(x, y),new SubstitutionPair(ApplyPredicate(p,CDot), LessThan(Real, CDot, Number(1)))))
    s.apply(ApplyPredicate(p,x)) should be ("y<1".asFormula)
  }

  "Uniform substitution of (x,y)(p(t),t>x) |-> p(x)" should "be y>x" in {
    val x = Variable("x", None, Real)
    val y = Variable("y", None, Real)
    val p = Function("p", None, Real, Bool)
    s = Substitution(Seq(new SubstitutionPair(x, y),new SubstitutionPair(ApplyPredicate(p,CDot), GreaterThan(Real, CDot, x))))
    s.apply(ApplyPredicate(p,x)) should be ("y>x".asFormula)
  }

  // q(\theta) apply on \theta

  "Uniform substitution of (x,1)(y,x) |-> q(x)" should "be q(1)" in {
    val x = Variable("x", None, Real)
    val y = Variable("y", None, Real)
    val q = Function("q", None, Real, Bool)
    s = Substitution(Seq(new SubstitutionPair(x, Number(1)),new SubstitutionPair(y, x)))
    s.apply(ApplyPredicate(q,x)) should be (ApplyPredicate(q,Number(1)))
  }

  "Uniform substitution of (x,1)(y,x) |-> q(x) where {x} is bound" should "not be permitted" in {
    val x = Variable("x", None, Real)
    val y = Variable("y", None, Real)
    val q = Function("q", None, Real, Bool)
    s = Substitution(Seq(new SubstitutionPair(x, Number(1)),new SubstitutionPair(y, x)))
    an [IllegalArgumentException] should be thrownBy applySubstitutionF(Set.empty, Set(x), ApplyPredicate(q,x))
  }

  "Uniform substitution of (x,y)(y,x) |-> q(x)" should "be q(y)" in {
    val x = Variable("x", None, Real)
    val y = Variable("y", None, Real)
    val q = Function("q", None, Real, Bool)
    s = Substitution(Seq(new SubstitutionPair(x, y),new SubstitutionPair(y, x)))
    s.apply(ApplyPredicate(q,x)) should be (ApplyPredicate(q,y))
  }

  "Uniform substitution of (x,y)(y,x) |-> p(x)=q(y)" should "be p(y)=q(x)" in {
    val x = Variable("x", None, Real)
    val y = Variable("y", None, Real)
    val p = Function("p", None, Real, Bool)
    val q = Function("q", None, Real, Bool)
    s = Substitution(Seq(new SubstitutionPair(x, y),new SubstitutionPair(y, x)))
    s.apply(Equals(Bool,Apply(p,x),Apply(q,y))) should be (Equals(Bool,Apply(p,y),Apply(q,x)))
  }

  // \theta =/>/< \eta

  "Uniform substitution of (x,1) |-> x=y" should "be 1=y" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "1".asTerm)))
    s.apply("x=y".asFormula) should be ("1=y".asFormula)
  }

  "Uniform substitution of (x,y) |-> x=y" should "be y=y" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "y".asTerm)))
    s.apply("x=y".asFormula) should be ("y=y".asFormula)
  }

  "Uniform substitution of (x,y) |-> x=y where {x} is bound" should "not be permitted" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "y".asTerm)))
    an [IllegalArgumentException] should be thrownBy applySubstitutionF(Set.empty, Set(V("x")), "x=y".asFormula)
  }

  "Uniform substitution of (x,y) |-> x=y where {y} is bound" should "not be permitted" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "y".asTerm)))
    an [IllegalArgumentException] should be thrownBy applySubstitutionF(Set.empty, Set(V("y")), "x=y".asFormula)
  }

  "Uniform substitution of (y,x+y) |-> z=x+y" should "be z=x+x+y" in {
    s = Substitution(Seq(new SubstitutionPair("y".asTerm, "x+y".asTerm)))
    s.apply("z=x+y".asFormula) should be ("z=x+(x+y)".asFormula)
  }

  "Uniform substitution of (x,y)(y,x+y) |-> x=y" should "be y=x+y" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "y".asTerm),new SubstitutionPair("y".asTerm, "x+y".asTerm)))
    s.apply("x=y".asFormula) should be ("y=x+y".asFormula)
  }

  // [\alpha]\phi

  "Uniform substitution of (x,1) |-> [y:=x;]x>0" should "be [y:=1;]1>0" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "1".asTerm)))
    s.apply("[y:=x;]x>0".asFormula) should be ("[y:=1;]1>0".asFormula)
  }

  "Uniform substitution of (x,1) |-> [x:=y;]x>0" should "be [x:=y;]x>0" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "1".asTerm)))
    s.apply("[x:=y;]x>0".asFormula) should be ("[x:=y;]x>0".asFormula)
  }

  "Uniform substitution of (x,t) |-> [{x:=x+y;}*]x>0" should "not be permitted" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "t".asTerm)))
    an [IllegalArgumentException] should be thrownBy s.apply("[{x:=x+y;}*]x>0".asFormula)
  }

  "Uniform substitution of (x,t) |-> [{x'=x+y;}*]x>0" should "not be permitted" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "t".asTerm)))
    an [IllegalArgumentException] should be thrownBy s("[{x'=x+y;}*]x>0".asFormula)
  }

  "Uniform substitution of (x,1) |-> [x'=y;]x>0" should "not be permitted" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "1".asTerm)))
    an [IllegalArgumentException] should be thrownBy s("[x'=y;]x>0".asFormula)
  }

  "Uniform substitution of (x,t) |-> [x:=1 ++ x:=x+1 ++ z:=x;]x>0" should "be [x:=1 ++ x:=t+1 ++ z:=t;]x>0" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "t".asTerm)))
    // TODO not yet supported, hence exception
    an [IllegalArgumentException] should be thrownBy s.apply("[x:=1 ++ x:=x+1 ++ z:=x]x>0".asFormula)// should be ("[x:=1 ++ x:=t+1 ++ z:=t;]x>0".asFormula)
  }

  // <\alpha>\phi

  "Uniform substitution of (x,1) |-> <y:=x;>x>0" should "be <y:=1;>1>0" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "1".asTerm)))
    s.apply("<y:=x;>x>0".asFormula) should be ("<y:=1;>1>0".asFormula)
  }

  "Uniform substitution of (x,1) |-> <x:=y;>x>0" should "be <x:=y;>x>0" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "1".asTerm)))
    s.apply("<x:=y;>x>0".asFormula) should be ("<x:=y;>x>0".asFormula)
  }

  "Uniform substitution of (x,1) |-> <x'=y;>x>0" should "not be permitted" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "1".asTerm)))
    an [IllegalArgumentException] should be thrownBy s("<x'=y;>x>0".asFormula)
  }

  /**
   * ==================================================
   * tests for complicated cases
   */

  "Uniform substitution of (x,y) |-> t:=0;t'=x;" should "be t:=0;t'=y;" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "y".asTerm)))
    applySubstitution(Set.empty, Set.empty, "t:=0;t'=x;".asProgram) should be (Set(V("t")), Set(V("t")), "t:=0;t'=y;".asProgram)
    s.apply("[t:=0;t'=x;]true".asFormula) should be ("[t:=0;t'=y;]true".asFormula)
    s.apply("[t:=0;][t'=x;]true".asFormula) should be ("[t:=0;][t'=y;]true".asFormula)
  }

  "Uniform substitution of (t,y) |-> t:=0;t'=x;" should "be t:=0;t'=x;" in {
    s = Substitution(Seq(new SubstitutionPair("t".asTerm, "y".asTerm)))
    applySubstitution(Set.empty, Set.empty, "t:=0;t'=x;".asProgram) should be (Set(V("t")), Set(V("t")), "t:=0;t'=x;".asProgram)
    s.apply("[t:=0;t'=x;]true".asFormula) should be ("[t:=0;t'=x;]true".asFormula)
    s.apply("[t:=0;][t'=x;]true".asFormula) should be ("[t:=0;][t'=x;]true".asFormula)
  }

  "Uniform substitution of (x,y) |-> (y,x+y) |-> x=y" should "be y=y+y" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "y".asTerm)))
    val s1  = new Substitution(Seq(new SubstitutionPair("y".asTerm, "x+y".asTerm)))
    s.apply(s1.apply("x=y".asFormula)) should be ("y=y+y".asFormula)
  }

  "Uniform substitution of (x,y) |-> (y,x+y) |-> x:=y" should "be x:=y+y" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "y".asTerm)))
    val s1  = new Substitution(Seq(new SubstitutionPair("y".asTerm, "x+y".asTerm)))
    s.apply(s1.apply("x:=y;".asProgram)) should be ("x:=y+y;".asProgram)
  }

  /**
   * ==================================================
   * tests for the cases that are forbidden
   */

  "Uniform substitution of [y:=1][y:=2+y;]true" should "not perform \\alpha renaming" in {
    val y = Variable("y", None, Real)
    val y0 = Variable("y0", Some(0), Real)

    s = Substitution(Seq(new SubstitutionPair("y".asTerm, "y0".asTerm)))
    s.apply("\\forall y. (y=1 -> [y:=2+y;]true)".asFormula) should not be "\\forall y0. (y0=1 -> [y0:=2+y0;]true)".asFormula
    s.apply("\\forall y. (y=1 -> [y:=2+y;]true)".asFormula) should be ("\\forall y. (y=1 -> [y:=2+y;]true)".asFormula)
  }

  "Uniform substitution of [{•:=•+1;}*;]true" should "not substitute be permitted" in {
    s = Substitution(Seq(new SubstitutionPair(CDot, "x".asTerm)))

    val o = BoxModality(Loop(Assign(CDot, Add(Real, CDot, Number(1)))), True)
    an [IllegalArgumentException] should be thrownBy s.apply(o)
  }

  "Uniform substitution of [{x:=x+1;}*;]true" should "not be permitted" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "y".asTerm)))
    an [IllegalArgumentException] should be thrownBy s.apply("[{x:=x+1;}*;]true".asFormula)
  }

  "Uniform substitution of [y:=t;]p(y) <-> p(t)" should "[y:=t;]y>0 <-> z>0" in {
    def p(x: Term) = ApplyPredicate(Function("p", None, Real, Bool), x)
    s = Substitution(List(new SubstitutionPair("t".asTerm, "z".asTerm),
      new SubstitutionPair(p("y".asTerm), "y>0".asFormula)))

    // [x:=t;]p(x) <-> p(t)
    val o = Equiv(BoxModality("y:=t;".asProgram, p("y".asTerm)), p("t".asTerm))
    s(o) should be ("[y:=z;]y>0 <-> z>0".asFormula)
  }

  "Uniform substitution (p(.) |-> .>0),z |-> 2) of [x:=2y+1;]p(3x+z)" should "[x:=2y+1;]3x+2>0" in {
    def p(x: Term) = ApplyPredicate(Function("p", None, Real, Bool), x)
    s = Substitution(Seq(new SubstitutionPair("z".asTerm, "2".asTerm),
      new SubstitutionPair(p("x".asTerm), "x>0".asFormula)))

    // [x:=2y+1;]p(3x+z)
    val o = BoxModality(Assign("x".asTerm, "2*y+1".asTerm), p("3*x+z".asTerm))
    s(o) should be ("[x:=2*y+1;]3*x+2>0".asFormula)
  }

  "Uniform substitution (p(.) |-> .>0),z |-> x+2) of [x:=2y+1;]p(3x+z)" should "throw a clash exception" in {
    def p(x: Term) = ApplyPredicate(Function("p", None, Real, Bool), x)
    s = Substitution(Seq(new SubstitutionPair("z".asTerm, "2+x".asTerm),
      new SubstitutionPair(p("x".asTerm), "x>0".asFormula)))

    // [x:=2y+1;]p(3x+z)
    val o = BoxModality(Assign("x".asTerm, "2*y+1".asTerm), p("3*x+z".asTerm))
    an [IllegalArgumentException] should be thrownBy  s(o)
  }

  "Uniform substitution (x |-> 9) of x=9 -> [x'=x;]x>=0" should "throw a clash exception" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "9".asTerm)))
    val o = "x=9 -> [x'=x;]x>=0".asFormula
    an [IllegalArgumentException] should be thrownBy  s(o)
  }

//  "Uniform substitution of p(x)"
  ignore should "alpha rename x to any other variable in modalities" in {
    s = Substitution(Seq(new SubstitutionPair(ApplyPredicate(Function("p", None, Real, Bool), "x".asTerm),
      "[x:=2;]x>5".asFormula)))
    s(ApplyPredicate(Function("p", None, Real, Bool), "y".asTerm)) should be ("[y:=2;]y>5".asFormula)
    s = Substitution(Seq(new SubstitutionPair(ApplyPredicate(Function("p", None, Real, Bool), "x".asTerm),
      "[x:=y;][x:=z;]x>5".asFormula)))
    s(ApplyPredicate(Function("p", None, Real, Bool), "y".asTerm)) should be ("[y:=z;]y>5".asFormula)
    s = Substitution(Seq(new SubstitutionPair(ApplyPredicate(Function("p", None, Real, Bool), "x".asTerm),
      "[x:=y;][x:=z;][{x:=x+1;}*;]x>5".asFormula)))
    s(ApplyPredicate(Function("p", None, Real, Bool), "y".asTerm)) should be ("[y:=z;][{y:=y+1;}*;]y>5".asFormula)

    s = Substitution(Seq(new SubstitutionPair(ApplyPredicate(Function("p", None, Real, Bool), "x".asTerm),
      "<x:=2;>x>5".asFormula)))
    s(ApplyPredicate(Function("p", None, Real, Bool), "y".asTerm)) should be ("<y:=2;>y>5".asFormula)
  }

  ignore should "not alpha rename to arbitrary terms in modalities" in {
    s = Substitution(Seq(new SubstitutionPair(ApplyPredicate(Function("p", None, Real, Bool), "x".asTerm),
      "[x:=2;]true".asFormula)))

    val o = ApplyPredicate(Function("p", None, Real, Bool), "a+1".asTerm)
    s(o) should be ("[x:=2;]true".asFormula)
    s(o) should not be "[(a+1):=2;]true".asFormula
  }

  ignore should "substitute to arbitrary terms in simple formulas" in {
    s = Substitution(Seq(new SubstitutionPair(ApplyPredicate(Function("p", None, Real, Bool), "x".asTerm),
      "x>5".asFormula)))

    s(ApplyPredicate(Function("p", None, Real, Bool), "a+1".asTerm)) should be ("a+1>5".asFormula)
  }

  ignore should "not rename bound variables before substitution except in modalities" in {
    s = Substitution(Seq(new SubstitutionPair(ApplyPredicate(Function("p", None, Real, Bool), "x".asTerm),
      "\\forall x. (x = 1 -> [x:=x+2;]x>0)".asFormula)))
    s(ApplyPredicate(Function("p", None, Real, Bool), "y".asTerm)) should be ("\\forall x. (x = 1 -> [x:=x+2;]x>0)".asFormula)

    s = Substitution(Seq(new SubstitutionPair(ApplyPredicate(Function("p", None, Real, Bool), "x".asTerm),
      "\\exists x. (x = 1 -> [x:=x+2;]x>0)".asFormula)))
    s(ApplyPredicate(Function("p", None, Real, Bool), "y".asTerm)) should be ("\\exists x. (x = 1 -> [x:=x+2;]x>0)".asFormula)
  }

  it should "substitute predicate constants" in {
    s = Substitution(List(SubstitutionPair(PredicateConstant("p"), "x>5".asFormula)))

    s(And(PredicateConstant("p"), "y!=1".asFormula)) should be ("x>5 & y!=1".asFormula)
  }

  it should "not be permitted to substitute predicate constants with bound names" in {
    s = Substitution(List(SubstitutionPair(PredicateConstant("p"), "x>5".asFormula)))

    an [IllegalArgumentException] should be thrownBy s("\\forall x. p".asFormula)
    an [IllegalArgumentException] should be thrownBy s("[x:=1 ++ y:=3]p".asFormula)
  }

  /*
   * Andre's tests
   */
  def sToT(s: String, t: String) = Substitution(List(SubstitutionPair(s.asNamedSymbol, t.asTerm)))

  "Substitution clash" should "be reported on substitution of (maybe) bound variables" in {
    def rndSubstDefs(max: Int) = {
      val rnd = new Random()
      val numSubsts = rnd.nextInt(max)
      val names = new RandomFormula(rnd).nextNames("lhs", numSubsts)
      names.map(SubstitutionPair(_, rndTerm(rnd.nextInt(10), rnd)))
    }
    def rndTerm(size: Int, rnd: Random = new Random()) = {
      val rndF = new RandomFormula(rnd)
      rndF.nextT(rndF.nextNames("rhs", size/3+1), size)
    }

    def rndExtensionOf(s: Substitution) = Substitution(new Random().shuffle(s.subsDefs ++ rndSubstDefs(5)))

    val cases =
      (sToT("x", "5"), "[{x:=0 ++ z:=z}; a:=x;]1>0".asFormula) ::         // subst(a:=x): x (maybe) bound by {x:=0 ++ ...}
      (sToT("b", "z+1"), "[{x:=0 ++ z:=z}; a:=b;]1>0".asFormula) ::       // subst(a:=b): z free in z+1 but (maybe) bound by {... ++ z:=z}
      (sToT("x", "5"), "[x:=0 ++ z:=z]x>0".asFormula) ::                  // subst(x>0): x (maybe) bound by {x:=0 ++ ...}
      (sToT("z", "1"), "[x:=x+1 ++ x:=x+z;z:=z-1]x>z".asFormula) ::       // subst(x>z): z (maybe) bound by {... ++ z:=z+1}
      (sToT("z", "2*x"), "[x:=x+1 ++ x:=x+z;z:=z-1]x>0".asFormula) ::     // subst(z:=z-1): x free in 2*x but bound by x:=x+z
      (sToT("z", "2*x"), "[x:=x+1 ++ x:=x+z]x>z".asFormula) ::            // subst(x>z): x free in 2*x but mustbe (and thus maybe) bound by {x:=x+1 ++ x:=x+z;...}
      (sToT("a", "2*x"), "[{x:=x+1 ++ y:=5}; z:=x-a]x>0".asFormula) ::    // subst(z:=x-a): x free in 2*x but (maybe) bound by {x:=x+1 ++ ...}
      (sToT("a", "2*x"), "[{x:=x+1 ++ ?1>0}; z:=x-a]x>0".asFormula) ::    // subst(z:=x-a): x free in 2*x but (maybe) bound by {x:=x+1 ++ ...}
      (sToT("x", "2"), "[{x:=x+1;}*; z:=x+z]1>0".asFormula) ::            // subst(z:=x+z): x (maybe) bound by {x:=x+1}*
      (sToT("a", "x"), "[{x:=x+1;}*; z:=a]1>0".asFormula) ::              // subst(z:=a): x free in x but maybe bound by {x:=x+1}*
      (sToT("a", "x"), "[x:=x+1; z:=a]1>0".asFormula) ::                  // subst(z:=a): x free in x but mustbe (and thus maybe) bound by x:=x+1
      (sToT("x", "a"), "[{x:=x+1;}*; x:=x+1]1>0".asFormula) ::            // subst(x:=x+1): x (maybe) bound by {x:=x+1}*
        Nil

    cases.foreach(c => withClue(c._1 + " on " + c._2) { an [IllegalArgumentException] should be thrownBy c._1(c._2) })

    cases.map(c => (rndExtensionOf(c._1), c._2)).
      foreach(c => withClue(c._1 + " on " + c._2) { an [IllegalArgumentException] should be thrownBy c._1(c._2) })
  }

  "Uniform substitution of mustbe bound" should "be same as input" in {
    val cases =
      (sToT("x", "5"), "[{x:=0 ++ z:=z}]1>0".asFormula) ::                // x no free occurrence
      (sToT("x", "5"), "[x:=0 ++ x:=1]x>0".asFormula) ::                  // x mustbe bound
      (sToT("z", "2"), "[{x:=x+1 ++ y:=5}; z:=x-1]x>0".asFormula) ::      // z mustbe bound
      (sToT("z", "2"), "[{x:=x+1 ++ y:=5}; z:=x-1]x>z".asFormula) ::      // z mustbe bound
        Nil

    cases.foreach(c => c._1(c._2) should be (c._2))
  }

  "Uniform substitution of free" should "be as expected" in {
    val cases =
      (sToT("z", "1"), "[x:=x+1 ++ x:=x+z;z:=z-1]x>0".asFormula, "[x:=x+1 ++ x:=x+1;z:=1-1]x>0".asFormula) ::
      (sToT("x", "2"), "[x:=x+1 ++ x:=x+z;z:=z-1]x>0".asFormula, "[x:=2+1 ++ x:=2+z;z:=z-1]x>0".asFormula) ::
      (sToT("x", "2"), "[x:=x+1 ++ x:=x+z;z:=z-1]x>z".asFormula, "[x:=2+1 ++ x:=2+z;z:=z-1]x>z".asFormula) ::
      (sToT("z", "2"), "[{x:=x+1;}*; z:=x+z]x>z".asFormula, "[{x:=x+1;}*; z:=x+2]x>z".asFormula) ::
      (sToT("x", "a"), "[x:=x+1; z:=a]1>0".asFormula, "[x:=a+1; z:=a]1>0".asFormula) ::
      (sToT("x", "a"), "[x:=x+1; {x:=x+1;}*]1>0".asFormula, "[x:=a+1; {x:=x+1;}*]1>0".asFormula) ::
      (sToT("z", "-z"), "[{x:=x+1 ++ x:=x+z}; z:=x-1]x>z".asFormula, "[{x:=x+1 ++ x:=x+-z}; z:=x-1]x>z".asFormula) ::
        Nil

    cases.foreach(c => c._1(c._2) should be (c._3))
  }
}
