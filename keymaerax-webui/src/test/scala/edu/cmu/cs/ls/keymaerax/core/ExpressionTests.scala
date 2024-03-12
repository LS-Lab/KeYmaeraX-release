/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.core

import edu.cmu.cs.ls.keymaerax.tags.CheckinTest
import testHelper.KeYmaeraXTestTags._

import scala.collection.immutable._
import org.scalatest.{FlatSpec, Matchers}

/**
 * Tests basic expression data structures
 *
 * @author
 *   Andre Platzer
 */
@CheckinTest
class ExpressionTests extends FlatSpec with Matchers {
  "Expressions" should "refuse empty names" in {
    a[CoreException] shouldBe thrownBy(Variable("", None, Real))
    a[CoreException] shouldBe thrownBy(new Function("", None, Unit, Real))
    a[CoreException] shouldBe thrownBy(new ProgramConst(""))
    a[CoreException] shouldBe thrownBy(new DifferentialProgramConst("", AnyArg))
  }

  it should "refuse names with primes" in {
    a[CoreException] shouldBe thrownBy(Variable("x'", None, Real))
    a[CoreException] shouldBe thrownBy(new DifferentialSymbol(Variable("x'", None, Real)))
    a[CoreException] shouldBe thrownBy(new Function("x'", None, Unit, Real))
    a[CoreException] shouldBe thrownBy(new ProgramConst("x'"))
    a[CoreException] shouldBe thrownBy(new DifferentialProgramConst("x'", AnyArg))
  }

  it should "refuse names with inner underscores to avoid confusion with name.index" in {
    a[CoreException] shouldBe thrownBy(Variable("x_1", None, Real))
    a[CoreException] shouldBe thrownBy(new DifferentialSymbol(Variable("x_1", None, Real)))
    a[CoreException] shouldBe thrownBy(new Function("x_1", None, Unit, Real))
    a[CoreException] shouldBe thrownBy(new ProgramConst("x_1"))
    a[CoreException] shouldBe thrownBy(new DifferentialProgramConst("x_1", AnyArg))
  }

  it should "refuse names with middle inner underscores to avoid confusion with name.index" in {
    a[CoreException] shouldBe thrownBy(Variable("x_a", None, Real))
    a[CoreException] shouldBe thrownBy(new DifferentialSymbol(Variable("x_a", None, Real)))
    a[CoreException] shouldBe thrownBy(new Function("x_a", None, Unit, Real))
    a[CoreException] shouldBe thrownBy(new ProgramConst("x_a"))
    a[CoreException] shouldBe thrownBy(new DifferentialProgramConst("x_a", AnyArg))
  }

  it should "refuse names with negative index" in {
    a[CoreException] shouldBe thrownBy(Variable("x", Some(-1), Real))
    a[CoreException] shouldBe thrownBy(new DifferentialSymbol(Variable("x", Some(-1), Real)))
    a[CoreException] shouldBe thrownBy(new Function("x", Some(-1), Unit, Real))
  }

  it should "support reapplying pairs" in {
    Pair(Number(5), Number(7)).reapply(Number(5), Number(7)) shouldBe Pair(Number(5), Number(7))
    Pair(Number(5), Number(7)).reapply(Number(-2), Number(-7)) shouldBe Pair(Number(-2), Number(-7))
  }

  it should "refuse ill-formed interpreted functions" in {
    // Interpreted function with incorrect codomain
    a[CoreException] shouldBe thrownBy(Function("bad", None, Tuple(Real, Real), Bool, interp = Some(True)))

    // Interpreted function with incorrect domain
    a[CoreException] shouldBe thrownBy(Function("bad", None, Bool, Bool, interp = Some(True)))

    // Interpreted function with ill-formed domain
    a[CoreException] shouldBe thrownBy(Function("bad", None, Tuple(Real, Unit), Bool, interp = Some(True)))

    // Interpreted function with free variables in interpretation
    a[CoreException] shouldBe
      thrownBy(Function("bad", None, Real, Real, interp = Some(Greater(Variable("x"), Number(0)))))

    // Interpreted function with free uninterpreted functions in interpretation
    a[CoreException] shouldBe thrownBy(Function(
      "bad",
      None,
      Real,
      Real,
      interp = Some(Greater(FuncOf(Function("f", None, Unit, Real), Nothing), Number(0))),
    ))

    // Interpreted function with too many dots in interpretation
    a[CoreException] shouldBe
      thrownBy(Function("bad", None, Unit, Real, interp = Some(Greater(DotTerm(Real, Some(5)), Number(0)))))
  }

  it should "accept well-formed interpreted functions" in {
    // f() = 0
    val f = Function("f", None, Unit, Real, interp = Some(Equal(DotTerm(Real, Some(0)), Number(0))))
    // g(x) = x
    val g = Function("g", None, Real, Real, interp = Some(Equal(DotTerm(Real, Some(0)), DotTerm(Real, Some(1)))))
    // h(x) = f + g(x)
    val h = Function(
      "h",
      None,
      Real,
      Real,
      interp = Some(Equal(DotTerm(Real, Some(0)), Plus(FuncOf(f, Nothing), FuncOf(g, DotTerm(Real, Some(1)))))),
    )
  }

  "Kinds" should "have expected strings" taggedAs (CoverageTest) in {
    (ExpressionKind :: TermKind :: FormulaKind :: ProgramKind :: DifferentialProgramKind :: FunctionKind :: Nil)
      .forall(k => k.toString + "Kind$" == k.getClass.getSimpleName) shouldBe true
  }

  "Sorts" should "have expected strings" taggedAs (CoverageTest) in {
    (Unit :: Bool :: Real :: Trafo :: Nil).forall(k => k.toString + "$" == k.getClass.getSimpleName) shouldBe true
    ObjectSort("lalalala").toString shouldBe "lalalala"
    Tuple(Real, Bool).toString shouldBe "(Real,Bool)"
  }
}
