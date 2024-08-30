/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.parser

import org.keymaerax.GlobalState
import org.keymaerax.btactics.{TacticTestBase, TactixLibrary}
import org.keymaerax.core._
import org.keymaerax.parser.StringConverter._
import org.scalatest.LoneElement._

import scala.annotation.nowarn

/** Tests the declarations parser. Created by nfulton on 9/1/15. */
@nowarn("msg=match may not be exhaustive")
class DeclsTests extends TacticTestBase {
  "Archive parser" should "parse declarations of z, z_0 as two separate declarations" in {
    val input = {
      """ArchiveEntry "Test"
        |ProgramVariables
        |Real x;
        |Real z;
        |Real z_0;
        |Real a;
        |End.
        |Problem
        |x + z + z_0 = z_0 + z + x
        |End.
        |End.
        |""".stripMargin
    }
    ArchiveParser.parseAsFormula(input)
  }

  "Problem/Solution Block" should "parse correctly" in withTactics {
    val input = {
      """ArchiveEntry "Test"
        |Definitions
        |  Bool A();
        |End.
        |Problem
        |  !(A() | !A()) -> !!(A() | !A())
        |End.
        |Tactic "t"
        |  implyR(1)
        |End.
        |End.
        |""".stripMargin
    }

    val parsed = ArchiveParser.parse(input, parseTactics = true).loneElement

    parsed.model shouldBe "!(A() | !A()) -> !!(A() | !A())".asFormula
    parsed.tactics.head._3 shouldBe TactixLibrary.implyR(1)
  }

  "function domain" should "parse correctly" in {
    val input = {
      """ArchiveEntry "Test"
        |Definitions
        |  Bool Cimpl(Real x, Real y, Real z);
        |End.
        |Problem
        |  Cimpl(0,1,2) <-> true
        |End.
        |End.
        |""".stripMargin
    }

    ArchiveParser.parseAsFormula(input) shouldBe Equiv(
      PredOf(
        Function("Cimpl", None, Tuple(Real, Tuple(Real, Real)), Bool),
        Pair(Number(0), Pair(Number(1), Number(2))),
      ),
      True,
    )
  }

  it should "parse def'n that do not use its arguments" in {
    val input = {
      """ArchiveEntry "Test"
        |Definitions
        |  Bool Cimpl(Real x, Real y, Real z) <-> true;
        |  Real zero(Real x, Real y) = 0;
        |End.
        |Problem
        |  Cimpl(0,1,2) <-> 0 = zero(3,4)
        |End.
        |End.
        |""".stripMargin
    }

    val parsed = ArchiveParser.parse(input).loneElement
    parsed.model shouldBe Equiv(
      PredOf(
        Function("Cimpl", None, Tuple(Real, Tuple(Real, Real)), Bool),
        Pair(Number(0), Pair(Number(1), Number(2))),
      ),
      Equal(Number(0), FuncOf(Function("zero", None, Tuple(Real, Real), Real), Pair(Number(3), Number(4)))),
    )
    parsed.defs.subst(parsed.model) shouldBe Equiv(True, Equal(Number(0), Number(0)))
  }
  it should "fail to parse when the function application has the wrong assoc" in {
    val input = {
      """ArchiveEntry "Test"
        |Definitions
        |  Bool Cimpl(Real x, Real y, Real z);
        |End.
        |Problem
        |  Cimpl((0,1),2) <-> true
        |End.
        |End.
        |""".stripMargin
    }

    a[ParseException] shouldBe thrownBy(ArchiveParser.parseAsFormula(input))
  }

  it should "fail to parse when the function def'n has the wrong assoc" in {
    val input = {
      """ArchiveEntry "Test"
        |Definitions
        |  Bool Cimpl((Real x, Real y), Real z);
        |End.
        |Problem
        |  Cimpl(0,1,2) <-> true
        |End.
        |End.
        |""".stripMargin
    }

    a[ParseException] shouldBe thrownBy(ArchiveParser.parseAsFormula(input))
  }

  it should "substitute in definitions" in {
    val input = {
      """ArchiveEntry "Test"
        |Definitions
        |  Bool Pred(Real x, Real y, Real z) <-> x + y <= z;
        |End.
        |Problem
        |  Pred(0,1,2) <-> true
        |End.
        |End.
        |""".stripMargin
    }

    val parsed = GlobalState.archiveParser(input).loneElement
    parsed.defs.decls.loneElement._2 match {
      case Signature(Some(domain), codomain, _, Right(Some(interpretation)), _) =>
        domain shouldBe Tuple(Real, Tuple(Real, Real))
        codomain shouldBe Bool
        interpretation shouldBe "x + y <= z".asFormula
    }
    parsed.model shouldBe "Pred(0,1,2) <-> true".asFormula
  }

  it should "yield correct substitution even with unused arguments" in {
    val input = {
      """ArchiveEntry "Test"
        |Definitions
        |  import kyx.math.max;
        |  Bool Pred(Real x, Real y, Real z) <-> y <= z;
        |  Real posSnd(Real x, Real y) = max(0,y);
        |  Real snd<<._0 = y>>(Real x, Real y);
        |End.
        |Problem
        |  Pred(0,1,2) <-> snd(0,1) != posSnd(3,4)
        |End.
        |End.
        |""".stripMargin
    }

    val parsed = GlobalState.archiveParser(input).loneElement
    parsed.defs.subst shouldBe USubst(
      SubstitutionPair(
        FuncOf(Function("max", None, Tuple(Real, Real), Real), "(._1,._2)".asTerm),
        FuncOf(InterpretedSymbols.maxF, "(._1,._2)".asTerm),
      ) :: SubstitutionPair(
        PredOf(Function("Pred", None, Tuple(Real, Tuple(Real, Real)), Bool), "(._0,._1,._2)".asTerm),
        "._1<=._2".asFormula,
      ) :: SubstitutionPair(
        FuncOf(Function("posSnd", None, Tuple(Real, Real), Real), "(._3,._4)".asTerm),
        FuncOf(InterpretedSymbols.maxF, "(0,._4)".asTerm),
      ) :: SubstitutionPair(
        FuncOf(Function("snd", None, Tuple(Real, Real), Real), "(._1,._2)".asTerm),
        FuncOf(Function("snd", None, Tuple(Real, Real), Real, Some("._0=._2".asFormula)), "(._1,._2)".asTerm),
      ) :: Nil
    )

  }
  "Declarations type analysis" should "elaborate variables to no-arg functions per declaration" in {
    val model = {
      """ArchiveEntry "Test"
        |Definitions
        |  Real b();
        |  Real m();
        |End.
        |
        |ProgramVariables
        |  Real x;
        |  Real v;
        |  Real a;
        |End.
        |
        |Problem
        |  x<=m & b>0 -> [a:=-b; {x'=v,v'=a & v>=0}]x<=m
        |End.
        |End.
        |""".stripMargin
    }
    val m = FuncOf(Function("m", None, Unit, Real), Nothing)
    val b = FuncOf(Function("b", None, Unit, Real), Nothing)
    val x = Variable("x")
    val a = Variable("a")
    val v = Variable("v")
    ArchiveParser.parseAsFormula(model) shouldBe Imply(
      And(LessEqual(x, m), Greater(b, Number(0))),
      Box(
        Compose(Assign(a, Neg(b)), ODESystem("{x'=v,v'=a}".asDifferentialProgram, GreaterEqual(v, Number(0)))),
        LessEqual(x, m),
      ),
    )
  }

  it should "not allow variables refer to functions with parameters" in {
    val model = {
      """ArchiveEntry "Test"
        |Definitions
        |  Real b(Real x);
        |  Real m(Real x, Real y);
        |End.
        |
        |ProgramVariables
        |  Real x;
        |  Real v;
        |  Real a;
        |End.
        |
        |Problem
        |  x<=m & b>0 -> [a:=-b; {x'=v,v'=a & v>=0}]x<=m
        |End.
        |End.
        |""".stripMargin
    }
    a[ParseException] should be thrownBy ArchiveParser.parseAsFormula(model)
  }

  it should "succeed when ()'s are used." in {
    val model = {
      """ArchiveEntry "Test"
        |Definitions
        |  Real b();
        |  Real m();
        |End.
        |
        |ProgramVariables
        |  Real x;
        |  Real v;
        |  Real a;
        |End.
        |
        |Problem
        |  x<=m() & b()>0 -> [a:=-b(); {x'=v,v'=a & v>=0}]x<=m()
        |End.
        |End.
        |""".stripMargin
    }
    ArchiveParser.parseAsFormula(model) shouldBe "x<=m() & b()>0 -> [a:=-b(); {x'=v,v'=a & v>=0}]x<=m()".asFormula
  }
}
