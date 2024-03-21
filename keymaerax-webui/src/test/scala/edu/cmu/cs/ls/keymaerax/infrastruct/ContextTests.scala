/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.infrastruct

import edu.cmu.cs.ls.keymaerax.bellerophon.ReflectiveExpressionBuilder
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.{BellePrettyPrinter, DLBelleParser}
import edu.cmu.cs.ls.keymaerax.core.{Choice, DotFormula, DotTerm, PrettyPrinter, Test, True}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter.StringToStringConverter
import edu.cmu.cs.ls.keymaerax.parser.{ArchiveParser, DLArchiveParser, KeYmaeraXPrettyPrinter}
import edu.cmu.cs.ls.keymaerax.{Configuration, FileConfiguration}
import org.scalatest.BeforeAndAfterEach
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/** Tests contexts. */
class ContextTests extends AnyFlatSpec with Matchers with BeforeAndAfterEach {

  override protected def beforeEach(): Unit = {
    Configuration.setConfiguration(FileConfiguration)
    ArchiveParser
      .setParser(new DLArchiveParser(new DLBelleParser(BellePrettyPrinter, ReflectiveExpressionBuilder(_, _, None, _))))
    PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter.pp)
  }

  "Contexts" should "reconstruct the original formula" in {
    val f = "\\forall x (0 = 1 | [x:=2;]true)".asFormula
    val (ctx, e) = Context.at(f, PosInExpr(0 :: Nil))
    ctx(e) shouldBe f
    val (ctx2, e2) = Context.at(f, PosInExpr(0 :: 1 :: 0 :: Nil))
    ctx2(e2) shouldBe f
    val (ctx3, e3) = Context.at(f, PosInExpr(0 :: 0 :: 0 :: Nil))
    ctx3(e3) shouldBe f
  }

  it should "reconstruct the original program" in {
    val a = "?true;x:=2;".asProgram
    val (ctx, e) = Context.at(a, PosInExpr(0 :: Nil))
    ctx(e) shouldBe a
    val (ctx2, e2) = Context.at(a, PosInExpr(1 :: 1 :: Nil))
    ctx2(e2) shouldBe a
    val (ctx3, e3) = Context.at(a, PosInExpr(0 :: 0 :: Nil))
    ctx3(e3) shouldBe a
  }

  it should "reconstruct the original term" in {
    val t = "2+f(x)".asTerm
    val (ctx, e) = Context.at(t, PosInExpr(0 :: Nil))
    ctx(e) shouldBe t
    val (ctx2, e2) = Context.at(t, PosInExpr(1 :: 0 :: Nil))
    ctx2(e2) shouldBe t
  }

  it should "reconstruct the original differential program" in {
    val c = "x' = y+2, y' = f(x)".asDifferentialProgram
    val (ctx, e) = Context.at(c, PosInExpr(0 :: Nil))
    ctx(e) shouldBe c
    val (ctx2, e2) = Context.at(c, PosInExpr(1 :: 1 :: 0 :: Nil))
    ctx2(e2) shouldBe c

  }

  "Context(dot)" should "behave as the identity" in {
    val ctx = Context(DotTerm())
    val t = "0".asTerm
    val aux = ctx(t)
    aux shouldBe t

    val ctx2 = Context(DotFormula)
    val f = "true".asFormula
    val aux2 = ctx2(f)
    aux2 shouldBe f

    import Context.DotProgram
    val ctx3 = Context(DotProgram)
    val p = "?true;".asProgram
    val aux3 = ctx3(p)
    aux3 shouldBe p

  }

  "Different context construction" should "lead to the same context" in {
    val ctx1 = Context("!⎵ -> true".asFormula)
    val ctx2 = Context("⎵ -> true".asFormula)(Context("!⎵".asFormula))
    val (ctx3, _) = Context.at("!false -> true".asFormula, PosInExpr(0 :: 0 :: Nil))
    val (ctx4, _) = Context.at("!true -> true".asFormula, PosInExpr(0 :: 0 :: Nil))
    ctx1 shouldBe ctx2
    ctx3 shouldBe ctx4
    ctx3 shouldBe ctx2 // This fails for TermContext (i.e. a hole is a term), as the behaviour differs.
    ctx2 shouldBe ctx3
  }

  "Non Context[Formula]" should "not fail when applied (without bounding variables)" in {
    import Context.DotProgram
    Context("x + .".asTerm)("0".asTerm) shouldBe "x + 0".asTerm
    Context(Choice(Test(True), DotProgram))("x:=2;".asProgram) shouldBe "?true;++x:=2;".asProgram
  }

  "TermContexts" should "FEATURE_REQUEST: not fail because of admissibility issue" in {
    val f = "[x:=2;]x = 0".asFormula
    val (ctx1, e) = Context.at(f, PosInExpr(1 :: 0 :: Nil))
    val ctx2 = Context("[x:=2;].=0".asFormula)
    ctx1(e) shouldBe f
    ctx2(e) shouldBe f // Currently fails
  }
}
