package bellerophon.pptests

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.{BelleParser, BellePrettyPrinter}
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.parser.UnknownLocation
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.UsualTest

/**
  * Very simple positive unit tests for the Bellerophon parser. Useful for TDD and bug isolation but probably not
  * so useful for anything else.
  *
  * @note It may be useful to turn on BelleParser.DEBUG if you're actually debugging.
  * @author Nathan Fulton
  */
@UsualTest
class SimpleBelleParserTests extends TacticTestBase {
  //region Atomic tactics with arguments

  "Atomic / Argument Parser" should "parse a built-in tactic" in {
    BelleParser("nil") shouldBe TactixLibrary.nil
  }

  it should "parse a built-in tactic with arguments" in {
    BelleParser("cut({`1=1`})")
  }

  it should "parse a built-in argument with an absolute top-level postion" in {
    BelleParser("andR(1)") shouldBe TactixLibrary.andR(1)
  }

  it should "parse a built-in argument with an absolute non-top-level postion" in {
    val pos = BelleParser.parseAbsolutePosition("1.1", UnknownLocation)
    BelleParser("boxAnd(1.1)") shouldBe HilbertCalculus.useAt(DerivedAxioms.boxAnd)(pos)
  }

  it should "parse a built-in argument with a position locator" in {
    BelleParser("boxAnd('L)") shouldBe HilbertCalculus.useAt(DerivedAxioms.boxAnd)(Find.FindL(0, None))
  }

  it should "parse a built-in argument with a 'R position locator" in {
    BelleParser("boxAnd('R)") shouldBe HilbertCalculus.useAt(DerivedAxioms.boxAnd)(Find.FindR(0, None))
  }


  it should "parse a built-in tactic that takes a whole list of arguments" in {
    BelleParser("diffInvariant({`1=1`}, 1)") shouldBe TactixLibrary.diffInvariant(Seq("1=1".asFormula) : _*)(1)
  }

  it should "Parse a loop tactic and print it back out" in {
    BelleParser("loop({`1=1`}, 1)") shouldBe TactixLibrary.loop("1=1".asFormula)(1)
    BellePrettyPrinter(TactixLibrary.loop("1=1".asFormula)(1)) shouldBe "loop({`1=1`}, 1)"
  }

  //endregion

  //region Sequential combinator

  "Sequential parser" should "parse e & e" in {
    val result = BelleParser("andR(1) & andR(2)").asInstanceOf[SeqTactic]
    result.left shouldBe TactixLibrary.andR(1)
    result.right shouldBe TactixLibrary.andR(2)
  }

  it should "parse seq right-associative -- e & e & e parses to e & (e & e)" in {
    val result = BelleParser("andR(1) & andR(2) & andR(3)").asInstanceOf[SeqTactic]
    result.left shouldBe TactixLibrary.andR(1)
    result.right.asInstanceOf[SeqTactic].left shouldBe TactixLibrary.andR(2)
    result.right.asInstanceOf[SeqTactic].right shouldBe TactixLibrary.andR(3)
  }

  it should "parse seq right-associative when there are a bunch of parens" in {
    val result = BelleParser("(andR(1)) & (andR(2)) & (andR(3))").asInstanceOf[SeqTactic]
    result.left shouldBe TactixLibrary.andR(1)
    result.right.asInstanceOf[SeqTactic].left shouldBe TactixLibrary.andR(2)
    result.right.asInstanceOf[SeqTactic].right shouldBe TactixLibrary.andR(3)
  }

  it should "parse e & (e & e)" in {
    val result = BelleParser("andR(1) & (andR(2) & andR(3))").asInstanceOf[SeqTactic]
    result.left shouldBe TactixLibrary.andR(1)
    result.right.asInstanceOf[SeqTactic].left shouldBe TactixLibrary.andR(2)
    result.right.asInstanceOf[SeqTactic].right shouldBe TactixLibrary.andR(3)
  }

  it should "parse (e & e) & e" in {
    val result = BelleParser("(andR(1) & andR(2)) & andR(3)").asInstanceOf[SeqTactic]
    result.left.asInstanceOf[SeqTactic].left shouldBe TactixLibrary.andR(1)
    result.left.asInstanceOf[SeqTactic].right shouldBe TactixLibrary.andR(2)
    result.right shouldBe TactixLibrary.andR(3)
  }


  it should "parse compositions of things that parse to partials" in {
    val tactic = BelleParser("nil & nil").asInstanceOf[SeqTactic]
    tactic.left shouldBe TactixLibrary.nil
    tactic.right shouldBe TactixLibrary.nil
  }

  //endregion

  //region Either combinator

  "Either parser" should "parse e | e" in {
    val result = BelleParser("andR(1) | andR(2)").asInstanceOf[EitherTactic]
    result.left shouldBe TactixLibrary.andR(1)
    result.right shouldBe TactixLibrary.andR(2)
  }

  it should "parse either right-associative -- e | e | e parses to e | (e | e)" in {
    val result = BelleParser("andR(1) | andR(2) | andR(3)").asInstanceOf[EitherTactic]
    result.left shouldBe TactixLibrary.andR(1)
    result.right.asInstanceOf[EitherTactic].left shouldBe TactixLibrary.andR(2)
    result.right.asInstanceOf[EitherTactic].right shouldBe TactixLibrary.andR(3)
  }

  it should "parse either right-associative when there are a bunch of parens" in {
    val result = BelleParser("(andR(1)) | (andR(2)) | (andR(3))").asInstanceOf[EitherTactic]
    result.left shouldBe TactixLibrary.andR(1)
    result.right.asInstanceOf[EitherTactic].left shouldBe TactixLibrary.andR(2)
    result.right.asInstanceOf[EitherTactic].right shouldBe TactixLibrary.andR(3)
  }

  it should "parse e | (e | e)" in {
    val result = BelleParser("andR(1) | (andR(2) | andR(3))").asInstanceOf[EitherTactic]
    result.left shouldBe TactixLibrary.andR(1)
    result.right.asInstanceOf[EitherTactic].left shouldBe TactixLibrary.andR(2)
    result.right.asInstanceOf[EitherTactic].right shouldBe TactixLibrary.andR(3)
  }

  it should "parse (e | e) | e" in {
    val result = BelleParser("(andR(1) | andR(2)) | andR(3)").asInstanceOf[EitherTactic]
    result.left.asInstanceOf[EitherTactic].left shouldBe TactixLibrary.andR(1)
    result.left.asInstanceOf[EitherTactic].right shouldBe TactixLibrary.andR(2)
    result.right shouldBe TactixLibrary.andR(3)
  }

  it should "parse e & b | c" in {
    val result = BelleParser("andR(1) & andR(2) | andR(3)").asInstanceOf[EitherTactic]
    result.left.asInstanceOf[SeqTactic].left shouldBe TactixLibrary.andR(1)
    result.left.asInstanceOf[SeqTactic].right shouldBe TactixLibrary.andR(2)
    result.right shouldBe TactixLibrary.andR(3)
  }

  //@todo fix or decide on a precedence of | and &...
  ignore should "parse e | b & c" in {
    val result = BelleParser("andR(1) | andR(2) & andR(3)").asInstanceOf[SeqTactic]
    result.left shouldBe TactixLibrary.andR(1)
    result.right.asInstanceOf[EitherTactic].right shouldBe TactixLibrary.andR(2)
    result.right.asInstanceOf[EitherTactic].left shouldBe TactixLibrary.andR(3)
  }

  //endregion

  //region Branching combinator

  "Branch combinator parser" should "parse e <(e,e)" in {
    val result = BelleParser("andR(1) <(andR(2), andR(3))").asInstanceOf[SeqTactic]
    result.left shouldBe TactixLibrary.andR(1)
    result.right.asInstanceOf[BranchTactic].children shouldBe Seq(TactixLibrary.andR(2), TactixLibrary.andR(3))
  }

  it should "parse e <()" in {
    val result = BelleParser("andR(1) <()").asInstanceOf[SeqTactic]
    result.left shouldBe TactixLibrary.andR(1)
    result.right.asInstanceOf[BranchTactic].children shouldBe Seq()
  }

  it should "parse e <(e)" in {
    val result = BelleParser("andR(1) <(andR(1))").asInstanceOf[SeqTactic]
    result.left shouldBe TactixLibrary.andR(1)
    result.right.asInstanceOf[BranchTactic].children shouldBe Seq(TactixLibrary.andR(1))
  }



  //endregion

  //region Kleene Star Comabinator

  "Kleene star parser" should "parse e*" in {
    val tactic = BelleParser("andR(1)*").asInstanceOf[SaturateTactic]
    tactic.child shouldBe   TactixLibrary.andR(1)
    tactic.annotation shouldBe TheType()
  }

  it should "parse (e&e)*" in {
    val tactic = BelleParser("(andR(1) & andR(2))*").asInstanceOf[SaturateTactic]
    tactic.child.asInstanceOf[SeqTactic].left shouldBe TactixLibrary.andR(1)
    tactic.child.asInstanceOf[SeqTactic].right shouldBe TactixLibrary.andR(2)
    tactic.annotation shouldBe TheType()
  }

  "NTIMES repeat combinator parser" should "parse e^22" in {
    val tactic = BelleParser("andR(1)^22").asInstanceOf[RepeatTactic]
    tactic.child shouldBe   TactixLibrary.andR(1)
    tactic.times shouldBe 22
    tactic.annotation shouldBe TheType()
  }

  "saturate parser" should "parse e+" in {
    val tactic = BelleParser("andR(1)+").asInstanceOf[SeqTactic]
    tactic.left shouldBe TactixLibrary.andR(1)
    tactic.right.asInstanceOf[SaturateTactic].child shouldBe   TactixLibrary.andR(1)
    tactic.right.asInstanceOf[SaturateTactic].annotation shouldBe TheType()
  }

  //endregion

  //region Comma lists

  "comma separatred list folding" should "work" in (withMathematica { implicit qeTool => {
    val t =
      """
        |nil<(nil, nil)
      """.stripMargin
    BelleParser(t) //should not cause an exception.
  }})

  it should "work for a tactic (e)" in (withMathematica { implicit qeTool => {
    val t =
      """
        |nil<((nil), nil)
      """.stripMargin
    BelleParser(t) //should not cause an exception.
  }})

  it should "work for a tactic (e) in the final position" in (withMathematica { implicit qeTool => {
    val t =
      """
        |nil<(nil, (nil))
      """.stripMargin
    BelleParser(t) //should not cause an exception.
  }})

  it should "work on tactic that caused original bug" in (withMathematica { implicit qeTool => {
    val t = """implyR(1) &
              |loop({`x<=m`}, 1) <(
              |  MathematicaQE,
              |  MathematicaQE,
              |  partial(composeb(1) & choiceb(1) & andR(1) <(
              |    assignb(1) & diffSolve(1) & nil,
              |    testb(1) & implyR(1) & diffSolve(1) & nil
              |  ))
              |)""".stripMargin
    BelleParser(t) //should not cause an exception.
  }})

  //endregion

  //region Partial tactics

  "partial tactic parser" should "parse partial(e)" in {
    val tactic = BelleParser("partial(andR(1))").asInstanceOf[PartialTactic]
    tactic.child shouldBe TactixLibrary.andR(1)
  }

  it should "parse e partial" in {
    val tactic = BelleParser("andR(1) partial").asInstanceOf[PartialTactic]
    tactic.child shouldBe TactixLibrary.andR(1)
  }

  //endregion
}
