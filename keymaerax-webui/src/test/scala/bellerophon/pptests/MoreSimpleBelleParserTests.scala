package bellerophon.pptests

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.core.Provable
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import org.scalatest.{FlatSpec, Matchers}

/**
  * These are probably unnecessary now that SimpleBelleParserTests is  around, but they are very fast so additional
  * coverage can't hurt.
  * @author Nathan Fulton
  */
class MoreSimpleBelleParserTests extends TacticTestBase {
  @deprecated("Switch to BelleParser", "4.2b1")
  private def oldParser(s: String): BelleExpr = BTacticParser(s).get

  private def newParser(s: String): BelleExpr = BelleParser(s)

  /** The parsing function to use for these test cases. */
  private val parser : String => BelleExpr = newParser

  "The Bellerophon Tactics Parser" should "parse nil & nil" in {
    val result = parser("nil & nil").asInstanceOf[SeqTactic]
    val expected = SeqTactic(Idioms.nil, Idioms.nil)
    result.left shouldBe expected.left
    result.right shouldBe expected.right
  }

  it should "parser nil < (nil, nil, nil)" in {
    val result = parser("nil < (nil, nil, nil)").asInstanceOf[SeqTactic]
    val expected = SeqTactic(Idioms.nil, BranchTactic(Seq(Idioms.nil, Idioms.nil, Idioms.nil)))
    result.left shouldBe expected.left
    result.right.asInstanceOf[BranchTactic].children
      .zip(expected.right.asInstanceOf[BranchTactic].children)
      .map(x => x._1 shouldBe x._2)
  }

  it should "parse expression arguments with {} in them" in {
    parser("loop({`[{x' = v, v' = -b}]x <= m`}, 1)") //ok
  }

  it should "parse partials and built-ins" in {
    val result = parser("partial(implyR)")
    result.isInstanceOf[PartialTactic] shouldBe true
    result.asInstanceOf[PartialTactic].child.prettyString shouldBe "implyR"
  }

  it should "parse post-fix partials and built-ins" in {
    val result = parser("implyR partial")
    result.isInstanceOf[PartialTactic] shouldBe true
    result.asInstanceOf[PartialTactic].child.prettyString shouldBe "implyR"
  }

  it should "parse either" in {
    val result = parser("nil | implyR").asInstanceOf[EitherTactic]
    result.left.prettyString shouldBe  """partial(nil)"""
    result.right.prettyString shouldBe "implyR"
  }

  it should "parse *" in {
    val result = parser("implyR*")
    result.isInstanceOf[SaturateTactic] shouldBe true
    result.asInstanceOf[SaturateTactic].child.prettyString shouldBe "implyR"
  }

  it should "parse *@" in {
    val result = parser("implyR*")
    result.isInstanceOf[SaturateTactic] shouldBe true
    result.asInstanceOf[SaturateTactic].child.prettyString shouldBe "implyR"
  }

  it should "parse positional tactics" in {
    val tactic = parser("implyR(1)")
    tactic.isInstanceOf[AppliedPositionTactic] shouldBe true
    val apt = tactic.asInstanceOf[AppliedPositionTactic]
    apt.locator.isInstanceOf[Fixed] shouldBe true
    apt.positionTactic.prettyString shouldBe "implyR"
  }

  it should "parse formula tactics" in {
    val tactic = parser("Loop({`v >= 0`})")
    tactic.isInstanceOf[DependentPositionTactic] shouldBe true
    val dpt = tactic.asInstanceOf[DependentPositionTactic]
  }

  it should "parse j(x) as a term or a formula depending on ArgInfo." in {
    val formulaTactic = parser("Loop({`j(x)`})")
    val termTactic = parser("diffGhost({`x`}, {`j(x)`}, {`j(x)`}, {`j(x)`})")
  }

  "Propositional Examples" should "close p() -> p()" in {
    val tactic = parser("implyR(1) & TrivialCloser")
//    val tactic = ExposedTacticsLibrary.tactics("implyR") & ExposedTacticsLibrary.tactics("TrivialCloser")
    val value = BelleProvable(Provable.startProof("p() -> p()".asFormula))
    val result = SequentialInterpreter()(tactic, value)
    result match {
      case BelleProvable(resultingProvable, _) => resultingProvable.isProved shouldBe true
      case _ => throw new Exception("Expected a BelleProvable.")
    }
  }
}
