package bellerophon.serializer

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btacticinterface.BTacticParser
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.core.{SuccPos, Provable}
import edu.cmu.cs.ls.keymaerax.tactics.SuccPosition
import org.scalatest.{FlatSpec, Matchers}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

/**
  * Created by nfulton on 12/23/15.
  */
class BTacticParserTests extends FlatSpec with Matchers {
  "The Bellerophon Tactics Parser" should "parse nil & nil" in {
    val result = BTacticParser("nil & nil").get.asInstanceOf[SeqTactic]
    val expected = SeqTactic(Idioms.nil, Idioms.nil)
    result.left shouldBe expected.left
    result.right shouldBe expected.right
  }

  it should "parser nil < (nil, nil, nil)" in {
    val result = BTacticParser("nil < (nil, nil, nil)").get.asInstanceOf[SeqTactic]
    val expected = SeqTactic(Idioms.nil, BranchTactic(Seq(Idioms.nil, Idioms.nil, Idioms.nil)))
    result.left shouldBe expected.left
    result.right.asInstanceOf[BranchTactic].children
      .zip(expected.right.asInstanceOf[BranchTactic].children)
      .map(x => x._1 shouldBe x._2)
  }

  it should "parse partials and built-ins" in {
    val result = BTacticParser("partial(ImplyR)").getOrElse(fail("Could not parse"))
    result.isInstanceOf[PartialTactic] shouldBe true
    result.asInstanceOf[PartialTactic].child.prettyString shouldBe "ImplyR"
  }

  it should "parse post-fix partials and built-ins" in {
    val result = BTacticParser("ImplyR partial").getOrElse(fail("Could not parse"))
    result.isInstanceOf[PartialTactic] shouldBe true
    result.asInstanceOf[PartialTactic].child.prettyString shouldBe "ImplyR"
  }

  it should "parse either" in {
    val result = BTacticParser("nil | ImplyR").get.asInstanceOf[EitherTactic]
    result.left.prettyString shouldBe  """partial(NilT)"""
    result.right.prettyString shouldBe "ImplyR"
  }

  it should "parse *" in {
    val result = BTacticParser("ImplyR*").get
    result.isInstanceOf[SaturateTactic] shouldBe true
    result.asInstanceOf[SaturateTactic].child.prettyString shouldBe "ImplyR"
  }

  it should "parse *@" in {
    val result = BTacticParser("ImplyR*@(TheType)").get
    result.isInstanceOf[SaturateTactic] shouldBe true
    result.asInstanceOf[SaturateTactic].child.prettyString shouldBe "ImplyR"
  }

  it should "parse positional tactics" in {
    val tactic = BTacticParser("ImplyR(1)").get
    tactic.isInstanceOf[AppliedPositionTactic] shouldBe true
    val apt = tactic.asInstanceOf[AppliedPositionTactic]
    apt.locator.isInstanceOf[Fixed] shouldBe true
    apt.positionTactic.prettyString shouldBe "ImplyR"
  }

  "Propositional Examples" should "close p() -> p()" in {
    val tactic = BTacticParser("ImplyR(1) & TrivialCloser").get
//    val tactic = ExposedTacticsLibrary.tactics("ImplyR") & ExposedTacticsLibrary.tactics("TrivialCloser")
    val value = BelleProvable(Provable.startProof("p() -> p()".asFormula))
    val result = SequentialInterpreter()(tactic, value)
    result match {
      case BelleProvable(resultingProvable) => resultingProvable.isProved shouldBe true
      case _ => throw new Exception("Expected a BelleProvable.")
    }
  }
}
