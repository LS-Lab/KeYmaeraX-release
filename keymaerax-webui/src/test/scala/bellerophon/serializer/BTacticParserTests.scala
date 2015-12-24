package bellerophon.serializer

import edu.cmu.cs.ls.keymaerax.bellerophon.{BranchTactic, SeqTactic}
import edu.cmu.cs.ls.keymaerax.btacticinterface.BTacticParser
import edu.cmu.cs.ls.keymaerax.btactics._
import org.scalatest.{FlatSpec, Matchers}

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

  //todo: either, repeat, ntimes, ...
}
