package bellerophon.serializer

import edu.cmu.cs.ls.keymaerax.bellerophon.BTacticParser
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BellePrettyPrinter
import org.scalatest.{FlatSpec, Matchers}

/**
  * Created by nfulton on 3/15/16.
  */
class BTacticPrettyPrinterTests extends FlatSpec with Matchers {
  val parser = BTacticParser

  "Printer" should "print a built-in guy" in {
    val tactic = parser("nil").get
    BellePrettyPrinter(tactic) shouldBe "partial(NilT)"

  }
}
