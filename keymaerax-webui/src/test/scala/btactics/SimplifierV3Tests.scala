package btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.PosInExpr
import edu.cmu.cs.ls.keymaerax.btactics.SimplifierV3._
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

import scala.collection.immutable._

/**
  * Created by yongkiat on 12/19/16.
  */
class SimplifierV3Tests extends TacticTestBase {

  "SimplifierV3" should "simplify propositions" in withMathematica { qeTool =>
    val fml = "R() -> P() & Q() -> P() & (R() & P()) & Q() & (R() & P() & Z() & Y())".asFormula
    println(formulaSimp(fml))
    println(simpWithDischarge(IndexedSeq(),fml))
  }

  "SimplifierV3" should "do dependent arithmetic simplification" in withMathematica { qeTool =>
    val fml = "ar > 0 -> (x - 0 + 0 * y + 0 + 0/ar >= 0 - k)".asFormula
    //V2 would not be able to simplify 0/ar
    println(formulaSimp(fml))
    println(simpWithDischarge(IndexedSeq(),fml))
  }
}
