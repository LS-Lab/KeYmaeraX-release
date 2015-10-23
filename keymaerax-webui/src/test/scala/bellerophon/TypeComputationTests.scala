package bellerophon

import edu.cmu.cs.ls.keymaerax.btactics.PropositionalTactics._
import org.scalatest.{FlatSpec, Matchers}

/**
 * Created by nfulton on 10/22/15.
 */
class TypeComputationTests extends FlatSpec with Matchers {
  "BelleExpr.belleType" should "computer the type of AndR" in {
    println(AndR.belleType)
  }

  it should "compute the type of (Lt.e) & (Lt.d) to be Lt(e&d)" in {
    val andandand = AndR & AndR
    println(andandand.belleType)
  }
}
