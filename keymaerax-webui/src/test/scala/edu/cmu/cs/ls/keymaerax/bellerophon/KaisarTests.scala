package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.bellerophon.Kaisar._
import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase
import edu.cmu.cs.ls.keymaerax.core._
import org.scalatest.{FlatSpec, Matchers}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._


/**
  * Created by bbohrer on 12/3/16.
  */
class KaisarTests extends TacticTestBase /*FlatSpec with Matchers */{
  "Proof with no programs" should "prove" in {
    val pq = "p() & q()".asFormula
    val p = "p()".asFormula
    val e:BelleExpr = /* "ImplyR(1) & AndL(1) & CloseId(1,1)" */
      implyR(1) & andL(-1) & close(-1,1)
    val proof: Proof = (Imply(pq,p), List(Show(Variable("x"), Imply(pq,p), (Nil, e))))
    Kaisar.eval(proof)
  }
}
