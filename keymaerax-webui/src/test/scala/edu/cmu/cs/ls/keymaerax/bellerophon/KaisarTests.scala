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
class KaisarTests extends TacticTestBase {
  val pq = "p() & q()".asFormula
  val p = "p()".asFormula
  "Proof with no programs" should "prove" ignore {
    val e:BelleExpr = /* "ImplyR(1) & AndL(1) & CloseId(1,1)" */
      implyR(1) & andL(-1) & close(-1,1)
    val proof: Proof = (Imply(pq,p), List(Show(Variable("x"), Imply(pq,p), (Nil, e))))
    Kaisar.eval(proof)
  }

  /* Next: program that modifies */
  "Proof with one program that modifies a relevant variable" should "prove" in {
    withZ3 (qeTool => {
      val box = "[x:=1;]x>0".asFormula
      val prog = "x:=1;".asProgram
      val e: BelleExpr = debug("what") & chase(1) & debug("what") & QE
      val proof: Proof = (box, List(Run(Variable("a"), prog), Show(Variable("x"), "x>0".asFormula, (Nil, e))))
      Kaisar.eval(proof)
    })

  }
  /* Program that doesn't modify */
  /* Multiple programs */

  /* Use facts */

  /* Use programs*/
}
