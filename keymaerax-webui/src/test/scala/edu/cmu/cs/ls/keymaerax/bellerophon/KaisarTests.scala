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

  "Proof with no programs" should "prove" in {
    val e:BelleExpr = /* "ImplyR(1) & AndL(1) & CloseId(1,1)" */
      implyR(1) & andL(-1) & close(-1,1)
    val proof: Proof = (Imply(pq,p), List(Show(Variable("x"), Imply(pq,p), (Nil, e))))
    Kaisar.eval(proof)
  }

  "Proof with one program that modifies nothing" should "prove" in {
    withZ3 (qeTool => {
      val box = "[?p();]p()".asFormula
      val prog = "?p();".asProgram
      val e: BelleExpr = debug("what") & chase(1) & implyR(1) & debug("what") & close
      val proof: Proof = (box, List(Run(Variable("a"), prog), Show(Variable("x"), "p()".asFormula, (Nil, e))))
      Kaisar.eval(proof)
    })
  }
  "Proof with one program that modifies a relevant variable" should "prove" in {
    withZ3 (qeTool => {
      val box = "[x:=1;]x>0".asFormula
      val prog = "x:=1;".asProgram
      val e: BelleExpr = debug("what") & chase(1) & debug("what") & QE
      val proof: Proof = (box, List(Run(Variable("a"), prog), Show(Variable("x"), "x>0".asFormula, (Nil, e))))
      Kaisar.eval(proof)
    })
  }

  /* Multiple programs */
  /* This test will pass once we start V()-ing in the appropriate programs after doing a step. */
  "Proof with two programs that independently modify a relevant variable" should "prove" in {
    withZ3 (qeTool => {
      val box = "[x:=2;][x:= 1;]x>0".asFormula
      val prog1 = "x:=2;".asProgram
      val prog2 = "x:=1;".asProgram
      val e: BelleExpr = debug("what1") & chase(1) & debug("what2") & QE
      val proof: Proof = (box, List(Run(Variable("a"), prog1), Run(Variable("b"), prog2), Show(Variable("x"), "x>0".asFormula, (Nil, e))))
      Kaisar.eval(proof)
    })
  }

  /* Use programs */
  "Proof with using of program" should "prove" in {
    withZ3 (qeTool => {
      val box = "[x:=2;][x:= x - 1;]x>0".asFormula
      val prog1 = "x:=2;".asProgram
      val prog2 = "x:=x - 1;".asProgram
      val e: BelleExpr = debug("what1") & chase(1) & debug("what2") & QE
      val proof: Proof = (box, List(Run(Variable("a"), prog1), Run(Variable("b"), prog2), Show(Variable("x"), "x>0".asFormula, (List(ProgramVariable(Variable("a"))), e))))
      Kaisar.eval(proof)
    })
  }

  /* Use facts */
  "Proof with using of facts" should "prove" in {
    withZ3 (qeTool => {
      val box = "[x:=2;][x:= x - 1;]x>0".asFormula
      val prog1 = "x:=2;".asProgram
      val prog2 = "x:=x - 1;".asProgram
      val e1: BelleExpr = debug("what1") & chase(1) & debug("what2") & QE
      val e2: BelleExpr = debug("what1") & chase(1) & debug("what2") & QE
      val proof: Proof = (box, List(
        Run(Variable("a"), prog1),
        Show(Variable("x"),"x > 1".asFormula, (Nil, e1)),
        Run(Variable("b"), prog2),
        Show(Variable("y"), "x>0".asFormula, (List(FactVariable(Variable("x"))), e2))))
      Kaisar.eval(proof)
    })
  }


}
