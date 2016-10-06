package btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.PosInExpr
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.btactics.SimplifierV2._
import edu.cmu.cs.ls.keymaerax.core._

import scala.collection.immutable._

/**
  * Created by yongkiat on 10/5/16.
  */
class SimplifierV2Tests extends TacticTestBase {

  "SimplifierV2" should "simplify repeated propositions under context" in withMathematica { qeTool =>
    val fml = "R() -> P() & Q() -> P() & (R() & P()) & Q() & (R() & P() & Z() & Y())".asFormula
    val ctxt = IndexedSeq("Y()".asFormula)
    val tactic = simpTac
    //Top level simplification at different succedents
    println(proveBy(Sequent(ctxt,IndexedSeq(fml)), tactic(1)))
    println(proveBy(Sequent(ctxt,IndexedSeq(fml,fml,fml)), tactic(2)))
    //Inner simplification
    println(proveBy(Sequent(ctxt,IndexedSeq(fml)), tactic(1,PosInExpr(1::1::Nil))))
    println(proveBy(Sequent(ctxt,IndexedSeq(fml,fml,fml)), tactic(3,PosInExpr(1::1::Nil))))
  }

  "SimplifierV2" should "simplify under quantifiers and modalities" in withMathematica { qeTool =>
    val fml = ("(\\forall x (P() & Q() & x = 0 & P() & Q())) & (\\exists y (P() & Q() & Q() & y = 5)) | " +
      "<{x_'=v&q(x_)}>(P() | P() & Q())").asFormula
    val ctxt = IndexedSeq("x=0".asFormula)
    val tactic = simpTac
    println(proveBy(Sequent(ctxt,IndexedSeq(fml)), tactic(1)))
  }

  "SimplifierV2" should "simplify terms" in withMathematica { qeTool =>
    val fml = "(\\forall t \\forall s (t>=0 & 0 <= s & s<=t -> x=v_0*(0+1*t-0) -> x >= 0))".asFormula
    val ctxt = IndexedSeq("x_0=0".asFormula,"v_0=0".asFormula)
    val tactic = simpTac
    println(proveBy(Sequent(ctxt,IndexedSeq(fml)), tactic(1)))
  }

  "SimplifierV2" should "simplify terms when applied to term position" in withMathematica { qeTool =>
    val fml = "x=v_0*(0+1*t-0) -> x >= 0".asFormula
    val ctxt = IndexedSeq("x_0=0".asFormula,"v_0=0".asFormula)
    val tactic = simpTac
    println(proveBy(Sequent(ctxt,IndexedSeq(fml)), tactic(1,PosInExpr(0::1::Nil))))
  }
}
