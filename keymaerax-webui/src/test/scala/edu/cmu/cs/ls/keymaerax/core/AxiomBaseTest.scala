package edu.cmu.cs.ls.keymaerax.core

import edu.cmu.cs.ls.keymaerax.bellerophon.{DependentPositionTactic, PosInExpr}
import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.AdvocatusTest

import scala.collection.immutable.Nil


/**
  * Test soundness for axioms in AxiomBase.
  *
  * @author Yong Kiam Tan
  */
@AdvocatusTest
class AxiomBaseTest extends TacticTestBase {

  it should "Axiom DV differential variant >= needs existence assumption" in withMathematica { _ =>
    // Exploit an unsound instance of DV
    // It requires a side condition that solutions exist for sufficient duration
    // This side condition is semantical, and difficult to express syntactically
    // There are other options, e.g. requiring Lipschitz continuity, see LAHS (3.5.7)

    //This is an unsound instance because the (right-maximal) existence interval is [0,1)
    val fml = "t=0 & x=1 -> <{x'=x^2,t'=1}> t>=1".asFormula
    val pr = proveBy(fml,implyR(1) & diffVar(1))

    // This one is sound
    val fml2 = "t=0 & x=1 -> [{x'=x^2,t'=1}] (x>=1 & x*(1-t)=1)".asFormula
    val pr2 = proveBy(fml2,implyR(1) &
      diffInvariant("x>=1".asFormula)(1) & dC("x*(1-t)-1=0".asFormula)(1) <(
      dW(1) & QE,
      dG("{y'=-x*y}".asDifferentialProgram,None)(1) &
      existsR("1".asTerm)(1) & dC("y!=0".asFormula)(1) <(
        diffInvariant("(x*(1-t)-1)*y=0".asFormula)(1) & dW(1) & QE,
        dG("{z'=x*z}".asDifferentialProgram,Some("y*z>0".asFormula))(1) &
        existsR("1".asTerm)(1) & dI('full)(1)))
    )

    // prove false
    val pr3 = proveBy("false".asFormula,
      cut("\\exists t \\exists x (t=0&x=1)".asFormula)<(skip,QE) & existsL('L) & existsL('L) &
        cut("<{x'=x^2,t'=1}>t>=1".asFormula) <(
          useAt("<> diamond",PosInExpr(1::Nil))(-2) & hideR(1) & notL('L) &
            dC("(x>=1 & x*(1-t)=1)".asFormula)(1) < (dW(1) & QE, implyRi & by(pr2)),
          hideR(1) & implyRi & by (pr)
        )
    )

    pr3 should not be 'proved
  }

}
