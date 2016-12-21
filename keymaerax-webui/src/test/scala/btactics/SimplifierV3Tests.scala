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
    val result = proveBy(fml, SimplifierV3.simpTac()(1))
    println(result)

  }

  "SimplifierV3" should "do dependent arithmetic simplification" in withMathematica { qeTool =>
    val fml = "ar > 0 -> (x - 0 + 0 * y + 0 + 0/ar >= 0 - k)".asFormula
    val result = proveBy(fml, SimplifierV3.simpTac()(1))
    println(result)
  }

  "SimplifierV3" should "do full sequent simplification" in withMathematica { qeTool =>
    val antes = IndexedSeq(
      "(x - 0 + 0 * y + 0 + 0/ar >= 0 - k)".asFormula,
      "ar>0".asFormula,
      "x * y = z + y + 0 - 0^2".asFormula,
      "dhd-(a*t_+dho)=(-w*ad)*0".asFormula
    )
    val succs = IndexedSeq(
      "P_() | Q_() & ar >0 | P_() | Q()".asFormula,
      "P_() | Q_() & ar >0 | P_() | Q()".asFormula,
      "dhd-(a*t_+dho)=-w*ad*0".asFormula
    )
    //todo: A 'not' like mechanism to simplify across multiple succedents?
    val pr = proveBy(Sequent(antes,succs),fullSimpTac)
    println(pr)
  }

  "SimplifierV3" should "search for close heuristics" in withMathematica { qeTool =>
    val fml = " 0 > x -> x <= 0 & y = 0 & z<x -> x != y+z | x >= 5 -> 5 < x | (x !=5 -> 5<x ) & a = 0 & y = z+a+b & a+z+b = y".asFormula
    val result = proveBy(fml, SimplifierV3.simpTac()(1))
    result.subgoals.head.succ should contain only "0>x->y=0&z < x->x!=y+z|x>=5->5 < x|!x!=5&a=0&y=z+a+b&a+z+b=y".asFormula
  }

  "SimplifierV3" should "allow controlled custom rewrites" in withMathematica { qeTool =>
    //Force any =0s to be rewritten
    val custom1 = proveBy("F_() = 0 -> (F_() = 0)".asFormula,TactixLibrary.QE)
    //Get rid of deMorgan once
    val custom2 = DerivedAxioms.notNotEqual.fact

    val fml = " 0 > x -> x <= 0 & y = 0 & z<x -> x != y+z | x >= 5 -> 5 < x | (x !=5 -> 5<x ) & a = 0 & y = z+a+b & a+z+b = y".asFormula
    val result = proveBy(fml,
      SimplifierV3.simpTac(taxs = composeIndex(defaultTaxs, (t => List(custom1))))(1)&
      SimplifierV3.simpTac(faxs = composeIndex((f=>List(custom2)),defaultFaxs))(1))
    result.subgoals.head.succ should contain only "0>x->y=0&z < x->5 < x|x=5&a=0&0=z+b".asFormula
  }

}
