package btactics


import edu.cmu.cs.ls.keymaerax.bellerophon.{PosInExpr, SuccPosition}
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.btactics.IntervalArithmetic._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._

import scala.collection.immutable.Nil

/**
  * Created by yongkiat on 9/8/16.
  */
class IntervalArithmeticTests extends TacticTestBase  {


  "interval arithmetic" should "derive repeated addition bounds" in withMathematica { qeTool =>
    val fml = "(x+y)+z+((x+y)+z+5) <= a+b".asFormula
    println(deriveFormulaProof(fml))
  }

  "interval arithmetic" should "derive lower bounds for different forms of squares" in withMathematica { qeTool =>
    val fml = "x^2<=xopost()^2 & (a+b)^2 <= c^2 | (a+b)^2 <= (c+d)^2".asFormula
    println(deriveFormulaProof(fml))
  }

  "interval arithmetic" should "derive checked bounds for simple divisor" in withMathematica { qeTool =>
    val fml = "a/b <= c/d".asFormula
    println(deriveFormulaProof(fml))
  }

  "interval arithmetic" should "derive checked bounds for complex divisor" in withMathematica { qeTool =>
    val fml = "(x+y)/(a+b) <= (a+b)/(x+y)".asFormula
    println(deriveFormulaProof(fml))
  }

  "interval arithmetic" should "fast multiplication on known variables" in withMathematica { qeTool =>
    val fml = "a*b*c <= a*b".asFormula
    println(deriveFormulaProof(fml))
  }

  "interval arithmetic" should "derive ETCS" in withMathematica { qeTool =>
    val uf = "((dpost()>=0&d^2-dpost()^2<=2*b*(mpost()-m)&vdespost()>=0)&(((((((((SBpost()=SB)&vpost()=v)&statepost()=state)&dopost()=d)&zpost()=z)&tpost()=t)&mopost()=m)))&apost()=a|(((((((((vdespost()=vdes&SBpost()=SB)&vpost()=v)&statepost()=brake)&dopost()=do)&zpost()=z)&tpost()=t)&mopost()=mo)&mpost()=m)&dpost()=d)&apost()=a)|v<=vdes&(apost()>=-b&apost()<=A)&((m-z<=(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)|state=brake)&(v>=0&0<=ep)&(((((((((vdespost()=vdes&SBpost()=(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v))&vpost()=v)&statepost()=state)&dopost()=do)&zpost()=z)&tpost()=0)&mopost()=mo)&mpost()=m)&dpost()=d)&apost()=-b|!(m-z<=(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)|state=brake)&(v>=0&0<=ep)&(((((((((vdespost()=vdes&SBpost()=(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v))&vpost()=v)&statepost()=state)&dopost()=do)&zpost()=z)&tpost()=0)&mopost()=mo)&mpost()=m)&dpost()=d))|v>=vdes&(apost() < 0&apost()>=-b)&((m-z<=(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)|state=brake)&(v>=0&0<=ep)&(((((((((vdespost()=vdes&SBpost()=(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v))&vpost()=v)&statepost()=state)&dopost()=do)&zpost()=z)&tpost()=0)&mopost()=mo)&mpost()=m)&dpost()=d)&apost()=-b|!(m-z<=(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)|state=brake)&(v>=0&0<=ep)&(((((((((vdespost()=vdes&SBpost()=(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v))&vpost()=v)&statepost()=state)&dopost()=do)&zpost()=z)&tpost()=0)&mopost()=mo)&mpost()=m)&dpost()=d))".asFormula
    //Conversion to NNF
    val refl = proveBy(Equiv(uf,uf),byUS("<-> reflexive"))
    val nnf = chaseFor((exp: Expression) => exp match {
      case And(_,_) => "& recursor" :: Nil
      case Or(_,_) => "| recursor" :: Nil
      case Imply(_,_) => "-> expand" :: Nil
      case Not(_) => AxiomIndex.axiomsFor(exp)
      case _ => Nil
    }, (s,p)=>pr=>pr)(SuccPosition(1,1::Nil))(refl)

    val pr = chaseFor((exp: Expression) => exp match {
      case And(_,_) => "& recursor" :: Nil
      case Or(_,_) => "| recursor" :: Nil
      case Greater(l,r) => "> flip"::Nil
      case GreaterEqual(l,r) => ">= flip"::Nil
      case _ => Nil
    }, (s,p)=>pr=>pr)(SuccPosition(1,1::Nil))(nnf)

    val f =pr.conclusion.succ(0).sub(PosInExpr(1::Nil)).get.asInstanceOf[Formula]
    println(deriveFormulaProof(f))
  }
}
