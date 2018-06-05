package btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.{AntePosition, OnAll, SuccPosition}
import edu.cmu.cs.ls.keymaerax.btactics.PolynomialArith._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.btactics.SimplifierV3
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.ParseException
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.{IsabelleConverter, TermProvable$}

import scala.collection.immutable._
import scala.collection.mutable.ListBuffer

/**
  * Created by yongkiat on 11/27/16.
  */
class WitnessArithTests extends TacticTestBase {


  "PolynomialArith" should "Arith 1" in withMathematica { qeTool =>
    val strs = List("\\forall v_0 \\forall t_0 \\forall ep_0 \\forall d_0 \\forall V_0 (V_0>=0&d_0>=v_0*(ep_0-t_0)&ep_0>=0&t_0>=0&V_0>=0&ep_0>=0&t_0<=ep_0&0<=v_0&v_0<=V_0&t_0<=ep_0->t_0>=0&v_0>=0&d_0>=v_0*(ep_0-t_0))",
      "\\forall v_0 \\forall t_0 \\forall ep_0 \\forall d_0 \\forall V_0 (V_0>=0&d_0>=v_0*(ep_0-t_0)&ep_0>=0&t_0>=0&V_0>=0&ep_0>=0&t_0<=ep_0&0<=v_0&v_0<=V_0&t_0<=ep_0->\\forall t (t<=ep_0->1>=0&0>=0&-v_0>=v_0*(0-1)))",
      "\\forall ep_0 \\forall d_0 \\forall V_0 (d_0>=0&V_0>=0&ep_0>=0&V_0>=0&ep_0>=0->0<=ep_0)",
      "\\forall ep_0 \\forall d_0 \\forall V_0 (d_0>=0&V_0>=0&ep_0>=0&V_0>=0&ep_0>=0->0<=V_0)",
      "\\forall v_0 \\forall t_0 \\forall ep_0 \\forall d_0 \\forall V_0 (V_0>=0&ep_0>=0&V_0>=0&ep_0>=0&d_0>=v_0*(ep_0-t_0)&t_0>=0&t_0<=ep_0&0<=v_0&v_0<=V_0->(d_0>=V_0*ep_0->\\forall v (0<=v&v<=V_0->d_0>=v*(ep_0-0)&0>=0&0<=ep_0&0<=v&v<=V_0))&d_0>=0*(ep_0-0)&0>=0&0<=ep_0&0<=0&0<=V_0)",
      "\\forall ep_0 \\forall d_0 \\forall V_0 (d_0>=0&V_0>=0&ep_0>=0&V_0>=0&ep_0>=0->d_0>=0*(ep_0-0))",
      "\\forall v_0 \\forall t_0 \\forall ep_0 \\forall d_0 \\forall V_0 (V_0>=0&ep_0>=0&V_0>=0&ep_0>=0&d_0>=v_0*(ep_0-t_0)&t_0>=0&t_0<=ep_0&0<=v_0&v_0<=V_0->d_0>=0)",
      "\\forall ep_0 \\forall d_0 \\forall V_0 (d_0>=0&V_0>=0&ep_0>=0&V_0>=0&ep_0>=0->0<=0)",
      "\\forall ep_0 \\forall d_0 \\forall V_0 (d_0>=0&V_0>=0&ep_0>=0&V_0>=0&ep_0>=0->0>=0)",
      "\\forall v_0 \\forall t_0 \\forall ep_0 \\forall d_0 \\forall V_0 (V_0>=0&ep_0>=0&V_0>=0&ep_0>=0&0<=v_0&v_0<=V_0&t_0<=ep_0&t_0>=0&v_0>=0&d_0>=v_0*(ep_0-t_0)->d_0>=v_0*(ep_0-t_0)&t_0>=0&t_0<=ep_0&0<=v_0&v_0<=V_0)"
    )

    val problems = ListBuffer[Formula]()
    for(s <- strs)
       try{
         val f = s.asFormula
         problems += f
       }catch { case e:ParseException => ()}

    val res = problems.map( s => proveBy(s,(allR(1)*) & prop & OnAll((allR(1)*) & prop) & OnAll(SimplifierV3.fullSimpTac() & ((RCF | close)*))))

    val nontriv = res.filterNot(_.isProved)

    val prepared = nontriv.map( p => proveBy(p,OnAll(prepareArith & printGoal)).subgoals).flatten

    val witnesses = List(((List(),List((1,"ep_0","wit__1^2 + t","-1"),(1,"t","-wit__1^2 + wit__2^2 + t_0","-1"),(3,"t_0","-wit__2^2 + wit__5^2","1"),(1,"V_0","wit__3^2 + v_0","-1"),(1,"v_0","wit__4^2","-1"),(3,"d_0","wit__2^2*wit__4^2 + wit_^2","1")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm)),List(("1","wit__0")).map( s => (s._1.asTerm,s._2.asTerm)),Some(List((0,"1"),(1,"0"),(2,"0")).map (s => (s._1,s._2.asTerm))))),
    ((List(),List((3,"d_0","V_0*ep_0 + wit__3^2","1"),(5,"ep_0","wit__6^2 + t_0","-1"),(1,"v","-wit__1^2 + V_0","1"),(1,"V_0","wit__1^2 + wit__2^2","-1"),(1,"v_0","wit__1^2 + wit__2^2 - wit__4^2","1"),(2,"t_0","wit__7^2","1")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm)),List(("1","wit__0*wit__1*wit__6"),("1","wit__0*wit__1*wit__7"),("1","wit__0*wit__3")).map( s => (s._1.asTerm,s._2.asTerm)),Some(List((0,"1"),(1,"-wit__0^2*wit__6^2 - wit__0^2*wit__7^2 + wit__0^2*wit__9^2"),(2,"0"),(3,"-wit__0^2*wit__1^2 - wit__0^2*wit__2^2 + wit__0^2*wit__4^2 + wit__0^2*wit__5^2"),(4,"0")).map (s => (s._1,s._2.asTerm))))),
    ((List(),List((5,"d_0","(ep_0 - t_0)*v_0 + wit__5^2","1"),(1,"V_0","wit__1^2 + v_0","-1"),(1,"v_0","wit__2^2","-1"),(1,"ep_0","wit__3^2 + t_0","-1"),(1,"t_0","wit__4^2","1")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm)),List(("1","wit__0*wit__2*wit__3"),("1","wit__0*wit__5")).map( s => (s._1.asTerm,s._2.asTerm)),Some(List((0,"1"),(1,"wit_^2*wit__0^2 - wit__0^2*wit__1^2 - wit__0^2*wit__2^2"),(2,"wit__0^2*wit__3^2 + wit__0^2*wit__4^2 - wit__0^2*wit__6^2")).map (s => (s._1,s._2.asTerm))))),
    ((List(),List((5,"d_0","(ep_0 - t_0)*v_0 + wit__5^2","1"),(1,"V_0","wit__1^2 + v_0","-1"),(1,"v_0","wit__2^2","-1"),(1,"ep_0","wit__3^2 + t_0","-1"),(1,"t_0","wit__4^2","1")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm)),List(("1","wit__0*wit__2*wit__3"),("1","wit__0*wit__5")).map( s => (s._1.asTerm,s._2.asTerm)),Some(List((0,"1"),(1,"wit_^2*wit__0^2 - wit__0^2*wit__1^2 - wit__0^2*wit__2^2"),(2,"wit__0^2*wit__3^2 + wit__0^2*wit__4^2 - wit__0^2*wit__6^2")).map (s => (s._1,s._2.asTerm))))))
    for ((p,w) <- prepared zip witnesses)
    {
      val linElim = w._2
      val sos = w._3
      val insts = w._4
      val pr = proveBy(p,linearElim(linElim) & genWitnessTac(List(),sos,insts))
      pr shouldBe 'proved
    }
  }
}
