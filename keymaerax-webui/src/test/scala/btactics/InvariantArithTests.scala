package btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.PolynomialArith._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

import scala.collection.immutable._

/**
  * Invariant arithmetic examples
  * From Lectures 10/11
  * Created by yongkiat on 2/3/16.
  */
class InvariantArithTests extends TacticTestBase {


  "InvariantArith" should "solve Lecture 10 DI arithmetic" in withMathematica { qeTool =>
    //All of these prove by normalizing both sides to 0 = 0
    //L10 Example 1
    val i1 = "v^2 + w^2 = r()^2 -> [{v'=w,w'=-v}] v^2+w^2 = r()^2"
    //L10 Example 11
    val i2 = "x^2+x^3-y^2 - c() = 0 -> [{x'=-2*y,y'=-2*x-3*x^2}] x^2+x^3-y^2 - c() = 0"
    //L10 Example 12
    val i3 = "x^4*y^2 + x^2*y^4-3*x^2*y^2+1= c()-> [{x'=2*x^4*y+4*x^2*y^3-6*x^2*y , y'=-4*x^3*y^2-2*x*y^4+6*x*y^2}]x^4*y^2 + x^2*y^4-3*x^2*y^2+1=c()"
    val i4 = "x^4+y^4 = 0 -> [{x'=4*y^3,y'=-4*x^3}]x^4+y^4 = 0"
    //L10 Exercises (6,7,8,9)
    val i5 = "x*y=c() -> [{x'=-x,y'=y,z'=-z}]x*y=c()"
    val i6 = "x^2+4*x*y-2*y^3 -y =1 -> [{x'=-1+4*x-6*y^2,y'=-2*x-4*y}]x^2+4*x*y-2*y^3 -y =1 "
    val i7 = "x^2+y^3/3 = c() -> [{x'=y^2,y'=-2*x}]x^2+y^3/3 = c()"
    val i8 = "(u^2 + v^2 + A()*x^2+B()*y^2)/2 + x^2*y - 1/3 * eps()*y^3 = 0 -> [{x'=u,y'=v,u'=-A()*x-2*x*y,v'=-B()*y+eps()*y^2-x^2}](u^2 + v^2 + A()*x^2+B()*y^2)/2 + x^2*y - 1/3 *eps()*y^3 = 0 "

    val problems = List(i1,i2,i3,i4,i5,i6,i7,i8).map(_.asFormula)

    val tactic = implyR(1) & dI('diffInd)(1) < (QE, //QE just for reflexivity, no problem
      chase(1) &
        normaliseAt(1, 0 :: Nil) &
        normaliseAt(1, 1 :: Nil) & cohideR(1) & byUS("= reflexive")
      )

    val res = problems.map(proveBy(_, tactic))
    res.forall(_.isProved) shouldBe true
  }

  "InvariantArith" should "solve Lecture 11 DI arithmetic (fig 11.5)" in withMathematica { qeTool =>
    val i = "1/3 <= 5 * x^2 -> [{x'=x^3}] 1/3 <= 5 * x^2".asFormula
    //No linear elimination
    val witness = List(("10","wit__0*x^2")).map( s => (s._1.asTerm,s._2.asTerm))
    // The first inequation is used here
    val ineq = List(0)
    val tactic = implyR(1) & dI('diffInd)(1) < (QE, //QE just for reflexivity, no problem
      chase(1) &
        DebuggingTactics.print("Before normalizing") &  prop &
        OnAll(prepareArith2) &
        printGoal &
        genWitnessTac(ineq,witness)
      )
    val res = proveBy(i, tactic)
    res shouldBe 'proved
  }

  "InvariantArith" should "solve Lecture 11 odd order dynamics (Example 11.4)" in withMathematica { qeTool =>
    val i = "x^2 >= 2 -> [{x'=x^5+7*x^3+2*x}] x^2 >= 2".asFormula
    val witness = List(("2","wit__0*x^3 + 7/5*wit__0*x"),("42/5","wit__0*x^2"),("2/25","wit__0*x")).map( s => (s._1.asTerm,s._2.asTerm))
    val ineq = List(0)
    val tactic = implyR(1) & dI('diffInd)(1) < (QE, //QE just for reflexivity, no problem
      chase(1) &
        DebuggingTactics.print("Before normalizing") &  prop &
        OnAll(prepareArith2) &
        printGoal &
        genWitnessTac(ineq,witness)
      )
    val res = proveBy(i, tactic)
    res shouldBe 'proved
  }

  "InvariantArith" should "solve Lecture 11 even order dynamics (Example 11.5)" in withMathematica { qeTool =>
    val i = "x^3 >= 2 -> [{x'=x^4+6*x^2+5}] x^3 >= 2".asFormula
    val witness = List(
      ("9/1499","1"),
      ("47101/1499","wit__0*x^2"),
      ("4524/1499"," wit__0*x^3 - 19957/9048*wit__0*x"),
      ("11049671/27125904","wit__0*x")).map( s => (s._1.asTerm,s._2.asTerm))
    val tactic = implyR(1) & dI('diffInd)(1) < (QE, //QE just for reflexivity, no problem
      chase(1) &
        DebuggingTactics.print("Before normalizing") &  prop &
        OnAll(prepareArith2) &
        printGoal &
        witnessTac(witness)
      )
    val res = proveBy(i, tactic)
    res shouldBe 'proved
  }

  "InvariantArith" should "solve Lecture 11 DI arithmetic (conjuncts)" in withMathematica { qeTool =>
    val i = "v^2 + w^2 <= r()^2 & v^2 + w^2 >= r()^2 -> [{v'=w,w'=-v}] (v^2 + w^2 <= r()^2 & v^2 + w^2 >= r()^2)".asFormula

    //val insts = List((0,"1".asTerm),(1,"3*wit__0^2*x^2".asTerm))

    val tactic = implyR(1) & DebuggingTactics.print("Entering diff ind") & dI('diffInd)(1) < (QE, //QE just for reflexivity, no problem
      DebuggingTactics.print("Before chase") &
        chase(1) &
        DebuggingTactics.print("Before normalizing") &  prop &
        OnAll(prepareArith) &
        DebuggingTactics.print("Before witness") &
        OnAll(witnessTac(List())) //The witnesses are just 1 because the groebner basis contains -1
      )

    val res = proveBy(i, tactic)
    res shouldBe 'proved
  }

  "InvariantArith" should "solve Lecture 11 DI quartic dynamics (Example 11.7)" in withMathematica { qeTool =>
    val i = "x^3 >= -1 & a() >= 0 -> [{x'=(x-3)^4 +a()}] x^3 >= -1".asFormula

    val witness = List(("3"," wit__0*x^3 - 6*wit__0*x^2 + 9*wit__0*x"),("3","wit__0*wit__1*x")).map( s => (s._1.asTerm,s._2.asTerm))
    //val insts = List((0,"1".asTerm),(1,"3*wit__0^2*x^2".asTerm))

    val tactic = implyR(1) & DebuggingTactics.print("Entering diff ind") & dI('diffInd)(1) < (QE, //QE just for reflexivity, no problem
      DebuggingTactics.print("Before chase") &
        chase(1) &
        DebuggingTactics.print("Before normalizing") &  prop &
        OnAll(prepareArith) &
        DebuggingTactics.print("Before witness") &
        witnessTac(witness)
      )

    val res = proveBy(i, tactic)
    res shouldBe 'proved
  }

  "InvariantArith" should "solve Lecture 11 DI damped oscillator" in withMathematica { qeTool =>
    val i = "w()^2*x^2 + y^2 <= c()^2 -> [{x'=y,y'=-w()^2*x-2*d()*w()*y & (w()>=0 & d()>=0)}]w()^2*x^2 + y^2 <= c()^2".asFormula

    val witness = List(("4","wit__0*wit__1*y*wit__4")).map( s => (s._1.asTerm,s._2.asTerm))

    val tactic = implyR(1) & dI('diffInd)(1) < (QE, //QE just for reflexivity, no problem
      chase(1) &
        DebuggingTactics.print("Before normalizing") &  prop &
        OnAll(prepareArith) &
        DebuggingTactics.print("Problem") &
        witnessTac(witness))

    val res = proveBy(i, tactic)
    res shouldBe 'proved
  }

  "InvariantArith" should "prove a nasty arithmetic problem from L4Q2" in withMathematica { qeTool =>
    val antes = IndexedSeq("minr>0","buffer>0","trackr>=minr","(tx-x)^2+(ty-y)^2=trackr^2","(tx-rx)^2+(ty-ry)^2>=(buffer+trackr)^2").map(_.asFormula)
    val succ = IndexedSeq("(x-rx)^2+(y-ry)^2>=buffer^2".asFormula)

    val linear = List((5,"trackr","wit_^2 + minr","1"),(2,"buffer","wit__1^2","1"),(2,"minr","wit__2^2","1")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm))
    val witness = List(("4","wit_*wit__0*wit__1"),("4","wit__2*wit__0*wit__1"),("2","wit__0*wit__3"),("4","-ty*x + tx*y + ty*rx - y*rx - tx*ry + x*ry"),("4","wit_*wit__1*wit__3"),("4","wit__2*wit__1*wit__3"),("4","wit_^2*wit__0 + wit__2^2*wit__0"),("1","wit__3^2")).map( s => (s._1.asTerm,s._2.asTerm))
    // The first inequation is used here
    val ineq = List(0)
    //The default basis isn't anywhere near to a groebner basis...
    val insts = Some(List((0,"-2*tx*x - x^2 - 2*ty*y - y^2 + 2*tx*rx + 4*x*rx - 3*rx^2 + 2*ty*ry + 4*y*ry - 3*ry^2 - 2*wit_^2*wit__1^2 - 2*wit__2^2*wit__1^2 - wit__1^4 - wit__3^2"), (1," 4*wit_^4 + 8*wit_^2*wit__2^2 + 4*wit__2^4 + 4*wit_^2*wit__1^2 + 4*wit__2^2*wit__1^2 + 2*wit__3^2"), (2," 2*tx*x - 3*x^2 + 2*ty*y - 3*y^2 - 2*tx*rx + 4*x*rx - rx^2 - 2*ty*ry + 4*y*ry - ry^2 + 2*wit_^2*wit__1^2 + 2*wit__2^2*wit__1^2 + wit__1^4 + wit__3^2")).map (s => (s._1,s._2.asTerm)))

    val tactic = prepareArith2 & DebuggingTactics.print("after") &
      printGoal & linearElim(linear) & genWitnessTac(ineq,witness,insts)

    val res = proveBy(Sequent(antes,succ), tactic)

    res shouldBe 'proved
  }

  "ACASX Arith" should "prove ACAS X fml (division rewritten by hand)" in withMathematica { qeTool =>
    val i = "(w_0*dhf_0>=0&r_0 < -rp_0&(0>=w_0*(dhf_0-dhd_0)&max_1=0|0 < w_0*(dhf_0-dhd_0)&max_1=w_0*(dhf_0-dhd_0))&(0<=w_0*dhd_0&min_1=0|0>w_0*dhd_0&min_1=w_0*dhd_0)&(r_0-ro_0>=0&abs_1=r_0-ro_0|r_0-ro_0 < 0&abs_1=-(r_0-ro_0))&(w_0=-1|w_0=1)&hp_0>0&rp_0>=0&rv_0>=0&a_0>0&(0<=t_0&a_0 * t_0 < max_1&ro_0=rv_0*t_0&ho_0=w_0*a_0/2*t_0^2+dhd_0*t_0|a_0*t_0>=max_1&ro_0=rv_0*t_0&ho_0*2*a_0=dhf_0*t_0*2*a_0-w_0*max_1^2)->abs_1>rp_0|w_0*h_0 < w_0*ho_0-hp_0)".asFormula
    val lwits = List(Some((List(0),List((0,"w_0","-1","1"),(0,"ro_0","rv_0*t_0","1"),(14,"rv_0","wit__10^2","1"),(13,"t_0","wit__9^2","-1"),(5,"a_0","wit__1^2","1"),(9,"dhd_0","-wit__6^2 + dhf_0","-1"),(0,"ho_0","-1/2*wit__1^2*wit__9^4 - (wit__6^2 - dhf_0)*wit__9^2","1"),(0,"abs_1","-wit__10^2*wit__9^2 + r_0","1"),(4,"r_0","-wit__3^2 - rp_0","1"),(0,"min_1","0","1"),(0,"max_1","0","1"),(1,"hp_0","wit__2^2","1"),(1,"rp_0","-1/2*wit__10^2*wit__9^2 - 1/2*wit__3^2 + 1/2*wit__4^2","2"),(1,"h_0","-1/2*wit__1^2*wit__9^4 - (wit__6^2 - dhf_0)*wit__9^2 + wit__2^2 - wit__5^2","-1"),(1,"dhf_0","wit__6^2 - wit__7^2","1")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm)),List(("1","wit__0*wit__1*wit__9")).map( s => (s._1.asTerm,s._2.asTerm)),Some(List((0,"-wit__1^2*wit__9^2"),(1,"0"),(2,"0"),(3,"0")).map (s => (s._1,s._2.asTerm))))),
      Some((List(0,2),List((0,"w_0","-1","1"),(0,"ro_0","rv_0*t_0","1"),(13,"rv_0","wit__9^2","1"),(4,"a_0","wit__0^2","1"),(8,"dhf_0","wit__5^2 + dhd_0","1"),(7,"ho_0","wit__4^2 + h_0 - hp_0","1"),(3,"max_1","0","1"),(1,"abs_1","-t_0*wit__9^2 + r_0","1"),(3,"r_0","-wit__2^2 - rp_0","1"),(1,"min_1","0","1"),(1,"hp_0","wit__1^2","1"),(1,"rp_0","-1/2*t_0*wit__9^2 - 1/2*wit__2^2 + 1/2*wit__3^2","2"),(1,"dhd_0","-wit__6^2","1")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm)),List(("1","wit__0^2*wit__2*wit__7"),("1","wit__0*wit__2*wit__9*wit__8"),("1","wit__0^2*wit__2*wit__10")).map( s => (s._1.asTerm,s._2.asTerm)),Some(List((0,"0"),(1,"wit__0^4*wit__2^2"),(2,"wit__0^2*wit__2^2*wit__9^2"),(3,"wit__0^4*wit__2^2"),(4,"0")).map (s => (s._1,s._2.asTerm))))),
      Some((List(0),List((0,"w_0","1","1"),(0,"ro_0","rv_0*t_0","1"),(14,"rv_0","wit__10^2","1"),(13,"t_0","wit__9^2","-1"),(5,"a_0","wit__1^2","1"),(9,"dhd_0","wit__6^2 + dhf_0","1"),(0,"ho_0","1/2*wit__1^2*wit__9^4 + (wit__6^2 + dhf_0)*wit__9^2","1"),(0,"abs_1","-wit__10^2*wit__9^2 + r_0","1"),(4,"r_0","-wit__3^2 - rp_0","1"),(0,"min_1","0","1"),(0,"max_1","0","1"),(1,"hp_0","wit__2^2","1"),(1,"rp_0","-1/2*wit__10^2*wit__9^2 - 1/2*wit__3^2 + 1/2*wit__4^2","2"),(1,"h_0","1/2*wit__1^2*wit__9^4 + (wit__6^2 + dhf_0)*wit__9^2 - wit__2^2 + wit__5^2","1"),(1,"dhf_0","-wit__6^2 + wit__7^2","-1")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm)),List(("1","wit__0*wit__1*wit__9")).map( s => (s._1.asTerm,s._2.asTerm)),Some(List((0,"-wit__1^2*wit__9^2"),(1,"0"),(2,"0"),(3,"0")).map (s => (s._1,s._2.asTerm))))),
      Some((List(0,2),List((0,"w_0","1","1"),(0,"ro_0","rv_0*t_0","1"),(13,"rv_0","wit__9^2","1"),(4,"a_0","wit__0^2","1"),(8,"dhf_0","-wit__5^2 + dhd_0","-1"),(7,"ho_0","-wit__4^2 + h_0 + hp_0","-1"),(3,"max_1","0","1"),(1,"abs_1","-t_0*wit__9^2 + r_0","1"),(3,"r_0","-wit__2^2 - rp_0","1"),(1,"min_1","0","1"),(1,"hp_0","wit__1^2","1"),(1,"rp_0","-1/2*t_0*wit__9^2 - 1/2*wit__2^2 + 1/2*wit__3^2","2"),(1,"dhd_0","wit__6^2","-1")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm)),List(("1","wit__0^2*wit__2*wit__7"),("1","wit__0*wit__2*wit__9*wit__8"),("1","wit__0^2*wit__2*wit__10")).map( s => (s._1.asTerm,s._2.asTerm)),Some(List((0,"0"),(1,"wit__0^4*wit__2^2"),(2,"wit__0^2*wit__2^2*wit__9^2"),(3,"wit__0^4*wit__2^2"),(4,"0")).map (s => (s._1,s._2.asTerm))))),
      Some((List(1),List((0,"w_0","-1","1"),(0,"ro_0","rv_0*t_0","1"),(14,"rv_0","wit__10^2","1"),(13,"t_0","wit__9^2","-1"),(6,"a_0","wit__2^2","1"),(10,"dhd_0","-wit__7^2 + dhf_0","-1"),(0,"ho_0","-1/2*wit__2^2*wit__9^4 - (wit__7^2 - dhf_0)*wit__9^2","1"),(0,"abs_1","wit__10^2*wit__9^2 - r_0","1"),(2,"r_0","wit__10^2*wit__9^2 - wit__0^2","1"),(0,"min_1","0","1"),(0,"max_1","0","1"),(1,"hp_0","wit__3^2","1"),(1,"rp_0","-wit__10^2*wit__9^2 + wit__0^2 - wit__4^2","1"),(2,"h_0","-1/2*wit__2^2*wit__9^4 - (wit__7^2 - dhf_0)*wit__9^2 + wit__3^2 - wit__6^2","-1"),(2,"dhf_0","wit__7^2 - wit__8^2","1")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm)),List(("1","wit__1*wit__2*wit__9")).map( s => (s._1.asTerm,s._2.asTerm)),Some(List((0,"-wit__2^2*wit__9^2"),(1,"0"),(2,"0"),(3,"0")).map (s => (s._1,s._2.asTerm))))),
      Some((List(1,3),List((0,"w_0","-1","1"),(0,"ro_0","rv_0*t_0","1"),(13,"rv_0","wit__9^2","1"),(5,"a_0","wit__1^2","1"),(9,"dhf_0","wit__6^2 + dhd_0","1"),(8,"ho_0","wit__5^2 + h_0 - hp_0","1"),(3,"max_1","0","1"),(1,"abs_1","t_0*wit__9^2 - r_0","1"),(2,"r_0","t_0*wit__9^2 - wit__0^2","1"),(1,"min_1","0","1"),(1,"hp_0","wit__2^2","1"),(1,"rp_0","-t_0*wit__9^2 + wit__0^2 - wit__3^2","1"),(2,"dhd_0","-wit__7^2","1")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm)),List(("1","wit__1*wit__9*wit__8*wit__0"),("1","wit__1*wit__3*wit__9*wit__8"),("1","wit__1^2*wit__3*wit__10"),("1","wit__1^2*wit__4*wit__0")).map( s => (s._1.asTerm,s._2.asTerm)),Some(List((0,"0"),(1,"wit__1^4*wit__0^2"),(2,"wit__1^2*wit__3^2*wit__9^2 + wit__1^2*wit__9^2*wit__0^2"),(3,"wit__1^4*wit__3^2"),(4,"0")).map (s => (s._1,s._2.asTerm))))),
      Some((List(1),List((0,"w_0","1","1"),(0,"ro_0","rv_0*t_0","1"),(14,"rv_0","wit__10^2","1"),(13,"t_0","wit__9^2","-1"),(6,"a_0","wit__2^2","1"),(10,"dhd_0","wit__7^2 + dhf_0","1"),(0,"ho_0","1/2*wit__2^2*wit__9^4 + (wit__7^2 + dhf_0)*wit__9^2","1"),(0,"abs_1","wit__10^2*wit__9^2 - r_0","1"),(2,"r_0","wit__10^2*wit__9^2 - wit__0^2","1"),(0,"min_1","0","1"),(0,"max_1","0","1"),(1,"hp_0","wit__3^2","1"),(1,"rp_0","-wit__10^2*wit__9^2 + wit__0^2 - wit__4^2","1"),(2,"h_0","1/2*wit__2^2*wit__9^4 + (wit__7^2 + dhf_0)*wit__9^2 - wit__3^2 + wit__6^2","1"),(2,"dhf_0","-wit__7^2 + wit__8^2","-1")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm)),List(("1","wit__1*wit__2*wit__9")).map( s => (s._1.asTerm,s._2.asTerm)),Some(List((0,"-wit__2^2*wit__9^2"),(1,"0"),(2,"0"),(3,"0")).map (s => (s._1,s._2.asTerm))))),
      Some((List(1,3),List((0,"w_0","1","1"),(0,"ro_0","rv_0*t_0","1"),(13,"rv_0","wit__9^2","1"),(5,"a_0","wit__1^2","1"),(9,"dhf_0","-wit__6^2 + dhd_0","-1"),(8,"ho_0","-wit__5^2 + h_0 + hp_0","-1"),(3,"max_1","0","1"),(1,"abs_1","t_0*wit__9^2 - r_0","1"),(2,"r_0","t_0*wit__9^2 - wit__0^2","1"),(1,"min_1","0","1"),(1,"hp_0","wit__2^2","1"),(1,"rp_0","-t_0*wit__9^2 + wit__0^2 - wit__3^2","1"),(2,"dhd_0","wit__7^2","-1")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm)),List(("1","wit__1*wit__9*wit__8*wit__0"),("1","wit__1*wit__3*wit__9*wit__8"),("1","wit__1^2*wit__3*wit__10"),("1","wit__1^2*wit__4*wit__0")).map( s => (s._1.asTerm,s._2.asTerm)),Some(List((0,"0"),(1,"wit__1^4*wit__0^2"),(2,"wit__1^2*wit__3^2*wit__9^2 + wit__1^2*wit__9^2*wit__0^2"),(3,"wit__1^4*wit__3^2"),(4,"0")).map (s => (s._1,s._2.asTerm))))),
      Some((List(0),List((0,"w_0","-1","1"),(0,"ro_0","rv_0*t_0","1"),(14,"rv_0","wit__10^2","1"),(13,"t_0","wit__9^2","-1"),(6,"a_0","wit__2^2","1"),(2,"dhd_0","-min_1","1"),(0,"ho_0","-1/2*wit__2^2*wit__9^4 - min_1*wit__9^2","1"),(0,"abs_1","-wit__10^2*wit__9^2 + r_0","1"),(4,"r_0","-wit__4^2 - rp_0","1"),(1,"min_1","-wit__0^2","-1"),(0,"max_1","0","1"),(1,"hp_0","wit__3^2","1"),(1,"rp_0","-1/2*wit__10^2*wit__9^2 - 1/2*wit__4^2 + 1/2*wit__5^2","2"),(1,"h_0","-1/2*wit__2^2*wit__9^4 + wit__0^2*wit__9^2 + wit__3^2 - wit__6^2","-1"),(1,"dhf_0","wit__0^2 + wit__7^2","1")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm)),List(("1","wit_*wit__0"),("1","wit__0*wit__7")).map( s => (s._1.asTerm,s._2.asTerm)),Some(List((0,"0"),(1,"0"),(2,"0"),(3,"wit__0^2")).map (s => (s._1,s._2.asTerm))))),
      Some((List(0),List((0,"w_0","-1","1"),(0,"ro_0","rv_0*t_0","1"),(13,"rv_0","wit__9^2","1"),(5,"a_0","wit__1^2","1"),(9,"dhf_0","wit__6^2 + dhd_0","1"),(8,"ho_0","wit__5^2 + h_0 - hp_0","1"),(3,"max_1","0","1"),(1,"abs_1","-t_0*wit__9^2 + r_0","1"),(4,"r_0","-wit__3^2 - rp_0","1"),(1,"dhd_0","-min_1","1"),(1,"min_1","-wit__0^2","-1"),(1,"hp_0","wit__2^2","1"),(1,"rp_0","-1/2*t_0*wit__9^2 - 1/2*wit__3^2 + 1/2*wit__4^2","2")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm)),List(("1","wit__0*wit__6"),("1","wit__0*wit_")).map( s => (s._1.asTerm,s._2.asTerm)),Some(List((0,"0"),(1,"0"),(2,"0"),(3,"0"),(4,"wit__0^2")).map (s => (s._1,s._2.asTerm))))),
      Some((List(0),List((0,"w_0","1","1"),(0,"ro_0","rv_0*t_0","1"),(14,"rv_0","wit__10^2","1"),(13,"t_0","wit__9^2","-1"),(6,"a_0","wit__2^2","1"),(2,"dhd_0","min_1","-1"),(0,"ho_0","1/2*wit__2^2*wit__9^4 + min_1*wit__9^2","1"),(0,"abs_1","-wit__10^2*wit__9^2 + r_0","1"),(4,"r_0","-wit__4^2 - rp_0","1"),(1,"min_1","-wit__0^2","-1"),(0,"max_1","0","1"),(1,"hp_0","wit__3^2","1"),(1,"rp_0","-1/2*wit__10^2*wit__9^2 - 1/2*wit__4^2 + 1/2*wit__5^2","2"),(1,"h_0","1/2*wit__2^2*wit__9^4 - wit__0^2*wit__9^2 - wit__3^2 + wit__6^2","1"),(1,"dhf_0","-wit__0^2 - wit__7^2","-1")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm)),List(("1","wit_*wit__0"),("1","wit__0*wit__7")).map( s => (s._1.asTerm,s._2.asTerm)),Some(List((0,"0"),(1,"0"),(2,"0"),(3,"wit__0^2")).map (s => (s._1,s._2.asTerm))))),
      Some((List(0),List((0,"w_0","1","1"),(0,"ro_0","rv_0*t_0","1"),(13,"rv_0","wit__9^2","1"),(5,"a_0","wit__1^2","1"),(9,"dhf_0","-wit__6^2 + dhd_0","-1"),(8,"ho_0","-wit__5^2 + h_0 + hp_0","-1"),(3,"max_1","0","1"),(1,"abs_1","-t_0*wit__9^2 + r_0","1"),(4,"r_0","-wit__3^2 - rp_0","1"),(1,"dhd_0","min_1","-1"),(1,"min_1","-wit__0^2","-1"),(1,"hp_0","wit__2^2","1"),(1,"rp_0","-1/2*t_0*wit__9^2 - 1/2*wit__3^2 + 1/2*wit__4^2","2")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm)),List(("1","wit__0*wit__6"),("1","wit__0*wit_")).map( s => (s._1.asTerm,s._2.asTerm)),Some(List((0,"0"),(1,"0"),(2,"0"),(3,"0"),(4,"wit__0^2")).map (s => (s._1,s._2.asTerm))))),
      Some((List(0),List((0,"w_0","-1","1"),(0,"ro_0","rv_0*t_0","1"),(14,"rv_0","wit__10^2","1"),(13,"t_0","wit__9^2","-1"),(7,"a_0","wit__3^2","1"),(2,"dhd_0","-min_1","1"),(0,"ho_0","-1/2*wit__3^2*wit__9^4 - min_1*wit__9^2","1"),(0,"abs_1","wit__10^2*wit__9^2 - r_0","1"),(2,"r_0","wit__10^2*wit__9^2 - wit__1^2","1"),(1,"min_1","-wit__0^2","-1"),(0,"max_1","0","1"),(1,"hp_0","wit__4^2","1"),(1,"rp_0","-wit__10^2*wit__9^2 + wit__1^2 - wit__5^2","1"),(2,"h_0","-1/2*wit__3^2*wit__9^4 + wit__0^2*wit__9^2 + wit__4^2 - wit__7^2","-1"),(2,"dhf_0","wit__0^2 + wit__8^2","1")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm)),List(("1","wit_*wit__0"),("1","wit__0*wit__8")).map( s => (s._1.asTerm,s._2.asTerm)),Some(List((0,"0"),(1,"0"),(2,"0"),(3,"wit__0^2")).map (s => (s._1,s._2.asTerm))))),
      Some((List(0),List((0,"w_0","-1","1"),(0,"ro_0","rv_0*t_0","1"),(13,"rv_0","wit__9^2","1"),(6,"a_0","wit__2^2","1"),(10,"dhf_0","wit__7^2 + dhd_0","1"),(9,"ho_0","wit__6^2 + h_0 - hp_0","1"),(3,"max_1","0","1"),(1,"abs_1","t_0*wit__9^2 - r_0","1"),(3,"r_0","t_0*wit__9^2 - wit__1^2","1"),(1,"dhd_0","-min_1","1"),(1,"min_1","-wit__0^2","-1"),(1,"hp_0","wit__3^2","1"),(1,"rp_0","-t_0*wit__9^2 + wit__1^2 - wit__4^2","1")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm)),List(("1","wit__0*wit__7"),("1","wit__0*wit_")).map( s => (s._1.asTerm,s._2.asTerm)),Some(List((0,"0"),(1,"0"),(2,"0"),(3,"0"),(4,"wit__0^2")).map (s => (s._1,s._2.asTerm))))),
      Some((List(0),List((0,"w_0","1","1"),(0,"ro_0","rv_0*t_0","1"),(14,"rv_0","wit__10^2","1"),(13,"t_0","wit__9^2","-1"),(7,"a_0","wit__3^2","1"),(2,"dhd_0","min_1","-1"),(0,"ho_0","1/2*wit__3^2*wit__9^4 + min_1*wit__9^2","1"),(0,"abs_1","wit__10^2*wit__9^2 - r_0","1"),(2,"r_0","wit__10^2*wit__9^2 - wit__1^2","1"),(1,"min_1","-wit__0^2","-1"),(0,"max_1","0","1"),(1,"hp_0","wit__4^2","1"),(1,"rp_0","-wit__10^2*wit__9^2 + wit__1^2 - wit__5^2","1"),(2,"h_0","1/2*wit__3^2*wit__9^4 - wit__0^2*wit__9^2 - wit__4^2 + wit__7^2","1"),(2,"dhf_0","-wit__0^2 - wit__8^2","-1")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm)),List(("1","wit_*wit__0"),("1","wit__0*wit__8")).map( s => (s._1.asTerm,s._2.asTerm)),Some(List((0,"0"),(1,"0"),(2,"0"),(3,"wit__0^2")).map (s => (s._1,s._2.asTerm))))),
      Some((List(0),List((0,"w_0","1","1"),(0,"ro_0","rv_0*t_0","1"),(13,"rv_0","wit__9^2","1"),(6,"a_0","wit__2^2","1"),(10,"dhf_0","-wit__7^2 + dhd_0","-1"),(9,"ho_0","-wit__6^2 + h_0 + hp_0","-1"),(3,"max_1","0","1"),(1,"abs_1","t_0*wit__9^2 - r_0","1"),(3,"r_0","t_0*wit__9^2 - wit__1^2","1"),(1,"dhd_0","min_1","-1"),(1,"min_1","-wit__0^2","-1"),(1,"hp_0","wit__3^2","1"),(1,"rp_0","-t_0*wit__9^2 + wit__1^2 - wit__4^2","1")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm)),List(("1","wit__0*wit__7"),("1","wit__0*wit_")).map( s => (s._1.asTerm,s._2.asTerm)),Some(List((0,"0"),(1,"0"),(2,"0"),(3,"0"),(4,"wit__0^2")).map (s => (s._1,s._2.asTerm))))),
      Some((List(4),List((0,"w_0","-1","1"),(0,"ro_0","rv_0*t_0","1"),(14,"rv_0","wit__10^2","1"),(13,"t_0","wit__9^2","-1"),(6,"a_0","wit__2^2","1"),(3,"dhd_0","dhf_0 + max_1","-1"),(0,"ho_0","-1/2*wit__2^2*wit__9^4 + (dhf_0 + max_1)*wit__9^2","1"),(0,"abs_1","-wit__10^2*wit__9^2 + r_0","1"),(4,"r_0","-wit__4^2 - rp_0","1"),(0,"min_1","0","1"),(5,"dhf_0","-wit__7^2 - max_1","1"),(0,"max_1","wit__0^2","-1"),(1,"hp_0","wit__3^2","1"),(1,"rp_0","-1/2*wit__10^2*wit__9^2 - 1/2*wit__4^2 + 1/2*wit__5^2","2"),(1,"h_0","-1/2*wit__2^2*wit__9^4 - wit__7^2*wit__9^2 + wit__3^2 - wit__6^2","-1")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm)),List(("1","wit__9*wit__10*wit__4"),("1","wit__4*wit__8"),("1","wit__4*wit__11")).map( s => (s._1.asTerm,s._2.asTerm)),Some(List((0,"0"),(1,"wit__4^2"),(2,"wit__4^2"),(3,"0")).map (s => (s._1,s._2.asTerm))))),
      Some((List(0,3),List((0,"w_0","-1","1"),(0,"ro_0","rv_0*t_0","1"),(13,"rv_0","wit__9^2","1"),(5,"a_0","wit__1^2","1"),(3,"dhf_0","dhd_0 - max_1","1"),(7,"ho_0","wit__5^2 + h_0 - hp_0","1"),(3,"max_1","wit__0^2","-1"),(1,"abs_1","-t_0*wit__9^2 + r_0","1"),(3,"r_0","-wit__3^2 - rp_0","1"),(1,"min_1","0","1"),(3,"dhd_0","-wit__6^2","1"),(1,"hp_0","wit__2^2","1"),(1,"rp_0","-1/2*t_0*wit__9^2 - 1/2*wit__3^2 + 1/2*wit__4^2","2")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm)),List(("1","wit__6^2*wit__3*wit__7 - wit__3*wit__7*wit_^2"),("1","wit__6^2*wit__3*wit__10 - wit__3*wit__10*wit_^2"),("1","wit__3^2*wit__8*wit_"),("1","wit__3*wit__7*wit__8*wit_"),("1","wit__3*wit__8*wit__10*wit_"),("1","wit__0*wit__6*wit__3^2"),("1","t_0*wit__1*wit__3*wit__9*wit_"),("1","wit__0*wit__6*wit__3*wit__7"),("1","wit__0*wit__6*wit__3*wit__10")).map( s => (s._1.asTerm,s._2.asTerm)),Some(List((0,"0"),(1,"t_0*wit__1^2*wit__3^2*wit_^2"),(2,"wit__3^4*wit_^2 + wit__3^2*wit__7^2*wit_^2 + wit__3^2*wit__10^2*wit_^2"),(3,"t_0*wit__1^2*wit__3^2*wit_^2"),(4,"-wit__0^2*wit__3^4 - wit__6^2*wit__3^2*wit__7^2 - wit__6^2*wit__3^2*wit__10^2 + wit__3^2*wit__7^2*wit_^2 + wit__3^2*wit__10^2*wit_^2")).map (s => (s._1,s._2.asTerm))))),
      Some((List(4),List((0,"w_0","1","1"),(0,"ro_0","rv_0*t_0","1"),(14,"rv_0","wit__10^2","1"),(13,"t_0","wit__9^2","-1"),(6,"a_0","wit__2^2","1"),(3,"dhd_0","dhf_0 - max_1","1"),(0,"ho_0","1/2*wit__2^2*wit__9^4 + (dhf_0 - max_1)*wit__9^2","1"),(0,"abs_1","-wit__10^2*wit__9^2 + r_0","1"),(4,"r_0","-wit__4^2 - rp_0","1"),(0,"min_1","0","1"),(5,"dhf_0","wit__7^2 + max_1","-1"),(0,"max_1","wit__0^2","-1"),(1,"hp_0","wit__3^2","1"),(1,"rp_0","-1/2*wit__10^2*wit__9^2 - 1/2*wit__4^2 + 1/2*wit__5^2","2"),(1,"h_0","1/2*wit__2^2*wit__9^4 + wit__7^2*wit__9^2 - wit__3^2 + wit__6^2","1")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm)),List(("1","wit__9*wit__10*wit__4"),("1","wit__4*wit__8"),("1","wit__4*wit__11")).map( s => (s._1.asTerm,s._2.asTerm)),Some(List((0,"0"),(1,"wit__4^2"),(2,"wit__4^2"),(3,"0")).map (s => (s._1,s._2.asTerm))))),
      Some((List(0,3),List((0,"w_0","1","1"),(0,"ro_0","rv_0*t_0","1"),(13,"rv_0","wit__9^2","1"),(5,"a_0","wit__1^2","1"),(3,"dhf_0","dhd_0 + max_1","-1"),(7,"ho_0","-wit__5^2 + h_0 + hp_0","-1"),(3,"max_1","wit__0^2","-1"),(1,"abs_1","-t_0*wit__9^2 + r_0","1"),(3,"r_0","-wit__3^2 - rp_0","1"),(1,"min_1","0","1"),(3,"dhd_0","wit__6^2","-1"),(1,"hp_0","wit__2^2","1"),(1,"rp_0","-1/2*t_0*wit__9^2 - 1/2*wit__3^2 + 1/2*wit__4^2","2")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm)),List(("1","wit__3^2*wit__8*wit_"),("1","wit__3*wit__7*wit__8*wit_"),("1","wit__3*wit__8*wit__10*wit_"),("1","wit__0*wit__6*wit__3^2"),("1","t_0*wit__1*wit__3*wit__9*wit_"),("1","wit__0*wit__3*wit__7*wit_"),("1","wit__0*wit__3*wit__10*wit_")).map( s => (s._1.asTerm,s._2.asTerm)),Some(List((0,"0"),(1,"t_0*wit__1^2*wit__3^2*wit_^2"),(2,"wit__3^4*wit_^2 + wit__3^2*wit__7^2*wit_^2 + wit__3^2*wit__10^2*wit_^2"),(3,"t_0*wit__1^2*wit__3^2*wit_^2"),(4,"-wit__0^2*wit__3^4")).map (s => (s._1,s._2.asTerm))))),
      Some((List(5),List((0,"w_0","-1","1"),(0,"ro_0","rv_0*t_0","1"),(14,"rv_0","wit__10^2","1"),(13,"t_0","wit__9^2","-1"),(7,"a_0","wit__3^2","1"),(3,"dhd_0","dhf_0 + max_1","-1"),(0,"ho_0","-1/2*wit__3^2*wit__9^4 + (dhf_0 + max_1)*wit__9^2","1"),(0,"abs_1","wit__10^2*wit__9^2 - r_0","1"),(2,"r_0","wit__10^2*wit__9^2 - wit__1^2","1"),(0,"min_1","0","1"),(6,"dhf_0","-wit__8^2 - max_1","1"),(0,"max_1","wit__0^2","-1"),(1,"hp_0","wit__4^2","1"),(1,"rp_0","-wit__10^2*wit__9^2 + wit__1^2 - wit__5^2","1"),(2,"h_0","-1/2*wit__3^2*wit__9^4 - wit__8^2*wit__9^2 + wit__4^2 - wit__7^2","-1")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm)),List(("1","wit__9*wit__10*wit__5"),("1","wit__5*wit__6")).map( s => (s._1.asTerm,s._2.asTerm)),Some(List((0,"0"),(1,"wit__5^2"),(2,"0"),(3,"0")).map (s => (s._1,s._2.asTerm))))),
      Some((List(2,4),List((0,"w_0","-1","1"),(0,"ro_0","rv_0*t_0","1"),(13,"rv_0","wit__9^2","1"),(6,"a_0","wit__2^2","1"),(3,"dhf_0","dhd_0 - max_1","1"),(8,"ho_0","wit__6^2 + h_0 - hp_0","1"),(3,"max_1","wit__0^2","-1"),(1,"abs_1","t_0*wit__9^2 - r_0","1"),(2,"r_0","t_0*wit__9^2 - wit__1^2","1"),(1,"min_1","0","1"),(4,"dhd_0","-wit__7^2","1"),(1,"hp_0","wit__3^2","1"),(1,"rp_0","-t_0*wit__9^2 + wit__1^2 - wit__4^2","1")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm)),List(("1","wit__7*wit__9^2*wit__8"),("1","wit__2*wit__9*wit__8*wit__1"),("1","wit__2*wit__4*wit__9*wit__8"),("1","wit__2^2*wit__4*wit__10"),("1","wit__2*wit__4*wit__9*wit_"),("1","wit__0*wit__7*wit__9^2"),("1","wit__0*wit__2*wit__9*wit__1"),("1","wit__2*wit__7*wit__5*wit__9"),("1","wit__2^2*wit__5*wit__1")).map( s => (s._1.asTerm,s._2.asTerm)),Some(List((0,"0"),(1,"wit__2^2*wit__7^2*wit__9^2 + wit__2^4*wit__1^2"),(2,"wit__2^2*wit__4^2*wit__9^2 + wit__7^2*wit__9^4 + wit__2^2*wit__9^2*wit__1^2"),(3,"wit__2^4*wit__4^2"),(4,"wit__2^2*wit__4^2*wit__9^2")).map (s => (s._1,s._2.asTerm))))),
      Some((List(5),List((0,"w_0","1","1"),(0,"ro_0","rv_0*t_0","1"),(14,"rv_0","wit__10^2","1"),(13,"t_0","wit__9^2","-1"),(7,"a_0","wit__3^2","1"),(3,"dhd_0","dhf_0 - max_1","1"),(0,"ho_0","1/2*wit__3^2*wit__9^4 + (dhf_0 - max_1)*wit__9^2","1"),(0,"abs_1","wit__10^2*wit__9^2 - r_0","1"),(2,"r_0","wit__10^2*wit__9^2 - wit__1^2","1"),(0,"min_1","0","1"),(6,"dhf_0","wit__8^2 + max_1","-1"),(0,"max_1","wit__0^2","-1"),(1,"hp_0","wit__4^2","1"),(1,"rp_0","-wit__10^2*wit__9^2 + wit__1^2 - wit__5^2","1"),(2,"h_0","1/2*wit__3^2*wit__9^4 + wit__8^2*wit__9^2 - wit__4^2 + wit__7^2","1")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm)),List(("1","wit__9*wit__10*wit__5"),("1","wit__5*wit__6")).map( s => (s._1.asTerm,s._2.asTerm)),Some(List((0,"0"),(1,"wit__5^2"),(2,"0"),(3,"0")).map (s => (s._1,s._2.asTerm))))),
      Some((List(2,4),List((0,"w_0","1","1"),(0,"ro_0","rv_0*t_0","1"),(13,"rv_0","wit__9^2","1"),(6,"a_0","wit__2^2","1"),(3,"dhf_0","dhd_0 + max_1","-1"),(8,"ho_0","-wit__6^2 + h_0 + hp_0","-1"),(3,"max_1","wit__0^2","-1"),(1,"abs_1","t_0*wit__9^2 - r_0","1"),(2,"r_0","t_0*wit__9^2 - wit__1^2","1"),(1,"min_1","0","1"),(4,"dhd_0","wit__7^2","-1"),(1,"hp_0","wit__3^2","1"),(1,"rp_0","-t_0*wit__9^2 + wit__1^2 - wit__4^2","1")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm)),List(("1","wit__7*wit__9^2*wit__8"),("1","wit__2*wit__9*wit__8*wit__1"),("1","wit__2*wit__4*wit__9*wit__8"),("1","wit__2^2*wit__4*wit__10"),("1","wit__2*wit__4*wit__9*wit_"),("1","wit__0*wit__7*wit__9^2"),("1","wit__0*wit__2*wit__9*wit__1"),("1","wit__2*wit__7*wit__5*wit__9"),("1","wit__2^2*wit__5*wit__1")).map( s => (s._1.asTerm,s._2.asTerm)),Some(List((0,"0"),(1,"wit__2^2*wit__7^2*wit__9^2 + wit__2^4*wit__1^2"),(2,"wit__2^2*wit__4^2*wit__9^2 + wit__7^2*wit__9^4 + wit__2^2*wit__9^2*wit__1^2"),(3,"wit__2^4*wit__4^2"),(4,"wit__2^2*wit__4^2*wit__9^2")).map (s => (s._1,s._2.asTerm))))),
      Some((List(5),List((0,"w_0","-1","1"),(0,"ro_0","rv_0*t_0","1"),(14,"rv_0","wit__10^2","1"),(13,"t_0","wit__9^2","-1"),(7,"a_0","wit__3^2","1"),(2,"dhd_0","-min_1","1"),(0,"ho_0","-1/2*wit__3^2*wit__9^4 - min_1*wit__9^2","1"),(0,"abs_1","-wit__10^2*wit__9^2 + r_0","1"),(5,"r_0","-wit__5^2 - rp_0","1"),(0,"min_1","-dhf_0 - max_1","1"),(1,"dhf_0","wit__1^2 - max_1","1"),(0,"max_1","wit__0^2","-1"),(1,"hp_0","wit__4^2","1"),(1,"rp_0","-1/2*wit__10^2*wit__9^2 - 1/2*wit__5^2 + 1/2*wit__6^2","2"),(1,"h_0","-1/2*wit__3^2*wit__9^4 + wit__1^2*wit__9^2 + wit__4^2 - wit__7^2","-1")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm)),List(("1","wit__9*wit__10*wit__5"),("1","wit__5*wit__8"),("1","wit__5*wit__11")).map( s => (s._1.asTerm,s._2.asTerm)),Some(List((0,"0"),(1,"wit__5^2"),(2,"wit__5^2"),(3,"0")).map (s => (s._1,s._2.asTerm))))),
      Some((List(0,4),List((0,"w_0","-1","1"),(0,"ro_0","rv_0*t_0","1"),(13,"rv_0","wit__9^2","1"),(6,"a_0","wit__2^2","1"),(3,"dhf_0","dhd_0 - max_1","1"),(8,"ho_0","wit__6^2 + h_0 - hp_0","1"),(3,"max_1","wit__0^2","-1"),(1,"abs_1","-t_0*wit__9^2 + r_0","1"),(4,"r_0","-wit__4^2 - rp_0","1"),(1,"dhd_0","-min_1","1"),(1,"min_1","-wit__1^2","-1"),(1,"hp_0","wit__3^2","1"),(1,"rp_0","-1/2*t_0*wit__9^2 - 1/2*wit__4^2 + 1/2*wit__5^2","2")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm)),List(("1","wit__1^2*wit__4*wit__7 + wit__4*wit__7*wit_^2"),("1","wit__1^2*wit__4*wit__10 + wit__4*wit__10*wit_^2"),("1","t_0*wit__1*wit__2*wit__4*wit__9"),("1","t_0*wit__2*wit__4*wit__9*wit_"),("1","wit__0*wit__4^2*wit__8"),("1","wit__0*wit__4*wit__7*wit__8"),("1","wit__0*wit__4*wit__8*wit__10")).map( s => (s._1.asTerm,s._2.asTerm)),Some(List((0,"0"),(1,"t_0*wit__1^2*wit__2^2*wit__4^2 + t_0*wit__2^2*wit__4^2*wit_^2"),(2,"wit__1^2*wit__4^4 + wit__1^2*wit__4^2*wit__7^2 + wit__1^2*wit__4^2*wit__10^2 + wit__4^4*wit_^2 + wit__4^2*wit__7^2*wit_^2 + wit__4^2*wit__10^2*wit_^2"),(3,"t_0*wit__1^2*wit__2^2*wit__4^2 + t_0*wit__2^2*wit__4^2*wit_^2"),(4,"-wit__0^2*wit__4^4 + wit__1^2*wit__4^2*wit__7^2 - wit__4^4*wit__8^2 - wit__4^2*wit__7^2*wit__8^2 + wit__1^2*wit__4^2*wit__10^2 - wit__4^2*wit__8^2*wit__10^2 + wit__4^2*wit__7^2*wit_^2 + wit__4^2*wit__10^2*wit_^2")).map (s => (s._1,s._2.asTerm))))),
      Some((List(5),List((0,"w_0","1","1"),(0,"ro_0","rv_0*t_0","1"),(14,"rv_0","wit__10^2","1"),(13,"t_0","wit__9^2","-1"),(7,"a_0","wit__3^2","1"),(2,"dhd_0","min_1","-1"),(0,"ho_0","1/2*wit__3^2*wit__9^4 + min_1*wit__9^2","1"),(0,"abs_1","-wit__10^2*wit__9^2 + r_0","1"),(5,"r_0","-wit__5^2 - rp_0","1"),(0,"min_1","dhf_0 - max_1","1"),(1,"dhf_0","-wit__1^2 + max_1","-1"),(0,"max_1","wit__0^2","-1"),(1,"hp_0","wit__4^2","1"),(1,"rp_0","-1/2*wit__10^2*wit__9^2 - 1/2*wit__5^2 + 1/2*wit__6^2","2"),(1,"h_0","1/2*wit__3^2*wit__9^4 - wit__1^2*wit__9^2 - wit__4^2 + wit__7^2","1")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm)),List(("1","wit__9*wit__10*wit__5"),("1","wit__5*wit__8"),("1","wit__5*wit__11")).map( s => (s._1.asTerm,s._2.asTerm)),Some(List((0,"0"),(1,"wit__5^2"),(2,"wit__5^2"),(3,"0")).map (s => (s._1,s._2.asTerm))))),
      Some((List(0,4),List((0,"w_0","1","1"),(0,"ro_0","rv_0*t_0","1"),(13,"rv_0","wit__9^2","1"),(6,"a_0","wit__2^2","1"),(3,"dhf_0","dhd_0 + max_1","-1"),(8,"ho_0","-wit__6^2 + h_0 + hp_0","-1"),(3,"max_1","wit__0^2","-1"),(1,"abs_1","-t_0*wit__9^2 + r_0","1"),(4,"r_0","-wit__4^2 - rp_0","1"),(1,"dhd_0","min_1","-1"),(1,"min_1","-wit__1^2","-1"),(1,"hp_0","wit__3^2","1"),(1,"rp_0","-1/2*t_0*wit__9^2 - 1/2*wit__4^2 + 1/2*wit__5^2","2")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm)),List(("1","wit__1^2*wit__4*wit__7 + wit__4*wit__7*wit_^2"),("1","wit__1^2*wit__4*wit__10 + wit__4*wit__10*wit_^2"),("1","wit__4*wit__7*wit__8*wit_"),("1","wit__4*wit__8*wit__10*wit_"),("1","wit__1*wit__4*wit__7*wit__8"),("1","wit__1*wit__4*wit__8*wit__10"),("1","t_0*wit__1*wit__2*wit__4*wit__9"),("1","t_0*wit__2*wit__4*wit__9*wit_"),("1","wit__0*wit__4^2*wit__8")).map( s => (s._1.asTerm,s._2.asTerm)),Some(List((0,"0"),(1,"t_0*wit__1^2*wit__2^2*wit__4^2 + t_0*wit__2^2*wit__4^2*wit_^2"),(2,"wit__1^2*wit__4^4 + wit__1^2*wit__4^2*wit__7^2 + wit__1^2*wit__4^2*wit__10^2 + wit__4^4*wit_^2 + wit__4^2*wit__7^2*wit_^2 + wit__4^2*wit__10^2*wit_^2"),(3,"t_0*wit__1^2*wit__2^2*wit__4^2 + t_0*wit__2^2*wit__4^2*wit_^2"),(4,"-wit__0^2*wit__4^4 + wit__1^2*wit__4^2*wit__7^2 - wit__4^4*wit__8^2 + wit__1^2*wit__4^2*wit__10^2 + wit__4^2*wit__7^2*wit_^2 + wit__4^2*wit__10^2*wit_^2")).map (s => (s._1,s._2.asTerm))))),
      Some((List(6),List((0,"w_0","-1","1"),(0,"ro_0","rv_0*t_0","1"),(14,"rv_0","wit__10^2","1"),(13,"t_0","wit__9^2","-1"),(8,"a_0","wit__4^2","1"),(2,"dhd_0","-min_1","1"),(0,"ho_0","-1/2*wit__4^2*wit__9^4 - min_1*wit__9^2","1"),(0,"abs_1","wit__10^2*wit__9^2 - r_0","1"),(3,"r_0","wit__10^2*wit__9^2 - wit__2^2","1"),(0,"min_1","-dhf_0 - max_1","1"),(1,"dhf_0","wit__1^2 - max_1","1"),(0,"max_1","wit__0^2","-1"),(1,"hp_0","wit__5^2","1"),(1,"rp_0","-wit__10^2*wit__9^2 + wit__2^2 - wit__6^2","1"),(2,"h_0","-1/2*wit__4^2*wit__9^4 + wit__1^2*wit__9^2 + wit__5^2 - wit__8^2","-1")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm)),List(("1","wit__9*wit__10*wit__6"),("1","wit__6*wit__7")).map( s => (s._1.asTerm,s._2.asTerm)),Some(List((0,"0"),(1,"wit__6^2"),(2,"0"),(3,"0")).map (s => (s._1,s._2.asTerm))))),
      Some((List(3,5),List((0,"w_0","-1","1"),(0,"ro_0","rv_0*t_0","1"),(13,"rv_0","wit__9^2","1"),(7,"a_0","wit__3^2","1"),(3,"dhf_0","dhd_0 - max_1","1"),(9,"ho_0","wit__7^2 + h_0 - hp_0","1"),(3,"max_1","wit__0^2","-1"),(1,"abs_1","t_0*wit__9^2 - r_0","1"),(3,"r_0","t_0*wit__9^2 - wit__2^2","1"),(1,"dhd_0","-min_1","1"),(1,"min_1","-wit__1^2","-1"),(1,"hp_0","wit__4^2","1"),(1,"rp_0","-t_0*wit__9^2 + wit__2^2 - wit__5^2","1")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm)),List(("1","wit__3*wit__9*wit__8*wit__2"),("1","wit__1*wit__3*wit__5*wit__9"),("1","wit__3*wit__5*wit__9*wit__8"),("1","wit__3^2*wit__5*wit__10"),("1","wit__3*wit__5*wit__9*wit_"),("1","wit__0*wit__3*wit__9*wit__2"),("1","wit__3^2*wit__6*wit__2")).map( s => (s._1.asTerm,s._2.asTerm)),Some(List((0,"0"),(1,"wit__3^4*wit__2^2"),(2,"wit__3^2*wit__5^2*wit__9^2 + wit__3^2*wit__9^2*wit__2^2"),(3,"wit__3^4*wit__5^2"),(4,"wit__3^2*wit__5^2*wit__9^2")).map (s => (s._1,s._2.asTerm))))),
      Some((List(6),List((0,"w_0","1","1"),(0,"ro_0","rv_0*t_0","1"),(14,"rv_0","wit__10^2","1"),(13,"t_0","wit__9^2","-1"),(8,"a_0","wit__4^2","1"),(2,"dhd_0","min_1","-1"),(0,"ho_0","1/2*wit__4^2*wit__9^4 + min_1*wit__9^2","1"),(0,"abs_1","wit__10^2*wit__9^2 - r_0","1"),(3,"r_0","wit__10^2*wit__9^2 - wit__2^2","1"),(0,"min_1","dhf_0 - max_1","1"),(1,"dhf_0","-wit__1^2 + max_1","-1"),(0,"max_1","wit__0^2","-1"),(1,"hp_0","wit__5^2","1"),(1,"rp_0","-wit__10^2*wit__9^2 + wit__2^2 - wit__6^2","1"),(2,"h_0","1/2*wit__4^2*wit__9^4 - wit__1^2*wit__9^2 - wit__5^2 + wit__8^2","1")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm)),List(("1","wit__9*wit__10*wit__6"),("1","wit__6*wit__7")).map( s => (s._1.asTerm,s._2.asTerm)),Some(List((0,"0"),(1,"wit__6^2"),(2,"0"),(3,"0")).map (s => (s._1,s._2.asTerm))))),
      Some((List(3,5),List((0,"w_0","1","1"),(0,"ro_0","rv_0*t_0","1"),(13,"rv_0","wit__9^2","1"),(7,"a_0","wit__3^2","1"),(3,"dhf_0","dhd_0 + max_1","-1"),(9,"ho_0","-wit__7^2 + h_0 + hp_0","-1"),(3,"max_1","wit__0^2","-1"),(1,"abs_1","t_0*wit__9^2 - r_0","1"),(3,"r_0","t_0*wit__9^2 - wit__2^2","1"),(1,"dhd_0","min_1","-1"),(1,"min_1","-wit__1^2","-1"),(1,"hp_0","wit__4^2","1"),(1,"rp_0","-t_0*wit__9^2 + wit__2^2 - wit__5^2","1")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm)),List(("1","wit__3*wit__9*wit__8*wit__2"),("1","wit__1*wit__3*wit__5*wit__9"),("1","wit__3*wit__5*wit__9*wit__8"),("1","wit__3^2*wit__5*wit__10"),("1","wit__3*wit__5*wit__9*wit_"),("1","wit__0*wit__3*wit__9*wit__2"),("1","wit__3^2*wit__6*wit__2")).map( s => (s._1.asTerm,s._2.asTerm)),Some(List((0,"0"),(1,"wit__3^4*wit__2^2"),(2,"wit__3^2*wit__5^2*wit__9^2 + wit__3^2*wit__9^2*wit__2^2"),(3,"wit__3^4*wit__5^2"),(4,"wit__3^2*wit__5^2*wit__9^2")).map (s => (s._1,s._2.asTerm))))))

    val tactic = implyR(1) & DebuggingTactics.print("Before normalizing") & prop &
      DebuggingTactics.print("Before split") &
      OnAll(prepareArith2) &
      printGoal

    val res = proveBy(i, tactic)

    val result = lwits.zipWithIndex.map(
      prind =>
        prind._1 match
        {
          case Some(w) =>
            {
              val _ = println("SOLVING",prind._2)
              proveBy(res.subgoals(prind._2), linearElim(w._2) & genWitnessTac(w._1,w._3,w._4) & done)
            }
        }
      )

    print(result)
  }

}
