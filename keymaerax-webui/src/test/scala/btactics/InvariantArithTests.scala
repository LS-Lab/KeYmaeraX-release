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
    val witness = List(("10","wit__0*x^2")).map( s => (s._1.asTerm,s._2.asTerm))
    val tactic = implyR(1) & dI('diffInd)(1) < (QE, //QE just for reflexivity, no problem
      chase(1) &
        DebuggingTactics.print("Before normalizing") &  prop &
        OnAll(prepareArith) &
        DebuggingTactics.print("Problem") &
        witnessTac(witness)
        //Note: this gives the conditions 0-15*(2*x^(2-1)*x^3))*z__0^2-1=0, 1-15*x_0^2+z_^2=0
        //However, these two polynomials are actually disjoint, so we could try to prove a contradiction from either
        //No need to consider both at once
        //TODO: optimization - can split input polynomial systems into disjoint systems
      )
    val res = proveBy(i, tactic)
    res shouldBe 'proved
  }

  "InvariantArith" should "solve Lecture 11 odd order dynamics (Example 11.4)" in withMathematica { qeTool =>
    val i = "x^2 >= 2 -> [{x'=x^5+7*x^3+2*x}] x^2 >= 2".asFormula
    val witness = List(
      ("4","7/10*wit__0*x^3 + wit__0*x"),
      ("1/25","wit__0*x^3"),
      ("42/5","wit__0*x^2")).map( s => (s._1.asTerm,s._2.asTerm))
    val tactic = implyR(1) & dI('diffInd)(1) < (QE, //QE just for reflexivity, no problem
      chase(1) &
        DebuggingTactics.print("Before normalizing") &  prop &
        OnAll(prepareArith) &
        DebuggingTactics.print("Problem") &
        witnessTac(witness)
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
        OnAll(prepareArith) &
        DebuggingTactics.print("Problem") &
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

  "ACASX Arith" should "prove ACAS X fml (division rewritten by hand)" in withMathematica { qeTool =>
    val i = "(w_0*dhf_0>=0&r_0 < -rp_0&(0>=w_0*(dhf_0-dhd_0)&max_1=0|0 < w_0*(dhf_0-dhd_0)&max_1=w_0*(dhf_0-dhd_0))&(0<=w_0*dhd_0&min_1=0|0>w_0*dhd_0&min_1=w_0*dhd_0)&(r_0-ro_0>=0&abs_1=r_0-ro_0|r_0-ro_0 < 0&abs_1=-(r_0-ro_0))&(w_0=-1|w_0=1)&hp_0>0&rp_0>=0&rv_0>=0&a_0>0&(0<=t_0&a_0 * t_0 < max_1&ro_0=rv_0*t_0&ho_0=w_0*a_0/2*t_0^2+dhd_0*t_0|a_0*t_0>=max_1&ro_0=rv_0*t_0&ho_0*2*a_0=dhf_0*t_0*2*a_0-w_0*max_1^2)->abs_1>rp_0|w_0*h_0 < w_0*ho_0-hp_0)".asFormula


    //val witness = List(("4","wit__0*wit__1*y*wit__4")).map( s => (s._1.asTerm,s._2.asTerm))

    val tactic = implyR(1) & DebuggingTactics.print("Before normalizing") &  prop &
        DebuggingTactics.print("Before split") &
        OnAll(prepareArith) &
        printGoal

    val res = proveBy(i, tactic)

    val elim = (linearElim _).tupled

    val lwits = List(
      Some((List((-4,"r_0","abs_1 + ro_0",true),(-1,"w_0","-1",false),(-5,"rp_0","wit__0^2 + abs_1",false),(-2,"ho_0","-1/2*a_0*t_0^2 + dhd_0*t_0",false),(-7,"abs_1","wit__4^2",false),(-3,"max_1","0",false),(-9,"rv_0","wit__8^2",false),(-2,"min_1","0",false),(-6,"t_0","wit__6^2",true),(-2,"hp_0","1/2*a_0*wit__6^4 - dhd_0*wit__6^2 + wit__1^2 + h_0",false),(-1,"ro_0","wit__6^2*wit__8^2",false),(-1,"dhd_0","-wit__2^2 + dhf_0",true),(-1,"dhf_0","wit__2^2 - wit__3^2",false)).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4)),List(("1","wit__8*wit__6*wit__11"),("1","wit__11*wit__9"),("1","wit__4*wit__11")).map( s => (s._1.asTerm,s._2.asTerm)))),
      Some((List((-4,"r_0","abs_1 + ro_0",true),(-1,"w_0","-1",false),(-5,"rp_0","wit__0^2 + abs_1",false),(-5,"ho_0","wit__1^2 + h_0 - hp_0",false),(-7,"abs_1","wit__4^2",false),(-4,"max_1","0",false),(-8,"rv_0","wit__7^2",false),(-3,"min_1","0",false),(-1,"ro_0","t_0*wit__7^2",false),(-2,"dhd_0","-wit__2^2 + dhf_0",true),(-2,"dhf_0","wit__2^2 - wit__3^2",false)).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4)),List(("1","wit__10*wit__4"),("1","wit__8*wit__10"),("1","wit__10*wit__6*wit__7*wit__5")).map( s => (s._1.asTerm,s._2.asTerm)))),
      Some((List((-4,"r_0","abs_1 + ro_0",true),(-1,"w_0","1",false),(-5,"rp_0","wit__0^2 + abs_1",false),(-2,"ho_0","1/2*a_0*t_0^2 + dhd_0*t_0",false),(-7,"abs_1","wit__4^2",false),(-3,"max_1","0",false),(-9,"rv_0","wit__8^2",false),(-2,"min_1","0",false),(-6,"t_0","wit__6^2",true),(-2,"hp_0","1/2*a_0*wit__6^4 + dhd_0*wit__6^2 + wit__1^2 - h_0",false),(-1,"ro_0","wit__6^2*wit__8^2",false),(-1,"dhd_0","wit__2^2 + dhf_0",false),(-1,"dhf_0","-wit__2^2 + wit__3^2",true)).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4)),List(("1","wit__8*wit__6*wit__11"),("1","wit__11*wit__9"),("1","wit__4*wit__11")).map( s => (s._1.asTerm,s._2.asTerm)))),
      Some((List((-4,"r_0","abs_1 + ro_0",true),(-1,"w_0","1",false),(-5,"rp_0","wit__0^2 + abs_1",false),(-5,"ho_0","-wit__1^2 + h_0 + hp_0",true),(-7,"abs_1","wit__4^2",false),(-4,"max_1","0",false),(-8,"rv_0","wit__7^2",false),(-3,"min_1","0",false),(-1,"ro_0","t_0*wit__7^2",false),(-2,"dhd_0","wit__2^2 + dhf_0",false),(-2,"dhf_0","-wit__2^2 + wit__3^2",true)).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4)),List(("1","wit__10*wit__4"),("1","wit__8*wit__10"),("1","wit__10*wit__6*wit__7*wit__5")).map( s => (s._1.asTerm,s._2.asTerm)))),
      Some((List((-4,"r_0","-abs_1 + ro_0",false),(-1,"w_0","-1",false),(-5,"rp_0","wit__0^2 + abs_1",false),(-2,"ho_0","-1/2*a_0*t_0^2 + dhd_0*t_0",false),(-12,"abs_1","-wit__0^2 + wit__9^2",false),(-3,"max_1","0",false),(-10,"rv_0","wit__8^2",false),(-2,"min_1","0",false),(-7,"t_0","wit__6^2",true),(-2,"hp_0","1/2*a_0*wit__6^4 - dhd_0*wit__6^2 + wit__1^2 + h_0",false),(-1,"ro_0","wit__6^2*wit__8^2",false),(-1,"dhd_0","-wit__2^2 + dhf_0",true),(-1,"dhf_0","wit__2^2 - wit__3^2",false)).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4)),List(("1","wit__8*wit__6*wit__11"),("1","wit__0*wit__11")).map( s => (s._1.asTerm,s._2.asTerm)))),
      Some((List((-4,"r_0","-abs_1 + ro_0",false),(-1,"w_0","-1",false),(-5,"rp_0","wit__0^2 + abs_1",false),(-5,"ho_0","wit__1^2 + h_0 - hp_0",false),(-11,"abs_1","-wit__0^2 + wit__8^2",false),(-4,"max_1","0",false),(-9,"rv_0","wit__7^2",false),(-3,"min_1","0",false),(-1,"ro_0","t_0*wit__7^2",false),(-2,"dhd_0","-wit__2^2 + dhf_0",true),(-2,"dhf_0","wit__2^2 - wit__3^2",false)).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4)),List(("1","wit__10*wit__6*wit__7*wit__5"),("1","wit__0*wit__10")).map( s => (s._1.asTerm,s._2.asTerm)))),
      Some((List((-4,"r_0","-abs_1 + ro_0",false),(-1,"w_0","1",false),(-5,"rp_0","wit__0^2 + abs_1",false),(-2,"ho_0","1/2*a_0*t_0^2 + dhd_0*t_0",false),(-12,"abs_1","-wit__0^2 + wit__9^2",false),(-3,"max_1","0",false),(-10,"rv_0","wit__8^2",false),(-2,"min_1","0",false),(-7,"t_0","wit__6^2",true),(-2,"hp_0","1/2*a_0*wit__6^4 + dhd_0*wit__6^2 + wit__1^2 - h_0",false),(-1,"ro_0","wit__6^2*wit__8^2",false),(-1,"dhd_0","wit__2^2 + dhf_0",false),(-1,"dhf_0","-wit__2^2 + wit__3^2",true)).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4)),List(("1","wit__8*wit__6*wit__11"),("1","wit__0*wit__11")).map( s => (s._1.asTerm,s._2.asTerm)))),
      Some((List((-4,"r_0","-abs_1 + ro_0",false),(-1,"w_0","1",false),(-5,"rp_0","wit__0^2 + abs_1",false),(-5,"ho_0","-wit__1^2 + h_0 + hp_0",true),(-11,"abs_1","-wit__0^2 + wit__8^2",false),(-4,"max_1","0",false),(-9,"rv_0","wit__7^2",false),(-3,"min_1","0",false),(-1,"ro_0","t_0*wit__7^2",false),(-2,"dhd_0","wit__2^2 + dhf_0",false),(-2,"dhf_0","-wit__2^2 + wit__3^2",true)).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4)),List(("1","wit__10*wit__6*wit__7*wit__5"),("1","wit__0*wit__10")).map( s => (s._1.asTerm,s._2.asTerm)))),
      Some((List((-4,"r_0","abs_1 + ro_0",true),(-1,"w_0","-1",false),(-5,"rp_0","wit__0^2 + abs_1",false),(-2,"ho_0","-1/2*a_0*t_0^2 + dhd_0*t_0",false),(-7,"abs_1","wit__4^2",false),(-3,"max_1","0",false),(-9,"rv_0","wit__8^2",false),(-2,"min_1","-dhd_0",false),(-6,"t_0","wit__6^2",true),(-2,"hp_0","1/2*a_0*wit__6^4 - dhd_0*wit__6^2 + wit__1^2 + h_0",false),(-1,"ro_0","wit__6^2*wit__8^2",false),(-1,"dhd_0","-wit__2^2 + dhf_0",true),(-7,"dhf_0","-wit_^2",true)).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4)),List(("1","wit__8*wit__6*wit__11"),("1","wit__4*wit__11"),("1","wit__11*wit__9")).map( s => (s._1.asTerm,s._2.asTerm)))),
      Some((List((-4,"r_0","abs_1 + ro_0",true),(-1,"w_0","-1",false),(-5,"rp_0","wit__0^2 + abs_1",false),(-5,"ho_0","wit__1^2 + h_0 - hp_0",false),(-7,"abs_1","wit__4^2",false),(-4,"max_1","0",false),(-8,"rv_0","wit__7^2",false),(-3,"min_1","-dhd_0",false),(-1,"ro_0","t_0*wit__7^2",false),(-2,"dhd_0","-wit__2^2 + dhf_0",true),(-8,"dhf_0","-wit_^2",true)).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4)),List(("1","wit__10*wit__4"),("1","wit__8*wit__10"),("1","wit__10*wit__6*wit__7*wit__5")).map( s => (s._1.asTerm,s._2.asTerm)))),
      Some((List((-4,"r_0","abs_1 + ro_0",true),(-1,"w_0","1",false),(-5,"rp_0","wit__0^2 + abs_1",false),(-2,"ho_0","1/2*a_0*t_0^2 + dhd_0*t_0",false),(-7,"abs_1","wit__4^2",false),(-3,"max_1","0",false),(-9,"rv_0","wit__8^2",false),(-2,"min_1","dhd_0",false),(-6,"t_0","wit__6^2",true),(-2,"hp_0","1/2*a_0*wit__6^4 + dhd_0*wit__6^2 + wit__1^2 - h_0",false),(-1,"ro_0","wit__6^2*wit__8^2",false),(-1,"dhd_0","wit__2^2 + dhf_0",false),(-7,"dhf_0","wit_^2",false)).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4)),List(("1","wit__8*wit__6*wit__11"),("1","wit__4*wit__11"),("1","wit__11*wit__9")).map( s => (s._1.asTerm,s._2.asTerm)))),
      Some((List((-4,"r_0","abs_1 + ro_0",true),(-1,"w_0","1",false),(-5,"rp_0","wit__0^2 + abs_1",false),(-5,"ho_0","-wit__1^2 + h_0 + hp_0",true),(-7,"abs_1","wit__4^2",false),(-4,"max_1","0",false),(-8,"rv_0","wit__7^2",false),(-3,"min_1","dhd_0",false),(-1,"ro_0","t_0*wit__7^2",false),(-2,"dhd_0","wit__2^2 + dhf_0",false),(-8,"dhf_0","wit_^2",false)).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4)),List(("1","wit__10*wit__4"),("1","wit__8*wit__10"),("1","wit__10*wit__6*wit__7*wit__5")).map( s => (s._1.asTerm,s._2.asTerm)))),
      Some((List((-4,"r_0","-abs_1 + ro_0",false),(-1,"w_0","-1",false),(-5,"rp_0","wit__0^2 + abs_1",false),(-2,"ho_0","-1/2*a_0*t_0^2 + dhd_0*t_0",false),(-12,"abs_1","-wit__0^2 + wit__9^2",false),(-3,"max_1","0",false),(-10,"rv_0","wit__8^2",false),(-2,"min_1","-dhd_0",false),(-7,"t_0","wit__6^2",true),(-2,"hp_0","1/2*a_0*wit__6^4 - dhd_0*wit__6^2 + wit__1^2 + h_0",false),(-1,"ro_0","wit__6^2*wit__8^2",false),(-1,"dhd_0","-wit__2^2 + dhf_0",true),(-7,"dhf_0","-wit_^2",true)).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4)),List(("1","wit_*wit__3"),("1","wit__2*wit__3")).map( s => (s._1.asTerm,s._2.asTerm)))),
      Some((List((-4,"r_0","-abs_1 + ro_0",false),(-1,"w_0","-1",false),(-5,"rp_0","wit__0^2 + abs_1",false),(-5,"ho_0","wit__1^2 + h_0 - hp_0",false),(-11,"abs_1","-wit__0^2 + wit__8^2",false),(-4,"max_1","0",false),(-9,"rv_0","wit__7^2",false),(-3,"min_1","-dhd_0",false),(-1,"ro_0","t_0*wit__7^2",false),(-2,"dhd_0","-wit__2^2 + dhf_0",true),(-8,"dhf_0","-wit_^2",true)).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4)),List(("1/2","wit__0*wit__10"),("1/2","wit__2*wit__3"),("1/2","wit__10*wit__6*wit__7*wit__5"),("1/2","wit_*wit__3")).map( s => (s._1.asTerm,s._2.asTerm)))),
      Some((List((-4,"r_0","-abs_1 + ro_0",false),(-1,"w_0","1",false),(-5,"rp_0","wit__0^2 + abs_1",false),(-2,"ho_0","1/2*a_0*t_0^2 + dhd_0*t_0",false),(-12,"abs_1","-wit__0^2 + wit__9^2",false),(-3,"max_1","0",false),(-10,"rv_0","wit__8^2",false),(-2,"min_1","dhd_0",false),(-7,"t_0","wit__6^2",true),(-2,"hp_0","1/2*a_0*wit__6^4 + dhd_0*wit__6^2 + wit__1^2 - h_0",false),(-1,"ro_0","wit__6^2*wit__8^2",false),(-1,"dhd_0","wit__2^2 + dhf_0",false),(-7,"dhf_0","wit_^2",false)).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4)),List(("1","wit_*wit__3"),("1","wit__2*wit__3")).map( s => (s._1.asTerm,s._2.asTerm)))),
      Some((List((-4,"r_0","-abs_1 + ro_0",false),(-1,"w_0","1",false),(-5,"rp_0","wit__0^2 + abs_1",false),(-5,"ho_0","-wit__1^2 + h_0 + hp_0",true),(-11,"abs_1","-wit__0^2 + wit__8^2",false),(-4,"max_1","0",false),(-9,"rv_0","wit__7^2",false),(-3,"min_1","dhd_0",false),(-1,"ro_0","t_0*wit__7^2",false),(-2,"dhd_0","wit__2^2 + dhf_0",false),(-8,"dhf_0","wit_^2",false)).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4)),List(("1/2","wit__0*wit__10"),("1/2","wit__2*wit__3"),("1/2","wit__10*wit__6*wit__7*wit__5"),("1/2","wit_*wit__3")).map( s => (s._1.asTerm,s._2.asTerm)))),
      Some((List((-4,"r_0","abs_1 + ro_0",true),(-1,"w_0","-1",false),(-5,"rp_0","wit__0^2 + abs_1",false),(-2,"ho_0","-1/2*a_0*t_0^2 + dhd_0*t_0",false),(-7,"abs_1","wit__4^2",false),(-3,"max_1","dhd_0 - dhf_0",false),(-9,"rv_0","wit__8^2",false),(-2,"min_1","0",false),(-6,"t_0","wit__6^2",true),(-2,"hp_0","1/2*a_0*wit__6^4 - dhd_0*wit__6^2 + wit__1^2 + h_0",false),(-1,"ro_0","wit__6^2*wit__8^2",false),(-2,"dhd_0","-wit__3^2",false),(-7,"dhf_0","-wit_^2",true)).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4)),List(("1","wit__11*wit__9"),("1","wit__8*wit__6*wit__11"),("1","wit__4*wit__11")).map( s => (s._1.asTerm,s._2.asTerm)))),
      None,
      Some((List((-4,"r_0","abs_1 + ro_0",true),(-1,"w_0","1",false),(-5,"rp_0","wit__0^2 + abs_1",false),(-2,"ho_0","1/2*a_0*t_0^2 + dhd_0*t_0",false),(-7,"abs_1","wit__4^2",false),(-3,"max_1","-dhd_0 + dhf_0",false),(-9,"rv_0","wit__8^2",false),(-2,"min_1","0",false),(-6,"t_0","wit__6^2",true),(-2,"hp_0","1/2*a_0*wit__6^4 + dhd_0*wit__6^2 + wit__1^2 - h_0",false),(-1,"ro_0","wit__6^2*wit__8^2",false),(-2,"dhd_0","wit__3^2",true),(-7,"dhf_0","wit_^2",false)).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4)),List(("1","wit__11*wit__9"),("1","wit__8*wit__6*wit__11"),("1","wit__4*wit__11")).map( s => (s._1.asTerm,s._2.asTerm)))),
      None,
      Some((List((-4,"r_0","-abs_1 + ro_0",false),(-1,"w_0","-1",false),(-5,"rp_0","wit__0^2 + abs_1",false),(-2,"ho_0","-1/2*a_0*t_0^2 + dhd_0*t_0",false),(-12,"abs_1","-wit__0^2 + wit__9^2",false),(-3,"max_1","dhd_0 - dhf_0",false),(-10,"rv_0","wit__8^2",false),(-2,"min_1","0",false),(-7,"t_0","wit__6^2",true),(-2,"hp_0","1/2*a_0*wit__6^4 - dhd_0*wit__6^2 + wit__1^2 + h_0",false),(-1,"ro_0","wit__6^2*wit__8^2",false),(-2,"dhd_0","-wit__3^2",false),(-7,"dhf_0","-wit_^2",true)).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4)),List(("1","wit__0*wit__11"),("1","wit__8*wit__6*wit__11")).map( s => (s._1.asTerm,s._2.asTerm)))),
      None,
      Some((List((-4,"r_0","-abs_1 + ro_0",false),(-1,"w_0","1",false),(-5,"rp_0","wit__0^2 + abs_1",false),(-2,"ho_0","1/2*a_0*t_0^2 + dhd_0*t_0",false),(-12,"abs_1","-wit__0^2 + wit__9^2",false),(-3,"max_1","-dhd_0 + dhf_0",false),(-10,"rv_0","wit__8^2",false),(-2,"min_1","0",false),(-7,"t_0","wit__6^2",true),(-2,"hp_0","1/2*a_0*wit__6^4 + dhd_0*wit__6^2 + wit__1^2 - h_0",false),(-1,"ro_0","wit__6^2*wit__8^2",false),(-2,"dhd_0","wit__3^2",true),(-7,"dhf_0","wit_^2",false)).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4)),List(("1","wit__0*wit__11"),("1","wit__8*wit__6*wit__11")).map( s => (s._1.asTerm,s._2.asTerm)))),
      None,
      Some((List((-4,"r_0","abs_1 + ro_0",true),(-1,"w_0","-1",false),(-5,"rp_0","wit__0^2 + abs_1",false),(-2,"ho_0","-1/2*a_0*t_0^2 + dhd_0*t_0",false),(-7,"abs_1","wit__4^2",false),(-3,"max_1","dhd_0 - dhf_0",false),(-9,"rv_0","wit__8^2",false),(-2,"min_1","-dhd_0",false),(-6,"t_0","wit__6^2",true),(-2,"hp_0","1/2*a_0*wit__6^4 - dhd_0*wit__6^2 + wit__1^2 + h_0",false),(-1,"ro_0","wit__6^2*wit__8^2",false),(-8,"dhf_0","-wit_^2",true)).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4)),List(("1","wit__8*wit__6*wit__11"),("1","wit__11*wit__9"),("1","wit__4*wit__11")).map( s => (s._1.asTerm,s._2.asTerm)))),
      None,
      Some((List((-4,"r_0","abs_1 + ro_0",true),(-1,"w_0","1",false),(-5,"rp_0","wit__0^2 + abs_1",false),(-2,"ho_0","1/2*a_0*t_0^2 + dhd_0*t_0",false),(-7,"abs_1","wit__4^2",false),(-3,"max_1","-dhd_0 + dhf_0",false),(-9,"rv_0","wit__8^2",false),(-2,"min_1","dhd_0",false),(-6,"t_0","wit__6^2",true),(-2,"hp_0","1/2*a_0*wit__6^4 + dhd_0*wit__6^2 + wit__1^2 - h_0",false),(-1,"ro_0","wit__6^2*wit__8^2",false),(-8,"dhf_0","wit_^2",false)).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4)),List(("1","wit__8*wit__6*wit__11"),("1","wit__11*wit__9"),("1","wit__4*wit__11")).map( s => (s._1.asTerm,s._2.asTerm)))),
      None,
      Some((List((-4,"r_0","-abs_1 + ro_0",false),(-1,"w_0","-1",false),(-5,"rp_0","wit__0^2 + abs_1",false),(-2,"ho_0","-1/2*a_0*t_0^2 + dhd_0*t_0",false),(-12,"abs_1","-wit__0^2 + wit__9^2",false),(-3,"max_1","dhd_0 - dhf_0",false),(-10,"rv_0","wit__8^2",false),(-2,"min_1","-dhd_0",false),(-7,"t_0","wit__6^2",true),(-2,"hp_0","1/2*a_0*wit__6^4 - dhd_0*wit__6^2 + wit__1^2 + h_0",false),(-1,"ro_0","wit__6^2*wit__8^2",false),(-8,"dhf_0","-wit_^2",true)).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4)),List(("1","wit__8*wit__6*wit__11"),("1","wit__0*wit__11")).map( s => (s._1.asTerm,s._2.asTerm)))),
      None,
      Some((List((-4,"r_0","-abs_1 + ro_0",false),(-1,"w_0","1",false),(-5,"rp_0","wit__0^2 + abs_1",false),(-2,"ho_0","1/2*a_0*t_0^2 + dhd_0*t_0",false),(-12,"abs_1","-wit__0^2 + wit__9^2",false),(-3,"max_1","-dhd_0 + dhf_0",false),(-10,"rv_0","wit__8^2",false),(-2,"min_1","dhd_0",false),(-7,"t_0","wit__6^2",true),(-2,"hp_0","1/2*a_0*wit__6^4 + dhd_0*wit__6^2 + wit__1^2 - h_0",false),(-1,"ro_0","wit__6^2*wit__8^2",false),(-8,"dhf_0","wit_^2",false)).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4)),List(("1","wit__8*wit__6*wit__11"),("1","wit__0*wit__11")).map( s => (s._1.asTerm,s._2.asTerm)))),
      None
    )

    val foo = lwits.zipWithIndex.map(
      prind =>
        prind._1 match
        {
          case None => proveBy(res.subgoals(prind._2),nil)
          case Some(w) =>
            proveBy(res.subgoals(prind._2), w._1.foldLeft(nil)( _ & elim(_)) & witnessTac(w._2))
        }
      )

    print(foo)
    //res shouldBe 'proved
  }

}
