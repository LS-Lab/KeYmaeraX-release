package btactics


import edu.cmu.cs.ls.keymaerax.btactics.DependencyAnalysis._
import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase
import edu.cmu.cs.ls.keymaerax.btactics.helpers.QELogger._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXArchiveParser, KeYmaeraXProblemParser}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import testHelper.KeYmaeraXTestTags.IgnoreInBuildTest

import scala.collection.immutable._
import scala.collection.mutable.ListBuffer

/**
  * Dependency analysis examples
  */
class DependencyAnalysisTests extends TacticTestBase {

  "DependencyAnalysis" should "correctly identify linear ODEs" in withMathematica { qeTool =>
    val p = "{x1'=d1,x2'=d2,d1'=-w*d2,d2'=w*d1,t'=1}".asProgram
    val t = "t".asVariable.asInstanceOf[BaseVariable]
    val x1 = "x1".asVariable.asInstanceOf[BaseVariable]
    val x2 = "x2".asVariable.asInstanceOf[BaseVariable]
    val d1 = "d1".asVariable.asInstanceOf[BaseVariable]
    val d2 = "d2".asVariable.asInstanceOf[BaseVariable]
    val w = "w".asVariable.asInstanceOf[BaseVariable]
    dependencies(p,HashSet(t))._1 should contain only t
    dependencies(p,HashSet(x1))._1 should contain only (w,x1,d1,d2)
    dependencies(p,HashSet(x2))._1 should contain only (w,x2,d1,d2)
    dependencies(p,HashSet(d1))._1 should contain only (w,d1,d2)
    dependencies(p,HashSet(d2))._1 should contain only (w,d1,d2)
    dependencies(p,HashSet(w))._1 should contain only w
  }

  "DependencyAnalysis" should "correctly identify non-linear ODEs" in withMathematica { qeTool =>
    val p = "{x'=1,y'=y^2}".asProgram
    // Optimised analysis: x depends on y, but y does not depend on x
    val x = "x".asVariable.asInstanceOf[BaseVariable]
    val y = "y".asVariable.asInstanceOf[BaseVariable]
    dependencies(p,HashSet(x))._1 should contain only (x,y)
    dependencies(p,HashSet(y))._1 should contain only y
  }

  "DependencyAnalysis" should "correctly identify non-linear ODEs (2)" in withMathematica { qeTool =>
    val p = "{x'=1,y'=x^10}".asProgram
    // Optimised analysis: y depends on x and y, but x only depends on itself
    val x = "x".asVariable.asInstanceOf[BaseVariable]
    val y = "y".asVariable.asInstanceOf[BaseVariable]
    dependencies(p,HashSet(x))._1 should contain only x
    dependencies(p,HashSet(y))._1 should contain only (x,y)
  }

  "DependencyAnalysis" should "compute assignments correctly" in withMathematica { qeTool =>
    val p = "{b:=a;++b:=e;};c:=b;d:=c;".asProgram
    val d = "d".asVariable.asInstanceOf[BaseVariable]
    val a = "a".asVariable.asInstanceOf[BaseVariable]
    val e = "e".asVariable.asInstanceOf[BaseVariable]
    dependencies(p,HashSet(d))._1 should contain only (a,e)
  }

  "DependencyAnalysis" should "compute fixed-point on loops" in withMathematica { qeTool =>
    val p = "{x:=x+1;y:=y+1;?y<=10;}*".asProgram
    val x = "x".asVariable.asInstanceOf[BaseVariable]
    val y = "y".asVariable.asInstanceOf[BaseVariable]
    dependencies(p,HashSet(x))._1 should contain only (x,y)
    dependencies(p,HashSet(y))._1 should contain only y
  }

  "DependencyAnalysis" should "compute fixed-point on linear ODEs with evol domain" in withMathematica { qeTool =>
    val p = "{t'=1,v'=a & v >= 0}".asProgram
    val t = "t".asVariable.asInstanceOf[BaseVariable]
    val v = "v".asVariable.asInstanceOf[BaseVariable]
    val a = "a".asVariable.asInstanceOf[BaseVariable]
    dependencies(p,HashSet(t))._1 should contain only (t,v,a)
  }

  "DependencyAnalysis" should "handle function symbols in ODEs" in withMathematica { qeTool =>
    val p = "{x1'=d1,x2'=d2,d1'=-w()*d2,d2'=w()*d1,t'=A()}".asProgram
    val t = "t".asVariable.asInstanceOf[BaseVariable]
    val x1 = "x1".asVariable.asInstanceOf[BaseVariable]
    val x2 = "x2".asVariable.asInstanceOf[BaseVariable]
    val d1 = "d1".asVariable.asInstanceOf[BaseVariable]
    val d2 = "d2".asVariable.asInstanceOf[BaseVariable]
    val w = "w()".asTerm.asInstanceOf[FuncOf].func
    val A = "A()".asTerm.asInstanceOf[FuncOf].func
    dependencies(p,HashSet(x2))._1 should contain only (x2,d1,d2)
    dependencies(p,HashSet(x2))._2 should contain only w
    dependencies(p,HashSet(t))._2 should contain only A
  }

  "DependencyAnalysis" should "compute assignments with functions" in withMathematica { qeTool =>
    val p = "{b:=a();++b:=e();};c:=b;d:=c;".asProgram
    val d = "d".asVariable.asInstanceOf[BaseVariable]
    val a = "a()".asTerm.asInstanceOf[FuncOf].func
    val e = "e()".asTerm.asInstanceOf[FuncOf].func
    dependencies(p,HashSet(d))._2 should contain only (a,e)
  }

  "DependencyAnalysis" should "correctly identify non-linearities" in withMathematica { qeTool =>
    val p = "{x'=1,y'=f(a(),b)^2}".asProgram
    val x = "x".asVariable.asInstanceOf[BaseVariable]
    val y = "y".asVariable.asInstanceOf[BaseVariable]
    val b = "b".asVariable.asInstanceOf[BaseVariable]
    val a = "a()".asTerm.asInstanceOf[FuncOf].func
    val f = "f(a(),b)".asTerm.asInstanceOf[FuncOf].func
    dependencies(p,HashSet(x))._1 should contain only x
    dependencies(p,HashSet(y))._1 should contain only (b,y)
    dependencies(p,HashSet(y))._2 should contain only (f,a)
  }

  "DependencyAnalysis" should "correctly find SCCs" in withMathematica { qeTool =>
    val Some((_,pr,seq)) = parseStr("@Chilled water#Tll() < a(), a() < Tlu(), h()>0, r()>0, e()=1, h()/r()+a() < Tlu(), Tw < Tl, Tl < Tlu(), a()<=Tw, l=1->v=1, v=0->l=0, l=0|l=1, v=1|v=0, v=1->Tw=a(), v=1, t=0\n  ==>  [{Tw'=-r()*(1-v)*(Tw-Tl),Tl'=-r()*(Tl-Tw)+1*h(),t'=1&(0<=t&t < e())&Tw=a()}]((1=1->v=1)&(v=0->1=0)&(1=0|1=1)&(v=1|v=0)&(v=1->Tw=a()))#Tll() < a(), a() < Tlu(), h()>0, r()>0, e()=1, h()/r()+a() < Tlu(), l=1->v=1, v=0->l=0, l=0|l=1, v=1|v=0, v=1\n  ==>  (0<=t&t < e())&Tw=a()->(1=1->v=1)&(v=0->1=0)&(1=0|1=1)&(v=1|v=0)&(v=1->Tw=a())")
    val p = stripSeq(pr).get
    val adjls = analyseModal(p,seq).mapValues( v => v._1)
    scc(adjls) shouldBe List(Set("v".asVariable), Set("Tl".asVariable), Set("t".asVariable, "Tw".asVariable), Set("l".asVariable))
  }

  "DependencyAnalysis" should "analyse dependencies for some examples" in withMathematica { qeTool =>
    val Some((_,pr1,seq1)) = parseStr("@ETCS#v_0()=v, z_0()=z, kyxtime_0()=kyxtime, v>=0&v=(-b())*(kyxtime-kyxtime_0())+v_0()\n  ==>  [{z'=v,v'=-b(),kyxtime'=1&v>=0&v=(-b())*(kyxtime-kyxtime_0())+v_0()}](z=(-b())/2*(kyxtime-kyxtime_0())^2+v_0()*(kyxtime-kyxtime_0())+z_0())'#v_0()=v, z_0()=z, kyxtime_0()=kyxtime, v>=0&v=(-b())*(kyxtime-kyxtime_0())+v_0()\n  ==>  \\forall kyxtime \\forall v (v>=0&v=(-b())*(kyxtime-kyxtime_0())+v_0()->v=(-b())/2*(2*(kyxtime-kyxtime_0())^(2-1)*(1-0))+v_0()*(1-0)+0)")
    val Some((_,pr2,seq2)) = parseStr("@Chilled water#Tll() < a(), a() < Tlu(), h()>0, r()>0, e()=1, h()/r()+a() < Tlu(), Tw < Tl, Tl < Tlu(), a()<=Tw, l=1->v=1, v=0->l=0, l=0|l=1, v=0, v=1->Tw=a(), t=0\n  ==>  [{Tw'=-r()*(1-v)*(Tw-Tl),Tl'=-r()*(Tl-Tw)+0*h(),t'=1&0<=t&t < e()}]Tw < Tl#Tll() < a(), a() < Tlu(), h()>0, r()>0, e()=1, h()/r()+a() < Tlu(), Tw < Tl, Tl < Tlu(), a()<=Tw, l=1->v=1, v=0->l=0, l=0|l=1, v=0, v=1->Tw=a(), t=0\n  ==>  \\exists y (0<=t&t < e()->(Tl-Tw)*y^2>0&\\forall Tl \\forall Tw \\forall t \\forall y (0<=t&t < e()->(-r()*(Tl-Tw)+0*h()--r()*(1-v)*(Tw-Tl))*y^2+(Tl-Tw)*(2*y^(2-1)*(r()*y+0))>=0))")
    val p1 = stripSeq(pr1).get
    val p2 = stripSeq(pr2).get

    val adjls1 = analyseModal(p1,seq1).mapValues( v => v._1)
    val adjls2 = analyseModal(p2,seq2).mapValues( v => v._1)

    val sccs1 = scc(adjls1)
    val sccs2 = scc(adjls2)

    sccs1 should contain only (Set("v".asVariable, "kyxtime".asVariable), Set("z".asVariable))
    sccs2 should contain only (Set("l".asVariable), Set("t".asVariable), Set("v".asVariable), Set("Tl".asVariable, "Tw".asVariable))
  }

  "DependencyAnalysis" should "provide a partial order to QE problems" in withMathematica { qeTool =>

    val p = "{A:=B; C:=D; {D'=E , E' = D & F>1}}".asProgram
    val seq = " ==> A+C+B+D+E+G() > 0".asSequent
    val adjls = analyseModal(p,seq).mapValues( v => v._1)
    val rtc = transClose(adjls)
    val vars = freeVars(seq)

    val indO = inducedOrd(rtc)

    //The dependency graph is
    // A -> B, C -> D <-> E -> F

    //x -> y ==> x < y (most dependent first)
    val ord1 = vars.toList.sortWith( (x,y) =>
      {
        val ord = indO.compare(x,y)
        if (ord==0) x.compare(y) < 0
        else ord < 0
      }
    )
    ord1 shouldBe List("A", "B", "C", "D", "E").map(v=>v.asVariable)

    //x -> y ==> x > y (least dependent first)
    val ord2 = vars.toList.sortWith( (x,y) =>
      {
        val ord = indO.compare(x,y)
        if (ord==0) x.compare(y) < 0
        else ord > 0
      }
    )
    ord2 shouldBe List("B", "A", "D", "E", "C").map(v=>v.asVariable)
  }

  private def timeCall[A](f : Unit => A) : Double = {
    val t0 = System.nanoTime()
    val _ = f()
    val t1 = System.nanoTime()
    (t1-t0).toDouble/1000000000.0
  }

  private def timeQE(problems:List[(Program,Sequent)]) : List[Double] = {
    val timeLs = ListBuffer[(Double)]()
    for( (p,seq) <- problems) {
      val t = timeCall(_ => proveBy(seq,QE))
      timeLs+=t
    }
    timeLs.toList
  }

  private def timeheuQE(problems:List[(Program,Sequent)]) : List[Double] = {
    val timeLs = ListBuffer[(Double)]()
    for( (p,seq) <- problems) {
      val t = timeCall(_ => proveBy(seq,heuQE))
      timeLs+=t
    }
    timeLs.toList
  }

  private def timeheuPOQE(problems:List[(Program,Sequent)], ignoreTest:Boolean) : List[Double] = {
    val timeLs = ListBuffer[(Double)]()
    for( (p,seq) <- problems) {
      val t = timeCall(_ => {
        val adjls = transClose(analyseModal(p, seq, ignoreTest).mapValues(v => v._1))
        proveBy(seq,heuQEPO(inducedOrd(adjls)))
      })
      timeLs+=t
    }
    timeLs.toList
  }

  //Timing with a fixed PO
  private def timeheufixedPOQE(problems:List[(Program,Sequent)], po:Ordering[Variable]) : List[Double] = {
    val timeLs = ListBuffer[(Double)]()
    for( (p,seq) <- problems) {
      val t = timeCall(_ => {
        proveBy(seq,heuQEPO(po))
      })
      timeLs+=t
    }
    timeLs.toList
  }

  //Timing tests
  "DependencyAnalysis" should "record time to re-prove the ODE logs" taggedAs IgnoreInBuildTest in withMathematica { qeTool =>
    val ls = parseLog(System.getProperty("user.home") + "/.keymaerax/ODElog.txt")
    val problems = ls("AxiomaticODESolver").flatMap ( r => {
      stripSeq(r._1) match {
        case None => None
        case Some(p) => Some(p,r._2)
      }
    })
    val t0 = timeQE(problems) //Apparently, this also warms up the QE connection
    //Ignore any problems that took < 2s
    val red_probs = problems.zip(t0).collect{case p if p._2 >= 2.0 => p._1}
    println(red_probs,red_probs.length)

    //println(t0,t0.sum)
    val t1 = timeQE(red_probs)
    println(t1,t1.sum)
    val t2 = timeheuQE(red_probs)
    println(t2,t2.sum)
    val t3 = timeheuPOQE(red_probs,false)
    println(t3,t3.sum)
    val t4 = timeheuPOQE(red_probs,true)
    println(t4,t4.sum)

  }

  "DependencyAnalysis" should "record time to re-prove the ETCS logs" taggedAs IgnoreInBuildTest in withMathematica { qeTool =>
    val ls = parseLog(System.getProperty("user.home") + "/.keymaerax/ETCS.txt")
    val problems = ls("ETCS").flatMap ( r => {
      stripSeq(r._1) match {
        case None => None
        case Some(p) => Some(p,r._2)
      }
    })
    val t0 = timeQE(problems) //Apparently, this also warms up the QE connection
    //Ignore any problems that took < 2s
    val red_probs = problems.zip(t0).collect{case p if p._2 >= 2.0 => p._1}
    println(red_probs,red_probs.length)

    //println(t0,t0.sum)
    val t1 = timeQE(red_probs)
    println(t1,t1.sum)
    val t2 = timeheuQE(red_probs)
    println(t2,t2.sum)
    val t3 = timeheuPOQE(red_probs,false)
    println(t3,t3.sum)
    val t4 = timeheuPOQE(red_probs,true)
    println(t4,t4.sum)

  }

  "DependencyAnalysis" should "record time to re-prove the STTT logs" taggedAs IgnoreInBuildTest in withMathematica { qeTool =>
    val ls = parseLog(System.getProperty("user.home") + "/.keymaerax/STTT.txt")
    val problems = ls("STTT").flatMap ( r => {
      stripSeq(r._1) match {
        case None => None
        case Some(p) => Some(p,r._2)
      }
    })
    val t0 = timeQE(problems) //Apparently, this also warms up the QE connection
    //Ignore any problems that took < 2s
    val red_probs = problems.zip(t0).collect{case p if p._2 >= 2.0 => p._1}
    println(problems.length,red_probs,red_probs.length)

    //println(t0,t0.sum)
    val t1 = timeQE(red_probs)
    println(t1,t1.sum)
    val t2 = timeheuQE(red_probs)
    println(t2,t2.sum)
    val t3 = timeheuPOQE(red_probs,false)
    println(t3,t3.sum)
    val t4 = timeheuPOQE(red_probs,true)
    println(t4,t4.sum)

  }

  "DependencyAnalysis" should "record time to re-prove the chilled water logs" taggedAs IgnoreInBuildTest in withMathematica { qeTool =>
    val ls = parseLog(System.getProperty("user.home") + "/.keymaerax/chilled.txt")
    val problems = ls("Chilled water").flatMap ( r => {
      stripSeq(r._1) match {
        case None => None
        case Some(p) => Some(p,r._2)
      }
    })
    val t0 = timeQE(problems) //Apparently, this also warms up the QE connection
    //Ignore any problems that took < 2s
    val red_probs = problems.zip(t0).collect{case p if p._2 >= 2.0 => p._1}
    println(problems.length,red_probs,red_probs.length)

    //println(t0,t0.sum)
    val t1 = timeQE(red_probs)
    println(t1,t1.sum)
    val t2 = timeheuQE(red_probs)
    println(t2,t2.sum)
    val t3 = timeheuPOQE(red_probs,false)
    println(t3,t3.sum)
    val t4 = timeheuPOQE(red_probs,true)
    println(t4,t4.sum)

  }

  "DependencyAnalysis" should "record time to re-prove the ACAS X logs" taggedAs IgnoreInBuildTest in withMathematica { qeTool =>
    val ls = parseLog(System.getProperty("user.home") + "/.keymaerax/ACASX.txt")

    val acasximplicit = KeYmaeraXProblemParser( io.Source.fromInputStream(
      getClass.getResourceAsStream("/examples/casestudies/acasx/sttt/safe_explicit.kyx")).mkString)

    val prog = stripImp(acasximplicit).get
    val adjls = analyseModalVars(prog,varSetToBaseVarSet(StaticSemantics.vars(prog).toSet),true)
    println(adjls)

//    val problems = ls("ACAS X Safe").flatMap ( r => {
//      stripSeq(r._1) match {
//        case None => None
//        case Some(p) => Some(p,r._2)
//      }
//    })
//    val t0 = timeQE(problems) //Apparently, this warms up the QE connection
//    println(t0,t0.sum)
//    val t1 = timeQE(problems)
//    println(t1,t1.sum)
//    val t2 = timeheuQE(problems)
//    println(t2,t2.sum)
//    val t3 = timeheuPOQE(problems)
//    println(t3,t3.sum)

  }

  //NOTE: Avoid committing the solutions to the repo

  "DependencyAnalysis" should "analyse dependencies for labs" taggedAs IgnoreInBuildTest in withMathematica { qeTool =>
    val l2 = scala.io.Source.fromFile("L2Q2.kya").mkString
    val l3 = scala.io.Source.fromFile("L3Q6.kya").mkString
    val archiveL2 :: Nil = KeYmaeraXArchiveParser.parse(l2)
    val archiveL3 :: Nil = KeYmaeraXArchiveParser.parse(l3)

    val (l2f, l2t) = (archiveL2._3.asInstanceOf[Formula], archiveL2._4.head._2)
    val (l3f, l3t) = (archiveL3._3.asInstanceOf[Formula], archiveL3._4.head._2)

    val p2 = stripImp(l2f).get
    val p3 = stripImp(l3f).get
    println(analyseModalVars(p2,varSetToBaseVarSet(StaticSemantics.vars(p2).toSet),true))
    println(analyseModalVars(p2,varSetToBaseVarSet(StaticSemantics.vars(p2).toSet),false))

    println(analyseModalVars(p3,varSetToBaseVarSet(StaticSemantics.vars(p3).toSet),true))
    println(analyseModalVars(p3,varSetToBaseVarSet(StaticSemantics.vars(p3).toSet),false))
  }

  "DependencyAnalysis" should "record time to re-prove lab 2" taggedAs IgnoreInBuildTest in withMathematica { qeTool =>
    val l2 = scala.io.Source.fromFile("L2Q2.kya").mkString
    val archiveL2 :: Nil = KeYmaeraXArchiveParser.parse(l2)

    val (l2f, l2t) = (archiveL2._3.asInstanceOf[Formula], archiveL2._4.head._2)

    val p2 = stripImp(l2f).get

    val pof = inducedOrd(transClose(analyseModalVars(p2,varSetToBaseVarSet(StaticSemantics.vars(p2).toSet),false).mapValues(v => v._1)))
    val pot = inducedOrd(transClose(analyseModalVars(p2,varSetToBaseVarSet(StaticSemantics.vars(p2).toSet),true).mapValues(v => v._1)))

    val ls = parseLog(System.getProperty("user.home") + "/.keymaerax/lab2.txt")

    val problems = ls("L2").flatMap ( r => Some(Test(True),r._2))

    val t0 = timeQE(problems) //Apparently, this also warms up the QE connection
    //Ignore any problems that took < 2s
    val red_probs = problems.zip(t0).collect{case p if p._2 >= 2.0 => p._1}
    println(problems.length,red_probs,red_probs.length)

    //println(t0,t0.sum)
    val t1 = timeQE(red_probs)
    println(t1,t1.sum)
    val t2 = timeheuQE(red_probs)
    println(t2,t2.sum)
    val t3 = timeheufixedPOQE(red_probs,pof)
    println(t3,t3.sum)
    val t4 = timeheufixedPOQE(red_probs,pot)
    println(t4,t4.sum)
  }

  "DependencyAnalysis" should "record time to re-prove lab 3" taggedAs IgnoreInBuildTest in withMathematica { qeTool =>
    val l3 = scala.io.Source.fromFile("L3Q6.kya").mkString
    val archiveL3 :: Nil = KeYmaeraXArchiveParser.parse(l3)

    val (l3f, l3t) = (archiveL3._3.asInstanceOf[Formula], archiveL3._4.head._2)

    val p3 = stripImp(l3f).get

    val pof = inducedOrd(transClose(analyseModalVars(p3,varSetToBaseVarSet(StaticSemantics.vars(p3).toSet),false).mapValues(v => v._1)))
    val pot = inducedOrd(transClose(analyseModalVars(p3,varSetToBaseVarSet(StaticSemantics.vars(p3).toSet),true).mapValues(v => v._1)))

    val ls = parseLog(System.getProperty("user.home") + "/.keymaerax/lab3.txt")

    val problems = ls("L3").flatMap ( r => Some(Test(True),r._2))

    val t0 = timeQE(problems) //Apparently, this also warms up the QE connection
    //Ignore any problems that took < 2s
    val red_probs = problems.zip(t0).collect{case p if p._2 >= 2.0 => p._1}
    println(problems.length,red_probs,red_probs.length)

    //println(t0,t0.sum)
    val t1 = timeQE(red_probs)
    println(t1,t1.sum)
    val t2 = timeheuQE(red_probs)
    println(t2,t2.sum)
    val t3 = timeheufixedPOQE(red_probs,pof)
    println(t3,t3.sum)
    val t4 = timeheufixedPOQE(red_probs,pot)
    println(t4,t4.sum)
  }
}
