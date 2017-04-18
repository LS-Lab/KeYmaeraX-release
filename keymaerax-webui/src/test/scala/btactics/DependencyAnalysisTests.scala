package btactics


import edu.cmu.cs.ls.keymaerax.btactics.DependencyAnalysis._
import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

import scala.collection.immutable._

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
    val x = "x".asVariable.asInstanceOf[BaseVariable]
    val y = "y".asVariable.asInstanceOf[BaseVariable]
    dependencies(p,HashSet(x))._1 should contain only (x,y)
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

}
