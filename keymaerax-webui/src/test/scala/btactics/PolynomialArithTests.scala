package btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.PolynomialArith._
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.core.{Variable, _}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tools.JLinkMathematicaLink

import scala.collection.immutable._

/**
  * Created by yongkiat on 11/27/16.
  */
class PolynomialArithTests extends TacticTestBase {

  "PolynomialArith" should "order variables" in withMathematica { qeTool =>
    val vars = List("x","z","x()","z()","a+b","c+d").map(_.asTerm)

    vars.combinations(2).toList.map{ case List(x,y) => {VarOrd.compare(x,y)}} shouldBe List(-2,-1,-1,0,0,-1,-1,0,0,-2,0,0,0,0,0)
    vars.combinations(2).toList.map{ case List(x,y) => {VarOrd.compare(y,x)}} shouldBe List(2,1,1,0,0,1,1,0,0,2,0,0,0,0,0)
  }

  "PolynomialArith" should "check monomial normalization" in withMathematica { qeTool =>
    //Note: recently changed to reverse lexicographic
    val m1 = "1 * a^5 * x^5".asTerm //Valid
    val m2 = "1 * x^5 * x()^5".asTerm //Valid
    val m3 = "1 * y^5 * x^5".asTerm //Invalid
    val m4 = "1 * (a^5 * x^5)".asTerm //Invalid
    val m5 = "1 * b^1 * x^7 * z()^8".asTerm //Valid
    val m6 = "1 * a^8 * x^7 * z()^1".asTerm //Valid
    (checkMono(m1),checkMono(m2),checkMono(m3),checkMono(m4),checkMono(m5),checkMono(m6)) shouldBe
       (true,true,false,false,true,true)
  }


  "PolynomialArith" should "check monomial ordering" in withMathematica { qeTool =>
    val m1 = "1 * a^5 * x^5".asTerm //Valid
    val m2 = "1 * x^5 * x()^5".asTerm //Valid
    val m5 = "1 * b^1 * x^7 * z()^8".asTerm //Valid
    val m6 = "1 * a^8 * x^7 * z()^1".asTerm //Valid
    val m7 = "1 * a^8 * x^7 * z()^1".asTerm //Valid

    val vars = List(m1,m2,m5,m6,m7)

    (vars.combinations(2).toList.map{ case List(x,y) => {MonOrd.compare(x,y)}}) shouldBe List(-1,-1,-1,-1,-1,1,0)
    (vars.combinations(2).toList.map{ case List(x,y) => {MonOrd.compare(y,x)}}) shouldBe List(1,1,1,1,1,-1,0)

  }

  "PolynomialArith" should "check polynomial normalization" in withMathematica { qeTool =>
    val p1 = "0 + 5 * (1 * a^5 * x^5) + 5 * (1 * b^5 * x^5)".asTerm //Valid
    val p2 = "0 + 5 * (1 * a^5 * c^5) + 5 * (1 * a^5 * x^5)".asTerm //Valid
    val p3 = "0 + 5 * (1 * a^5 * x^6) + 5 * (1 * a^5 * x^5)".asTerm //Invalid
    val p4 = "0 + 5 * (1 * a^6 * x^5) + 5 * (1 * a^5 * x^6)".asTerm //Valid
    val p5 = "0 + -5.5 * (1 * a^6 * x^5) + 5 * (1 * a^5 * x^6)".asTerm //Valid

    (checkPoly(p1), checkPoly(p2), checkPoly(p3), checkPoly(p4), checkPoly(p5)) shouldBe(true,true,false,true,true)
  }

  "PolynomialArith" should "do poly add" in withMathematica { qeTool =>
    val p1 = "0 + 5 * (1 * a^5 * x^5) + 5 * (1 * b^5 * x^5)".asTerm //Valid
    val p2 = "0 + 5 * (1 * a^6 * x^5) + 5 * (1 * a^5 * x^6)".asTerm //Valid
    val p3 = "0 + -5.5 * (1 * a^6 * x^5) + 5 * (1 * a^5 * x^6)".asTerm //Valid

    val (p4,r4) = addPoly(p1,p2)
    val (p5,r5) = addPoly(p4,p3)
    val (p6,r6) = addPoly(p5,p5)
    (checkPoly(p4),checkPoly(p5),checkPoly(p6)) shouldBe (true,true,true)
    (r4.isProved,r5.isProved,r6.isProved) shouldBe (true,true,true)
  }

  "PolynomialArith" should "do mono mul" in withMathematica { qeTool =>
    val m1 = "1 * a^5 * x^5".asTerm
    val m2 = "1 * b^1 * x^7 * z^8".asTerm
    val m3 = "1 * x^8 * z^7 * a()^1".asTerm

    val p1 = "0 + 5 * (1 * x^5 * a()^5) + 5 * (1 * x^5 * b()^5)".asTerm

    val (m4,r4) = mulMono(m1,m2)
    val (m5,r5) = mulMono(m4,m3)
    val (m6,r6) = mulMono(m5,m5)

    val (p2,r2) = mulPolyMono(p1,Number(5),m4)

    //println(m4,m5,m6)
    //println(p2)
    (checkPoly(p1),checkPoly(p2)) shouldBe (true,true)
  }

  "PolynomialArith" should "do poly mul" in withMathematica { qeTool =>
    val p1 = "0 + 1 * (1 * x^2) + 1 * (1 * a^2)".asTerm
    val p2 = "0 + 2 * (1 * y^1) + 1 * (1 * a^2)".asTerm

    val (p3,r3) = addPoly(p1,p2)
    val (p4,r4) = mulPoly(p1,p2)
    val (p5,r5) = mulPoly(p3,p4)

    //println(p4)
    //println(p5)
    (checkPoly(p1),checkPoly(p2),checkPoly(p3),checkPoly(p4),checkPoly(p5)) shouldBe (true,true,true,true,true)
  }

  "PolynomialArith" should "do poly add with proof" in withMathematica { qeTool =>
    val p1 = "0 + 2 * (1 * x^ 1) + 2 * (1 * b()^2)".asTerm
    val p2 = "0 + -2 * (1 * x^1) + 2 * (1 * a()^2)".asTerm

    val (p3,r3) = addPoly(p1,p2) //Cancelling coefficients
    val (p4,r4) = addPoly(p1,p1) //Adding coefficients
    val (p5,r5) = addPoly(p2,p1) //Inverse

    p3 shouldBe "0+2*(1*a()^2)+2*(1*b()^2)".asTerm
    p4 shouldBe "0+4*(1*x^1)+4*(1*b()^2)".asTerm
    p5 shouldBe "0+2*(1*a()^2)+2*(1*b()^2)".asTerm

    r3 shouldBe 'proved
    r4 shouldBe 'proved
    r5 shouldBe 'proved
  }

  "PolynomialArith" should "do mono mul with proof" in withMathematica { qeTool =>
    //Note: ^0.5 isn't actually allowed
    val m1 = "(1 * y^ 0.5 * x()^2)".asTerm
    val m2 = "1* y^-0.5 * a()^2 ".asTerm

    val (m3,r3) = mulMono(m1,m2) //Cancelling coefficients
    val (m4,r4) = mulMono(m1,m1) //Adding coefficients
    val (m5,r5) = mulMono(m2,m1) //Inverse

    m3 shouldBe "1*a()^2*x()^2".asTerm
    m4 shouldBe "1*y^1.0*x()^4".asTerm
    m5 shouldBe "1*a()^2*x()^2".asTerm

    r3 shouldBe 'proved
    r4 shouldBe 'proved
    r5 shouldBe 'proved
  }

  "PolynomialArith" should "do poly mono mul with proof" in withMathematica { qeTool =>
    val m1 = "1 * x^5 * a()^5".asTerm
    val p1 = "0 + 5 * (1 * x^2) + 5 * (1 * y()^2)".asTerm
    val (p2,r2) = mulPolyMono(p1,Number(5),m1)

    p2 shouldBe "0+25*(1*x^7*a()^5)+25*(1*x^5*a()^5*y()^2)".asTerm
    r2 shouldBe 'proved
  }

  "PolynomialArith" should "do poly mul with proof" in withMathematica { qeTool =>
    val p1 = "0 + 1 * (1 * x^2) + 1 * (1 * a()^2)".asTerm
    val p2 = "0 + 2 * (1 * y^1) + 1 * (1 * a()^2)".asTerm

    val (p3,r3) = addPoly(p1,p2)
    val (p4,r4) = mulPoly(p1,p2)
    val (p5,r5) = mulPoly(p3,p4)

    p4 shouldBe "0+2*(1*x^2*y^1)+2*(1*y^1*a()^2)+1*(1*x^2*a()^2)+1*(1*a()^4)".asTerm
    p5 shouldBe "0+4*(1*x^2*y^2)+4*(1*y^2*a()^2)+2*(1*x^4*y^1)+8*(1*x^2*y^1*a()^2)+6*(1*y^1*a()^4)+1*(1*x^4*a()^2)+3*(1*x^2*a()^4)+2*(1*a()^6)".asTerm

    r4 shouldBe 'proved
    r5 shouldBe 'proved
  }

  "PolynomialArith" should "do iterated squares with proof" in withMathematica { qeTool =>

    val (t1,r1) = iterSquare("(x+yz+k)".asTerm,3)
    val (t2,r2) = iterSquare("(x+z+y)".asTerm,9)
    val (t3,r3) = iterSquare("(xyz+yzx)".asTerm,12)

    t1 shouldBe "(x+yz+k)^2*(x+yz+k)".asTerm
    t2 shouldBe "(((x+z+y)^2)^2)^2*(x+z+y)".asTerm
    t3 shouldBe "(((xyz+yzx)^2*(xyz+yzx))^2)^2".asTerm

    r1 shouldBe 'proved
    r2 shouldBe 'proved
    r3 shouldBe 'proved
  }

  "PolynomialArith" should "do poly normalize with proof" in withMathematica { qeTool =>
    val p1 = "x * x + y + z * 5".asTerm
    val p2 = "y*(z + z + x ) * (x* y)".asTerm
    val p3 = "- (x^2 + y^2*z)".asTerm
    val p4 = "x^2 - (x^2 + y^2*z)".asTerm
    val p5 = "(x+y*z -x - y*z + a)^3".asTerm
    val p6 = "1+(a*b*c)^2-(x-y-1*a^2)*(0+-1*(1*y^1*c^2*b^2))".asTerm

    val (t1,r1) = (normalise(p1))
    val (t2,r2) = (normalise(p2))
    val (t3,r3) = (normalise(p3))
    val (t4,r4) = (normalise(p4))
    val (t5,r5) = (normalise(p5))
    val (t6,r6) = (normalise(p6))

    (checkPoly(t1),checkPoly(t2),checkPoly(t3),checkPoly(t4),checkPoly(t5),checkPoly(t6)) shouldBe (true,true,true,true,true,true)
    r1 shouldBe 'proved
    r2 shouldBe 'proved
    r3 shouldBe 'proved
    r4 shouldBe 'proved
    r5 shouldBe 'proved
    r6 shouldBe 'proved
  }

  "PolynomialArith" should "do mono div" in withMathematica { qeTool =>
    val m1 = "1 * x^5 * a()^5".asTerm
    val m2 = "1 * x^1 * z^7 * b()^8".asTerm
    val m3 = "1 * z^8 * a()^7 * x()^1".asTerm
    val m4 = "1 * z^5 * x()^1".asTerm

    println(divMono(m2,m1)) //Not Divisible
    println(divMono(m2,m2)) //Divisible
    println(divMono(m3,m2)) //Not Divisible
    println(divMono(m3,m4)) //Divisible

  }

  "PolynomialArith" should "do poly div" in withMathematica { qeTool =>
    val p1 = normalise("x - y -1*a^2".asTerm)._1
    val p2 = normalise("z-b^2".asTerm)._1
    val p3 = normalise("z*(y-x)*c^2-1".asTerm)._1
    val p = normalise("1+(a*b*c)^2".asTerm)._1

    println(reduction(List(p1,p2,p3),p))
  }

  "PolynomialArith" should "prove with oracle witness" in withMathematica { qeTool =>
    val p1 = "x - y -1*a^2".asTerm
    val p2 = "z-b^2".asTerm
    val p3 = "z*(y-x)*c^2-1".asTerm
    val w = "(a*b*c)".asTerm

    val insts = List((1,"a^2*c^2".asTerm),(0,"z*c^2".asTerm),(2,"1".asTerm))

    //Guided reduction
    val pr1 = proveWithWitness(List(p1,p2,p3),List(w),Some(insts))

    //Confluent automated reduction
    val pr2 = proveWithWitness(List(p1,p2,p3),List(w))
    val pr3 = proveWithWitness(List(p2,p1,p3),List(w))
    val pr4 = proveWithWitness(List(p3,p2,p1),List(w))

    pr1 shouldBe 'proved
    pr2 shouldBe 'proved
    pr3 shouldBe 'proved
    pr4 shouldBe 'proved
  }

  "PolynomialArith" should "generate non-zero squares witness" in withMathematica { qeTool =>
    val witness = List("x+y+z ".asTerm,"z-b^2".asTerm,"a-b^2*c".asTerm)
    println(assertWitness(witness))
  }

  "PolynomialArith" should "normalize pure arithmetic sequent" in withMathematica { qeTool =>
    // A sequent of pure arithmetic only has (in)equational formulas (operators >,>=,=  TODO: !=)
    // i.e. no dL, no &, |, <, <= negations, etc.
    val antes = IndexedSeq(
      "x + y + z >= F() + G()".asFormula,
      "k * z > a + b".asFormula,
      "c - d > z".asFormula,
      "d * f = 12".asFormula
    )
    val succs = IndexedSeq(
      "k >= z".asFormula,
      "k+b = z+y+a".asFormula,
      "c > d".asFormula,
      "g() >= f()".asFormula,
      "K() = A+B+C".asFormula
    )
    val pr = proveBy(Sequent(antes,succs),prepareArith)
    println(pr)
  }

  //Example from Harrison(TPHOL 07)
  "PolynomialArith" should "run on quadratic formula" in withMathematica { qeTool =>
    val succ = IndexedSeq("(\\forall y x < y^2)->[{x'=1,y'=y}](\\forall y x < y^2)".asFormula)
    //val succ = IndexedSeq("(x>0)->[{x'=1,y'=y}](x>0)".asFormula)


    val prr = proveBy(Sequent(IndexedSeq(),succ),
      implyR(1) & diffInd()(1)// & OnAll(prop) & cohideR(1)

    )//diffInd('full)(1))// <( QE,cohideR(1) & chase(1)))
    println(prr)
//    val succs = IndexedSeq(
//      "a* x^2 + b*x + c = 0 -> b^2 - 4*a*c >= 0 ".asFormula
//    )
//
//    val pr = proveBy(Sequent(IndexedSeq(),succs),prop & clearSucc & DebuggingTactics.print("foo") & normAnte)
//    println(pr)
//
//    val polys =
//      pr.subgoals(0).ante.map(
//        f => f match {
//          case Equal(l, _) => l
//          case _ => ???
//        }
//      ).toList
//
////    val polys = List("a^2-x+y","b^2-z","x*z*c^2-y*z*c^2+1").map(_.asTerm)
//
//
//    val vars = polys.flatMap(p => StaticSemantics.vars(p).symbols[NamedSymbol].toList.sorted)
//
//    println(qeTool.witness(polys))

  }

}
