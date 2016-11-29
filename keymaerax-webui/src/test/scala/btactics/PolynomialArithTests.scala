package btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.{AntePosition, PosInExpr, RenUSubst, SuccPosition}
import edu.cmu.cs.ls.keymaerax.btactics.PolynomialArith._
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.core.{Variable, _}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

import scala.collection.immutable._

/**
  * Created by yongkiat on 11/27/16.
  */
class PolynomialArithTests extends TacticTestBase {

  "PolynomialArith" should "check monomial normalization" in withMathematica { qeTool =>
    val m1 = "1 * x^5 * a^5".asTerm //Valid
    val m2 = "1 * x^5 * x^5".asTerm //Invalid
    val m3 = "1 * x^5 * y^5".asTerm //Invalid
    val m4 = "1 * (x^5 * a^5)".asTerm //Invalid
    val m5 = "1 * z^1 * x^7 * b^8".asTerm //Valid
    val m6 = "1 * z^8 * x^7 * a^1".asTerm //Valid

    (checkMono(m1),checkMono(m2),checkMono(m3),checkMono(m4),checkMono(m5),checkMono(m6)) shouldBe
       (true,false,false,false,true,true)

    (cmpMono(m5,m6)) shouldBe (true)
  }

  "PolynomialArith" should "check polynomial normalization" in withMathematica { qeTool =>
    val p1 = "0 + 5 * (1 * x^5 * b^5) + 5 * (1 * x^5 * a^5)".asTerm //Valid
    val p2 = "0 + 5 * (1 * c^5 * a^5) + 5 * (1 * x^5 * a^5)".asTerm //Invalid
    val p3 = "0 + 5 * (1 * x^5 * a^6) + 5 * (1 * x^5 * a^5)".asTerm //Invalid
    val p4 = "0 + 5 * (1 * x^6 * a^5) + 5 * (1 * x^5 * a^6)".asTerm //Valid
    val p5 = "0 + -5.5 * (1 * x^6 * a^5) + 5 * (1 * x^5 * a^6)".asTerm //Valid

    (checkPoly(p1), checkPoly(p2), checkPoly(p3), checkPoly(p4), checkPoly(p5)) shouldBe(true,false,false,true,true)
  }

  "PolynomialArith" should "do poly add" in withMathematica { qeTool =>
    val p1 = "0 + 5 * (1 * x^5 * b^5) + 5 * (1 * x^5 * a^5)".asTerm //Valid
    val p2 = "0 + 5 * (1 * x^6 * a^5) + 5 * (1 * x^5 * a^6)".asTerm //Valid
    val p3 = "0 + -5.5 * (1 * x^6 * a^5) + 5 * (1 * x^5 * a^6)".asTerm //Valid

    val (p4,r4) = addPoly(p1,p2)
    val (p5,r5) = addPoly(p4,p3)
    val (p6,r6) = addPoly(p5,p5)
    //println(p4,p5,p6)
    (checkPoly(p4),checkPoly(p5),checkPoly(p6)) shouldBe (true,true,true)
  }

  "PolynomialArith" should "do mono mul" in withMathematica { qeTool =>
    val m1 = "1 * x^5 * a^5".asTerm
    val m2 = "1 * z^1 * x^7 * b^8".asTerm
    val m3 = "1 * z^8 * x^7 * a^1".asTerm

    val p1 = "0 + 5 * (1 * x^5 * b^5) + 5 * (1 * x^5 * a^5)".asTerm

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
    val p1 = "0 + 2 * (1 * x^ 1) + 2 * (1 * b^2)".asTerm
    val p2 = "0 + -2 * (1 * x^1) + 2 * (1 * a^2)".asTerm

    println(addPoly(p1,p2)) //Cancelling coefficients
    println(addPoly(p1,p1)) //Adding coefficients
    println(addPoly(p2,p1)) //Inverse
  }

  "PolynomialArith" should "do mono mul with proof" in withMathematica { qeTool =>
    val m1 = "(1 * y^ 0.5 * x^2)".asTerm
    val m2 = "1* y^-0.5 * a^2 ".asTerm

    println(mulMono(m1,m2)) //Cancelling coefficients
    println(mulMono(m1,m1)) //Adding coefficients
    println(mulMono(m2,m1)) //Inverse
  }

  "PolynomialArith" should "do poly mono mul with proof" in withMathematica { qeTool =>
    val m1 = "1 * x^5 * a^5".asTerm
    val p1 = "0 + 5 * (1 * x^2) + 5 * (1 * y^2)".asTerm
    val (p2,r2) = mulPolyMono(p1,Number(5),m1)

    println(p2,r2)
  }

  "PolynomialArith" should "do poly mul with proof" in withMathematica { qeTool =>
    val p1 = "0 + 1 * (1 * x^2) + 1 * (1 * a^2)".asTerm
    val p2 = "0 + 2 * (1 * y^1) + 1 * (1 * a^2)".asTerm

    val (p3,r3) = addPoly(p1,p2)
    val (p4,r4) = mulPoly(p1,p2)
    val (p5,r5) = mulPoly(p3,p4)

    println(p4)
    println(r4)
    println(p5)
    println(r5)
  }

  "PolynomialArith" should "do iterated squares with proof" in withMathematica { qeTool =>

    println(iterSquare("(x+yz+k)".asTerm,3))
    println(iterSquare("(x+z+y)".asTerm,9))
    println(iterSquare("(xyz+yzx)".asTerm,12))

  }

  "PolynomialArith" should "do poly normalize with proof" in withMathematica { qeTool =>
    val p1 = "x * x + y + z * 5".asTerm
    val p2 = "y*(z + z + x ) * (x* y)".asTerm
    val p3 = "- (x^2 + y^2*z)".asTerm
    val p4 = "x^2 - (x^2 + y^2*z)".asTerm
    val p5 = "(x+y*z -x - y*z + a)^3".asTerm

    println(normalise(p1))
    println(normalise(p2))
    println(normalise(p3))
    println(normalise(p4))
    println(normalise(p5))
  }

  "PolynomialArith" should "do ax" in withMathematica { qeTool =>
    //RWV part of example in Fig 2

    //val test = proveBy("x=0 -> x^2 = 0".asFormula,QE)
    //val test2 = proveBy(Sequent(IndexedSeq("x = 0".asFormula),IndexedSeq()),CEat(test)(-1))
  }
}
