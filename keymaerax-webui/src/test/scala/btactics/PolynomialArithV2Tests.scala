package btactics

import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettierPrinter
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import testHelper.KeYmaeraXTestTags.SlowTest
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.infrastruct.PosInExpr
import edu.cmu.cs.ls.keymaerax.tools.ext.RingsLibrary

import scala.collection.immutable._
import org.scalatest.LoneElement._

/**
  * @author Fabian Immler
  */
class PolynomialArithV2Tests extends TacticTestBase {

  lazy val pa4 = new PolynomialArithV2("x,y,f(),g()".split(',').map(_.asTerm).toIndexedSeq)
  lazy val pa20 = new PolynomialArithV2("x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19".split(',').map(_.asTerm).toIndexedSeq)

  "Initialization" should "initialize four Variables" in withMathematica { _ =>
    pa4
  }

  "it" should "initialize twenty Variables" in withMathematica { _ =>
    pa20
  }

  "Coefficient" should "construct" in withMathematica { _ =>
    import pa4._
    val coeff = Coefficient(BigDecimal("0.1"), BigDecimal("3"))
    coeff.prv shouldBe 'proved
    coeff.prv.conclusion.ante shouldBe 'empty
    coeff.lhs shouldBe "0.1/3".asTerm
    coeff.rhs shouldBe "0.1/3".asTerm
  }

  it should "multiply" in withMathematica { _ =>
    import pa4._
    val c1 = Coefficient(BigDecimal("0.1"), BigDecimal("3"))
    val c2 = Coefficient(BigDecimal("123.12"), BigDecimal("2"))
    val res = (c1*c2)*(c1*c2*c2)
    res.num shouldBe BigDecimal("18663.18755328")
    res.denum shouldBe BigDecimal("72")
    res.prv shouldBe 'proved
    res.prv.conclusion.ante shouldBe 'empty
    res.prv.conclusion.succ.loneElement shouldBe Equal(Times(Times(c1.lhs, c2.lhs), (Times(Times(c1.lhs, c2.lhs), c2.lhs))),
      Divide(res.numN, res.denumN)
    )
  }

  it should "add" in withMathematica { _ =>
    import pa4._
    val c1 = Coefficient(BigDecimal("0.1"), BigDecimal("3"))
    val c2 = Coefficient(BigDecimal("123.12"), BigDecimal("2"))
    val res = (c1+c2)+(c2+c2)
    res.num shouldBe BigDecimal("4433.12")
    res.denum shouldBe BigDecimal("24")
    res.prv shouldBe 'proved
    res.prv.conclusion.ante shouldBe 'empty
    res.prv.conclusion.succ.loneElement shouldBe Equal(Plus(Plus(c1.lhs, c2.lhs), (Plus(c2.lhs, c2.lhs))),
      Divide(res.numN, res.denumN))
  }

  "monomials" should "test" in withMathematica { _ =>
    import pa4._
  }

  it should "be constructed" in withMathematica { _ =>
    import pa4._
    val res = Monomial(Coefficient(2, 3), IndexedSeq(0, 1, 0, 2))
    res.rhs shouldBe "2/3*(1*y^1*1*g()^2)".asTerm
  }

  it should "prove template lemmas" in withMathematica { _ =>
    import pa4._
    monomialTimesLemma shouldBe 'proved
//    val pp = new KeYmaeraXPrettierPrinter(100)
//    println(pp.stringify(monomialTimesLemma))
    monomialTimesLemma.conclusion.succ.loneElement shouldBe
      """
        |l_(||) = cl_(||) * (xl0_(||) * xl1_(||) * xl2_(||) * xl3_(||)) &
        |r_(||) = cr_(||) * (xr0_(||) * xr1_(||) * xr2_(||) * xr3_(||)) &
        |cl_(||) * cr_(||) = c0_(||) &
        |xl0_(||) * xr0_(||) = x0_(||) &
        |xl1_(||) * xr1_(||) = x1_(||) & xl2_(||) * xr2_(||) = x2_(||) & xl3_(||) * xr3_(||) = x3_(||) ->
        |l_(||) * r_(||) = c0_(||) * (x0_(||) * x1_(||) * x2_(||) * x3_(||))""".stripMargin.asFormula
  }

  it should "multiply" in withMathematica { _ =>
    import pa4._
    val pp = new KeYmaeraXPrettierPrinter(100)
    val m1 = Monomial(Coefficient(2, 3), IndexedSeq(0, 1, 0, 2))
    val m2 = Monomial(Coefficient(4, 2), IndexedSeq(2, 3, 0, 0))
    val res = m1 * m2 * m2
    //    println(pp.stringify(res.prv))
    res.eq shouldBe ("2 / 3 * (1 * y^1 * 1 * g()^2) * (4 / 2 * (x^2 * y^3 * 1 * 1)) * (4 / 2 * (x^2 * y^3 * 1 * 1)) =" +
      " 32 / 12 * (x^4 * y^7 * 1 * g()^2)").asFormula
  }

  it should "multiply (again)" in withMathematica { _ =>
    import pa4._
    val pp = new KeYmaeraXPrettierPrinter(100)
    val m1 = Monomial(Coefficient(2, 3), IndexedSeq(0, 1, 0, 2))
    val m2 = Monomial(Coefficient(4, 2), IndexedSeq(2, 3, 0, 0))
    val res = m1 * m2 * m2
    //    println(pp.stringify(res.prv))
    res.eq shouldBe ("2 / 3 * (1 * y^1 * 1 * g()^2) * (4 / 2 * (x^2 * y^3 * 1 * 1)) * (4 / 2 * (x^2 * y^3 * 1 * 1)) =" +
      " 32 / 12 * (x^4 * y^7 * 1 * g()^2)").asFormula
  }

  it should "add" in withMathematica { _ =>
    import pa4._
    val pp = new KeYmaeraXPrettierPrinter(100)
    val m1 = Monomial(Coefficient(2, 3), IndexedSeq(0, 1, 0, 2))
    val m2 = Monomial(Coefficient(4, 2), IndexedSeq(0, 1, 0, 2))
    val res = ((m1 + m2).get + m2).get
    // println(pp.stringify(res.prv))
    res.eq shouldBe ("2 / 3 * (1 * y^1 * 1 * g()^2) + 4 / 2 * (1 * y^1 * 1 * g()^2) + 4 / 2 * (1 * y^1 * 1 * g()^2) =" +
      "56 / 12 * (1 * y^1 * 1 * g()^2)").asFormula
  }

  "powerLemmaCache" should "fill itself" in withMathematica { _ =>
    val res24 = pa4.powerLemmaCache(2, 4)
    res24.conclusion.succ.loneElement shouldBe "x_(||)^2*x_(||)^4=x_(||)^6".asFormula
  }


  "Var" should "be constructed" in withMathematica { _ =>
    import pa4._
    val x = Var(0, 2)
    val x2 = Empty(None) + Monomial(Coefficient(1, 1), IndexedSeq(2, 0, 0, 0), None)
    val y = Var(1, 3)
    val y2 = Empty(None) + Monomial(Coefficient(1, 1), IndexedSeq(0, 3, 0, 0), None)
    x.rhs shouldBe x2.rhs
    y.rhs shouldBe y2.rhs
  }

  "Const" should "be constructed" in withMathematica { _ =>
    import pa4._
    val a = Const(42)
    val a2 = Empty(None) + Monomial(Coefficient(42, 1), IndexedSeq(0, 0, 0, 0), None)
    val b = Const(4, 3)
    val b2 = Empty(None) + Monomial(Coefficient(4, 3), IndexedSeq(0, 0, 0, 0), None)
    a.rhs shouldBe a2.rhs
    b.rhs shouldBe b2.rhs
  }

  "Polynomial" should "cover all cases of add Monomial" in withMathematica { _ =>
    import pa4._
    val pp = new KeYmaeraXPrettierPrinter(100)
    val zero = Empty(None)
    def x(i: Int) = Monomial(Coefficient(1, 1), IndexedSeq(i, 0, 0, 0))
    val res1 = zero + x(2) // insert empty
    res1.treeSketch shouldBe "[., x^2, .]"
    val res2 = res1 + x(4) // sprout in left of 2-Node
    res2.treeSketch shouldBe "{., x^4, ., x^2, .}"
    val res2u = res2 + x(4) // update in left of 3-Node
    res2u.treeSketch shouldBe "{., 2 x^4, ., x^2, .}"
    val res2v = res2u + x(2) // update in right of 3-Node
    res2v.treeSketch shouldBe "{., 2 x^4, ., 2 x^2, .}"
    val res3 = res2v + x(8)  // sprout in left of 3-Node
    res3.treeSketch shouldBe "[[., x^8, .], 2 x^4, [., 2 x^2, .]]"
    val res4 = res3 + x(8) // update value of 2-Node
    res4.treeSketch shouldBe "[[., 2 x^8, .], 2 x^4, [., 2 x^2, .]]"
    val res5 = res4 + x(5) // sprout in right of 2-Node
    res5.treeSketch shouldBe "[{., 2 x^8, ., x^5, .}, 2 x^4, [., 2 x^2, .]]"
    val res6 = res5 + x(2) // stay in right of 2-Node (after an update)
    res6.treeSketch shouldBe "[{., 2 x^8, ., x^5, .}, 2 x^4, [., 3 x^2, .]]"
    val res7 = res6 + x(7) // sprout in mid of 3-Node
    res7.treeSketch shouldBe "{[., 2 x^8, .], x^7, [., x^5, .], 2 x^4, [., 3 x^2, .]}"
    val res8 = res7 + x(8) // stay in left of 3-node (after an update)
    res8.treeSketch shouldBe "{[., 3 x^8, .], x^7, [., x^5, .], 2 x^4, [., 3 x^2, .]}"
    val res9 = res8 + x(5) // stay in mid of 3-node (after an update)
    res9.treeSketch shouldBe "{[., 3 x^8, .], x^7, [., 2 x^5, .], 2 x^4, [., 3 x^2, .]}"
    val res10 = res9 + x(3) // stay in right of 3-node (after a sprout)
    res10.treeSketch shouldBe "{[., 3 x^8, .], x^7, [., 2 x^5, .], 2 x^4, {., x^3, ., 3 x^2, .}}"
    val res11 = res10 + x(1) // sprout in right of 3-node
    res11.treeSketch shouldBe "[[[., 3 x^8, .], x^7, [., 2 x^5, .]], 2 x^4, [[., x^3, .], 3 x^2, [., x^1, .]]]"
  }

  it should "cover all cases of add Polynomial" in withMathematica { _ =>
    import pa4._
    val pp = new KeYmaeraXPrettierPrinter(100)
    def x(i: Int) = Var(0, i)
    def y(i: Int) = Var(1, i)
    val res = y(2) + (x(1) + x(2) + y(1) + y(2) + y(3))
    res.treeSketch shouldBe "{[., x^2, .], x^1, [., y^3, .], 2 y^2, [., y^1, .]}"
  }

  it should "cover all cases of subtract Polynomial" in withMathematica { _ =>
    import pa4._
    val pp = new KeYmaeraXPrettierPrinter(100)
    def x(i: Int) = Var(0, i)
    def y(i: Int) = Var(1, i)
    val res = y(2) - (x(1) - x(2) - y(1) - y(2) - y(3))
    res.treeSketch shouldBe "{[., x^2, .], -x^1, [., y^3, .], 2 y^2, [., y^1, .]}"
  }

  it should "multiply with monomials" in withMathematica { _ =>
    import pa4._
    val pp = new KeYmaeraXPrettierPrinter(100)
    def x(i: Int) = Var(0, i)
    def y(i: Int) = Var(1, i)
    val m = Monomial(Coefficient(3, 4), IndexedSeq(1, 2, 3, 0))
    val res = (x(1) + x(2) + y(1) + y(2) + y(3)) * m
    res.prv.conclusion.succ(0) shouldBe ("(x^1+x^2+y^1+y^2+y^3)*(3/4*(x^1*y^2*f()^3*1))=" +
      "0+3/4*(x^3*y^2*f()^3*1)+0+3/4*(x^2*y^2*f()^3*1)+(0+3/4*(x^1*y^5*f()^3*1)+0)+3/4*(x^1*y^4*f()^3*1)+(0+3/4*(x^1*y^3*f()^3*1)+0)").asFormula
  }

  it should "power" in withMathematica { _ =>
    import pa4._
    val x = Var(0, 1)
    val y = Var(1, 1)
    val pp = new KeYmaeraXPrettierPrinter(100)
    ((x + y)^0).treeSketch shouldBe "[., 1 , .]"
    ((x + y)^1).treeSketch shouldBe "{., x^1, ., y^1, .}"
    ((x + y)^2).treeSketch shouldBe "[[., x^2, .], 2 x^1 y^1, [., y^2, .]]"
    ((x + y)^3).treeSketch shouldBe "[[., x^3, .], 3 x^2 y^1, {., 3 x^1 y^2, ., y^3, .}]"
    ((x + y)^4).treeSketch shouldBe "{[., x^4, .], 4 x^3 y^1, [., 6 x^2 y^2, .], 4 x^1 y^3, [., y^4, .]}"
    ((x + y)^5).treeSketch shouldBe "{[., x^5, .], 5 x^4 y^1, [., 10 x^3 y^2, .], 10 x^2 y^3, {., 5 x^1 y^4, ., y^5, .}}"
    ((x + y)^6).treeSketch shouldBe "[[[., x^6, .], 6 x^5 y^1, [., 15 x^4 y^2, .]], 20 x^3 y^3, [[., 15 x^2 y^4, .], 6 x^1 y^5, [., y^6, .]]]"
  }

  it should "negate" in withMathematica { _ =>
    import pa4._
    def x(i: Int) = Var(0, i)
    val tree = (1 until 10).map(x).reduce(_ + _)
    tree.treeSketch    shouldBe "[{[., x^9, .], x^8, [., x^7, .], x^6, [., x^5, .]}, x^4, [[., x^3, .], x^2, [., x^1, .]]]"
    (-tree).treeSketch shouldBe "[{[., -x^9, .], -x^8, [., -x^7, .], -x^6, [., -x^5, .]}, -x^4, [[., -x^3, .], -x^2, [., -x^1, .]]]"
  }

  it should "subtract Monomials" in withMathematica { _ =>
    import pa4._
    def x(i: Int) = Var(0, i)
    val tree = (1 until 10).map(x).reduce(_ + _)
    val m1 = Monomial(Coefficient(2, 1), IndexedSeq(1, 0, 0, 0))
    val m2 = Monomial(Coefficient(1, 1), IndexedSeq(0, 1, 0, 0))
    println((tree-m1).treeSketch)
    println((tree-m2).treeSketch)

  }
  it should "work with many variables" in withMathematica { _ =>
    import pa20._
    def x(i: Int, p: Int) = Var(i, p)
    val a = (Const(3)*x(19, 2) + Const(5)*x(0, 4) + x(1, 2) + Const(123)*x(10, 3))*(x(17, 1) + x(5, 2) + x(15, 7))
    val b = (x(17, 2) + x(0, 3)*x(15, 4))*(x(0, 1)*x(15,3) + x(3, 2) + x(1, 8))
    a.treeSketch shouldBe "{[[., 5 x0^4 x5^2, .], 5 x0^4 x15^7, [., 5 x0^4 x17^1, .]], x1^2 x5^2, [[., x1^2 x15^7, .], x1^2 x17^1, [., 123 x5^2 x10^3, .]], 3 x5^2 x19^2, [[., 123 x10^3 x15^7, .], 123 x10^3 x17^1, {., 3 x15^7 x19^2, ., 3 x17^1 x19^2, .}]}"
    b.treeSketch shouldBe "{[., x0^4 x15^7, .], x0^3 x1^8 x15^4, [., x0^3 x3^2 x15^4, .], x0^1 x15^3 x17^2, {., x1^8 x17^2, ., x3^2 x17^2, .}}"
  }

  var time = System.nanoTime()
  def tic() = {
    time = System.nanoTime()
  }
  def toc(msg: String) = {
    val t = System.nanoTime()
    println(msg + ": " + (t - time)/1000000000.0 + "s")
    tic()
  }

  "Timing" should "compare multiply with polynomials" taggedAs SlowTest in withMathematica { _ =>
    import pa4._
    def timeMethods(msg: String, eval:()=>Polynomial, skipPA1: Boolean = false) : Polynomial = {
      println(msg)
      val ringsLib = new RingsLibrary(pa4.vars)
      tic()
      val res = eval()
      toc("  Time for PolynomialArithV2                 ")

      PolynomialArith.normalise(res.lhs, true)
      toc("  Time for PolynomialArith(skip_proofs=true) ")

      if(!skipPA1) {
        PolynomialArith.normalise(res.lhs, false)
        toc("  Time for PolynomialArith(skip_proofs=false)")
        PolynomialArith.normalise(res.lhs, false)
        toc("  Time for PolynomialArith(skip_proofs=false)")
      }
      toc("  Time for PolynomialArith(skipped)          ")

      val ringRes = ringsLib.toRing(res.lhs)
      toc("  Time for RingsLibrary (no proofs)          ")

      proveBy(Equal(res.lhs, ringsLib.fromRing(ringRes)), QE & done)
      toc("  Time for RingsLibrary (QE)                 ")

      res
    }

    def x(i: Int) = Var(0, i)
    def y(i: Int) = Var(1, i)
    def f(i: Int) = Var(2, i)
    def g(i: Int) = Var(3, i)
    val res = timeMethods("x + y + f^2 + g^3", () => (x(1) + y(1) + f(2) + g(3)))
    val res2 = timeMethods("...^2", () => res*res)
    val res4 = timeMethods("...^2", () => res2*res2)
    val res8 = timeMethods("...^2", () => res4*res4, true)
  }

  "USubst" should "be faster for (||)" taggedAs SlowTest in withMathematica { _ =>
    /** hypothesis: USubst() is slower, because of USubstOne object creations ->  */
    val t = "1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 * 12 ^ 13 - 15 / 16 + 17 - 18 * 19 + 20".asTerm
    val f = "f_()".asTerm
    val fastTimesIdentity = DerivedAxioms.timesIdentity.fact.apply(USubst(Seq("f_()~>f_(||)".asSubstitutionPair)))
    val n = 100000
    val timesIdentity = DerivedAxioms.timesIdentity.fact
    val s = Plus(t, t)
    val u = Times(s, s)
    val v = Times(u, u)

    tic()
    for (i <- 0 until n)
      SubstitutionPair(f, t)
    toc("SubstitutionPairs")
    for (i <- 0 until n)
      fastTimesIdentity(USubst(Seq(SubstitutionPair(f, v))))
    toc("USubst(||)")
    for (i <- 0 until n)
      timesIdentity(USubst(Seq(SubstitutionPair(f, v))))
    toc("USubst()")
  }
}
