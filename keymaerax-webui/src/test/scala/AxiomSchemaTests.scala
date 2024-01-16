/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

import scala.collection.immutable

/**
  * Tests the implementation of axiom schemas.
  *
  * @author Yong Kiam Tan
  */
class AxiomSchemaTests  extends TacticTestBase {

  "Vectorial DG" should "return 1D VDG" in {
    val vdg = Provable.vectorialDG(1)

    vdg._1 shouldBe Symbol("proved")
    vdg._2 shouldBe Symbol("proved")
    vdg._1.conclusion shouldBe "==> [{y__1'=g1(||),c{|y__1|}&q(|y__1|)}]y__1*y__1<=f_(|y__1|)->[{y__1'=g1(||),c{|y__1|}&q(|y__1|)}]p(|y__1|)->[{c{|y__1|}&q(|y__1|)}]p(|y__1|)".asSequent
    vdg._2.conclusion shouldBe "==> [{c{|y__1|}&q(|y__1|)}]p(|y__1|)->[{y__1'=g1(||),c{|y__1|}&q(|y__1|)}]p(|y__1|)".asSequent
  }

  it should "throw core exceptions on out-of-bounds dimension arguments" in {
    an[CoreException] should be thrownBy Provable.vectorialDG(0)
    an[CoreException] should be thrownBy Provable.vectorialDG(-1)
  }

  it should "return a 2D VDG" in {
    val vdg = Provable.vectorialDG(2)

    val y1 = Variable("y_",Some(1))
    val y2 = Variable("y_",Some(2))
    val except = Except(y1::y2:: Nil)
    val code = DifferentialProgramConst("c", except)
    val ppred = UnitPredicational("p", except)
    val qpred = UnitPredicational("q", except)
    val ffunc = UnitFunctional("f_",except,Real)
    val yode1 = AtomicODE(DifferentialSymbol(y1), UnitFunctional("g1",AnyArg,Real))
    val yode2 = AtomicODE(DifferentialSymbol(y2), UnitFunctional("g2",AnyArg,Real))

    val ghostode = ODESystem(DifferentialProduct(yode1,DifferentialProduct(yode2,code)),qpred)

    val f1 = Imply(Box(ghostode, LessEqual(Plus(Times(y1,y1),Times(y2,y2)),ffunc)),
      Imply(Box(ghostode, ppred), Box(ODESystem(code,qpred), ppred)))

    val f2 = Imply(Box(ODESystem(code,qpred), ppred), Box(ghostode, ppred))

    vdg._1 shouldBe Symbol("proved")
    vdg._2 shouldBe Symbol("proved")
    vdg._1.conclusion shouldBe Sequent(immutable.IndexedSeq(), immutable.IndexedSeq(f1))
    vdg._2.conclusion shouldBe Sequent(immutable.IndexedSeq(), immutable.IndexedSeq(f2))

    vdg._1.conclusion shouldBe "==> [{y__1'=g1(||),y__2'=g2(||),c{|y__1,y__2|}&q(|y__1,y__2|)}]y__1*y__1+y__2*y__2<=f_(|y__1,y__2|)->[{y__1'=g1(||),y__2'=g2(||),c{|y__1,y__2|}&q(|y__1,y__2|)}]p(|y__1,y__2|)->[{c{|y__1,y__2|}&q(|y__1,y__2|)}]p(|y__1,y__2|)".asSequent
    vdg._2.conclusion shouldBe "==> [{c{|y__1,y__2|}&q(|y__1,y__2|)}]p(|y__1,y__2|)->[{y__1'=g1(||),y__2'=g2(||),c{|y__1,y__2|}&q(|y__1,y__2|)}]p(|y__1,y__2|)".asSequent
  }

  "Diff Adjoint" should "return 1D diff adjoint" in {
    val da = Provable.diffAdjoint(1)

    println(da)
    da shouldBe Symbol("proved")
    da.conclusion shouldBe "==>  <{x__1'=f__1(x__1)&q_(x__1)}>x__1=y__1<-><{y__1'=-f__1(y__1)&q_(y__1)}>x__1=y__1".asSequent
  }

  it should "throw core exceptions on out-of-bounds dimension arguments" in {
    an[CoreException] should be thrownBy Provable.diffAdjoint(0)
    an[CoreException] should be thrownBy Provable.diffAdjoint(-1)
  }

  it should "return 2D diff adjoint" in {
    val da = Provable.diffAdjoint(2)

    println(da)
    da shouldBe Symbol("proved")
    da.conclusion shouldBe "==>  <{x__1'=f__1(x__1,x__2),x__2'=f__2(x__1,x__2)&q_(x__1,x__2)}>(x__1=y__1&x__2=y__2)<-><{y__1'=-f__1(y__1,y__2),y__2'=-f__2(y__1,y__2)&q_(y__1,y__2)}>(x__1=y__1&x__2=y__2)".asSequent
  }
}
