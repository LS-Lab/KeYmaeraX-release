/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.tools

import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tools.qe.DefaultSMTConverter
import edu.cmu.cs.ls.keymaerax.{Configuration, FileConfiguration}
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import org.scalatest.{BeforeAndAfterAll, BeforeAndAfterEach}

/**
 * Created by ran on 3/23/15.
 * @author
 *   Ran Ji
 */
class SMTConversionTests extends AnyFlatSpec with Matchers with BeforeAndAfterEach with BeforeAndAfterAll {

  override def beforeAll(): Unit = {
    Configuration.setConfiguration(FileConfiguration)
    KeYmaeraXTool.init(interpreter = KeYmaeraXTool.InterpreterChoice.LazySequential, initDerivationInfoRegistry = false)
  }

  override def afterAll(): Unit = { KeYmaeraXTool.shutdown() }

  private lazy val converter = DefaultSMTConverter

  "Numbers" should "convert numbers" in {
    converter("1 > 2".asFormula) shouldBe "(assert (not (> 1 2)))\n(check-sat)\n"
  }

  it should "convert legal big positive numbers" in {
    converter("9223372036854775807 > 1".asFormula) shouldBe "(assert (not (> 9223372036854775807 1)))\n(check-sat)\n"
  }

  it should "convert legal big negative numbers" in {
    converter("-9223372036854775807 < 1".asFormula) shouldBe
      "(assert (not (< (- 9223372036854775807) 1)))\n(check-sat)\n"
  }

  it should "throw exception in converting illegal big positive numbers" in {
    a[ConversionException] should be thrownBy converter("9223372036854775808 > 1".asFormula)
  }

  it should "throw exception in converting illegal big negative numbers" in {
    a[ConversionException] should be thrownBy converter("-9223372036854775808 < 1".asFormula)
  }

  "Variables" should "convert numbers" in {
    converter("x > 2".asFormula) shouldBe "(declare-fun _v_x () Real)\n(assert (not (> _v_x 2)))\n(check-sat)\n"
  }

  it should "convert numbers complex" in {
    converter("x > 2 & y < 3".asFormula) shouldBe
      """(declare-fun _v_x () Real)
        |(declare-fun _v_y () Real)
        |(assert (not (and (> _v_x 2) (< _v_y 3))))
        |(check-sat)
        |""".stripMargin
  }

  it should "convert numbers const" in {
    converter("x > a & y < x".asFormula) shouldBe
      """(declare-fun _v_a () Real)
        |(declare-fun _v_x () Real)
        |(declare-fun _v_y () Real)
        |(assert (not (and (> _v_x _v_a) (< _v_y _v_x))))
        |(check-sat)
        |""".stripMargin
  }

  "Constant function" should "convert" in {
    converter("g() > 0".asFormula) shouldBe "(declare-fun _f_g () Real)\n(assert (not (> _f_g 0)))\n(check-sat)\n"
  }

  "Quantifiers" should "convert forall" in {
    converter("\\forall x x>y()".asFormula) shouldBe
      """(declare-fun _v_x () Real)
        |(declare-fun _f_y () Real)
        |(assert (not (forall ((_v_x Real)) (> _v_x _f_y))))
        |(check-sat)
        |""".stripMargin
  }

  it should "convert exists" in {
    converter("\\exists x x>y()".asFormula) shouldBe
      """(declare-fun _v_x () Real)
        |(declare-fun _f_y () Real)
        |(assert (not (exists ((_v_x Real)) (> _v_x _f_y))))
        |(check-sat)
        |""".stripMargin
  }

  it should "convert nested qutifiers" in {
    converter("\\forall x \\exists y x>y".asFormula) shouldBe
      """(declare-fun _v_x () Real)
        |(declare-fun _v_y () Real)
        |(assert (not (forall ((_v_x Real)) (exists ((_v_y Real)) (> _v_x _v_y)))))
        |(check-sat)
        |""".stripMargin
  }

  it should "convert complex quantifiers" in {
    converter("\\forall x \\forall y \\exists z x^2+y^2=z^2".asFormula) shouldBe
      """(declare-fun _v_x () Real)
        |(declare-fun _v_y () Real)
        |(declare-fun _v_z () Real)
        |(assert (not (forall ((_v_x Real) (_v_y Real)) (exists ((_v_z Real)) (= (+ (^ _v_x 2) (^ _v_y 2)) (^ _v_z 2))))))
        |(check-sat)
        |""".stripMargin
  }

  "Exponentials" should "convert positive" in {
    converter("3^3 > 1".asFormula) shouldBe "(assert (not (> (^ 3 3) 1)))\n(check-sat)\n"
  }

  it should "convert negative" in {
    converter("3^-2 < 1".asFormula) shouldBe "(assert (not (< (^ 3 (- 2)) 1)))\n(check-sat)\n"
  }

  it should "convert index 0" in {
    converter("(x+y-z)^(1-1) = 1".asFormula) shouldBe
      "(declare-fun _v_x () Real)\n(declare-fun _v_y () Real)\n(declare-fun _v_z () Real)\n(assert (not (= (^ (- (+ _v_x _v_y) _v_z) (- 1 1)) 1)))\n(check-sat)\n"
  }

  it should "convert base 0" in {
    converter("(0+0)^(x+y-1) = 1".asFormula) shouldBe
      "(declare-fun _v_x () Real)\n(declare-fun _v_y () Real)\n(assert (not (= (^ (+ 0 0) (- (+ _v_x _v_y) 1)) 1)))\n(check-sat)\n"
  }

  it should "convert fractions" in {
    converter("3^(-0.5) < 1".asFormula) shouldBe "(assert (not (< (^ 3 (- 0.5)) 1)))\n(check-sat)\n"
  }

  it should "convert complex" in {
    converter("(x+y-z)^3 = 1".asFormula) shouldBe
      """(declare-fun _v_x () Real)
        |(declare-fun _v_y () Real)
        |(declare-fun _v_z () Real)
        |(assert (not (= (^ (- (+ _v_x _v_y) _v_z) 3) 1)))
        |(check-sat)
        |""".stripMargin
  }

  it should "convert complex 2" in {
    converter("(x+x+x)^3 = 1".asFormula) shouldBe
      """(declare-fun _v_x () Real)
        |(assert (not (= (^ (+ (+ _v_x _v_x) _v_x) 3) 1)))
        |(check-sat)
        |""".stripMargin
  }

  it should "convert complex 3" in {
    converter("(x+y-z)^(y*2-y-y+3) = 1".asFormula) shouldBe
      """(declare-fun _v_x () Real)
        |(declare-fun _v_y () Real)
        |(declare-fun _v_z () Real)
        |(assert (not (= (^ (- (+ _v_x _v_y) _v_z) (+ (- (- (* _v_y 2) _v_y) _v_y) 3)) 1)))
        |(check-sat)
        |""".stripMargin
  }

  it should "convert bouncing ball" in {
    converter(
      "c<1 & c>=0 & H>=0 & g>0 & v^2<=2*g*(H-h) & h>=0 & kxtime_1=0 & h_2=h & v_2=v & kxtime_4=kxtime_1 & v_3=-1*kxtime_5*g+v_2 & h_3=1/2*(-1*kxtime_5^2*g+2*h_2+2*kxtime_5*v_2) & h_3>=0 & kxtime_5>=kxtime_4 & h_3=0 & v_5=-c*v_3 -> v_5^2<=2*g*(H-h_3)"
        .asFormula
    ) shouldBe
      """(declare-fun _v_H () Real)
        |(declare-fun _v_c () Real)
        |(declare-fun _v_g () Real)
        |(declare-fun _v_h () Real)
        |(declare-fun _v_h_2 () Real)
        |(declare-fun _v_h_3 () Real)
        |(declare-fun _v_kxtime_1 () Real)
        |(declare-fun _v_kxtime_4 () Real)
        |(declare-fun _v_kxtime_5 () Real)
        |(declare-fun _v_v () Real)
        |(declare-fun _v_v_2 () Real)
        |(declare-fun _v_v_3 () Real)
        |(declare-fun _v_v_5 () Real)
        |(assert (not (=> (and (< _v_c 1) (and (>= _v_c 0) (and (>= _v_H 0) (and (> _v_g 0) (and (<= (^ _v_v 2) (* (* 2 _v_g) (- _v_H _v_h))) (and (>= _v_h 0) (and (= _v_kxtime_1 0) (and (= _v_h_2 _v_h) (and (= _v_v_2 _v_v) (and (= _v_kxtime_4 _v_kxtime_1) (and (= _v_v_3 (+ (- (* (* 1 _v_kxtime_5) _v_g)) _v_v_2)) (and (= _v_h_3 (* (/ 1 2) (+ (+ (- (* (* 1 (^ _v_kxtime_5 2)) _v_g)) (* 2 _v_h_2)) (* (* 2 _v_kxtime_5) _v_v_2)))) (and (>= _v_h_3 0) (and (>= _v_kxtime_5 _v_kxtime_4) (and (= _v_h_3 0) (= _v_v_5 (- (* _v_c _v_v_3)))))))))))))))))) (<= (^ _v_v_5 2) (* (* 2 _v_g) (- _v_H _v_h_3))))))
        |(check-sat)
        |""".stripMargin
  }

  it should "convert bouncing ball constfun" in {
    converter(
      "c<1 & c>=0 & H>=0 & g()>0 & v^2<=2*g()*(H-h) & h>=0 & kxtime_1=0 & h_2()=h & v_2()=v & kxtime_4()=kxtime_1 & v_3=-1*kxtime_5*g()+v_2() & h_3=1/2*(-1*kxtime_5^2*g()+2*h_2()+2*kxtime_5*v_2()) & h_3>=0 & kxtime_5>=kxtime_4() & h_3=0 & v_5=-c*v_3 -> v_5^2<=2*g()*(H-h_3)"
        .asFormula
    ) shouldBe
      """(declare-fun _v_H () Real)
        |(declare-fun _v_c () Real)
        |(declare-fun _f_g () Real)
        |(declare-fun _v_h () Real)
        |(declare-fun _f_h_2 () Real)
        |(declare-fun _v_h_3 () Real)
        |(declare-fun _v_kxtime_1 () Real)
        |(declare-fun _f_kxtime_4 () Real)
        |(declare-fun _v_kxtime_5 () Real)
        |(declare-fun _v_v () Real)
        |(declare-fun _f_v_2 () Real)
        |(declare-fun _v_v_3 () Real)
        |(declare-fun _v_v_5 () Real)
        |(assert (not (=> (and (< _v_c 1) (and (>= _v_c 0) (and (>= _v_H 0) (and (> _f_g 0) (and (<= (^ _v_v 2) (* (* 2 _f_g) (- _v_H _v_h))) (and (>= _v_h 0) (and (= _v_kxtime_1 0) (and (= _f_h_2 _v_h) (and (= _f_v_2 _v_v) (and (= _f_kxtime_4 _v_kxtime_1) (and (= _v_v_3 (+ (- (* (* 1 _v_kxtime_5) _f_g)) _f_v_2)) (and (= _v_h_3 (* (/ 1 2) (+ (+ (- (* (* 1 (^ _v_kxtime_5 2)) _f_g)) (* 2 _f_h_2)) (* (* 2 _v_kxtime_5) _f_v_2)))) (and (>= _v_h_3 0) (and (>= _v_kxtime_5 _f_kxtime_4) (and (= _v_h_3 0) (= _v_v_5 (- (* _v_c _v_v_3)))))))))))))))))) (<= (^ _v_v_5 2) (* (* 2 _f_g) (- _v_H _v_h_3))))))
        |(check-sat)
        |""".stripMargin
  }
}
