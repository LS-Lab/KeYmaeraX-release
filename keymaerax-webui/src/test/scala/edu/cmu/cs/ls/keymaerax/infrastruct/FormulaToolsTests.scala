/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.infrastruct

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.FormulaTools._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter
import edu.cmu.cs.ls.keymaerax.parser.StringConverter.StringToStringConverter
import edu.cmu.cs.ls.keymaerax.{Configuration, FileConfiguration}
import org.scalatest.BeforeAndAfterEach
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

class FormulaToolsTests extends AnyFlatSpec with Matchers with BeforeAndAfterEach {

  override protected def beforeEach(): Unit = {
    Configuration.setConfiguration(FileConfiguration)
    PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter.pp)
  }

  "Reassociate" should "rewrite a simple example" in {
    reassociate("(p & q) & r".asFormula) shouldBe "p & (q & r)".asFormula
    reassociate("(p | q) | r".asFormula) shouldBe "p | (q | r)".asFormula
    reassociate("(((p1 & p2) & p3) | q) | r".asFormula) shouldBe "(p1 & p2 & p3) | (q | r)".asFormula
  }

  it should "rewrite reasonably fast" in {
    val n = 10000
    val fml = (0 until n)
      .map(i => PredOf(Function("p", Some(i), Unit, Bool), Nothing))
      .reduceLeft[Formula]({ case (b, f) => And(b, f) })
    val expected = (0 until n)
      .map(i => PredOf(Function("p", Some(i), Unit, Bool), Nothing))
      .reduceRight[Formula]({ case (b, f) => And(b, f) })
    val tic = System.currentTimeMillis()
    reassociate(fml) shouldBe expected
    val toc = System.currentTimeMillis()
//    println("Reassociated in " + (toc - tic) + "ms")
  }

  "DNF" should "rewrite a simple example" in {
    disjunctiveNormalForm("(a|b) & (c|d) & e & f".asFormula) shouldBe "a&c&e&f | a&d&e&f | b&c&e&f | b&d&e&f".asFormula
  }

}
