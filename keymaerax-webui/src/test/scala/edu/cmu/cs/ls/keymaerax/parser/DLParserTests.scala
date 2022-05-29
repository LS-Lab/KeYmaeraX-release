/**
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.bellerophon.LazySequentialInterpreter
import edu.cmu.cs.ls.keymaerax.core.{Formula, Program}
import edu.cmu.cs.ls.keymaerax.tools.KeYmaeraXTool
import edu.cmu.cs.ls.keymaerax.{Configuration, FileConfiguration}
import org.scalamock.scalatest.MockFactory
import org.scalatest.{BeforeAndAfterAll, BeforeAndAfterEach, FlatSpec, Matchers}

import scala.collection.mutable.ListBuffer

/**
 * Tests the DL parser.
 * @author James Gallicchio
 */
class DLParserTests extends FlatSpec with Matchers with BeforeAndAfterEach with BeforeAndAfterAll with MockFactory {

  override def beforeAll(): Unit = {
    Configuration.setConfiguration(FileConfiguration)
    KeYmaeraXTool.init(Map(
      KeYmaeraXTool.INIT_DERIVATION_INFO_REGISTRY -> "true",
      KeYmaeraXTool.INTERPRETER -> LazySequentialInterpreter.getClass.getSimpleName
    ))
  }

  override def afterEach(): Unit = {
    Parser.parser.setAnnotationListener((_, _) => {})
  }

  "DLParser" should "parse multiple invariants" in {
    val annotations = ListBuffer.empty[(Program, Formula)]
    Parser.parser.setAnnotationListener((prg, fml) => annotations.append(prg -> fml))
    val parsed = Parser.parser.programParser(
      """{{x'=v, v'=-g+r*v^2, t'=1 & t<=T & x>=0 & v<0}@invariant(
        |  (v'=-g+a*v^2 -> v-g*(T-t)>-(g/p)^(1/2)),
        |  (v'=-g+p*v^2 -> v>=old(v)-g*t))
        |}""".stripMargin
    )
    annotations.length shouldBe 2
  }

  it should "parse parenthesized" in {
    Parser("(x+1)") shouldBe Parser("x+1")
    Parser("(x>=0)") shouldBe Parser("x>=0")
  }

}