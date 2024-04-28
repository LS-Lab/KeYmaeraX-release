/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

/**
 * Test Kaisar parsing
 * @TODO:
 *   The tests don't test much automatically yet, mostly useful to step through in debugger
 * @author
 *   Brandon Bohrer
 */
package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase
import edu.cmu.cs.ls.keymaerax.tags.{KaisarTest, UsualTest}
import fastparse._

@KaisarTest @UsualTest
class KaisarKeywordParserTests extends TacticTestBase {
  val whitespaces = List("", " ", "   ", " \n ")

  "whitespace" should "parse" in withMathematica { _ =>
    val parsed = whitespaces.map({ s: String => parse(s, KaisarKeywordParser.ws(_)) })
    parsed
  }

  val idents: List[String] = List("foo", "x", "fooBar")

  "parseable idents" should "parse" in withMathematica { _ =>
    val parsed = idents.map({ s: String => parse(s, KaisarKeywordParser.ident(_)) })
    parsed
  }

  val literals: List[String] = List("\" \"", "\"foo\"", "\"s T r I n g\"")

  "parseable literals" should "parse" in withMathematica { _ =>
    val parsed = literals.map({ s: String => parse(s, KaisarKeywordParser.literal(_)) })
    parsed
  }

  val formulas: List[String] = List("\"x=0\"", "\"(x+y)*z <= 7\"")

  "parseable formulas" should "parse" in withMathematica { _ =>
    val parsed = formulas.map({ s: String => parse(s, KaisarKeywordParser.formula(_)) })
    parsed
  }

  val reserved: List[String] = List("xval", "(xval)", "using", "by")

  "reserved words" should "parse" in withMathematica { _ =>
    val parsed = reserved.map({ s: String => parse(s, KaisarKeywordParser.reserved(_)) })
    parsed
  }

  val proofTerms: List[String] = List("xval", "(xval)", "(xval) by auto")

  "parseable proofTerms" should "parse" in withMathematica { _ =>
    val parsed = proofTerms.map({ s: String => parse(s, KaisarKeywordParser.proofTerm(_)) })
    parsed
  }

  val methods: List[String] = List("by auto", "using (xval) by auto")

  "parseable methods" should "parse" in withMathematica { _ =>
    val parsed = methods.map({ s: String => parse(s, KaisarKeywordParser.method(_)) })
    parsed
  }

  val statements: List[String] =
    List("assume xval:\"x=1\"", " assume xval:\"x=1\"", "have xPos:\"x>0\" using xval by auto")

  "parseable statements" should "parse" in withMathematica { _ =>
    val parsed = statements.map({ s: String => parse(s, KaisarKeywordParser.statement(_)) })
    parsed
  }

  val proofs: List[String] = List(
    s""" assume xval:"x=1"
       | have xPos:"x>0" using xval by auto""".stripMargin
  )

  "parseable proofs" should "parse" in withMathematica { _ =>
    val parsed = proofs.map({ s: String => parse(s, KaisarKeywordParser.proof(_)) })
    parsed
  }
}
