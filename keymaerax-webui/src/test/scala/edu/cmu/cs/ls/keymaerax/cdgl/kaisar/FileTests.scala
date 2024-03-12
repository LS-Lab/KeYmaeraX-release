/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import edu.cmu.cs.ls.keymaerax.btactics.{Integrator, RandomFormula, TacticTestBase}
import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.KaisarProof._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.RandomParserTests
import edu.cmu.cs.ls.keymaerax.tags._
import fastparse.Parsed.{Failure, Success}
import fastparse._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

class FileTests extends TacticTestBase {
  val check: String => Unit = { s =>
    ProofOptions.proofText = Some(s)
    val decls = KaisarProgramParser.parseProof(s)
    FileChecker(decls)
  }

  "file checker" should "check simple proof " in withMathematica { _ =>
    val pfStr =
      "proof thm begin ?xZero:(x >= 1); {{x := x + 1; !IS:(x >= 1) using x xZero by auto;}*} !xFin:(x>=0) using xZero by auto; end"
    check(pfStr)
  }

  it should "refine trivial proof" in withMathematica { _ =>
    val pfStr = {
      """
        |let game ::= { x := 0; };
        |proof example begin
        | x := 0;
        |end
        |proves example ([game;]true) ;
        |"""
    }.stripMargin
    check(pfStr)
  }

}
