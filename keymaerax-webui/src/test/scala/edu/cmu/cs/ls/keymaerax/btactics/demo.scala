/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.core.{PrettyPrinter, Sequent}
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/** Created by nfulton on 11/3/15. */
class demo extends AnyFlatSpec with Matchers {
  val listener = new IOListener() {
    override def begin(input: BelleValue, expr: BelleExpr): Unit = {}
    override def end(input: BelleValue, expr: BelleExpr, output: Either[BelleValue, Throwable]): Unit = {}
    override def kill(): Unit = ()

  }

  val interp = ExhaustiveSequentialInterpreter(listener :: Nil)

  PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter)

  "usubst style dL tactic" should "work" in {
    val s = Sequent(IndexedSeq("[x:=1;]x>0".asFormula), IndexedSeq("[x:=1;]x>0".asFormula))
    val output = interp(TactixLibrary.monb, BelleProvable.plain(ProvableSig.startPlainProof(s)))
    output match { case BelleProvable(p, _) => () }
  }
}
