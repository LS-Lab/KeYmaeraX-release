/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.PosInExpr
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tags.SummaryTest

import scala.collection.immutable._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import TactixLibrary._
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXParser, StringConverter}

/**
 * Automatic Propositional Prover tests.
 * @author Andre Platzer
 */
@SummaryTest
class PropositionalProver extends TacticTestBase  {

  // huntington axioms of boolean algebraic logic
  val propFacts: List[String] = "a()&b() <-> b()&a()" ::
    "a()|b() <-> b()|a()" ::
    "(a()&b())|c() <-> (a()|c()) & (b()|c())" ::
    "(a()|b())&c() <-> (a()&c()) | (b()&c())" ::
    "a()&true <-> a()" ::
    "a()|false <-> a()" ::
    "a()&!a() <-> false" ::
    "a()|!a() <-> true" ::
    // derived laws
    "(a()&b())&c() <-> a()&(b()&c())" ::
    "(a()|b())|c() <-> a()|(b()|c())" ::
    "a()&a() <-> a()" ::
    "a()|a() <-> a()" ::
    "a()|(a()&b()) <-> a()" ::
    "!!a() <-> a()" ::
    "!(a()&b()) <-> !a()|!b()" ::
    "!(a()|b()) <-> !a()&!b()" ::
    "(a()->b()) <-> (!b()->!a())" ::
    "(a()->b()) <-> !a()|b()" ::
    "!(a()->b()) <-> a()&!b()" ::
    "(a()->b()) <-> !(a()&!b())" ::
    "(a()<->b()) <-> (b()<->a())" ::
    "((a()<->b())<->c()) <-> (a()<->(b()<->c()))" ::
    "(a()<->b()) <-> (a()->b())&(b()->a())" ::
    "(a()<->b()) <-> (a()&b())|(!a()&!b())" ::
    "(a()<->b()) <-> (a()|!b())&(!a()|b())" ::
    "(a()&b()->c()) <-> (a()->(b()->c()))" ::
    "!a() <-> (a()->false)" ::
    "!(a()&!a())" ::
    "a()|!a()" ::
    "a()->a()" ::
    "(p()->q())&p() -> q()" ::
    "(p()->q())&!q() -> !p()" ::
    "(p()->q())&(q()->r()) -> (p()->r())" ::
    "(p()|q())&!p() -> q()" ::
    "p()->p()|q()" ::
    "p()&q()->p()" ::
    "a()->(b()->a())" ::
    "(p()->!p())->!p()" ::
    "(p()->(q()->r())) -> (p()&q()->r())" ::
    "(p()->(q()->r())) -> ((p()->q())->(p()->r()))" ::
    "(p()->(p()->q())) -> (p()->q())" ::
    "(p()->(q()->r())) -> (q()->(p()->r()))" ::
    "(!p()->p())->p()" ::
    "(p()->r()) & (q()->s()) -> (p()&q() -> r()&s())" ::
    "p()->(q()->p())" ::
    "p()->!!p()" ::
    "!!p()->p()" ::
    "false->a()" ::
    "(p()->q())|(q()->p())" ::
    Nil

  "prop" should "prove list of simple propositional tautologies" in {
    for (s <- propFacts) {
      val fact = KeYmaeraXParser.formulaParser(s)
      TactixLibrary.proveBy(fact, prop) shouldBe 'proved
    }
  }

}
