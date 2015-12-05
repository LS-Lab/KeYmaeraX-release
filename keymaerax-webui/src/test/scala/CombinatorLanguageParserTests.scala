/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
import edu.cmu.cs.ls.keymaerax.tacticsinterface.CLParser
import org.scalatest.{Matchers, FlatSpec}
import edu.cmu.cs.ls.keymaerax.tacticsinterface._

/**
 * Created by nfulton on 2/26/15.
 */
class CombinatorLanguageParserTests extends FlatSpec with Matchers {
  val c = BuiltInC("c")
  val m = BuiltInC("m")
  val u = BuiltInC("u")

  "CL parser" should "parse c & m & u" in {
    CLParser("c & m & u") match {
      case Some(SeqC(c, SeqC(m,u))) =>
      case Some(x) => fail("incorrect parse: " + x)
      case None => fail("failed parse.")
    }
  }

  it should "parse c && m & u" in {
    CLParser("c && m & u") match {
      case Some(StrongSeqC(c, List(SeqC(m,u)))) =>
      case Some(x) => fail("incorrect parse: " + x)
      case None => fail("failed parse.")
    }
  }

  it should "parse c & m && u" in {
    CLParser("c & m && u") match {
      case Some(SeqC(c, StrongSeqC(m,List(u)))) =>
      case Some(x) => fail("incorrect parse: " + x)
      case None => fail("failed parse.")
    }
  }

  it should "support n-ary strong seq" in {
    CLParser("c && (m,u)") match {
      case Some(StrongSeqC(c, List(m,u))) =>
      case Some(x) => fail("incorrect parse: " + x)
      case None => fail("failed parse.")
    }
  }

  it should "parse c & m(a0)" in {
    CLParser("c & m(a0)") match {
      case Some(SeqC(c, PosApplyC(m, pos))) => pos.isAnte && pos.index == 0 shouldBe true
      case Some(x) => fail("incorrect: " + x)
      case None => fail("failed parse.")
    }
  }

  it should "parse c && m(s0)" in {
    CLParser("c && m(s0)") match {
      case Some(StrongSeqC(c, List(PosApplyC(m, pos)))) => !pos.isAnte && pos.index == 0 shouldBe true
      case Some(x) => fail("incorrect: " + x)
      case None => fail("failed parse.")
    }
  }
}
