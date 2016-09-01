/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.core

import edu.cmu.cs.ls.keymaerax.btactics.{RandomFormula, StaticSemanticsTools}
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXParser, KeYmaeraXPrettyPrinter}
import testHelper.KeYmaeraXTestTags.{CheckinTest, SlowTest, SummaryTest, UsualTest}

import scala.collection.{LinearSeqLike, immutable}
import scala.collection.immutable
import scala.collection.immutable._
import scala.collection.mutable
import org.scalatest.{FlatSpec, Matchers, PrivateMethodTester}

/**
 * Tests hash code and some collection expectations such as lookup and adds and removes.
  *
  * @todo more exhaustive tests
 * @author Andre Platzer
 */
class HashTests extends FlatSpec with Matchers {
  PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter.pp)
  val randomTrials = 1000
  val randomComplexity = 30
  val collectionSize = 2*randomTrials
  val rand = new RandomFormula()
  val cp = new RandomReapplyTests

  "Hash code" should "be consistent" in {
    for (i <- 1 to randomTrials) {
      val e = rand.nextExpression(randomComplexity)
      e.hashCode() shouldBe e.hashCode()
      e.hashCode() shouldBe cp.reapplied(e).hashCode
      e shouldBe e
      e shouldBe cp.reapplied(e)
    }
  }

  it should "lookup in hash sets" in {
    test((1 to collectionSize).map(i=>rand.nextExpression(randomComplexity)).to)
  }

  private def test(data: List[Expression]): Unit = {
    val other: List[Expression] = (1 to collectionSize).map(i=>rand.nextExpression(randomComplexity)).
      filter(e => !data.contains(e)).to
    if (other.length != data.length) println("Probabilistic collisions: " + (data.length - other.length))
    val set:HashSet[Expression] = data.to
    test(data, other, set)
    val set2:ListSet[Expression] = data.to
    test(data, other, set2)
    val set3:mutable.HashSet[Expression] = data.to
    testM(data, other, set3)
    val set4:mutable.LinkedHashSet[Expression] = data.to
    testM(data, other, set4)
  }

  private def test(data: List[Expression], other: List[Expression], storage: Set[Expression]): Unit = {
    for (e <- data) storage.contains(e) shouldBe true
    for (e <- other) storage.contains(e) shouldBe false
    val extra = storage++other
    for (e <- data) extra.contains(e) shouldBe true
    for (e <- other) extra.contains(e) shouldBe true
  }

  private def testM(data: List[Expression], other: List[Expression], storage: mutable.Set[Expression]): Unit = {
    for (e <- data) storage.contains(e) shouldBe true
    for (e <- other) storage.contains(e) shouldBe false
    storage ++= other
    for (e <- data) storage.contains(e) shouldBe true
    for (e <- other) storage.contains(e) shouldBe true
  }

  it should "lookup in hash maps" in {
    testmap((1 to collectionSize).map(i=>rand.nextExpression(randomComplexity)).to)
  }

  private def testmap(data: List[Expression]): Unit = {
    val other: List[Expression] = (1 to collectionSize).map(i=>rand.nextExpression(randomComplexity)).
      filter(e => !data.contains(e)).to
    if (other.length != data.length) println("Probabilistic collisions: " + (data.length - other.length))
    val map:Map[Expression,Int] = data.map(e=> (e,e.hashCode())).toMap
    testmap(data, other, map)
    val map2:ListMap[Expression,Int] = ListMap(data.map(e => e -> e.hashCode):_*)
    testmap(data, other, map2)
    val map3:HashMap[Expression,Int] = HashMap(data.map(e => e -> e.hashCode):_*)
    testmap(data, other, map3)
    val map4:mutable.ListMap[Expression,Int] = mutable.ListMap(data.map(e => e -> e.hashCode):_*)
    testmapM(data, other, map4)
    val map5:mutable.HashMap[Expression,Int] = mutable.HashMap(data.map(e => e -> e.hashCode):_*)
    testmapM(data, other, map5)
    val map6:mutable.LinkedHashMap[Expression,Int] = mutable.LinkedHashMap(data.map(e => e -> e.hashCode):_*)
    testmapM(data, other, map6)
  }

  private def testmap(data: List[Expression], other: List[Expression], storage: Map[Expression,Int]): Unit = {
    for (e <- data) {
      storage.contains(e) shouldBe true
      storage.get(e) shouldBe Some(e.hashCode())
    }
    for (e <- other) {
      storage.contains(e) shouldBe false
      storage.get(e) shouldBe None
    }
    val extra = storage ++ other.map(e=> (e,-e.hashCode())).toMap
    for (e <- data) {
      extra.contains(e) shouldBe true
      extra.get(e) shouldBe Some(e.hashCode())
    }
    for (e <- other) {
      extra.contains(e) shouldBe true
      extra.get(e) shouldBe Some(-(e.hashCode()))
    }
  }

  private def testmapM(data: List[Expression], other: List[Expression], storage: mutable.Map[Expression,Int]): Unit = {
    for (e <- data) {
      storage.contains(e) shouldBe true
      storage.get(e) shouldBe Some(e.hashCode())
    }
    for (e <- other) {
      storage.contains(e) shouldBe false
      storage.get(e) shouldBe None
    }
    storage ++= other.map(e=> (e,-e.hashCode())).toMap
    for (e <- data) {
      storage.contains(e) shouldBe true
      storage.get(e) shouldBe Some(e.hashCode())
    }
    for (e <- other) {
      storage.contains(e) shouldBe true
      storage.get(e) shouldBe Some(-(e.hashCode()))
    }
    storage --= other
    for (e <- data) {
      storage.contains(e) shouldBe true
      storage.get(e) shouldBe Some(e.hashCode())
    }
    for (e <- other) {
      storage.contains(e) shouldBe false
      storage.get(e) shouldBe None
    }
  }

  //  ignore should "probably be diagonal" in {
//    testDiagonal((1 to collectionSize).map(i=>rand.nextExpression(randomComplexity)).to)
//  }

//  private def testDiagonal(list: List[Expression]) = {
//    for (i <- 0 until list.length-1)
//      for (j <- 0 until list.length-1)
//        {
//          if (i==j) {
//            list(i).hashCode() shouldBe list(j).hashCode()
//            list(i) shouldBe list(j)
//          } else {
//            //@note this is probably true but not if unlucky
//            list(i) should not be list(j)
//            //@note this could be unlucky for hash collisions
//            list(i).hashCode() should not be list(j).hashCode()
//          }
//        }
//  }
}
