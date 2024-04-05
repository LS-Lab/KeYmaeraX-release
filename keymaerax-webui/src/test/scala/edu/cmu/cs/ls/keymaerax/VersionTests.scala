/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax

import edu.cmu.cs.ls.keymaerax.tags.CheckinTest
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * Tests version number parsing and comparisons.
 *
 * @author
 *   Stefan Mitsch
 * @author
 *   Nathan Fulton
 */
@CheckinTest
class VersionTests extends AnyFlatSpec with Matchers {

  /** Valid versions in ascending order. */
  private val versionStrings = List(
    ("0.0.0", Version(0, 0, 0)),
    ("0.0.1", Version(0, 0, 1)),
    ("0.1.0", Version(0, 1, 0)),
    ("0.1.1", Version(0, 1, 1)),
    ("1.0.0", Version(1, 0, 0)),
    ("1.0.1", Version(1, 0, 1)),
    ("1.1.0", Version(1, 1, 0)),
    ("1.1.1", Version(1, 1, 1)),
    ("123.456.7890", Version(123, 456, 7890)),
  )

  private val invalidVersionStrings = List(
    // Too few components
    "4",
    "4.0",
    "4.1",
    "4.2",
    "4.2.",
    // Old letter and incr formats no longer valid
    "4.1a1",
    "4.1a2",
    "4.1a",
    "4.1b",
    "11.33x7",
    // These were never valid
    "4.1a22",
    "4.1a.2",
    "4.1.1a",
    // Leading zeroes not allowed
    "00.1.23",
    "0.01.23",
    "0.1.023",
    // Signs and negative numbers not allowed
    "-0.1.2",
    "0.-1.2",
    "0.1.-2",
    "+0.1.2",
    "0.+1.2",
    "0.1.+2",
    // Number too large, must fit into integer
    "12345678901234567890.2.3",
    "1.23456789012345678901.3",
    "1.2.34567890123456789012",
  )

  behavior of "Version"

  it should "correctly parse valid version strings" in {
    for ((s, v) <- versionStrings) { Version.parse(s) shouldBe v }
  }

  it should "throw exception on invalid version strings" in {
    for (s <- invalidVersionStrings) { assertThrows[IllegalArgumentException] { Version.parse(s) } }
  }

  it should "correctly compare versions" in {
    val versions = versionStrings.map(_._2).zipWithIndex
    for (List((v1, i1), (v2, i2)) <- versions.combinations(2)) { v1.compare(v2) shouldBe i1.compare(i2) }
  }

  it should "preserve version through parsing and formatting" in {
    for ((s, v) <- versionStrings) {
      Version.parse(s).toString shouldBe s
      Version.parse(v.toString) shouldBe v
    }
  }
}
