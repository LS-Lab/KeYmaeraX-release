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

  /** Versions in ascending order. */
  private val versionStrings = List(
    ("4.0", Version(4, 0, -1, None, None)),
    ("4.1a1", Version(4, 1, -1, Some('a'), Some(1))),
    ("4.1a2", Version(4, 1, -1, Some('a'), Some(2))),
    ("4.1a", Version(4, 1, -1, Some('a'), None)),
    ("4.1b", Version(4, 1, -1, Some('b'), None)),
    ("4.1", Version(4, 1, -1, None, None)),
    ("4.1.1", Version(4, 1, 1, None, None)),
    ("4.2", Version(4, 2, -1, None, None)),
    ("11.33x7", Version(11, 33, -1, Some('x'), Some(7))),
    ("11.33.999", Version(11, 33, 999, None, None)),
  )

  private val invalidVersionStrings = List("4", "4.1a22", "4.1a.2", "4.1.1a")

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

  it should "correctly do a few more comparisons" in {
    assert(Version.parse("4.0b1") == Version.parse("4.0b1"))
    assert(Version.parse("4.0b1") >= Version.parse("4.0b1"))
    assert(Version.parse("4.0b1") > Version.parse("4.0a9"))
    assert(Version.parse("5.0") > Version.parse("4.0"))
    assert(Version.parse("4.0") > Version.parse("4.0b9"))
    assert(Version.parse("4.1b1") > Version.parse("4.0b1"))
    assert(Version.parse("4.1b1") >= Version.parse("4.0b1"))
    assert(Version.parse("4.0b1") < Version.parse("4.1b1"))
    assert(!(Version.parse("4.1b1") < Version.parse("4.0b1")))
  }
}
