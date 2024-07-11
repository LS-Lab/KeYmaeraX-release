/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra

import java.security.SecureRandom
import javax.crypto.SecretKeyFactory
import javax.crypto.spec.PBEKeySpec

import javax.crypto.SecretKeyFactory
import javax.crypto.spec.PBEKeySpec

/**
 * Password generation and checking using PBKDF2. Based on security advice from OWASP web security project.
 * @see
 *   www.owasp.org Created by bbohrer on 12/29/15.
 */
object Password {
  /* Make a basic effort to confound timing attacks based on short-circuiting string comparisons. This is the
   * recommended algorithm for comparing strings in a way that will never short-circuit, regardless of compiler
   * optimizations. */
  def hashEquals(str1: String, str2: String): Boolean = {
    if (str1.length != str2.length) return false

    var acc = 0
    for (i <- str1.indices) { acc |= str1(i) ^ str2(i) }
    acc == 0
  }

  /* SQLite tragically won't read string values past a NUL byte. The SQLite solution to this is using BLOB instead,
   * which the Scala driver does not support. To get around this, make sure we only store NUL-free strings, it this
   * case by base-64 encoding them. Since base-conversions preserve entropy, this *shouldn't* damage the quality of
   * our passwords.*/
  def sanitize(s: Array[Byte]): String = java.util.Base64.getEncoder.encodeToString(s)

  def hash(password: Array[Char], salt: Array[Byte], iterations: Int): String = {
    val spec = new PBEKeySpec(password, salt, iterations, Math.min(160, salt.length * 8))
    val skf = SecretKeyFactory.getInstance("PBKDF2WithHmacSHA1")
    sanitize(skf.generateSecret(spec).getEncoded)
  }

  def generateSalt(length: Int): String = {
    val saltBuf = new Array[Byte](length)
    val rng = new SecureRandom()
    rng.nextBytes(saltBuf)
    sanitize(saltBuf)
  }

  def generateKey(password: String, iterations: Int, saltLength: Int): (String, String) = {
    val salt = generateSalt(saltLength)
    val hash = this.hash(password.toCharArray, salt.getBytes("UTF-8"), iterations)
    (hash, salt)
  }
}
