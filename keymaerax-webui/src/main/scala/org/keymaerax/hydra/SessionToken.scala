/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra

/** @note a custom Option so that Scala doesn't use None as an implicit parameter. */
trait SessionToken {
  def isLoggedIn: Boolean = this.isInstanceOf[UserToken]

  def belongsTo(uname: String): Boolean = this match {
    case ut: UserToken => ut.username == uname
    case _: EmptyToken => false
  }

  def tokenString: String = this match {
    case ut: UserToken => ut.token
    case NewlyExpiredToken(t) => t
    case _ => ""
  }
}
abstract class UserToken(val token: String, val username: String) extends SessionToken
case class NewlyExpiredToken(token: String) extends SessionToken
case class ReadWriteToken(override val token: String, override val username: String) extends UserToken(token, username)
case class ReadonlyToken(override val token: String, override val username: String) extends UserToken(token, username)
case class EmptyToken() extends SessionToken
