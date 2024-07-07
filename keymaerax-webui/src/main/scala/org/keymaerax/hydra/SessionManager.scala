/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra

import java.security.SecureRandom
import java.util.{Calendar, Date}

import org.keymaerax.Configuration

import scala.annotation.tailrec
import scala.language.postfixOps

object SessionManager {
  type Session = scala.collection.mutable.Map[String, Any]

  private var sessionMap: Map[String, (UserPOJO, Date)] = Map() // Session tokens -> usernames
  private var sessions: Map[String, Session] = Map()
  private[hydra] var defaultUserTokenKey: Option[String] = None

  def token(key: String): SessionToken = sessionMap.get(key) match {
    case Some((user, timeout)) =>
      if (new Date().before(timeout)) { createToken(key, user) }
      else {
        remove(key)
        // on local host, recreate default user token
        if (
          Configuration.getString(Configuration.Keys.USE_DEFAULT_USER).contains("true") &&
          Configuration.contains(Configuration.Keys.DEFAULT_USER)
        ) { createToken(key, user) }
        else NewlyExpiredToken(key)
      }
    case None => EmptyToken()
  }

  /** Creates a token with token `key` representing `user`. */
  private[this] def createToken(key: String, user: UserPOJO): SessionToken = {
    // @HACK need better way of mapping user levels to tokens
    if (user.level == 0 || user.level == 1) ReadWriteToken(key, user.userName)
    else if (user.level == 3) ReadonlyToken(key, user.userName)
    else ???
  }

  def add(user: UserPOJO): String = {
    val sessionToken = generateToken() // @todo generate a proper key.
    sessionMap += sessionToken -> (user, timeoutDate)
    sessions += sessionToken -> scala.collection.mutable.Map()
    sessionToken
  }

  def session(token: SessionToken): Session = token match {
    case ut: UserToken => sessions(ut.token)
    case _ => scala.collection.mutable.Map()
  }

  def remove(key: String): Unit = {
    sessionMap -= key
    sessions -= key
  }

  private def timeoutDate: Date = {
    val c = Calendar.getInstance()
    val expiresIn =
      // local user: sessions don't expire
      if (
        Configuration.getString(Configuration.Keys.USE_DEFAULT_USER).contains("true") &&
        Configuration.contains(Configuration.Keys.DEFAULT_USER)
      ) { Int.MaxValue }
      else 7
    c.add(Calendar.DATE, expiresIn)
    c.getTime
  }

  @tailrec
  private def generateToken(): String = {
    val random: SecureRandom = new SecureRandom()
    val bytes = Array[Byte](20)
    random.nextBytes(bytes)
    val candidate = bytes.toString
    if (sessionMap.contains(candidate)) generateToken() else candidate
  }
}
