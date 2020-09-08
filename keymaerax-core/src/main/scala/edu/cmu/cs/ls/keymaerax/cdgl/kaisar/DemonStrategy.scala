package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.KaisarProof.Ident

class DemonException(val msg: String) extends Exception (msg)

trait DemonStrategy[T] {
  def init(): Unit = ()
  def readLoop: Boolean
  def readChoice: Boolean
  def readAssign(x: Ident): T
  def writeAssign(x: Ident, f: T): Unit
}
