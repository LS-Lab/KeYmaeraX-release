package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.KaisarProof.Ident

trait DemonStrategy[T] {
  def readLoop: Boolean
  def readChoice: Boolean
  def readAssign(x: Ident): T
  def writeAssign(x: Ident, f: T): Unit
}
