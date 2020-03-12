/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
/**
  * Proof data structures for Kaisar
  * @author Brandon Bohrer
  */
package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import KaisarProof._
import edu.cmu.cs.ls.keymaerax.core._

object KaisarProof {
  type Ident = String
}

sealed trait Method {}
case class RCF() extends Method {}
case class Auto() extends Method {}
case class Prop() extends Method {}

sealed trait ProofTerm {}
case class Var(x: Ident) extends ProofTerm {}

sealed trait Selector {}
case class ForwardSelector(forward: ProofTerm) extends Selector {}

final case class Proof(ss: List[Statement])
final case class Justification(sels: List[Selector], meth: Method)

sealed trait Statement {}

case class Assume(x: Ident, f: Formula) extends Statement
case class Have(x: Ident, f: Formula, just: Justification)
