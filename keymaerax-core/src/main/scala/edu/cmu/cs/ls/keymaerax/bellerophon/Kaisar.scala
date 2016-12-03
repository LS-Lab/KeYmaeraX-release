package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.core.{Formula, Program, Variable}

/**
  * Created by bbohrer on 12/2/16.
  */
object Kaisar {
  abstract class Resource
  case class ProgramVariable(a:Variable) extends Resource
  case class FactVariable(p:Variable) extends Resource

  case class ProofStep(using: List[Resource], by: BelleExpr)

  abstract class Statement
  case class Run (a:Variable, hp:Program) extends Statement
  case class Show (x:Variable, phi:Formula, proof: ProofStep)
}
