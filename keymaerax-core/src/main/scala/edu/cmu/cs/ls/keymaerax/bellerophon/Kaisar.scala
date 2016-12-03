package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.core.{Formula, Program, Variable}

/**
  * Created by bbohrer on 12/2/16.
  */
object Kaisar {
  abstract class Resource
  case class ProgramVariable(a:Variable) extends Resource
  case class FactVariable(p:Variable) extends Resource

  type ProofStep = (List[Resource], BelleExpr)

  abstract class Statement
  case class Run (a:Variable, hp:Program) extends Statement
  case class Show (x:Variable, phi:Formula, proof: ProofStep)

  type Proof = (Formula, List[Statement])

  class History {
    var progs:Seq[Program] = Seq()
    var nextTime:Int = 0
  }

  class Context {
    def concat(other: Context):Context =
      ???
  }
  object Context {
    var empty = new Context()

  }

  def eval(hist: History, ctx: Context, step:Statement):(History,Context) = {
    /* step match */
    ???
  }

  def eval(hist: History, ctx: Context, steps:List[Statement]):(History,Context) = {
    steps match {
      case (Nil) => (hist, Context.empty)
      case (step :: steps) =>
        var AD1 = eval(hist, ctx, step)
        var AD2 = eval(AD1._1, AD1._2, steps)
        (AD2._1, AD1._2.concat(AD2._2))
    }
  }

}
