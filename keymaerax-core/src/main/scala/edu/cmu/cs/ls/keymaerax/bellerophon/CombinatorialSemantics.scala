package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.core.Provable

trait CombinatorDefinition extends BelleValue {
  def setGoal(p: Provable) : Unit
  def &&(e: BuiltInTactic) : CombinatorDefinition
}

object CombinatorSemantics {
  var definition : CombinatorDefinition = null
  def &&(e: BuiltInTactic) = definition.&&(e)
}

object SequentialInterpreter extends CombinatorDefinition {
  var value : Provable = null

  override def &&(e: BuiltInTactic): BelleValue = BelleProvable(e.result(value))

  override def setGoal(p: Provable): Unit = this.value = p
}

//object Blah {
//  def asdf = {
//    CombinatorSemantics.definition =
//    import CombinatorSemantics._
//  }
//}


