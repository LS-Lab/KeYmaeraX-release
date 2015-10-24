package edu.cmu.cs.ls.keymaerax.bellerophon

class SequentialInterpreter(listeners : Set[((BelleExpr, BelleValue) => _)] = Set()) extends Interpreter {
  override def apply(expr: BelleExpr, v: BelleValue): BelleValue = {
    listeners.foreach(f => f(expr, v))
    expr match {
      case builtIn : BuiltInTactic => v match {
        case BelleProvable(provable) => BelleProvable(builtIn(provable))
        case _ => throw BelleError(s"Attempted to apply a built-in tactic to a non-Provable value: ${v.getClass.getName}")
      }
      case builtIn : BuiltInPosTactic => v match {
        case BelleProvable(provable) => BelleProvable(builtIn(provable, ???))
        case _ => throw BelleError(s"Attempted to apply a built-in tactic to a non-Provable value: ${v.getClass.getName}")
      }
    }
  }
}