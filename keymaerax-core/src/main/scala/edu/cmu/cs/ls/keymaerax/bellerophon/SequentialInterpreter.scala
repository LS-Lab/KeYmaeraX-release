package edu.cmu.cs.ls.keymaerax.bellerophon

case class SequentialInterpreter(listeners : Seq[((BelleExpr, BelleValue) => _)] = Seq()) extends Interpreter {
  override def apply(expr: BelleExpr, v: BelleValue): BelleValue = {
    listeners.foreach(f => f(expr, v))
    expr match {
      case builtIn : BuiltInTactic => v match {
        case BelleProvable(provable) => BelleProvable(builtIn(provable))
        case _ => throw BelleError(s"Attempted to apply a built-in tactic to a non-Provable value: ${v.getClass.getName}")
      }
      case BuiltInPositionTactic(_) | BuiltInLeftTactic(_) | BuiltInRightTactic(_) | BuiltInTwoPositionTactic(_) =>
        throw BelleError(s"Need to instantiate position tactic ($expr) before evaluating with top-level interpreter.")
      case SeqTactic(left, right) => {
        val leftResult = apply(left, v)
        apply(right, leftResult)
      }
      case EitherTactic(left, right) => {
        try {
          apply(left, v)
        }
        catch {
          case e : BelleError => apply(right, v)
          case _ => apply(right, v) //@todo Decide if we really want to swallow up all errors.
        }
      }
    }
  }
}