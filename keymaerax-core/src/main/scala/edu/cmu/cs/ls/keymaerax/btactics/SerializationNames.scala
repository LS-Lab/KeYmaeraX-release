package edu.cmu.cs.ls.keymaerax.btactics

/**
  * Deprecated but still need to refactor. Migration path is moving everything into DerivationInfo.
  * @author Nathan Fulton
  */
@deprecated("Special case some something we already need, which is now DerivationInfo", "4.2b1")
object SerializationNames {
  trait SerializationName {
    override def toString(): String = this match {
      case cutLName => "cutL"
      case cutRName => "cutR"
      case cutName  => "cut"
      case cutLRName => "cutLR"
    }
  }

  case object cutRName extends SerializationName
  case object cutLName extends SerializationName
  case object cutName  extends SerializationName
  case object cutLRName extends SerializationName
}
